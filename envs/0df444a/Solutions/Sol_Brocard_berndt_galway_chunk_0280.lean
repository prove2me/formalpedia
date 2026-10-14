-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:56:34.270731+00:00
-- url     : https://prove2.me/submissions/5e499a4c-5fc4-42f4-98c6-40acd76b04fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50179860 ≤ n < 50359716 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50181110 1250 50179860 50179873
    0x1305030f060c07030513030f0201090801020418150503011103070e030d1403060a030c0b0702011d0f01081308030a050601120905030414030a0c0b070b10062c100513090e 74
    0xb19002d596400c140d004030100300040100c403000100c4104802d0040d8030400400c1c40304041440007414441c0e1035088008260302c10301c81004a011007001000020404c03420000b0103454030071403441280056040541c0540c2404910f540c0202d1031401948204080d503600202980d1110805860340329003d4954005850489441c80c1602d095009503007240740201640a420758030382d24008001180d5005c0c40504101040350003d550300209042002d80e5400c44038544002442c00203882d1810400b402810000d00304000340210080b0b69180500640000d8001d4591514480078005800d08442d40b0b4006801c1c0d6441c00001e0f4424040c0e03003a45079021015605207030a1815007208046515a00c41c0c0c54030560b800b44002c11404801c58001d0443e12011550300d8920303050a1440540180c01003075102140f207820012650301039003080000e42d448406ea0303c44d540c03d841d050000e150165110f035021100302c1400e82003580190080c9440d0307607544010900d85650781c1d070110440701c0001400c0b800342c0080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50182360 1250 50181110 50181121
    0x306101805091b010c020907111203060604120f14010f0b1207051903060f02120c04060203031302150307020a06111e0d020c070b04051306060c030c050705040f021305030f06 76
    0x643c04658000010314011a0303550480c0c0004001810903201040410b0583c4c00a1580f0343c3c0030300410003450401d41c1c2c00b6165042c500c0208503948035601c40c400d5541d0380303095400104021030f06c0b61030303040341c1101402d0411912600744a001f403007281ca103042c490b4501444281c0310300b085015013500161000c0034060141c948818843d02e003000010010241440350000b0000402034800c5158658101200607110f20000d201d021002c840542102180c180c144000c125442c0c0c000b007200c0e4807908992291010b00500d1020840485000000203480c2e0307404810000300300e0b400119040c86900a40040c04200c80c556119441c41c072516003880300003400008400c0d00d488000f070040140c801e1182e0014a03103040c212410b424610a90000d8201510002d030030052454031030301401d200040c00a0410030b02d880c04902500c48020503c009041c0036011203980240202482100010100640280075006009441c20000c0d13001003501d0380342c00e9070381d4404240e40c1800262048030346050f000800442c1c030703107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50183610 1250 50182360 50182393
    0x1f08010b100f1d0f030114010f0509060303040303030c03200d0c110304060509030a0c080f060f0106120b0d080c03040303091205030f0d020d06061e0f020d050904020702030610180509 80
    0x41100701074100d100c0410525040c0c90910840c141c084c075a1f00750031810750400141d0710300440c007540a6803040355100280f10b03266502004480480c2c0c0c4c14100010181c0070b03002d00382c2c043c013420b8440001c042002095801d1060b40d2200501004480c00401c00040042e09405c0d43d18106181540900ea807040c071051000034000c0000b00340c090401400c40d4051800f42c1e807054041441c0c0d4002180c1038110550120246e2410001690448035490456543d581020300c014100c030b101801e40a0507030f46070007000c251a1038800b04001c2c81c81c0c00c8800940d4032610942115540d80c03182c4007c80007c0c042c41c1740040c618425045481d0b1040e4003034061460421420712031041604102900c1d440c259080001c5140c2c81050311078000241201d85a03844840020100203086520302c015250900192900c035501075076001c1140300c1008149c7c1415903e030344004020400034011403e0080d014400d001c240062806062034540440d211000d04004040d8510901000da960039103001003964010703900005190301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50184860 1250 50183610 50183657
    0x403050418020f030c07120203071a130605150102160b0a0302130906031115070b06100203130b1b03040b0f07060b040c08060f010f020303040204051f08010b100f 71
    0x3407080058100724900703814100a510984003090400c1c00041c1030b804201c0440c2034400022101d0010358209078840d2640c0400e003001e1084608400e034028005509000140c0d408103086801c0f010821080ca480e4607021007041c0d506501502511851106200240c0e00d41e40c090103860344a8075446c28490084d8040c2c02a41042c0b05107c1300c0700c042c0501150308205803040100460050780240320402910003400380161a074a10640034407030800880010501107140241c210505480761111001d086008074154020b100e14225a550000000550120020045d001020384440340c0c49110703018104543d940d105034402d2410402040c400c0f0003071b41100001521940307000386d6012406000341c40006044580d4903214801003000b20040c807105050681c618800f40710b0030300306507040c420b450784069034902005100910568071880001c00081c4030104002c4881504000c03100a2500c42c1011406001003079407aa02a944400e03501201034490021a00108020b8441083d0304082c404007664004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50186110 1250 50184860 50184899
    0x3080c21060a1205030a030c110606220c08010f0603050f01090b0406090905030a080a0b18060607060603080c010e06060a030303020c0708070f230306070503150604030c1d04030504 79
    0x59411030002501d42c1c020403d5403000c0d20490240d580d41194000241c11030f040d40c614482003100c803030f0500d40d040305d0000d000303904444101d0310f03100410003441100c100340d1030016441001c07604008289041c240c11507903080c1603490223040c0704034264070f41c1e4044085aa0440302401540d01c890010401c0300910391083e28a40c00c040d20104005440d0341100003981c4a120007240e0355440000c0310450306d544408415045621454280400d07000f01e400101d4040080d84910020080703040481d07150b80e5048115840e03d5401682488603560303038140900c850304040120151542864055180d04a020590314480c0000070580c0c262503083d500d00320001d4001e40421440d07440b40904c0031890315410400d0000400f41014506881401c213200b000c00c1085040394149080740c10007440101d55030101c3c816600c0903461511940740d54854215100b00c014403c482da40003400000c001c014800186d403170703605036104c0ba110400754034491800030341e10720f108031070140000f8020f00c001c1c04000c115030301c0381140340c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50187360 1250 50186110 50186119
    0xb060c0a0b1308030106080105010806010201150902090103150602010207230d122004052803020d05070306050108030909060306040c1517090109031e0e220203040c0303080c2106 78
    0x12950750f20005941e00a800690110340f0050042005685c040241544800288001d02a07000800d0341c0765013070286800303041d01803900400c0740301c0140d00c130354420921800148108604942c3d2080064000e5105600039101d03070700e0409030381940d11260317003803c19400302010092a10090420080f10f0540141074401001a1250b10900005505403d0718046000d5840c5080c0c1e241d02c2d05040100c0a10101c40c440001810210907401200c42c0a451000b104c0e019501c182c0c07001d40501e861030904400750401005540741c48000b00303c0032000009403031700910a81d160359841d1501e00c1010740e10f8500311002485001501c2e018001c81c1a162502e101d910000d05044020800030440703407101e031808a5180c14160b55550503a024140e0255404e4000c5e4210301500b601c0b07500824005000c3c42403001401e014800c0d4088802c00198912448001482c0a41d002c5440c0d0030309107803440d44203506200c00d8000a46d04008030700711745404400c0340c1c0c100d1318001075500000c0c041205d08075020030041170745511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50188610 1250 50187360 50187391
    0x1606030b01180e190c0e0a080d05120612060103060c030501050a0503061504021b0a020301060b030f04060903050d090605060a090c0c060e07030203070b0715060b0904090609060615030b060c0a0b 85
    0x40b62413902a000c4403840c281c0399003041ea44400c3c02d2014042d15a400000c4d80d600842800c0c01480d082011201c20b890307001c1591a0556614002c90509a00c10f2074002052052900020a01605a100c02087d00942d039043c4030383e0f40d031031040148208480c054203034035400c064041200c0c403111507044c2c444a10080c1001d4101100c804400028682e0b10a465180780c00000401c01185400c0c424400600443d0581d80c0c1141480c400d07810105070001c2009085035503919201003414004e1080d6103020b001e142050140f82194500140601825120a0300841203c038020582c20310a002d048141601c07035070ba1000724403440d110b41c07003d809081100215402040b4001c80035031002c2c4580006418000700e903940c0c03074110385009007103040c0720034244403417615042d0140840d60340718040342e2489034100c034045500c01d84d9090190080c900344100070031091501400048030207d5a2021251110548013080442c8041c01806002e200d00c0003c41c0301500840c04000024030708000305074000c002040740c1000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50189860 1250 50188610 50188651
    0x9050907090302150d0506040603120c1704241106060d170406050c070f050102060a0e0f0616020f0a080d111b03040f05221d1606030b01180e 62
    0x201c20398044e2403a0a0440080c140b81400464054950400c40c00d45e02003000901e5610351000304412b640c540b0041049014402003400300109402080a0002c1c080c01d40e05d941d80c11400390704034040d10018100500382d40f4411007090281199442e200e40360000703013110b80d44010401c400c00c40e0300c4408850340d00700c541c1d41869100c21580500f0140156860b402d035a80c41e000c0c50945011070542c40803242075031800c1d00b4042ca90f80420300c1504441d185402190340d09050211505100c0c44200380001d41c441c8038108824283d025101e000c0301142c50302035902030000c0c1d1284030703100c8802d54405041c86000b0030040d210001646d00c00101080900503035402c0140181c10428102c3c1c0310080281c05500c0403070140400c000704840d880045c0070440c1d20840c01c0e80268603c42c04141c1000941c641c943c1c0d1032005c0090902c000d5585140c140310141668403425130740c00d80b00b40e40b0309240070f2200004d150403000307121940503860010a00902d00300c2c0d000c0d003500e4144245c502c010003c004601003e0b50105890 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50191110 1250 50189860 50189869
    0x10908040b0307080105030d0f080c070609050a0312111606060e0a020304060513050a0201030506040b0a0f080f010b0607080a091a0a02010b01050f0909150604061206080c0109050907090302 83
    0x905800c0c9400703503581c2455403000f000260107811007803003074112003035188c0000e802008400c81110541840300c4c040c2d40e01304c202007540c050310801400007400c2811075020060042219000c11344261105154881e0080301d00003200c11712540d9000c030071401c2003405503107507400114140c0f951007400f0200b03030b15882c0c8804582c50b030020703100303014050340100a2008210482c02420b41c041040c10142c1101185915038503520703006540060f0515130f85802150043d103464225072080c0310003505070403016550320541207085540e1700c107c4040b409800920312008406004040c0305445c003e10315802c1420641b24030309543c2c407442800781804510030000a60204601a0441d92401c42d0031440c0c40c0c02c982d000103801c1d1035907464158108041003007217524401d6010252000714000b07548020180c0d030b60614102c000100c0c1815168480004200081d00c1070748004041180e05440e9003e00120390b9501c4516078a881c82c02c5a5408107213116020300450826012141e80800d00e07140c03400040e0354070740115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50192360 1250 50191110 50191117
    0x4020403051606030b030a02011704061b0e01030e160302010f050c060a0b090916090b0d050124150906030f021303030203031506040305070302010f21050f070503090c01030e010908 79
    0x302c059030b01c0303900400c031294141c401c44140340c1c8103034003921005140703500090003082c4050f0400d419000b044041001d001d00e540c170255040380d145141034018541514064990384d20703040500d0020b4140302c01c01d54030240108030329500e1040a4842008542154015620a000940302d181000018443d548402404000c2070b40a0680c04500244101e00c2c94140b02d401000103200400fa42e020140706541c0c801e90455503411500d40c0c4400041e015079500000302480454a00908150b003000d40188118201c0302204002e058080b040d61042581c3e5034122820101e103054000c0480c030140b4041280c3d81c080d80001010812503500141b41c001981c8a0148400b100e03041a401030340044100596500d24802c14a0700b000304484040c246851541c4940e901d58050000074104001d5075808108940115462480c0c03405100d02103803880203416035003000702411206202a500d0072008503034a14040d000b200e001d0b00e034080c080e01d0072403000c8006601405e00b5602d00d001e1590303201c0018002c07a4403075015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50193610 1250 50192360 50192383
    0x4020d021206190f05070e060a090914090706020a0f060506150d140117030d0c05040b030a021c0207020d120e030102070302010614042304110a0801020d050c0322020402040305 77
    0x103000c10801c4450f08001103941445111412516000c20b209409070440d00d910310b142800c84e807481e91165200e0341200c8100705a03120003020703824a5041600c002d1010314542c42400f02c00c00301c40e521555084120781d61920321402600c0140d032119480301040c0d0076080303981d00003c0904040e1280c18045c2164010340e0024000320302c03540d0340700e503c000f003406504042c1e80104942219404c6c40035001800645030b2240038040a9541e607184165901070b401102a00d004000c0003203001e40f81e240a4050001a5111588080081580d00c1038003e00f21203e100f640d4038550080d0544031519080c0d5541004500f00302c085005000118410060a5400340000c20540d8407942c00820b100d843d040311003610005100003503200b2410030031402d4920842201130a00d0070b00402031000da64441e410039030658195811881d412001603000400c1549054004103000160034a08220f2035480d60000c0845000c142c0d0030b000c0101e4078001c0c002c0e00b10140f4405804003400188018070341592a40c52503e007500c40c40c0b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50194860 1250 50193610 50193631
    0x803041e170d0b010216050603041110091a04030c030b07031116050610050904080a050d02040306061d10090207050313030606050102070902030c09060a020a020310020315040209030604020d021206 86
    0x1040200c02d521070240d403421403c207000500070702280402d82040b0b0209030059900560000c000201800160101c400e144034001d020311480225040c0028010380060180724000401f034800d80b4070040c4141e00300ca08594000c2e01036121307182141d483c260040e0010700300f00200f5890314406041401c2803002410490783c0078030514001041c1d071415a0424038010803a60300c064038060100042c0d154841180ea0040d4890b5170b643c0c1c0c03600d11900c26100707800b030160129415440801c0100402055500040a90b904c510741c550169581140301d600e40b003822140000301400c2d4102c00c000010b6540c024140301c51048080c1c0c0d042c0200c10041c943c100700242d000b540c10a803034801c10851941c042c400c200c081c011002c420b5156282420480155105070311384107000710000034401090340e1090001c4c540c7c03183d00a0a5603101d84250b002c2c01e019400039510100c40c200000109103031858035108031101c001019000c2c203070130303079a5408000074455820070a030303000389460001e00c1c0d11035001e126281c03003105143c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50196110 1250 50194860 50194867
    0x30e0a020a0b091203040e070e0102070312090321020c010e0a03080f07060b0306070905090c09040207050d03110c102403030302030f0c0304020904020906120d090518040803041e17 79
    0x810241000d1584c00c109160010801400107501e4440340a5000a45080c80f00d1013440d0500100d1800020754406800c52129108608640d03501072507110881e801030100f40c600803003004843d5a142600600c44000d6882515060125405071144000000c0010a1302c030549659407210720560f84140d032810002100092001c0c10841148180d0260340d00640040c241490010f00107801040503014440c400d041d4080001c10581094007210100d00d805441591114014500a6a07070a03811103a580842d08010007410101c004000740c6080305ea0101c010822940404d803030f480100700c00c9040549003001901200c0d03181c14941001c10080d031003944c0c0180c0e00d00d030840b88560012000381c0948410701e410000d000c0580c0d240c01c1c5031900150121090038060301d50800243d2a88440707129610203014080c480842c450308945440100e460680c0d10091914001615050700c24017201c000303040040a0000c1004141a0504159010501e0001c080d201c2e9a80d1508400c02c011800659141e40c03001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50197360 1250 50196110 50196127
    0x503030c011508010603021c06020403020d030804060c0509010f1d210c180604020912190218040b070f05041a030106110f06060409060b040e0604030f1707030e0a020a0b 74
    0x100b01e450b0082ca99000200320050440d8005030101103103291013441032411420742d074140710441e0304440041d036004040402c44e480d07030f2801408261003118103442c0740b03180a0305428058000e400f19000c5c010160348440c9002c2c1c1c28041a2a402036000c0c0d11079550714080c001850701c0d151181100d164580c00c82900c0d550350064032005141201500300a8000c020385c0c26000321551404075100e030019400c0b9005610f400740240402c64a090000200b43d06102d0020340030445800d4452410700c20740251840e80910b503090010070f181803c10340c1c0080020341c2740e000080c0c0c994411021703860800707054502249003554401c1809500503500348000301c001c00c008010000c036a040004001401c0202000c0c1100d2f101456005803140c1004040710b01554954545a0401a00d43d1040488040082040142c0300440c480381b1740c0c5810803141100440e0800c42c07003443c51406000814103440b03240c2001c40c03107642c5030001200906440506041c1c40d205800c61100103179a50500c2002030660401c20070340b0380c101d6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50198610 1250 50197360 50197391
    0xd060213061803020402030c120103060509011d0601060e060415080a05070c020a0501051c050903040302030f15010303211409070605070203070302060306060c0f0f10050717100503030c01 82
    0x55501c404140000c4580029084101c0c1c44108102d0303404407401600d9a80d200c541035924414050903110103042180040100600c9a11040c000d0449038020800c0c01c80c40d17041c1c1d191300c2203900680c80043d41700600420040784200312021207204094042c60500d996043d200c00340e4240080c031140892601810411020300c94800d0742d42c80700c02ea103000d200000940e008104840320764002d40d81000000602c02d0b000900901d080180090220300801c2a0700c5c0180c1ca254480e0440c2c0030891003401912180140d0840c009031502140180440381b180a034a0f580d0240d98110b519252645100001001c18003000d80c02d110f42042410180040000c42c9002c200036400c00c051a08542d040c40700c28014403002d6280020b40b0020f41e40c4c15601079940e07882d82c000040050041c80c070403c116106403540c800d14001c011500c0b2a901d1a4001201c40480070110b0420503118222516800500c0c40541240310144081c0c1c0180c001e003101240300e0b180d07921100841e0031a404031801041980d12a2203807aa0100d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50199860 1250 50198610 50198647
    0x51b07030507050c0d12081810060e0106030203010b030a0b01141206010806010f0e06071a01060507030305010b04120312060e010b071b06020c2715040b030a110d0606050d0602 77
    0x13046a070160003980c140d030380c2031029034a000307500d04200600740024099030503459503c11183c0d40c036085805400003a128072014040b140070380d540c1144182d00005244d4000d000343d038141c900b41c0700658250794440b4a01c0c4001c120440715141005840310607220080503240003001041072009100e10300e498154005400c4ac2e002804043c10008041c14401c07550380d0042600c200d036002103411a507901d001d0308041001e41030011702a4030400300100000360640e0410000c1042c944651070600c030607a652000228a4000c80c030400d055030381c801030b00c03800091140c02ea543c000c0e0304c12840000d2490f1224000f0700303481001d800c80d152842000030b0784e1050000306d13468903107031404000c04049968208a4002d456000340c61219000e40501d082c650840c0c401a11804517100400d5400e403110324080742c0c40403003d408000c1c80c0d17004503e48800441c2c14200030405c1004941c204a03100d19401d83d800c1031000030007202006039540d650b2040080760300d41e01c1c0540702c0d450502a100140e150b07003481140c910b0240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50201110 1250 50199860 50199883
    0x10111315050405192108190c15020a12110921100507021b03120f0c010e0705150711010503060414010e0a0509070f06030c030209040c020a0506060d02090109051b0703050705 76
    0x10b0740b10b6400000383c0124100d40c07ca19898841348161005403400340e41c0701030b10101c0100b18000510041c03480783d0309540905110400c5a035031580088046814200300c2e0107010018800940400000c411410400c001c00303045144028502c884d403412480c2c0b1401e0501d18035400f8400c503107501c2404a002e80c100030441e060002c01c0c80d4035000388603640000b60b9803040d00301c4824903210081109801c0c40c201c0d406a580111078000280b01c0c41d984107121640700c000c01e0240c1c171b02c5000c001180d4214803280f50f0a039200203600590491003400000b00541e20b40c4c02c014600ca61054650f5189809454604801070082c910345600d03080341e08001c0e007810103458005062076600c3c1c1c0a403104102042c211143c40003100e0f1a0306000892a40104080303000e0f1103401c40c00b82e0081d04042d41100e106500040203c1542d01640c2904c3d55500c5110810079500300005c40030307500c0019200184010207040d44102c0c1c0010111255880300801407003c0c0c0029003014009a006c240081034040c03d01406006030703003140b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50202360 1250 50201110 50201159
    0x305060a0506030a0903020a12030c0206070908030307080402030c121b030f07030f050a02090c090301051807180906091a0906040206030c0307201011131505040519 72
    0x3801c0c20301140c224040141060b582d0380d210107211301458001c0c012840b01c1a0800034904070a0900040640584028646080188201c9001642c0d40344520b27046416180300780c0c0550b145840e075013022156000040e2040ea41800790300310b111041d60741c80c0d03048008c461500015000a8560000c221001251001002d020740c111040c100a4480085002401d603a03100d084802c651615060403440c22958a80003500881004203103d04d240c4070030060003641100f20028010f42e525544c1c406417800c540320840c2115031181b030050004035800d0390940e44003d8040070015070003900c0e84a040685003402001d4800c502c145000780c040c2012000d203168040c40c5d0100422217030515501160311840700811541c032501021011903e110f04c07440724140b500c112124401c55923070080d603200e03855003e141e03071103002a46009d181c2e1545090890585002c003d00c1014503580a240c01d01030007035800da094505082040801000c0f1719a0785260304c615207040045030181c0014144000c00042078001380350f441c0107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50203610 1250 50202360 50202379
    0x201060f0b090a03020112020918010504150509070c06020c100902010f0201060e01030f0f02090106020d0f1b020103020a050d05010306020403030807180302060a09050d050c030c010503040c06030b0d05010e0706030506 95
    0x40d103d009203081100c1c2e0a01e00301d40080f601003810b000034000c0015a65000c04a6910011200101c11a041c140c1d84111020846c00d40f00211111025040b4480c0c2034000402400007178115020f01c54900031702d0b000310f80240c0b0f440940c0f2001b13410709030703845a1040d856a5403020380040d943c3c010000241808a400200300d410f00b46401059080014440100060030350044c01041040d10b603448868540e000d00945159615260702940350203034256520300040c1c1916840d104c03107114401c48403d00070000b5080c1c0c004c90301500110b000e54081e6044100303002e030400100d0407111052182030700840c00740c00d00607100c074250704d0001c1c60010003408030000c000d118442c40d41c0baa2400a240c038100c0e039044032007561b1550318070025101c1410541c0419031040144440c04d05200d0040f83d00100d5460403400c1c1d5207810b02200054500c1d000c2954045c00120442c4018003145001f07901031544804000c10003042400035170380385825902a03200d0200250041c200030006190540121500a5411290042c1d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50204860 1250 50203610 50203627
    0xf060d0308010504020901140304060f05090a1109040f05070b0c01050a02030910090204060504020d1505060a2c0d030c050c0a1d150d080403030906030b09012903070201060f0b 77
    0x1c4841801014410340e4000b401c0a060780c016648401c022160341003031500c2e89800d04100006186410031070300030500f807900242c0d50070b4001c1403285c042a81b01c1068502510b07584180302c1003900042c400ca4031030700c1514480c004035804005050090140c0700e6043d5865290f141402e096610203480440001e0044c0203001441c01c0105006030744000c0300000040441e241e00020707016140650259803c2407000031400c0300482e580e0094003500740c4c250005810190b440041c0200e902c501c0400360300052804850700440180d03d00d510514880200c0202e84036030003c0002044221b01050880210f14044000010040c0600c14040002400c0ba880900305140170280410701d201b03400c808211400020010f912040125015035081102034548140c0442514000441c0e6019010660216410400005041d440b034002c40300341000282401c07915910300b078030210500c40502d140c201d844040c1e4044032070302c840f60700245101c0c03c0254000b10700c1c285802c0c1c01d185008816000840c4c04102009802c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50206110 1250 50204860 50204867
    0x803030403020f03090d08070510021c060503030909010b030a0b040c11010b0a0b030a02070c09090309061b020a0b0306031f0204050a050a1a0901020a060f0c0807181a0c0a05060f060d03 81
    0x401c464100c847d01d5501d40d16071034a039007443c81072480009a42c0c0302080000e441450f08074148104140051f0401c03109855a01f050fa4a004001c1e0341a4803444240040c41386140c00c0c009903810031300800d40842c1000240002809a804c025442c00c009600710480ca4441c07002400740d4001e69806450148419041c000c80700614800100362440c400d80000d205401c02250000110040c64031040400c50341d40d0303034036004041e9030281c4903440c00540c81901e4a0380314074580c540f0101640d8010542201c151408004190301e4100170f00b0107601d8050118980404045400c45030343d001210440180d645003082c04106803001c05412103030241d0044401030280c078118181c0c9940340c00c003a003611a1101a4000100c0c82c01c00720040c001c0c415030a1080244101e96581c020180307240b035544078500740e550b07801c01c11141c1d41011404500c4005801808200400d8441c1d2315401007140030420b079161448860b022450641d400000b02c1f15a80510100280d01c04000070903070b00700e0b00032266a1010031468a008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50207360 1250 50206110 50206129
    0x303060414040201080a110c1c08010812030106120b0603070e0301061a0708070609021309060605040e150903040b040e0105040608010507050711010207050a091a0102010204081914070803030403020f0309 89
    0x10306c03946a458008010342d1490700160340b148003100381218842c11a08115135500800080e100d004109a04004101284082504100780d94280182815a842c013501240e14010700c0084544103aa2000d000c2000d84840000318421040c0d41c8400c00548034610030b150844500394095a12580c401c1481644006204112203d0540080c85247c032482d2a08104000701812480250b00034000641e40c2130700a0150040070000b40170b12001c01c426680d0714240300c1924800c01c042d80040d048001440d1541202842c0241c004861900300ca04081c0c0b58520307103045a01a8100111004440c40104114640b900130803010740a494000d1001c1d04002102030024091010003d010306480018080300e40d1081086200030300005041100e1300e41c0e14808035004201407102c9920314a14180d04131003d5005008481c00c840f58003001b0600c03524000080c06003900300707a408071100540c06048440c08041041407101400c02c00c000707182d032030505207006480c01300b034115039004c580c0080c000c2c80c2c400d5440d094032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50208610 1250 50207360 50207371
    0x31c0906030b060c0304030b040b10050a05010f0e13060e150a0e0a090204050703140f01030c14060403020402040806060a12050618010e01060602071d04080a030c20030306041404020108 81
    0x10620198200c0090340c3d60240c003140303410f42d200120740001840780c1e1994580c00f40380076128051301604c4210308042402c845004440c0c00c503400c50700812895114100781041d0103000d1512204000e412800119244166140455841c2e1110070501449800d1303c075403074008814111401003074101e60042086403440382b0902c9111914040040e891301500d0b040442c201d0b600034404c000b9440d190700b01400600600c0c0d208042240701c400001c2e00e015041d40024140e80d081000c200c1c1d41c41c6481e5943d241c40f08045c0c00281c016100740f100000580722400600050006070f400b41c4041d01d4070300c060064030407441e40a244003130380740000d079000b02e0804100c050700440ea070270360394881043c11400540506840c440010940d843d0803000240c190f80800c0d42c50030307070308000c004080080843c82a06a0004103807400b40030b00404011103d0100c0c0240e006110b5101c0904001c90300d904800101264001501c0b02c182240c2c00010402107149050301c074400c0303207048101c51790490382440c2e000280482d0300100b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50209860 1250 50208610 50208617
    0x106140a0f051e0102070b160605070f0c1103011103010f140901060e04020a0302090607051b031f0914060a020c0c0103021c0504020f041802090c0705060403121509050402031c0906 79
    0x1803c03c0c80c0d109005040c0900342c0081c04950310701807591450f000400201c41550202e2420000c10b40091050740110f189407030030f68512519001030381300c1000d0031901400441c0d166694504003100d041c0d00030040c5000704000d49605107001c0c904071400e8000195500420b01c1420000011300c06580c02ca0320080610006a400588842459005400074820b0b00180d960160000c140d150030400005091030608000003104542c0e007212400b4199200f90403003e00e0000e401e800c0789001030200304d90100c006280035100c0003240c94211700400d410110241c3d9421020364000030400242c100070411142c40310400e190031032404820000d40410b0203102141040b001d40c541002c1003c2d17664030048540c506000030010001600500003080c0c0c0d400c1c0b5a2422030103030a40000181c6850b607500e0a41d650a50031070301402b02da030b031550f904a446540090034515400d58991440010320b481441c4080940030514000440e810709004041c680140320202c42c4140813509590003095500000240840d40c4504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50211110 1250 50209860 50209909
    0x40912031e0e0a030306150e040e0109080f03070806011803030e040b04020c0a020a0f050a050909100207060603021201052206020403051006030308011d0408090409050106140a0f05 79
    0x1034410907a18100380c12040c450628500d00196200031480d0074070507110b51070070408941da480d04801500107091401c80030500b203880030380d0b8900f42500480c511080395000002c00403407580d100240c0ba0046040c04503000303408400c1220003a000941181c000c1d80034203100ca40741c3c1d80404c071542c030380c00103000c02000c1110f41103840e00e441d1240d4101b00310041000700195161040e00e04495640d6008902c1a881501920390000700061212404426a040035040308039a40c100024014000009130030b0400c944210356101c1600810fa201900c040c5201c0c940c04203800d0314500401890070007000740b100345640342ca024040e00030b040c031011160480940b48201c0c8841082e040c403a00a01072540045c01c079000e0b880d0400041c556944c03004040d203101e900c0301c0002c1d90303c6141c4070700582400c40c14003522640b117102284c041550000174050b02e1a00030f001003406001c0e03a64007030a4840a501500020000e41c0709003002d0b107403142480d03010301004200004400d20340000100100060344502c003491704600c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50212360 1250 50211110 50211131
    0x3120d1e020309070f080c010e03071205010504020907031b0e010e030601030b090f0a0b0609060d150e0606040b0904020d03111501050f0f01210e0a051b04091203 71
    0x35003100c0d069001a4080031003505000c03884001070b41c42140c1092407130081c4600400c15802040281c401c0d5030b504e41c0144000580f080043d0740100d004002c5580c14494100b00190311245c1c0100c0040d0300c1c0c41040041802d04151060008c0c00380c2c090824024142048004592064100d58450205125280c142e1925000c100141c03030000e12428080e03014028540040306105007034200302c0c019044902100d201400501c0c407983c450b41d5404000b0043c1440f0404036105e850029600740d0840c000400702e61480b17400ea03460a02800c01c1d071401c0b080310341c0c0303030220051101010f02215501c043c00741c1d801e104220b118000940ca0100007000240310390030f040b611005052217400c010240198010840b0b07080617954000c1041d498007403280c584215031000071480a41044a41100b0010040c1c480c1e08024800a20001c02240c0301214907046035135074030103001001810031513041c40078041c0e00940b01d80041013030b01901e009000c011150185040c80c1c00c940000d84840c44480100038103140018129800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50213610 1250 50212360 50212387
    0x1e0804110a080a0305040f05060304050a060c0909060305060a0b0a120303110903010518240106030c1e0504061806050f0a1e091508100605090a0b070602070b01090204050312 76
    0x10b0704554228468401980704164100c4002c205039040c43c0d04a03054603985c1d400b0040075100c220f500400d41c0c0c110b100500300048050b00803074542c0105060484001d030302c4001e44000c40d1525403007554964440d805000c11001144640d000c03810f4192038844605050504215400c00801e03001010183e4641c1082441c25004041e5007140500a0091019080650b10f204035a034091015100342c0c02580c03407036a00601c10b05042c4039a1640c40100300e820342e10b012010ba0003003104030110000e00c5952550031003000354070021403080c14981e494072500e8504000f070040c0320300c1200076154083c0355040e030305008003038001081e034645103501c503c01c641c1c0e6200c0c003004482d10100c4202c00c85c3c00040360a103c0682c00d402c052044d05940d401d80b10360070a60182d1b40f0031a4000c0302520b800d50f202401c504203000c407501c20002031115a50180c1074606069651b407400399903900040303041d102a50701040034020800c40c10070710390040000f0701c0194241828540002d8a4030142c903280c04104000080940361440c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50214860 1250 50213610 50213629
    0x2031207110a0b070506090a030804030c05030706090602040f05041515090902030a090b07080f04110105070b0901051e010b0a031a03030c0a060c090e011517040c061e080411 76
    0x10080c120082c1c0c15542c1900303c81680203d4000c40d03150145000241b0504000611882500c0c0c0664601e826074907140c400b44c135651184c41c3d0945441c00100101008104180903103078072035214100050781e076407070700c446c581800740300341c00140c0716604001a01d20814070071600c445c01d484505641901c61031840f9810703680301000394400b0f100103001101b040700700e004651244442a006071089100341d5a403400444405400f2124085814090301c0850b010800343c85540a9022060400500e4a02951a10010110100d4840c881603450b64100100880d901e0981c0355002e038410082c0c5c00e29410b0510b184614081c506c0c00104050f51110f548035060080050040007a00180c1a25604e003076502c4062340b42c44441000b0340d582c0e402d0908088040d80b2450310682221850705619250b0703403e04d40143c0403560245104802c005141c84c1c110306854240171164090791203a402a00d80c1483d040c0090300354480c0c48850245050781c025440101600a03a155a0191380500741d810302d403c0303000003c3c49916 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50216110 1250 50214860 50214893
    0x40303140f160302030a0206010f0308030f091006030b100501030509030a08090a08030c07170405010c1502072111030901200f03041707050402041a0a030930030902031207 75
    0x20314110550b0b00340b40d00400244650302c030540c283ca01907130300c40c40e10007041c58444c400240224010000911103005d00e40038650420209401d03918141d41c0200800265100b6410039140101d188041c42090318030806101c005103028281840989031042e41e5540341e004074296a800d0000000014000300c10901100800e154840101920303400d241d001a0350b01d40200404850251a0420500c8900e03400400d071170840704c1c16034900d4880402039584422520301000140b400e6502407100c6400984c0254603244614440c0084043c01e226a0740000c0401101d8030711154960000c101d041e43c240d901000c41d510411f92038040c100d0700e070040714005151821b02c140b200c541f804081030224050010400500c1c1d10b80a1008844490b44c0b40c6080001700d1056110320100c00740b04954004a8142c450f01a040400d00c90400180d41c0c1442e4440030280d41383c9a0700c0714025500c0e10400311071038800ca042c804043c2c0c6079150130800e42c0104e6000c0703a954065403408012882d03000c0f5a85040116800d0282200c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50217360 1250 50216110 50216137
    0x307020307030c06030b010e0307060302090607060204060527011706030f06151503090a060b131803111c03110c07090902030105090a03140a09030501180506060303040303140f 77
    0x603030b01d00f00351070300320700500a0350002402c2c120310240301c0d07104100d02c000d404130060140c00c0700c80c606a0250001e500420350640c1100013482458041515803000c1c0000f450a0b484244d55a2040306102c40008480610302102e444080070404c420b9a010a09480261034000c050407140c0702c4000091a008550150081503c02c45007044540c0108030029040c1d81c009440f010119940ca000c3c418a80c08111a00f6100740d0000180d8008244503400c0801c0e0054098180320f401c81c0400410010b645145d02400c00c142001c0c00003c08044c2c0c81410800491003101c0070b4141b01501b460174182c18640349400e070082540361407c1000b802080740c216424022007108443d02981d49080d0701d0042c0c205a1400e91095107404005414003401140c2c1a00040d4580d03a95100300340c1001401d0100e070860060b103000c0010617003003c4005642446583d0f82000d42c404512a0081c0ca444d019140075001424280280c0040c4410000a0340041c40906078141c0d00d11844d850300c8080e0242e407014041c407072008100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50218610 1250 50217360 50217373
    0x609020909010e0d051e030a060806090a0b0f01060503060111010b0d051507050c0601090f0603060f0509070f0501020d081815010906050105160f0c09021902060a0e1e03070203 77
    0x2071010540c010b0a007800841c007914050340006070300f9201809000d41c003000702c40f9541c000300045c40c08a4010350344444481c03000078900351030b40a294507121040792507481c0c1740d20020700402844045505c0540c020a0070400380342c6d44d030515074010400d00001d08143e050001c000c0d04140404003c2d040040d10342000340c041100d400003811704590b1068868074070310003020030501140d040e134401e5003125030507401c000081046920300790009009094000c0c0310b4030300942e00c00000c00006c1507402103420102c918680404c080c00e07c2d40c061400d1160340d80c0700b1810315a040b0f80c200510b9802080e5101852128108580700740d0790a09880d00c4552404400c0c0c04500440080c4112254105c6200d4161034861404110964a620066541b0310401414090480f00e002e201800a006040400c551702e2181c10707002070311684c03140c008007030b0307040414680120301c200048001202d40c10840b442e4400d151082c2404242002c1106075102e40308020021500445595100c40c3e070303502001105e0003e50b01504803600f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50219860 1250 50218610 50218621
    0x1b060a0603140115030f0c09060f0602010e0106050901060e0402190c03180303020a080a02010e0607030f0c0503040f06020a0207030506090601051011120a030b041406011403100308030406090209 85
    0x24200d9000440b0852840d902c001c160400500c10319450821032100811080d0560320b40c4000034400700320445600440745004900102c01e4000c540080140721242b40503d0306002010f425112000c001c0c03c01d507032401c54200100d50740c0034803a80c1110f14500b0507203030400512020402a220344160000210b41c0641c401e1142a400b4279540c0d01d41e03000c1e0f556020b54002442103154160b0b600d10002d00141c2c131000c2404003080c1d07002c000b0b01c1c0d00117641c0000604003481c03014590516004442070004684e07296610500815507028001c0f0b80742051801c58518502035a40b116510342c480d102400d041d502040c07454095008000c1840550f80142c211215458101d105c1550b51209014007070003510701040c1c0600c2c2e60b02647c843d0300100c1043c40904210481c140c680f900e43c1c2c206094403410980c5501c084042a140c2e481802c4080c0a90364a001c61450400000f5010000101102202440410811045075581c0800303106407507200f4a00da540ba01d0364105207010b00540d2034086d6006030035000380107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50221110 1250 50219860 50219881
    0x3090102090d0f0308091501090506120a03020d0201050c0901020304150302091e181e040c050d0303050103061413061806390905010c050328020f030406050702061b06 73
    0x4aa03501c070380da0719001c2c0c0d620150660b86a4081888050303021f80607000602c600b881541055a00000151684076804204c041980c50000103103010350161700302c90902c2c160558207015096110358034840c4145840344080000755a84101c2c4141040303005d85400004543e0301c2034040310702441d002007002900c201092141d035500d15807140c10398400d848810382b4942c100e64642559110703a140c0e10380c06048000c031010f002c0c40b41c0c09c002c00440381e50411142c0400d6964078400c0000382c00d070003590001034a4ac114505101264440720450350805402d50800c48122029000002c2003076100270007041107903175041c26942e03c0030b466100030142800e00000904900c60106a2860310300c41500643c0e450703007041a00341000810f200e81c04006192400b040c0a15400340c0f0f88a06030902c6a000c0b04e203007801c0d481058005020300e5400315404c080c56414480755681c104144481076240e00051071a00b072403e00060403c1c854454001d0045001288000d03207482204620406a00040305a50b0a8134212400b40c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50222360 1250 50221110 50221133
    0x90506012c0103030801141203040602030d060e0906010605070303020909070c0302010b01030c0815010207080105090102040302182412070611070b03090709090206070f0c2c070503090102090d 84
    0x1503502007a988650080c0d80803009281201c0d0192140300a690901041e550214040c954403504402c01c00380d1000088020002030000b8003940d40035640b04c441c102c03101c030b064500342e50140c2d603007018000c03d0050082000c610035044071100d00345140d07146c82615050340680294207040d98415284820007404540000c01d2200d218031079070080003c0c0d04a0001502101e503c86500400910b04200046901c5a501104c3d409000c0c140101c450842d981cad0402803d5900490f012003051750041010030850912440115104160320081f0350310307107400c4580c01c8042c51681d210b4440d030760305c4c03546000300b580700c0032000004181c41405903000f00f40c0701e01d009400106481c01602c468403400342d0014580181c1c500ba6401142070501a0086900c0c141c802009004104800d983c450010030400c0e0000c1ea15880c440c1e000c0d44504200d00101d4503180004200081032242d00350824401031000c0000280e0303a500c5c035031000c0542071064403500d42d121410700900484142320780202440080c5001d00c514044d11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50223610 1250 50222360 50222399
    0x612070305030d050106030216110303090405010920041d1308070b010e06030a08121b04120201170403020d03050c13080606090a060b04060e04020f0714060705181309050601 76
    0x4d20080c1d070703079080440403442082814110b4101e0281c02c0400144c0c5030842c0442400000c04803030910001200117022075070207a1203118456901d4605414001c0100103810140748821000d505040c5002030440c4100c2e0001000030041d4045400030700c6a907281192001c032560041901d03a00e451241ca0070f00c43c2d00e5000c0c000c55840c1c02d481c1d0006400362900189114881e68031107201810281c0402c0e100c2c07010310020308160070b8483c1461034460505d5410010b00000d203405008000b41c011140009400007180c50940070700140605d0420010903000500346485190a180000d2242d90706086007030301c2d01940384d003c3d20300e98448a00181014002a10030301810045520030603d80700e0f03804080c1201d0032481a0070b0012070a0008000803801030507030a50041c1c2c0544094904241c131403000c03195510100080380d1403800714409042551007044400e41c02034286c2802841c4c26095200720080504040d80c0a204c1c0e0503200780700d09012010380120314560b900c0801c4030100e5031281e2041200c680428003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50224860 1250 50223610 50223637
    0x40b19020a03050414060105030a021318080d0606020606090f150303030a0609051303080f09031c020c100618020a0509040606110f030301030b06040506060c070b0406180506040e061207030503 84
    0x71103d11401c0821b64a04950000700208500c5910354203210000c2005145801c50903a110002c079007114480100b1402c1c603104100c0965144403004901e002c5400c1c80c3c009a086602510800000da10381f242400e401c000c0400e0400c0980c4d8520b44124103040c0e50310202e5801d4000442400b01400642d0801001c4d9684207a090019a8450481e00c0e5102150380c0080e00081d801800b2900d0300d10842c0c80a604124a10300f500d291184030303007506000d0010444000b041550000304003035520405c2c002440500070201c03080c4501c501d4482014003800c2580242c9007660f500041c0c000400303009004494015401a009200d4260344035800b404100c1101001c20440c0602d00590203100303008400c030381c16640c0c041010900340d2540740c10320004000017000303650010300400003103055840030071000300245030b20210183d0f680d0034004020104580160403400c440c14100c0280601d81e6402e0584045c0c8014100d444050361b11180041c00c00008d042140040e40580403011017030000100007040800d02846 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50226110 1250 50224860 50224883
    0x418120503090f030304020906010c020114040621020a0e042c0d0306050d0804060c03050d0212011a0a050708030402060912060105010f0906020a0f060f021201090b0a03020306040b19020a030504 85
    0xf00350b03480381301c202d40007035001c02c105000546540c040c076207848141d4010b141c05040c20007111190710b116800340d04800003151101d080e80310312000f03d0f900b2020320006004190304054a0039006030a64400c030000710701c40c985500e034040c0c522510010b52034400001180f07e408602191184541f1240d000d110000043c0c10140041214205a1518075209501c004c42d5850103103010805c44900d03c0b4540d00b142049000c1048214175107013800904482e51241c0304144140d450300c040032030098a00c6882c81c464100074032458a1054010302600c4205801c103a5840e600d61355480050719920a426040760f008044000b01c0d1002d043c00210b584c182d803c01e0300da0700f84125001c0019584030a040c401d1000581c8070000000004118032007080c1802d10800010608004180104050f6000314500905c2c55010000400c0900b05034018070780c0741d41c2e0590303c2e00041d5003190046074407008001e0001d400e41a80d4408100c240d050816103141c400d03030b0310404546410701110024040c00003030740d040e0b40100440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50227360 1250 50226110 50226133
    0x60c020f0312030406020a0302040b0c010b01080f100608060303040518010e0604060b030402011b0204060909020f0409031e1e0302210105010e040b030a05010606020708120315041812050309 83
    0x5201031590b000e10305403070b056a84503074600300690f110f80d1901342056000d00c00040c00d60152005041000031002c00401c200400800060140d0030050031084044d11003c2800240056100ca54003512501c1ca00f41425560f188040b900c1c611a507407000340c01c00b0a15114485205c80450640c0c180e80141740302104544558040000f5203a007030280d18251786003040450010f600a1030a10601c0079010404041464140c0006048403d20343c08500302d9915500ba000c21440e0006400413402c10880e810842c440032034400514950340400f040c0d40c850482100008200d0107044610605401000c2401c0304202820b03000b0003030340010a20400508908801c80c1000d0710b03000299060f5001a51380900780f140d050100320140840c1c1107401e800d405503001c204081503081c0140d001404a540091910034039006e485803400000246038a9000018420b00003052070310516404c4d01801200c0c0400c6401101c080e00200040b141801002e00740c0a07010451704c10342080145100381054000d07a4007410b000b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50228610 1250 50227360 50227363
    0x4110415090e040c05040903030f09080d0c17150303070609050d080106030b01120203070c1505040506130f080f0c01020d0c1407051002180a03032a0308060d060f06060c020f03 77
    0x19a00100f6400704c0303001c1441903042071b034001c0121a000b49408516040010700000888002c1c007010354009400141c8420f04a085000b091004505880c1407984000c120052000c181e80140c17042e6060b280c1c1001051440d039040064603540c039080001004107183c039192030b03903603980c06130301c150080754010300001071180c0a84160004071a040e151a0700e0076650840010095200902a9041c410f215041c000401e50801d5010034140b20503030001400d0405040c00c6107800c20003450140d00c018801c070804000b030103101308518404d50140d6000c0d1a0003035080e03d170724240644100069a50320200303400f1001c3e50203400440f100880350b200c0407125060f6040c00c1d10036214119010744a81d10a44080d26000b031540d00500300c801201030f801600c42602000034145d50195402500010414641c1000c07000c451304000038111500708000d07078001e2041d40c0143c5161001054140700b01e043c0c0d102e0b0018092140c211946007a40901c082044948130070b4050303c1d280840c2c05c00d0b4025200c100256046060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50229860 1250 50228610 50228639
    0x909060e0c030a0506130c0206100906050a151707021c08070203040b090f03011118030a0b010b070606030222050928050a020301060b1b070b0a0e0411041509 69
    0x1a800926550343c0402d410701901019140507040b60a188150f0700b4402c4501c15840d002c90f2580c054001d90804458130300d0450416000301b01c0c403524026003088140d075214503c008964070302c00a55410403c45106441c0d01204158258100300d210040060a56003c544031201c0d01710740314554402c0caa0719908481c0c0d41011106e031405a402007009100c280e40d500080d10038100b00804103411115880301190a590300c00c68001c20145011480741111002001d01702c1d400b00701980140f90703a040f43e031034008044006119885822100141c16410f1104907003290b0091600034160103d0b90080104031204066030034880b100381413420300400e4422501113448134288882e000544080068640604c0d441842c00c40c04490610596200d070300161000e000d450001d081c040d800d16104c003070851030102a03000420101d00e407904014424480c808281040da803031840d681c904100c03d00c0e88000841c009003a00b0a040d80000360108000500111010b0022807645040d61504580744d9140150818140f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50231110 1250 50229860 50229871
    0x191a041508060913050f030a020105060306091203060f0d1b080c0108040b040206030c07140606150a020d0e0a0e090d030e0d0c0b0a14040515070c02060405090603030403120909060e 79
    0x3d15500032a480c090000d07900b0201e940100d0954415450030100e151030740e403002c5503200240c0d45441c10441c152600b4400c0c42d5200f4101ea01410002d400600000c15601c801050b007446881541000b01e00c0da2280c00c0806880c90b80300040c0c030942d4100280c450141d00c03291041ca401889200d20171059075118108481c000d07580801c44d005192515401c10120b50070081a501c4009424011400829245c2e1000c0c061f807403440010b044030b41080d09c1032003030004140c518400c400404201d44040503900080b94034540303046103406103c5031402400030f220604103030b00c40d105104940003400806080411858640c25403034500300309522406d0301242d190301c00c090441c030114403c0d0002c9400701e100785a94561060900d84005644038a00d0750380f000040f420345040d9503a520030380c4005900c181100341c01d40c0140f039030f0070b00e144074050903030019400d84610b00640c0c0c081e500a00c0031502684080081d0750285038450498065a04042c100402040b030501c01c4c20016424644000784900800c0a903074002c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50232360 1250 50231110 50231119
    0x60903050303010b09030a08040e01060f030c020309040b040b030a050c0f030105040804030312270201080108070f121103061806061f1b02030607030204060e0a1202191a04150806 78
    0x581c0384c1a20b0300b40c660040030300c2e107806018025011001444220080010b090303207900c6010700c0c0d41440d000800c00504020410181840d00101d1304a03103400109276902002e0880380400c0b42c40f01200814054407409140c0380e054400c2c00c030000108000450701d00010340c0c0c25120300313440074025410142079544c203036006054440104404d00c0482d1040d8040490201072600116415000c20710f2a0fa040c1800441d500c81c80a60416000441d03a02c200910700404015005000c224240f800c880801c5400740714644940700c95141c0c004c1000061003115100c15802001d403022490303d40c03088414070084600d1108980146000074055281c1011024500400ca051821001c9d03540e503003d80d02d55000501407007800301508140c0e0b00594080060742e01c1004e8940c0e001d40c4a6150820103852202c12840c660710445030010700b4000002d003559804401354041321447d00c0c9803d41034501e1000d08068001401801c003083c0c0542200195030002d00482d441d0010910500041c03500445904105a5aa84c1d11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50233610 1250 50232360 50232367
    0x30a02101803080703020c03040303081e060108152101020406110601060804020d14010903030b0102010c02150f0403051303120908010507091701060506070515011203050d020a09090906150609030503 87
    0x400e12900c0c3d0140d10101c45d0400607d04000003900e1441c682165000300d0001d40e000c0708111a02d0490655401000540c80b085040e600303051001070080080203001950680c030241441a0640d50b04039601802c2d0242d06008107561140c0300658043c0d401130140c00c000c41d00b0b81980c0c15100c4400185541207135070320766a10b41c2d44e8486900300406a02529000d40701d454050361a0104020284640301c40903201c0d8400042460840c0700190a507040700c03070010250340003008844c401810b090b84056008440710020f050560340c0d440c06950034020800340c44802d1188810210811091a001c480c81004645603034095960741c029070382c01d0352001c0756074000040807804204035500102d008415142115030010400540f54004202c0e5034008840584031513001d0340d8541e42c0d00c401c1c0900c0394058003807281c00990f8044c4548020300303588202c80009514030740c005a89040c0e00d00c07450700d21020b80b030599011321803011141007540203445070000220246983c00ca0004185000d1001401107c3d84400a03606 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50234860 1250 50233610 50233613
    0xc0102070b0d110f0c01050739020105070c0806010305010609020316110f1516050703050304030e0f0904080316020c01020a0209060316030b0403020705041802090910020c030a021018 80
    0x1e40f107010443c1915120a22511883c41c1c00740003c1d2480030031070f0000148a2810f007400622503908840500030303120f078003000c022070b103001000604c20050300d00d44d01000600181c80106ca052017202d1001c1c0a05c004210302040744000422a6812240203000910095440e2101d580c00c83c4002c2e182c0008910190249258040c003500d4628021003016060b14540b01c6808030a40c2441c44403501642006a401c040240b0303a40c20540c00301000100d441c0141c103004082e54042d0031844041e0028040c0100011088141d50350111041000c200c0a00381c03001c14103280c40c20503880d4100703690a8400044500007260445c2c03000a21540c1b03404164024084200c0640a1008003540541404d4242c0202c0b500c040c100007d03640807800a5119011032501480c042c1002814190181c0190340f041d41000080121051b2400a001d40150105c0e03142e6216181e1000c4580303048202d03661b0650703090022075142801000130014181200d040e400340c540301e051004840049843c0309a003814a10b40c0d4050450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50236110 1250 50234860 50234887
    0x60b040b1e010c0506010915090908030103080f040810020c0c012f07080a03090501020d031814030702090406020901030b01021507080702030412060504060b091506090414100501020c0102070b 84
    0x36007100107050010001189842d03050038241c1c260001c00c4259203400f0361501c0d20075501c0c0100010401441c003001004041d6603000303120310042c4805400020045070f07442810000300125402440302401f110104040041e50350083e40280c046660180500101c050055002c0e40f490039804c0c501000c0c0b04800075020455203500e02000350349440c82d2054000204003000304002c04814240642c03124015035207020002440d00f52000d40b410101414203c070308110412004440940301d51002c444c90504807148006443c5000c0c03004043c0d80320502c4030500003801020340c003c01d4040000c3c1c0e4140a510b101000690703851040b0403030b2900f0b0400c8074002070510b5221744115a08044a841130341d203400e5481a000d1044016140c0550341290342d0411b02003002402d10400b00c0c0e00b10150355103001841c1c10081c07162468103400c01a800390300c000504d51804d0750703243d10401e0260145000800780b810148840d02c150901805800d0161042c2e11007060030398000100380c2c08486820124503c0e000c1190217030b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50237360 1250 50236110 50236159
    0x12020a020304120b01150219020d020607060c0c0606120203031803070e040501060918051c0201150b030a0605040902030319050f0406050903071e0509040f0602030c07060b040b 77
    0x5208500007807001003140c040403006010494044c004500d003950411142158510320000010159445070342441c01d543c4440c1844110365030110390600e00e400c424004203c05100e1000020240c0780740070f0001044540041d101c0d03c05a004500401009440c0e1320f511300c10440519000e98903a200b40b00c03940304088000e264000d40c0d04040d09440d406a0b40340100503401c542070710100ca07280d443d03500c00c0c85003e001c3d128094280744c00046584001d51aa00c800e900d030140d00003000b0340c140c1d0402d0140421030003500715481010b800e0400402b1140c0c1c801448500e90420b48083c03001d5814080000ba041c81c00e4000c040703045030010040e52515941540400344028a910507106101d4144068455400c1d000701410040810b6110a5510a00f0710b08150402e455500541c81020120041400a501c03220450044d180180d4124002d51118140f2422030400248001d0840d400001007000104100c07020f462103a00c41c0314280500300040382003006a13069a0103064004080702410219400c119488 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50238610 1250 50237360 50237377
    0xe12090d0501060504110d0c0c1109271506030303010f0b070f05060c071b060801060f030f090302010603021003020f0304120c05161d0c030a0504081204030806010e060a1202 76
    0x5200340e4480c007080c1030703414180e08001b006c400401d07480c2c02c8010030700411444913464500580b401da110342da60601130740321003606800b424441001407601c50719224076949003520b03118240e4115211661507903542c02c581004140c42c07448140483d2090030300106480c187c6088200d130400480c140054400c0a8000200c1515115042030481c000301c0e40501c0458020060181c00c16a102a1030401000c54200d01c9141210410600300401680d41c1c00090241541c100e40b400303043c052240003044010744070715003100d00e100380380040c05020540c0551101040b2482603c140b1102440c003a001c0c1d04034081c0c6a54026aa13404100060000c0c00c11704030301c1c0d582101414080c45a519544410340b4012540c0c141c40031981d440001800440344851481c003c400000c003036207115146c40c0b980380325103010142151000c2900d56008c07900300101d480a591a80003021100d610600c2c040c01e008186800680301c041c017180f0003100903d00c90a150040b035030205016110703140350403045142480250b01280c2c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50239860 1250 50238610 50238613
    0x906050907031808070c0f080d081f0302032d120a0c0f0615060908010218040504050c060c060703060f12020f0a0f0b070b16080c070f0b0108060a0e12090d05 69
    0x54500013000800548101801103c541e94540c0c2030440c0241e0000032508402080e621907100c006449a2214036075a0244d102c0c4602141c041c0f104001c11200c0d1650342009500d0300038010380b0202c040c00e41a804d07004641075424694010003035080540c03a11000500702170f5540d0100216903030140624a40c03140640f0442100c2e031002401c1c0c40f41400c64112a002c2c51489111500403c1b8039540102808007031b1420304021840d1005068810384107504140c0318030b004940b900d0004050040501907000b101a0241c9803a950b4200f0f10850358a5001c00c0320420003191400001040d5081c0035204401a07a407038401c0741c1000b4415801701f040c91030320391500350340c131122506010802407100654100248841c2c51207680350b20b101d1500c50b040f210000c10440b02407040602c950f1610758440c045e84d410bd00c820281503070381e00d914103203a84c806c05038000140c02004090700020b0341d400002640d610540041c1020800c00e40e01105203070310b0300780f0541c003280903800034040d06405290101140f64100d01c21070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50241110 1250 50239860 50239901
    0x7020712080906070818060f040905090703061530060209040f060602010b0306010506070c030f030302070506041a070801030302060c18030105010905040c0b07170906070209041407090605090703 85
    0x600041c000d070b0280304e040b1001c40e804110400703550346030002601d0424044031020300380200c1c6220390419018508c5140015512040422018082408040c000c1d41e0400c0e02071158400f0903283e404504030030301c6620302c6007102c030f00d0b142507030a41c0340d0700381e0b85016207114100c80c00010f43d1078100294115000c100d0380f2594071027050743c40c103205204403002040e190300007040108240c1d0800d424540144d10650240908002c0b502c0000c100740307100000d80350721401160b01c4c0002414120b0003401203000040151042e80e040c4000e1019800c0c003910100e41700922060180d86022080b107001c5401c1c0320040150f40b081012502d4920080050450040702e42d0000101098440c00a825200d0a0b4402866031340ea0710284414403540b40510005407500703e07522468080319075208529000d0b50b07600211542d02c007080c0c00080342e03141c00840c0c071556001007803004142000e0409403103c01764030510501e54030800100013000700f101d010310421540c00a1180910b0f41d0340316002d6001d021202e410401d0552040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50242360 1250 50241110 50241127
    0xc080d0e0f0105090c01020a020619090f090614010518041e0f050702010605030f060406020304031e2c01140c0717030a02010b0a140f0303090307080c13050702071208 73
    0x2003044480c07020300d0714000304a900748100e40074141240144150b046402c449050f40140e10b80004541c5e5581d000d89200903c0301c2c01d090304030b40382003043d000226402c20140000450f41c149810003810f680d9030301d074800f40303021310300c4010f640a02c6441804a446650100c011000c0e00d050b501100180e0a00002180b800c5a03000c0002d04030b5090103142d1500ca6071324800d00c40d49550902c2000081c18044c1c008012209102d54412b9030356034000c000914581d000400142010310600c0f0307044d21420700420310031818040302c1001e40a040030080c03590410f0a4a210410f2001c05c05088501e0110107840704960b10100415500a585c006101c075690b030b129406002881035001c04000b1031618851000d95254220000000d09540b212100e8a11421200000f8409418642c41c0103941150840310034400300c2000d400300b8194054030fa05113502d40680c84000032030003000704400c50f44103002c844990740c3da01c4141030203040380c400ba00d0040041e88000300c14401001081122005213000f0b940582c01d04182 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50243610 1250 50242360 50242363
    0x6090c0801020705071703070201092304020c10151203030f0207020603010f03030f0804121101060902030109090606090603050a02100314070917010e0d05070201030902060d0e060a0c0c080d0e 84
    0x43c2400300c646900680c1d08010200103d100d40d038501402c5400743d440e01016800083c0521464040c072510070110b50382c040d40c0d00d0410715614a00e2480500250345411041e0f200304e0301d4000e6103154007806401c201d21054050061008c120644030064207407004102103032030840050182152401c02030b03600304a40f402683e0340f070020b14000c0004200e10010a4298030b80100141d1501c1801c4041c040360006110011714403c512250506061402e0310860140c0d020701c901521090748000d207110300c000004199074109800240e04c2900800003440916034400c1d207203044400c0d030301c009001c50700324024540041c58009480c000c2c5103401e24010800c0043c09882500031201520400c0100c0c1280200f0044181401d40b446451000900200b010f2008a00003648600d1003652100070800d0009a4004582c060b83c0500d41c02900079003125110f88548100c3c9006090700820380304588034010004544030810b00842440c07543c0e039034582212455591310800541c00039800e02d0112030f2a0120740400910 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50244860 1250 50243610 50243617
    0x1a180904080406020f03030c070f0809040c020c0406051509060a0903050105010608040b070e030601030206030601020a08033d050103050408090907020105100f0b121b0703021605040c0c06090c080102 87
    0x10300d03003140d0b00c5203040c00103480c0c00b44142022800381c0007841006881400c0c413050351010344c1c002c1c4203240c10b02c4040ca0144040d101c1d5080b650340c068a000005814507030b000405003045003050f141080a20f80b244108a00c2105007401c0700030100041060002c141800e902030442d00c4568100001c90a07220f5950a084d12000d0300300d10006400795040109102d5400b68454100e40e15041c01e5034009203070000f083d1100c0050102174041c800020100d4051f0b442008402411508250701913228180548007581e0454a07810032004050079202d1003c141041804403030b003010b6200d030a84800c80c80e140064014150042c01580d45000c240162541901c034410024410714142d8000900e926092892129441d0960400c0c103542035804020f04ca00f101c00c904550300800111150705007551241d000c10154540c8008400400c06c021500500f01900040c42100701e002a0b0a008441070b1104248030454050b500540c002910035125030011685aa001400f11409050211102c0c0c3c2c41da824182a0ba2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50246110 1250 50244860 50244863
    0x7180204170f011a060a08060f10030e0d020115120f0204020a0c02091005010504050402070c1a1b1b0f0f0a06050405090f06010804021c050a060504030314011a180904 73
    0x40000034003a14074842881420701300c0340c440544080f4039820402041d0075000381c10b44d0005000d50400492041d0381c80340e01003a05c09600030144a00f0060201c03000b4090b11240da0b102e50b01c0c0c89402420200e1a00600601d000714800041c4082801d15202141000b07400c108000d40c1c41c0440d0f0310035000581c450780000c4c50743d0740031a1a000303150200c3d4414044008070050003800382c0909410180001c0c1c1c0e0180454044400441d0056210005c41c00e141e055440c0507400001340040043c003e10360140f8000141c6a9521060101501410100d6180b5100d003040c10300e1030140c01601030f000809103443c4001150101018105000054800012584544041d001400441c01c041010406894a80396042c4d1003103030701c1a590702c0d40c01c01d000080d19540014000a10a04c0000680f081c0350300352484418085812508503012441c01e41021002440d05a070140c0c00a0b0030040800740e240303d0124407034100c952107402d458000611102094140d004005000f14282200a5000b20780c1d40d5422a10300a6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50247360 1250 50246110 50246113
    0x705031807030b0c130f06020a050d030212010509040807050d08101a07031b2a060305040f030513050a081b010807090302090c0405040f05070e01110718020417 70
    0x24104003554140d2510050040c440540c8204030070320000b01200741e040d80180e0024212900c1d0050301803280c09021044d040103070a0010180001505540042c4003c507149c00368060356003541030420201c041c1d10804084034211901900100300340d0600404181d8054003844030030341030038540d6450b5070819050f0240c40d0002a040000e000c2d40110428034800100400c02007207007000e43c014031003102d40c000c029000d01030100b04020548040b1080164003000341c0d01c2925203440c0030f0f2205040044440d51030700c403003c010b42d1081c0403c0c0b160103841810300070741c0c02007180c0074801802d940890f5250301071031601c4c0503039038040000284c0741c4540c000100945400005400f120182842c50462010203003c41810044000c0a0161194000010b14240c81e0140e56205140e070f11306940162034411a07000c5a00689480050340b003c1c44158451030080c103499444035a001410741c0116a00848400e600149400c94803013003008441030b00e05003104210081000d404d082d543c0b445801e95490040b4141c0301e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50248610 1250 50247360 50247367
    0x10030b030a030e010e010215011e080a080a0311040b120903091c06050a0c0819090b13120906140903010912022103010f0506030a061e061704050312070c0b0705 70
    0x3d5038102540c0846800c0a200038018100c403007035403000e208010304c03c0120f00c0c0d007111502503281c4144000da402034500101241c240040740c3c5840c1a00e9840012031130002490310140c1401104180111801c5403825001c0500740035404081180d8a44090420f0312a484200005130241c0c0310074254400015401c50038030b1124500e401d01c1003da600040203000414902038075003ca4035040500e0f60341100000158500a412102d030240040c0760340407002e40070103170980401040310170302d01c1c0820703c05110b941d52030209a079452094440890b02d0080b00c0101e001181000400701032140900810040140080b43e4101d09403144124410750319031640050304411a401d01c2c40a940401d0b80d0341d1950400031502d9589030440403042c04496010741841a2000000f003004005203400c650040c10780304000741e0140d0a4400380303070040540791044001003507803008414000c04421660070310071074006000c0c0d450000410920700420400500a01c01e01024611000204501126843c80b821003a01c495aa = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50249860 1250 50248610 50248637
    0xe0a0213020306211f020406022506030b060f030414190201020c040509011b0905011701030c03080702060d0c030b0108060904051c110f01020a2c10030b030a03 70
    0x200d0030200c0085400e5a0040050000700d1300c419032001805024a2421501d40c261103002a00302030031082c1c1c1d032002204030310820740c041000c1d60003441100d12a03004c860802d2081107003a03850003c4240d512401030160300c0c080100a00a40203d4140c96000b400030386003510100d110900f54006a900341c4007611784107a6055405030070040c10b2515581142844800e10740355000030741d0b5039520701005019070b85500100c0c1d43c411003500080c03005018149510301c5014942e0005100c0d502d20311940380002c01070788002c0c2c8000007100d2a00c0c103803a0005149440749085403202040c942c000c0604a8000c5020810321404510310700c2280240c3c01d690740e0104140040310700062a24102038203042c440c03410b01c41800006403002800305d02003901c1d403000c183c004560720740030740700210700c04020b5403030b80206800b8420188041d0b004000b61101074072400b54940b05401045d50a03402a0302c55000040e440481d03084520f080b50034071519002d030740b50202d080403e400200342000c5125000b1030102d207502000d0701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50251110 1250 50249860 50249869
    0x7030c3207051011040803030c090d1a070305070e0108060607110603040c0f0603020c0c0d050f030a11060c04030510053c090f0d0c15060e09010b01020c010c030f0908010e0a02 77
    0x1040413144886013402e003400c050400c0c0d200d100280c03503c110110000f0300c260454481c1d000307000046400410400341d144132001c40c46d80300705040303c8080000b4900000201503d0107682a20040041030351039000544e0303404140911030b0303c8540182c030300c488182828001130355450011481144145000c0d001d151070700410a130342c100e0a400c0b0106050040c040000c41034400901071680203800c444007440c4110b00e090107810f240c0943d102e11071030b0000041e4120081d07042801c0304148412001201c4007039580030b901d605a0702680c00010300640058000031000c0b202900b00315000074802078031000600e0040c00b09920822040f02e85070307400481e00400c4078242114881e1960000401024128200300307040116141c1c4600d84031340b001e0042c4121300e20180314005a42c1c0e1003a0400c04000c101c4151030304032000d00b0400480d51601c1540c281071a409a55201040304039a0700010f86a0681c1c0c1d529079038095601c0d50480603c8001c105034250300141d508000d00030308142d001c3c401d01a140003581ea00521 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50252360 1250 50251110 50251121
    0xc1207050a021501050607020f1201060b2a030a0c03020304051c0201020c03070311041a060f0304050d05070803150d150204060f080f0a0b060c0303010906050907030c32070510 77
    0xc0403e80d0030801040309441d05012600701d568100d0300368001061400c00a0400600240301c00c560350719281d000704510308018000d05a109801041d00d54620b0340c0c2864100c00c054900c10f0745003540060045a00160091241810080c403038015030381410b45460100c3c2040c6011556130401100103101241903503010301c4003010341c078000c2c0c000d45001800c580740c1400100146c00c9180c01203079168460130701d1a402d40340380752014a00908250303031005c07030796020210740c0c0081e6002c1c0c4185c02611040000da0340070f541251071a90b44802264290741d17540d81900b840301c881a220341e0700000c4a07521440083c3e91090140c0e0341148c5242c1c010384841c280b0380000e108484070030343c4d130003403103018414005680c0c120000ca50303010b1000303403010584111f10750104559004a06403150340340b00c040004900359045402c02c1c02620000c1c0d400341c810356a000b000b103041c0c1d4250000302c0e003c10702031070148280444e0108401007c00e0080480c0203213120300409003109605c0020281e9850b0041300318084090928042c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50253610 1250 50252360 50252383
    0x60501090506090411062b0b01050c0c040906112a030c1b04090f0c0303020606010c080313050c0a09050f10030203120a090b0307230a0c03080c1207050a02 68
    0x10800740c50504046031010402400180c1740f4005408400020b64401c002c031a440303981c808103281c0c110003d91010710000401c07891782d42c22904064032048294411015030382d0b24030310385009108140700315050000624100100350380c01a100c5d000000c0c000306274001002a95421291031200c204d100110308030a03000d0505426990f0001c1003080e40d0f0307540010340e4100d00140d4202800225a0240011f0010100d6280c014002c0040400789024496064103103821640650265043c3d9a40c2100440312680300150041840d4002c0c00070030368080c0b42d4860101e219126004a440741da150100144004125500c15040e6030b072904208030128000c440e040b0b030015010021400d200c3e04642c00607488280c00104e6102400000c100c82d41e03194840d91801d0000d20210b00c10310394a00780510000d0901242d80900812121038210005400100c0e02c11207403401400ea481c03a0380b101d02a0f90440344038201909507043c000081c00b68000c540117402d4000d00800e00e070b4031f071140e9400040ca406030501604250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50254860 1250 50253610 50253629
    0x203010c03050c09040e011506050a12020a0921050102270303070f0b1504060609140d020f04090503070b1f0e0c09011b0506040c05040b0a080304050f01110118060501 73
    0x40c042510f09480c161002c408080b0340c0031550500a002c41801003241401c2c480c62601c2e501c200060710754101c0014080c003541a03840e502002c2038810800b081e0322440503c80000b44040380208034a4011001c0e00408a1103e42c02000150f402c1c0c441c20301760f801502141c1841012031414079024004111050040002500a035040004540f41c0101042882d00068084800c28000070035100d078546103410b641034014000c108146e180e190080c400d102c14010345508110b43e070fa413420540380401074440c450f81d008080e01292810304003840003400d001602140c40d440140f0a25001a804030340301071040400d41c1900d10007039100494920000c0c04d543c40620252a85010f0007640c000f0902121034014081c01c0000c1d4032030003280c5818005009400c05072003406480140030070010714028260803030703070304583c2070013010f60360400c0184501c0240f0548045500400c400c102c02c0c01d100040c0d901c114014141007a001d488500001d0075a011041801d0441e17601d00e030b020b01005124400c19000d07001c14030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50256110 1250 50254860 50254871
    0x8010e0c031b240d050109052505070c03050c150309150402060d0507020c04110f0306040b0f060a020601061d090f09011b030501050a090912270b070203010c03 70
    0x4000c07a807603440e480c081c2666550502c008022544030300d000410380e0b0f0340c180c402e00c0ba1818080c1d030211140d00b120386441d0642d400c20000258411950140c903025030038800303808400010203200706000755003c0344100203010090220314003141ca034500c1c6000650080010302003801035401007000b14115004480b00280b0b0a0060015807480020310722058150050945116119800060510f020340c4d6420a42281090308000c03450741e011400d00013601043d00c0c10702c40040b1400c02c00c44c00340219a60400503050a2000400350b103425017100c0102100a00015901640d58001c00d506510442d8550f0160b0f11030001088115072080d012645040c0d00c00015814040400029074090800380010300380003480f0340410742143d000c3d480804080059400c2c1081005100c0c4040c0c00307081c0034031070b451241420b990300140c00c01d05405110701c0c5640c883e82950803040404030a42d01140d0302c01003082c1203190700302601c0418282454580c050b0260b4240151900d520348101400d4442d2048550704041c20207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50257360 1250 50256110 50256133
    0x73b0409080d09030c060e030c070602030a0f0810030f030c1e120e010210020a020a0b0108010509030307051308070f0302040506100203031909050601030f05060703020901050405280b0408010e 84
    0x40240c0e50b0444078140045000c8a040c01c040303c0000281401421003403400184020300440017009045101d110020b603030800795501810380e142e004400410000c90046a10207501e05e21903a0041c0d03101115100040065450340c44140b0700080584044010480181c00c0da018081c0b204521406008484006038001146582d00d810b000340309656101403044680420f50b07560300034001201c0c4140f110400b1500c0d006001c01c025038400251341c042c1c03007854801001040c1402c06000b41e521840e4100c000b98655262200c00f01e803a44d0251203801086040c0050125007441300b48503641c0140101e40440c80c0c002e0a500400c0111800982501e124280c0b45410116854006c07040d41d43c865540802001003050401801e0007904220f040240103004240c004410440b1a1038005a228000c00440d00299641c140c141c0491241c01009408107405220400c010302d007503805080c81407100c0e20b1205221105e0341e03009007240c005800443d80084003140c00e00049409104032446003040c00020300382c24202 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50258610 1250 50257360 50257373
    0x15090e0702070e0603010b090f010f0902070203070e100803040602010c11030703020a03051605010519050c070c1509090e0106031104020a080a0e010603020904080d0c080c030609073b0409 82
    0x6a100f01c40c900400c0c3ca0024040f541c0a503c90000d10301e000e452030000b0f240200c3c3d070310101d4001740900540b010b0b00e50808039200c0124801c0d585800e90142c001d050003402d083c0c1035020a2002480310345800b0083c1004641c0c0316003400500010b10403900007080c00c03c0720400283c00c2024008190101e0351003401035901007540050000c807000d416092695854500321030716000d421040a001c0c10f03d600340403e01c03044070445030025001c0079001e00c0c2007159844292070319055202d82034010341000c030340c00000d00c80360252240002c0813a81d103080c2480c0041d40d07101080107507503981c80b0a10291b5925101003007070200038000042810300494046140100d0010041d10360340024104901046d03171140c000e603012009500140185130028a04542e074a8540b90500c4241d10400380c40c14968101140d43d8601c038043c540a60040600c651781c20b0035969040188100c0c2c000082440702048500d0030310100300108200b01e050031822031000d419040f101074006c0c4c8028440c040311a80198130b02507051001ca41c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50259860 1250 50258610 50258623
    0x2010c030305091e030415090807210210021501050406150804080705030705030319060312030c02160b09031b0306060112020706020301060306030b061f0315030c15090e0702 76
    0x915060020300d644400800364134000800b008070b480080c182e081440f500d1800130240c41198104985000000c2c0c0100d0b045505070384600c0b61918950086d042030100e03940c2c1e18044040d040c004485004101182c1d0002841440040300034805a00100c10f908034040032100d0721400340600799024000c0610f03010404028011003134841080001940100701003040e420200c600c002d8000088940361001414031503200c0c1d005480c21200c00343c02500000305000f4a0044c0ca0459401c000f01c0101d004c0d20440a4001e02800c05024085005040858880d5410240a10050900914800d413142061801c0c5440c00503204500304000380d245220710f84a513000a00141c1c804403e1a1100300c4040c20320f4604040e003d089402809140084000704280741d16902000490740540804502c07501c1c1e020900c0084811000c031001070840700c0e1400d5812a00940100240b2600641088071507903a070788510705480400c2d001920781901704c03100c1080050b031104000011700381c008090209420b0411020f583c508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50261110 1250 50259860 50259863
    0xb07030903090306020304120f02160b09010c0b071d0303090a26030307020604030306051212030c07080d0207050607080f161106090c040c03150b030406091a07020c090402010c 77
    0x103448100c60401c040c40358102800650f4400c809544a050500d45840b2804142c0c5a84000031440645004040d1000451460001d004000000d54904140201083d030740000b0ba41e50500014101000009a0b10281907214407066500c01004903255a5440c501c1000308610030b1187e401480784100650703855428404644044201011102c01000e02442c2070091100485443c0404401c00c4840c6401051a0744214844d540410207030742c442c4100142e101a2024100403036000c1c900c0c298200c074a4100030340c0c002d240260342604100d6039903903251a42e408000100d080700d0300444c8d0002009010002c2c170390800124105a095494000441c07078204800238520042000c941012242d1603008501d0720030550451000d4680514188150a50301d071313074451080d0b014503e00b440c1d080e42988280302d1651040603101078103600b00c0c500360149401d41c1010b032054440f00d81d640c40c018005060001c0850100c3c41440308409140341240c400b9052055146d8920301400c41601040011f031b031f008041c1031489 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50262360 1250 50261110 50261117
    0xe030904020c0a0c030b0708060409120305040c090204030c030b0c16030e0402071208061002060114060c070509042001050304030819092f0d05070509070201111818040b07 75
    0x2c88803100705a02c2e240900b040030704842030a01010040c440d07010340513881802c6c2d64445400c1c3d81c81d020306000031a01c108401800301c40c0140030607203605110b600031a0b013140c095101920543d8540710007500320303442a4012181c40507010010002c218181407500e40c0120b222418a06024200d000c0740b240214000c03008042101c0c00440d09400c0d940d550549109a030820703441c0101d64901a406014010143ca1051060800401030354841d480068214141c0344940c03c9100740380000b100f44651030b0000860703100d440c0105540814103448810016100e24000c1e94481e607190380030740844020001441c929810440c0c1001080040394000b41c1d10b94204107030707408801c000555480020006d02d600d0760000d0040110120f40743c45803c0b08100e48002e072541e03040320080036194100704403a281107007200420310303002020200211b04c0c24051042d4800214000400e400040345c0484240b03501816159100307401c401900b0405040501da0011071821881c8000b842c4e00b81134842c4c500d0a60002c08034804c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50263610 1250 50262360 50262367
    0xc330703050a0503220602040314010603051903030f0c0503061503060a060c06140106050307110a1a0702030d0e07030b060102011812050d050901050403020d020712080d022a010606030e03090402 85
    0xb640c0780401700c81c6101d1582c0110394845a82c1c0c50848040d42c0705100640d9a019042100314044d030b810b200c0c8078216a800001004103100b5040c55201e0460303140e40541c10715958048101d404030705801403009049065686a0703480c0b410004020450890a600c01c2c4405024010030060b5150201c41c40c003569110704190010041ca4078180015110340c01008400980f0140002003403074001c00598010a0070340c6800e400381d90320715030705640c40c01201005024075858602101d074908200d5442038000d891407066a107052a0003404c0e2040c3c40da03064440c2c0940d40007041c108207200c0d0240d50075401030000d04c001e0040d02740d403458034034120076409009403d1400300c40e5a14520381c000c2d411142040414030040c001890400d041d14000c01c81114181c015000300603141c3c802c284003080072004d45039156204d60940b502500c0d0306020b81c000c4400110110383c2000301420301c411034200210700d064140801c80b140c200d000b54441c2134408a52042091500780600d089110301c0103c140c415009043c0e800580303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50264860 1250 50263610 50263621
    0x8060f1003081201050f04020c03030c0c07080a050601230306070e0109080d0305040c080609060411041e090606090b0a06080624070311060601090303030506030c330703050a0503 78
    0x2000c140c950008190210000d41c1010504102001070304032101111401c42848045013808140d10650b1005080d0f03800c10000541d2400c50000076201c2801e808040350750103516070317140516000400600b40e4140d8030503070040050425000056200d4828101115000a40320020aa580e0806071180041c00104498102e03142d10480b0988014466401210642c20001d100540240025602a18044103500000c611b525000510b0fa0140703a8000080010340e40769162a0242108806815841911a00503449080342d02c3c210760100884a000059081500e29224040b6111684000340701420800f48800942d00c0750010421a600e5040c00000e9a9507200003802441e00e62074001030700d144440f030002170850b8240113000050f1186e20340620110b802b40c406a904d16080318141e000688803a01400024800d400c020741213880038049030800007030fa0000540703403002d2010340c5581480440240f1010710605401c0c0040d0b130064071400c3d00e4500c0c151002007203441f402484c00c05005c4000080b40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50266110 1250 50264860 50264881
    0xf040b07020c0a290a030e0f071202010810120b071101061503020a0207050d0606050a06050403110409050102070609080a03200f03060109030f05030904061d0115052502010f0908060f 80
    0x2020f125284110a80d600c00601003d170090075007803031f120300600c01c01100c000b103401d0000b40f220030348070a000c2050f01c00d07595600444007520000e100c1c140c541e00700c00c2c00003601c4074180392100005102d108840700030724040380e00400071201c0450f20b04190381000002c000c21090364000ba0307040860340c90003513035900399100300b6490300060740d00081e00559400340900134024694402016500c049400303c18050b07480b00c044440c7d0241d4080a0300360781c905580e14401e450543e0111420610501c00507040140c0394031600211954294192080100041c80081041d8540314816080d60f00c0d441490301c2040c4040c11402d41c0c040c41d00d400801d0b4800002088403030f070040e9856401103500021a43c04107442d460615240e40000c0400b601030b50408401180941120100042862141c000c041213a0318085c500700c40142070b0351086041c003000700701e69110058802140041c401c804000c032500c042003880018000c803407000340c000070801035000a100a010100715550496450011000603465410654 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50267360 1250 50266110 50266169
    0x26150301090c0e040b0912031306060e040308040c0504021804090302150106030903020c0d1e08090d05010203060307050303310504020d05060a060201020408150c0c01050f040b07020c0a 81
    0x90206011540d00180041d12262018404c500c00c4041c14116110442e02075903804806a000b000001c040c4001105c0e13802d00030325070394898042d03907000c200d003950350b0760700b04800034182c405030002040d4800b00300c01d220172014142e000700800d44045182940503990105201c070210000362266031111104018148200500066002080d4000c00c2c1541d444102800805140e4411400f50042e804040d4941c0350080c00280070380c1c2c0005000081d05400203181882101d007100840e04030700103001c0d80300541c54201404010302c1c401c200069503418076504040c5094a15480544264001c10800281d40b083d105003202d01a114105081031091802c81000c00007800d820003504503101145501c011041c0c5d4100c60b01840c01134801d0109280c540303804a00342c1c8500d0140f0200d60b400103140b08a1440d442903115480032210b404c003030421109000160039128155107880261107071505200a00a038031009c1a002240e60009050001c240c4002c6000007446120701082d00ea40300361854040700100520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50268610 1250 50267360 50267363
    0xa0f06020903071203020c2209060e01150801140c160305090303030f07031a101b05120c0601060509100c03020f0a060c0e01051e03090f0303010602010c2615030109 72
    0xe841200d911810074104c5501850015401440f540b0007454003030918601c81c610b41d0032510301c0c1808044c1d00d4003503c0040c1c00c04500403905607990786105040c80000f84200c3d4801c648403030410700713072034548240702d801c0d60315120111030701c494054148200021407030b0446004d52072030200020700f10840d0034180d0b241d001c0d42c0f0250350036000001c00c01c1441400e11420b113100e0401501d0412030034945020300d010303900381c0405e00c0350480a0303004600e403d18090102814852180707200c60f805008956101c0e802c00c01c0d44840031145c04030110341407010b0310080c041640506011301d00030741000102000a0620581c0da1407040500400c000040c0505200b404514200c1c060301e01211660126441d184000340f82c2c80c0b07124800100440042c40c400c1d88940f04980c0102100c1e03c0340460100c0e031200c0d0b00040da00c0540103004130712546120400281c018400b48d4020000d9070000111101d480c5000742c0018034903c0881d100d44031f07444d00300300042034101589400c039000c0740030f0400c541d04002c003082c01800c51150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50269860 1250 50268610 50268613
    0x20304030f061d0f0604060b0f060f03070e011b0605070504030f0c0e0a11040302100e10020c0a050604080a151104090f140708010b03190c05071407080a0f06020903 72
    0x41e840180031003074020b031002d207000c00d4555503560320b00d031403850f11401e11802c2c040c802d4014001107800f203615500724411009005040c00c50300b0071424000751480d4483c80340c10a0f04030340801002442a04503002000d800028240a9007019020070b4040190079500d0000301043d40d1ba02c08209054400d038181c401441e44a182d0421031801800c11001c440818415540d203090110000b46c00089135004402c250010301d907080e82002d04541c200140068000b0869040005090255001c0d40d9210074111158003140c015001d0f43d80c2070700c180010455035400980c000c2204010402c2000f01c00102c00041a4014200c14600f9107454181c0b400317048001c80d04031002c0c602040215081c0e9544d44500c0d003542030306d041044061074036904403003150b40840d120004258001c0040080406401c01558800000644103200d005248141c0048441c0b401054000800c0400c1c8002084040ea071080300032281c00c0f008201c554a03010f40b081e0f03203000c0034200074685442c810034081046043c1c0c0607501c545034000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50271110 1250 50269860 50269883
    0x3080a02011d0c150405130e01020c150405010b090717090703020402040603020408060109110403141f0912020715140c0601030f0218060a1703130b03070f090b0304110102030403 78
    0x9815a50b4807a4010f80b244200e8000c0c1c1c0b81c10703102e10a4012034044803800340140b50081c1d1207050110003002900c5d48c040300c554003040010030f00300051280168230740380034411100606142c1443d508480f030714803e00c0d02545a5405100c141900b043c441200000c160f4a500c4066403100026418000e00b503200039040381c00884d0115160b80c2640107007080d01c0ca050f003213441c41da076942400341c00d5070700740320aa4a21500c200801e0001c16030321220007030500c1c0315104880c8200e0071440030101c18041c00600101c21541c65800c1410003c1b003603020301b00f5681d00d00c020090541842e090744641c2030300f04a0032091195035000590800842001e50f80022841ca042d542a503035242407808550000e000c04921075005500034200078504501c41e5030060380041c2c03101000ca800c01404c980c002c000d01c40b075111584402d0080803955241c1401c00c0c00542805014980c036424640005090056803503546024403400072024000281801c060380c0d0308c2a0410200104e00c1d41840041c1d0851045400281c40c030300601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50272360 1250 50271110 50271161
    0x70303020d020f1f090c030c0b0403060b0103020a1e020a02030f0c03010b03190206090103020906032403030702150706110301150e010801030206180f130f06120503030103080a0201 79
    0x4120404001c549409682a041501c81c200e91100c0d00c200720f00718400e011804564611401d40d1001315140c1c401c55002c0b0b081d42e02d0f5110040721041540c018542008001000d000700180c50203412441082801c0940c1400e55080018015640c070751500c00c2c404c141003101d400d03c540700304a80c02d8001c2e000350966a0420b45040c180340c41d201814000381c040d6003048040d050700d050016069850520212000c0d01d50501c1e0341c00c00041d9401942001d04040d000c0c032000007145c2d90040250301940055113501e0880351202510b45402400d144141d01c2038000348a0750780503840700c0701041c2814600e540d80699031052485d0001c001c00300c051440882e02000300000c52000e0a8007414006c840f0b243d00c40d4800c084c001801101c1d9041e003400001c4d000b01d003c1c00740001e40040110f0000c0e1544005008aa0b03c10005c00404e4480d80641d40a1240070345a49070780c00d100e0824400d502c06840c0c01e8804007101c18058403200c0e0b0368401840b000300b10032400070b100103030b843c400c1d800904441c00e50a0100c4260907035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50273610 1250 50272360 50272363
    0xb07060504051203010803180307031e030806010e060702040e0a060c08010e010803070c090f0e0d17130302071e090501060806090f06010207060e0a0510170702060609040f1407030302 80
    0x21142202c03039101c1c818003442c20034881030503a4100e90224008501e0200031390719260380088103000941d01403040030400700002c0c0180180510340f007000c6180c081c1803000350500402d1000c1c054260b13814840702041d2340d82d098542c4011100c0d25501070b1404565040302194807031034501104009002e803407400448402980c0e11000c0281203e40110811005989802d0002d8072403149980003806c4505c02c0e04100b10800c10740e0040004940b40342e03000529081442d03500350034510f41210b41d030001030941c03d404401450050384c5a0308030800e41481032916500d80d030040e5442540740100103181e140580410301714043d40089101400d00300c0c80074002541e540700060640b12050740d0503481216154009403180c084d206138203201e81c005038014504107152800658405006201d0130b82c01c02495440490203884802007c151040c007540c0d4040c1201007150549141d00026142d03c4c03c5400c000107100240e56025172103904a42c00c0f6070704400c52036080c900f0840c1e450b01e00c440c5015a000e080b10000034983c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50274860 1250 50273610 50273621
    0x6020f070203060f060904060504030509120705010f090803030f040f0f0507150810150302070804180b10020703030302030606040503010c0201050a0c0f021005040305090306090d02010b15030f060a0b0706 89
    0x800c1d001c460f0342e40c8410014a22150044401c81c4e00040c8190016000c51507a401c4942c20074001d0405a01d400f081c840440e00b113460801110b002540145010816960b121540c0345240c501e51034111106400c0503c019100d11014144113140040380d0701040034071554a503004003c42e48020170b0840114103103002611520203114032141c401160b031a0b03810050290300c801e441464013800070101e890821001001c1a001600c13003070105a03003880900700090800e00240050b1171589a840203040208610400342c4081c2401a80290a1b441c00310004903000500a004d40b0717803505001d030702e9682c1e80703011400e01c2c05680d01090b032560030303c5000f542e0113070198060303030041c03540b032400f07000c3e040600c10306031405500400c490303005901501e0300e110880ea6580c4840c0d0810b10a00d407051418070b503e000240383c514251110f2403e9001420120000c0d40c0902c1224000070013074030340d00d140c18202c140d40c2015000c011301c1822034a10020009056580d81c44680d0060481c0461003500e488450070084010300d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50276110 1250 50274860 50274863
    0x6010206010609050f0d060b040906090b0108210703120c031d030c070501080c09030109140106090507081302010e04052a0405090612120a0305090c04090c060c020a0306020f07 77
    0xd10000802c096103e915101c06813000646850185d044071030174822681010401910810356038415440140e43e40c3c05001c40c464003617107002c507070080d4a040c400c140701e1040e4000d0300e4903404005044155481a0451702100000f0000d03285ca850300c504042d00c25420003000300e03000c1ca260400300ba19294055000c816001c1031440c03ca038840d80c0d40c41019a0320322402c81c0d03514482e40822002c00184d03200b2524030350300c2100039140c2818988035001007030a540360284c0403510b14618402e14644101300f44503d0307006100b1140300784981d081228028241641c00750600d451104159041c07801e690094050000451020300108501c0c500051071000da05c0070301c084c400e90b980740003004a440d021000e00792410341d0350081c41d0740c07541e844400030085261100c0440000c01c0c040d04814070320212070f071000341440101a89020400740742c5071001070b081484190380340780301c3c034a4039140384080b4071210b076002c050302d0050070f040072144014000a80c10084981c0010400d6000203a0652180c40020180100d203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50277360 1250 50276110 50276113
    0xd02040e07080603120409110403051e1207030801060e010c0c0e0603011109090c0705070b04080115051c020103020f0f0403050304030203061b071704031b03020a0b090a03060c2006060102 82
    0x1030f20b0714000c01d41c5924100c4071940c0c450304240401d220000856000c0160303000505117152600d95a940e8080c01c00c4c03605003044016814a0070342d580703140401c2c05a0429066030207145454148a664050601030041c040e42c020000a044540f50b01c0e4082c000501c030042e004240b4103005a550045404041c10445006010f542402603083d2260000015642d6041d402000400c56603640d00c045405600000d401390361501c00c81a0004031149070720020405002d442c0d00208000401e0076101030001d429500917405409001c10b507074101020400b80100c40f0781c0c24a405640c07000c0324151002c0d1800344480f02c0d160b5040001d000001c020b0004000c2007202d100380c013550780d6643c50161448220031102c8501103105e40801c4040001a003041a62105204503044541460340702d40b42c04c1100805071707101c0018518003e07800d2040d8600209010000d1940203a01440c00980c0b07000704200020600c07009000688480541c801c15006151000f0b1400000c0000080c000318030326503070b60f00c000680300603025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50278610 1250 50277360 50277377
    0xa08301006020d3207050102030103020f0906030a060c02070503010c020c0405090105010f0303030c05190314060f030309040b030a0219170606011b15050a0603030201060b0306010816050d02040e07 86
    0x41d030000c1600304800d0119203034040b80003031006418100c050710030220780c62102a800b5914134540c000300a00400b90040000680300e42c1507105005608040c41996442050b90030704110882c1d50004a840311503a10850100e1261000c840030381c0780015a801180e031650829200008190303000901c01c0741d04004540c188007a44030040c540e401c0381c00030300035507000711400c14051001c20700030b800039410101307503180c030900e007008602e8000f0307801006031000800680c0701c0c2e245848011401912030b4100a0807900307203003003840d6040001c0d40c0f48580c03048103004949a030303a4226165001e01c00055040d4020344015135a2020066124920840d8084e071404240799600340c800c02200083c25500c94041a11000c0615026050b50110042400f80845803240a01c09071040c6868501940c0c1c01400341401c0419140d05500e0003070f0a40b1a550841400d0600034010070a042c1ea210344900e41000c040f90b081d4050605083d402c0380d40740328021001980b01c1c000a0b0001301c0d1104030b890b840c455402582c95464 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50279860 1250 50278610 50278619
    0x3060513060b09010501080403050304080705060711160b180409120309030207090605180411120d09050d1e0c150f030605030a020904080a020a0c0b07030801170a083010 74
    0x4003c1084c002c2c4c60004000d0030001d0006405080195009406618524104286643c82e24500502120f11500240c42410f14441101c4108040303800300c0c1d82d1080811300a03080c00c02d000018003c40c00440364104106035144d40b6a1a594404894140c112901083c58504124050042c08291f50101c0051060303080014800280d44500402c0c2ca030001c103400c80780011240020200d410180041d0340d4290683c80300e01069aa4000c4841d030b03d0320b00009403046c8003c0440c00741860060341d202d07034021090a5100000619100c0300000c641203c03070451b11881015091800d681c00003038001c041c545c07200d00d400f00041d40d00901c081055410320b560502070582c941040c0754071748004c0c2500a4010b521030011a001070751001c05040c8103d800d20480e032080855403203010448030319501079044490002401400c1c958040550340c0906141c15802002801c0700412568600840802a010390303008900c042c0398525481c0b000801c12401906280c40102420fa20350416130240d030320070014612a040040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 50281110 1250 50279860 50279869
    0xb070b10080604030906050f0904051003021203040b0415210204051f08160e0a0e090c03010b01051e090901030602090108150102030d05100b0403080406080912090103090c03060513060b 81
    0x10320442c0c4c1591050301852500d002599580c010700e480d406012000c1c058005a80c03581d1040034455445002d07080c001c80d2a600505c9280b801030b61208065410400c0244042c8840d03408440442d5281291034030048004081201d500a4013100f550342c280309058101a01195900940f09548044170f07660390310301d00c011244032a160030880d0400070602c1c240004142c0c01c05038200c42c03442c600c0d900344004103400400000d4034081064102c05421002503060200c070711000c0141c466100c130140c0c000c00c0340174150380002c0c0c5a1701503650344810400c01d4607004500308000c041038600c100d0020340b11071099610382ca801c002941140e9003403030016511000245001c40d128155011540d41a00510700d0300f0f9490340e203580505001016048200011075001400e01c4030900107000840c003801400b074a440c18400024a10900540444c10350b030701481d014150f50b46160202c07000c10701d0900740041c8000e0286089202120b0560000d80b00718504000c0110203044c02241100e07052086004202c001150700802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 50282360 1250 50281110 50281123
    0x504030f0212010b04020a0f0210050f2a07060204080114061507140f01020a0f0e010f0f030902100e0f040504050c011112070c1d0702120906040b070b1008 68
    0x508a500661404405410282602d4503442801c10020070800d10708400306043e039100c00303114070000d4541c00d09031820340e9060000107004441d840c030a10807414078400380303400d00c6400fa007140400d07041444103071942c50361442001c58140002c8012904c50b03146082400c025080703071281d0910755080c5036087c41e41000400741d46106100042012556035200400c52034980c02154007280c52545694403100d01c80000c00c00710001d0f0300c060b40090ba85040490000b0859450440d40301e0500c0070000d4a034000340e0300864410611162803a201c2c4401c0600541200600000500a03401120942607800c009505c1340440c000c41605980041400614009110071660115405840c2c1e8001d10b1f6400310561240e030f28009080c1d007100441d40b420040d012010010390100c00300310b45d0012550800c1040d903602d50039010b11403082e84d105203070f585000745029481d0700481c1c00c22880104001912017056403441c040d90060f19501c4450390f2210260720340341e404801c00b80c40030301c600d80c031304a80010b0050001520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 50283610 1250 50282360 50282363
    0x150806030706050906090306040c090b1503130f02090403090e3d0302120a0203010605091e0612012c010902031203070c020603040b0f06060307020c090402130e070306060501050403 79
    0x106031140c60a0b508450640040000d01e45c0624200030320ba9055800b0007200740654012000040102d141600c80d108541030242c0b00d40c000c40507000c040d44085e80b01016030303030b001030741071900d03904120640341c403007503000b174210380203500011000902c001d050303020794001c060380c6070320566122503116113030001e85078000c0c80d0074045d0055520008484d040e081e01e06010041c1500c002043e10301c0d0b100e9000810b00d403103a45c030a0449511000c908015480c0034000e0300020901520814a01d003441c1c600d006040310303c1681840c01c50403001c0030402a03202c518007000041202c1001b00702e8429042c06000d030f0f080d805078458400d512001c041074074082040c030601c5c003c0c1c1c0e07000b4010043c10500c11748425481e00020050000d00c03504c920140701503200c2800a5109a124802001d214500500680300082000d04441d01400d800e00810903941d4000408000c1c00d03608a0ba1043c440c1d8840c40014005d2600da203400e0306690a0401480d148800000c0b04004e4902ca2101844807a4035000110b4407405240f00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 50284860 1250 50283610 50283613
    0x1080705030a0314090607080a090b03100b070302150705070507050f0108070f030906021b010c0305101403030904140601020f0d090504050606090901031203060506040b0306011b0b040c15080603 85
    0xb034100080c0640444e6540d083c1040b642402c0c040c0c290f00040b85500001c0c0265200c0c8030000fa034654040d0301c0321700100a488000c40c3c0c1411805c0c158446990758005008030840c86400103148414503000b00181c00811005c1c185502580c5803c0c00d00400b2038100040c12100c910541401007640d14104504111002040c0c0d02c40c141680d41e600c003150b41c07482d40e030105c50a041c1da8542800104030240010102211070031039001260a030304000e42d007143c054207040003c05243c9003d2001d040c0c5404500d1003240d100349070015251890707100081c210301c628401582e0141c07801460311000080b13141d01c40c1c80780c0402d801343c2c2c2956468a20b07a540b102141c440900001d80d40f2003080c0804c0c40e083c0e004a4003d00058901070500e100600404c1c1450b400707801c03c2d166100014041410380e81d15004a03030190800340e41c55800c11b8907010b945403044c003014000c94103100202000d030b582090140c980c2c4000c00e80058a011450400b410140799003c014012000c0c44141e03c003609240354045c9030003500a060240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 50286110 1250 50284860 50284873
    0x60321080f0604021308120711090610142505011b09030b1902030702060604050109060e040b0408120c040302030c010e18040302030f120a06060c1e0203150c0703080108070503 77
    0x10100002540081411100410b405c0000300f40d42c042000300c144802056103000c0d6681060b400d00700e2030020010740c0b580c49080f0756001c0101fa626172217003000300003085040c0804124000003083d8200c0c0140c4e400c0e0303090520703101040440742045460005080e0f0260300200300d80401c9010076000780604880f040702044040004000144220070040e5000903405d80c401c2814401c120080e0903640180c0f00e9100581c848010b0180501d410f100b403900400d051041040720341d107468044240410300a20285c0b411a0010024007404104011180481400c490303030749036880c044100d0f0405800c1404180d0180c130580d08845c0e180d5010300341107810744400400e00c221819458203001d03600603000300300710700710702050214049120a0700058200d810780315a40d80c0452411050100448190303601880030071401061610204051b0100c48032039035502940c3e26401e64942c0040307498440c50000e080c1e60501c0810401004684140250489500c80d50710441541d0340c035070400341e58004030701415134550440b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 50287360 1250 50286110 50286121
    0xb010203040b1902031905030609060a080a0b0c0403050304060216050f0f09040203010b0405161206030314030406060f1503050f040818011707050306030f06010f180f060321080f 78
    0x1042034603c0b02075441228070308040d40421001c2d000c41c944411011840100070300c905403600c000b00544c03002d0182e030008250382c50503260329950800000040c126080b0766002c991a03204031011200950b41001c100d03956150b0384c582c02541d40e41080c4090700c40c089070140100d03140c90301030301c200c11007940249a0300020250034200181316030094401c83e03040d0341e5041100016280e60103920b1141c2d80d40110481400c040303010180c0344400d0030f204030450340c1c5089024400a034012080450005076580141d1700e0f039989252241c000c0c039158200d9680a6040c1000044100c10f14070070700400380ba566414409508c5608442183c3c0e8000e80c0e009000500911030121011501c04e07aa0b840c100052611001203114400c40107a245815108800000d04c00010440103003007c0083d0b80442074010300812156141c201031403c121028011603a04003840c0d4515140034110303410451095020380c0c020800e856403854001a010303480c0e0f02803143d20120900d19154240a80e06e030f28818241889051415600c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 50288610 1250 50287360 50287387
    0x81207031110050a022a0a0b19020d0b0a120f06021608180102060c04030c0b1c0c030506040b1806040908040f14030c0f18091f0f0b010203040b 63
    0xc0903021040d4801d0b5405096620748a014042c003c1180c2000180e8403400e8910b41036006450300000000140017041c2c2080c50940055005c0480307400c01088541c03616803101c980c1100c06408454848140040b0f08407443c1a500d80c0000740b030003070440361842d942d90f491014446107022050098041c0844465038800704038550002c107442c01003d68a81603daa00f65507412143d0042a079121141c80c103040d1202d10741d60104119508950202245403c2c01d00d540d450008510640c001c901c01031030081100303000e000580d401d621464541441c00d222094000d04000c004110485083e8070440c00e040c0034074505c1c1401059100b02480400146c2c46a550701c4c02880080c0000c040201c8020204200006013065134001800161003021240c50701d0001290816141c8410501e1507407046c0000c4144070b182e41d0390126580303400d1002c1c001c1c0003c641d0b203d03200c242c100041041002125481c00c0e4149224440780c0d800a09440d010600802c0368000600c012a030728042c6010307645400b0010050750001641e03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 50289860 1250 50288610 50288627
    0x8010303120f02040f0803040801061706150f040504060915020f040902070503040e0702031c05070801030b040f12050a02122d04030602040b04030605090609101802090112030908120703 81
    0x700140d02620b4030b0b581740d9a9951484c0300360300030041c86e003001c1000c0c0700d20142809a0380060110070726500608031401c402680394000a842200015a040c04038052621600e01030030381c4c0c1d04d00500800c0a0718041c20610302801c0e50b40000c954001030070382d4201d005100740c0b080d105020031030031100d401c050600c01003000a6104480c20388003407006000014400c00352041e824400d203142d5001c2e640760700350f004074180b000c00301d540c1c001005404c0804005015902c080078904503500044103800940b40c904010202051aa601500c40250038042080070342e0890000c10042c2074990844550016010341c14400307000f07140251503a46100c0100b5010703c00d02d42455260070b52445861460a50341c2d566034000c0f40c0c8643e0001d84241301c04101081031041d02e10680d540811408050718007858036116440c0c07510b1402c03007690107107565a86000341d0000b2151020031402d502400040b0a07503100e0007042c196102e101d40c101c001401c2c406010403071041c00b0542c0160304d040b01428604102080d03900b89c03101e85 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 50291110 1250 50289860 50289881
    0x40f14011a0708070804060908011109040c1206090203070f03050906060d020604090507080a0c03051e090705030a060212070f02070b18100f020c01030605010e190513060906060801030312 82
    0x81c09200390004544803000400c66035104a0106540e00c0c076100d00071b00403011b60791248050340d00d80481007014945900441d058007004071400900701541550903503c0c003280c2030050000614264000c515103590b54011400303507106448441d040d4805840c01c81c25074008a454015540001d40401c0250511406240c2c6d41c91008017441d06060b01c1764030020460303a00b118071100081c40441480011a100e00c11150041c107645000e0026203040c8050680524400d41216190000080001c1d841d940910030000540401000d41d0030000e0030741001800fa40009424006010440020a5880d4003031844441c0d41c1d8016000303482c0161030800001c0203034001400840320b501c00d902010b00c0e266181c210804010416480f842c006a8080d0350080c0b90610480303055040c5480c01100b03000a83c0c05c18042c010920044524640d0840c6e01166250074111039070040b0b41040e50303645040d910300c2158001c1807c1c0d0300e0007801041030310b07656907045540410a10000c0d004c20190980c4100f0700400303801c28120007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 50292360 1250 50291110 50291159
    0x130e0402040b0303030915070309051504020103061e030c05030703030f030b0a0509041505160c0809030c040501030804031e020904061a0307060306030312021908040302100609020702040f1401 84
    0x50b501e0703901007425135004580c0a000754004882d11400b901041c1c402507004131413071404110710311481e9070b401d680391000f1911300c100452840020301160f100e500540003510030450360042115610302c01c041c020000340400c40750700b003c503000401d00d401d0018183c0300712a05940c42404010002d501a0000c0040c1140380d070704100500c2c40403038540c59940c4131030b005512071410742d00038007010381d00442200d4000d03180da014031091415250406611600300040a41c2101e5084c0d51111030000091801584202803504241840300000900c22100302a0003100d0150329540360041c490120407240d021070800013503100c019800403c000c510564040c0c26503028000c0686143d09070180000c1c500021355224500190306e44600f44101544141c0140070903a0010f0113600308103c0a00245549885084140400101d103001030f06162003081b001c840464240d0080003141c0d11034402d01c002e9400410f05034000d0707003400c4a22043c00100e1103420300e201000890304011703900340402c4040c100c1240300901100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 50293610 1250 50292360 50292371
    0xd031103070c05040c1d01050a090306050c09030f12030f09030d060b0322020a0302010f050d0f0c11030304020d0b0c090411041a0301030f060209040204080a050a03020c06130e040204 80
    0x44100400051070490302500401c0b40d12440e003400c000564811840d2101001a003100280141d0794191006041034024204035899240805040f070398061242d2016210600308814403010400c0306008109440c016001c1d00c10760b035808121140e492601d014007805060080000400a8031586501608900c0e04c0085e03074901348141c4484002e40783c0680001d000f0003c004148400606074045000045004210700c00c18807800e038001910078034141c0310103414414a4407c1550741b0f4800d008940ba0004450404c101c2100c005018100030844107140f400030880c1c2d0050070341202d5000095034410343d0300a11340d4004100c00c0d6540d55512a000d404050708000901c032425031613885014000c1200c3d094403100f51210700d002603112551b200701e40400c40303659040006102145510f0011040523401041c050f944070441408039009121b1030340b01d216280640e02c071000400002103a5501030901a03822100e100c1d90780310401c08148a00c6680d01c02102440c20100444c004056040e60f0007400100b0000c0c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 50294860 1250 50293610 50293637
    0xc0307120e07060e0409020306040206131d061009080a14070906030305071209060c0605070c020607051f0506060a110106090509060709060e0901030f050a02151b0d0c020d03 76
    0x985640a864140035002140d09003c0300d82d001c6401d0b04641d0b0100c506020803016500400d403100000340010f806044002080c2855035030103e504801000d045901c3d4100e29a03410202d1040b08050b2130140c41801c5e10030005030060300c13843d0540c1c1650390110240c00c1401840d640d2401c01e1840c1c03141501d6034051000d00140100c030a11481340154042d80304c031641c83d446031400d007c240800f4401c91081c882c1c003d07004e00006034030101c41000709070b12801c00203864407402c5050364801d0741100003d500840019181d010010081001d006074106884141d030640307007160501d82998000c80789a90421028090801901e101d524881c20320102000001011621107d4500a44030116940100b5030b00000a00c1160303030340480e540c0010702ca02e00d40070b4801c074840d000254012206100c0500b8035080140305400740101403124600c1954002c002805c0300110590320351035504241903902d440b070620507840b494580086200307403004000d5900e0801501813035007045054112410164100704c4135012842 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 50296110 1250 50294860 50294897
    0x170f011e0f150e060a0203030c0d06030b0a090b06090402011b0804091107020a090b0d112215080601030221030f07050c090a02130303080901020f04030f0308010e010e0c0307 76
    0x2002c0c004030158800e682e5a40080505010850211240985020004401c000c2d90110942e5045514800100c0d921035021041c0c0307020303112642000d4000f21410b41481000c0c0440c0c3c3c01506c1e11846182c0c200c54983c0c0303807810004642e0044038041c2c04140c14840020a5003504840400d0a80c030903d009802c06480d00c401404032040c0049000c40c40b140020444150311304191000010048040288211b214000108502c0b0b0641d8100502420300d0801101d49603459590428070641c1c103080482c51090424a101d020300901d0f004000d1000103030101043c0d0314004680d080c1640d0700500174205084011181c83d20559103a11402183e02003405201800703645180140510b40c0150000c00c0c0800380c4004000c1c80d4040a800141041e10410040342d18070924058801129094240b080360356843d1012180a17114900e190007600d04000350100801c0b0140b00c50a0300719009170f8401d4a640c0e281c10446001c2d490a014840a1144140c00215580788440085900c40d1652400c482250040d9900d83c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 50297360 1250 50296110 50296139
    0xa020118050d03060f060905041512060501090608010209090c0a02070b070c060f030509100902190b0d05160912110a0603020a0f02010b0a060c0c081606170f011e 71
    0x21a415000b00c540d800300990301d070003148050241c245008001c50f162a40c09010f80c001d621410307003c1c9844050086010078400306c54001881500128542181c2e10f180031801000240584c2c400c1528007980450180e9051007030300d21100c0040d200f08125120582e0b02041c580040c01241e04600c40e10340045017005043c000717042c02c64400c14050715464240035000d4150f1000c00484c1041500d003408001d0b5281c80021403100600100c100001d0940444c000b0420240342ca4428512021290000181d00000e40b801840c0f1041d02920070007640d01c422291080306d07409a01000005a01c5c03010600145003103640504409100307038901d2184da007960300402c104030b03096400030000c00d030302140c41c0b24401d03041012081c50301924070003000f81e00358801c005008803425004500420240c0700c0442c0802100c00150b1010300310030003c480d0b00040035108203070f003440d140c000d500000b5040585402600321040714240100805214640c5907828501c50f2855900003020360558410320071400201c00d4030100c40d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 50298610 1250 50297360 50297363
    0x50402070503120a050705030708041a0c040504051311060c0a0b040605090c010906050307030b0406030507241701050111030702040905060108070f0e01090903020a14060f0c03060a03080a020118 85
    0x916150015111a00c0c8143c0b001072000000604007006c2101e8903030b21034101c2c0c3c0d000d0b07a00c2c1030040309a240c50a00c503050780728a40307107450341001400600007514401d401500417610f007100d00740810b68481d03070a56a80407040100a00700d4140c111405102d2421501a15821010070220382001e001500c981703403444816101076454645e14000c1c0040d840062081122110013824141a55441e01c00020460b2000600000405503519103640240d07484ea00400f0081d5084000c5400c078980300d50040004d600d140c1c502541c1200c00d40280032400b40200c8921445120302c90868100b0b80c0b03000c0040d0380d014000750f060f080a000c108404001642c4521800d10310b240184000c1100b07606007449280780c1071039a00301141d02ca29950342000b064560003585030540d401c420010803808494a4264903094940350004c040c01c82e08000307003441070070000c3d03480c0c0b0031401d1402e05007164031128070a50003407100741c0346203806c1542e80400f44081f92074200286100303d0305200002d01c414101c10440c1050368038090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 50299860 1250 50298610 50298613
    0x503071a0a05010504090209060103270c0807060801080a03120b060d09020f03030705070302040c0519050909010902090f0d1b06020f0105060a0807121b080303040507090c050f070c0504020705 84
    0x611840a1140c455103015003825a400c01154020347c00040c0070b9030005100c1707410541c840142250100014410020302100d40003140c1d012030b81860950300089a601441c01248920a00041c945104403c2a4100d0300c004c0060400441540c60440e240c1892046203a402600c5810041d51070300e07401c00074422200f50190002c0d04000c180704000d940714201501e00d1180d4014010400821004a448402c40383d0403200010706104800080c0d40c280140c2c0305282c003988a04200545041d0088001d28500500700c1e52294960f0b00c415540c400c0307020305980507821590300600d007035060030235060090119028410401c108404444d4118150109800c035400582100c007962070382c007609011310360b0002001c07640400420305280303419541310341501c5015280000c0d280c405c4180554800c180b20501c01d03144076402120b0b1503440c2c40355268000d131000c490030b2150b020001000d5040d0b200d180d00c1840c0e2075842d1407610300c407404c1ca84401d80200c80c00307840c49101030500007407940d101e200030502035202c0e80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 50301110 1250 50299860 50299913
    0x9030306051210062903090a080f0309060709030b040b0612070f05010201140105031f0e0304030b010303020606041406040207060b0a15140306030607050a02010b0405090f0d0905060405010c050307 86
    0xc840c0031358085601000b40041d140801c0e510ba100e1240f80901c160309416046901da69481014034500303107000300301400c5800001054560004024000d610501485040320342c40c4d140c9443c21148104c591001406401c0013001250001e084824402d4000000a1031003404900403480241410619444840e0841a00c1800c200a58080c003070f84440b1403400e0f02c9451298034080101c0c0d12400e54004103007842c18261070030007140040f580f0240e0018001c80407240c40d1a20fa00d80540408000c0c00158094440d401c0010014500ba006910f507038601c000d40006140c443e03405100103504005021902c82e911408002c40980300e9402900c028003042002034000c008403003019001510111030170501880c2001005183c2d100003400580141c11490003598503501d05100301d00500703403d14216030207800c01050003101c03480082e800c40d0444a907070541e41c4800c1c154109a82c8000c96208494204009201c00c0089600600c0c80c00185030044040d6484d140083d9194005000303041d11180c0d1940000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 50302360 1250 50301110 50301133
    0x801060807050405010320271e04050c0910030f0503030a0e070f0506090d0b0f0a0c0509030705240a21050103021e040e03040303020307020f041509090303060512 71
    0x4000e000010314003030350100811750440c0c0300c4c6480403c0303021001402580f440038000b00d540b0762046000604090089144040040b180b2061481c041680c00c00210712302800e4589468000601d6907000c0c5a01c20014450100c0314000d0100111005011802e24402c1910000108001d10320807000507110b80c0113195030b0f140c0581800c0848401700d0100d4003641c002001031040517803601221003916802c40c4c90705d8840c001030000954405000c01d008001c0306070001481052000c0c101c00030302a050324181030261840f014400c13207171402102115030f80760340a410104400e080980303600c07200c200009261120284c0c030f44c000850a52200071410001251618002d1150340c0500c1d8045800404a205104a525540005541c1004209011660313508180011500d40c1d56074094011407040340103580c0c4580d641c0c20040c0d16604941001c0e806214038480d0712100f0b1a103481486c4070001c4218a00d6103003401c0c640c0803801402d504000310241585d400e404a500c1ea071340550300d030006402c800140305c0003514 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 50303610 1250 50302360 50302363
    0x1a030108150105030604060b03010f0912030506061c0b0d0501020a02070e010510090b0a110601060e090603060907150216120201020f28020406090c0e150406020a0201050309010e0708010608 83
    0x1e410600c407041d00c080014045903802103809a0426000200850314090850010340140099072036018072504e00801c20781001094200c600c060042c644040044c0e5985a0901400740300e10304101154222040a00b10000c1d100c2c3d01c030303450082c405410f401c480c03102075076094220ba00c00340421003d030b4040c12040008801031280180034000a032205d040b40d0900040207040b40146005d010740c0104003040380140705e03100b8202c64826010740e0044443d01d5a452101408514100c00709034028040c541c00101e1504000071130500414544000344581071030003000d041c125005140d0201103000742031030108804002290007010b0b003840d0b214003148a800b40300292074007103119440c6284d9004180900c80b401d501501000c45110b0050406040c00f100388002801480150064181207181105c2c01001607440110030b1080c1c0008c0d200d0b0050b0300d0740120004410300862007a800144c0c04601d1180065105201071500058254008a80c8040c005e00746814102c05411101090b95200000c001c1c0820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 50304860 1250 50303610 50303623
    0x20a240309050307110d05100209040e03070803070e1c20010216050910090e060106030e030301080304121a090607020705040603030203030c0307180815062e05041a030108 75
    0xa880c1420000e07244103640d03264490240310b4000d002d00304035190b0150030740ca601a610403204d9200303060314489034a46844000070b40040503024061843c09121980780880002101c202a0700b05a2076415503442c1c0e40100c0302000603c00413900903d01c8055131b0390a281d240440b24005108401c0c60603602000041540d02d68803041182c1c0c11503000107100e100350b0030045112015600c0c140c030300030036540c0e034610401040c04503030340012103652403c03005862240c0e01240403030580340d0a50b402d020100071407603210348d40e0100703010b80c10a682080000700903154480c812464918480c94400f401c050722a01c80e085166030855840741c1c2c44e0002010490030a905204410140604803000c204413404d50700c00130340d80d00000744017580c00d080c00004181d8860041810400103030404000c010303c15100c1842944600850746c08501c0c546800e8042103991600c1c0d0100c0b207200c036520209404c20145000301c124000d10b4441c03d1001e0000412001c105000e003220354042d540168690255654900b400e124036148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 50306110 1250 50304860 50304929
    0xd030c020c06030621010e101a06030403050a08090703060606020303040303061e06050c0c0907050705060703050705160c0b18090a0603031707211a03061012030507020a 74
    0xa0302001003204c56a9211024440e4180a10f0003402c0b001c140c4c800d15004242c444116000e41c07154101e582000380650300a4240a40895080601c2c21210f10038000f890006540040104a0a0040b201064891f540b40c5034002216001c0324221592600d5010031504250001c9005070800001c110526406010b2000140004911032015001546a850408056009100c10001c0009161818a0041100c4100c10400811042d901c1c00d201e00c002e0040e5009200c1112240226400644503134068464940300c1c15503500c6290bd00011002c003090281e01e60302c1d0440b00005000c1c00803480305030040c0500003c90780e20007004071075000350040050a02d002401202414141082072000070ba01c180d4500ca10100346101e40000e031a590816249035041040e10002d8405a60030081e0004d5141c002c2d00c1680080c1c4041c4010a140300d0625848450032143e00f40395074015081003110785103414811156602a141c568105480c0350b000600414080c1d028500c0b40800d4442d5100c0c40608220403841c21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 50307360 1250 50306110 50306119
    0x8060d0c05040633050414040f0e0304060807020a03020c01110307171b0604051002090a0806090a03030606020c09040308150604151b031707030209030303100806090d1202030603010e0d030c020c 85
    0x480c0b030080003005c6104d9070040359412030006810303c06644598114003001c02c440d5100707001c2071551885c4941e481d0018440c07400091545004950f9450002c00c6086426405d0360150024007440d000640303414031036020309001440200300d030742e001c2004002444c42c0501c10b81441c50756108185c80e00f401e0b003036040c440a0b200d03404c14414400060780000c2e201c0703038140e4803000150300c883c0280009240d82c5c6495108015600a0000b0130540081c0030418081c0380b40300f52000c010240d1203c20490780c4076604036085420101034004607020900400f14164410422807560014902c08170204940b03420a41c442010361031203003000880c3c550441ea2081c0c01c0343c1b84c0000110307183d41a0f03c0081c02074004003002d03800510701c080030502c40c602c680c040b5011401301608880e0b4030b0920750020b03c4859420312803111a03000303d4002c100780c1100450741945440c6d2540e102c0f07400c1c40700740f2801d10003544090180c95066680d6200030804410a0050060030621910300064403c40024040d041154008075140705 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 50308610 1250 50307360 50307449
    0x30c0301110405040b06040b0f090405010e0c070303110c0d05030109050c120c180a0b0d050108030a1202090a05030a0b18010c05040b0c1614150304020108060d0c050406 74
    0x44074916070039101101c504482c08620860003c010424600c11a0059640c20200040d41070301c1c0c804d240000d002401c07040d06d040041c1c2e039807085401c0312004192400801e4031020413070400401d10903003000180c141d190b04024a00070004440610703140280502c00d0101380040010003240900d0710401c1e40c02008448620f00d414a1040d12802d218401803c0c812414808109890304041c80b58900c8484100580003409003a1070304a5072400c2c2d0460750129071400c2c2014000300c0c0c0c5200100590b94041f4540e2a0211000a001d4406010f50000d9070007035004044041c0001e8541c1e01000031128090007501c1c050010300b41002d9048801158134403000300d07681025a1340c0c810341e61010490317048600c402c1c409604d03011203000203804c003d0151201e10982c990280b0110b07410b1070003155176030200e0b0b0489140d182030010700d503a042d0310f00007241c002e404190200005004c1d800c100001401c3e2900c03d511013411143c0f03130000241100c03001d422008504028a80181140f805a542c082150600801046a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 50309860 1250 50308610 50308631
    0x61306110a0f0b04050102040902030a090615052b020d0f0201090906030b070809031306090801060602160b090111010f060e0c0717090d060f0207061104080a03080c07050102070302070302030c0301 86
    0x70400c540b08000302285446000581801820750540303004d03050243c001d5542c0d040150f0960040e0000707441c182c6030546001a60301111201e07c00250813580c0140c02c1008610890b0a14400e1015044c1901200000383e0083c0c0010b07540c406407402c4a910608000e00c40c2c11881c000100584055001251810b103131050900214001000b125441112480d1482c0580c0d0307a44441403e50240d240c03962028101a2070120344207400818003816924084002c104866498504030f80e1075103c140d8001d0309891065040c002400d0a000418500c42d040c10a4548041d180c40e6090845004604004040da902c41d4207115015040100c04d0b08407410120300d50034141213031130b05000091078000c0d41110f20340000b015001900c0b41d1440b0954a500440c003000030861003581c03100a54810442150880e141a030202a801802e00030342d026205c1410003805a4491035406441e4207102602e0703946165024454080050001d00003440c0307031446a07001d00009491841410303d09048003009520a0341407000c21030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 50311110 1250 50309860 50309873
    0x4060e0d03020312040807020d050c09071d0d06020903061905100501200111070b01080d05030408040605070f0602030a090c06050c100b0a03050a120f03090209040f03030b061306110a 80
    0xe5501341c0224030841c1c161124908036101d07118019009400500c030390359050a218001c96031940e0400f00f5114286903583d045c0089800c2000c0101d031114410980c0c503c03401c3c50900c034104034003c503c20100107150100b44d000180c546041215000c80c1e0502451080c208001c01d03010301d0380c100d900310201d8030b440d80c00d003800070f0318616071030701c0e14006040a1034040c1c101803c00d41010a66601e444a03550b581c010500301032031600c03003d0003040d045100719200080c02c5481801240d01c2030b60051082800c1509008044409a00c200c00030380ba5004201c03040c0c0003280c0c4904c0114054112014005001d0f040f80c540340544101541c40303202807100500107088120700c04036408092a01180c03002520b02d401c94005040c124103900050101e1043e41d28070020000d2103401011556403e46603072070001c01c045011003d0300e1034581c0094000804001040004070050000f4241c148603040215600820b080440c1c0160440400c071542c882c841d520403c049600b0020031641048410050240001c0c6602c840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 50312360 1250 50311110 50311117
    0xa060605070c09020d1e0b0913020306010303080907081014130206030a090302010615020f06010806060607080c10090605060f010309081617030709210b01090e010b03010e0304060e0d030203 83
    0x3c10542c0c000071030000710485640700061500c003003811084800c0d60424180c4c010300d113408203140103d420a0210710350034100c181302c403445940180100460781c2075070b40031648010050b04c01c51140c45030900c0400c20304000d2155004801300340d4800112098543d984001d40f110180c210700700c03c1590200030000d038441d081101e0b803121601c0f2010580c6095844e04900402e0254070624001034020412018584d01040d00c4140d02d504c2c82c200c40300c2da601c1d0380c101d03502c0301c000707031145a4020307001c00c0201c0006040d030028000700c01d40101581c00c1c503480c050a0788261040114100c6411b9503c8082052900e0907240320200041c0a103810800f09805079550900d80c450000104c4460681755107a100b0007210560071503280302e000c11100e840342401c0b54085d080d075060340503000c6524818104401f0710800c04440000c519080b00465089900e02400c3d00010403148018107015501d1314091503040d14240140303aa098050b00095076924a400b01c0103207030070205c1d20075911503a003904009c0003090340002603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 50313610 1250 50312360 50312369
    0xc040606110d030c0e0301090804030b0105150d09021f020703170403050a021507080408030309100b0f040902010e0301020406090f060903080409051012050d080a0506100e04021e030a060605070c 85
    0x10f032480c002d84141d41749817017030309800e90540c03d01802104004c40740d070240084a1182030360344034a98865081004821001900580030f040074004040030070300c00e400002c80f85002600100302c034003040c01d0203400840c07603030b403000c0150348025020010050480140d0243c0c20a00741b00034206420f43ea1070b9600c0b03110980300a4800c04440c0503141d044010041110651075014030403e6440381d0710490780351260400c94404d003031030150407c519542c000c640140c0f08041d0006000c0320036000140100301c0102842d88050b4104400204049161341f403d10040c4041c090a4540c0c082d0307149040b9180e001c00405402c09410000421020000501204281e400340e810380039001c140c554071520f0500c5800c5041c4d0040d03043e00842e010003014000302041c0e00525484641c4e031092070f5500e40440000390746050b10815080b030381c10152140303894801c03043c590000c903000b003015207004501031003412513540081040031201340000a001014075188034803001010103040540c00e03c1610341740d40501c1d032014402c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 50314860 1250 50313610 50313617
    0x6010b0a11010b041805010509010b130e0106030206030a09020423220c091415030c040f09050a0309080d03140601080720011a03160308090a030f03020c040606110d 72
    0x907107180004080d000314200d5200500f042046140072818603e007505032400550b2694a40381c0410102070301130094010b90301014007141c1005145004080c010a4803090f00780240d566401c1c00700040c1d60b99001180a10940840403c2c1c00b10300d80108401c813881402e03146c1500317854041c41c045000a92048950000001911450300d02d03e08465603d520340003223004041507003607030380813820884507800106034003054035880b40f842e91050710060000405078801a0305d0350118000901c02c0c41c2075003290821103510b4a02081c0d51f06070381d940501e8a0400c400440c0490b411010a0000c9441000841500c00c00341c602031103070291000d0f80c0325400e01301414090411008c900040c010500815003441e1010500c07150140c1c242c00000940e000f004c010004201c0510819004511440c00144810745054400110341605180d51b803030320100d0307021a110b44d4021542c1500040400c11b80c544191040340030741c0181240c02e11041c10041114115041007080c00324030640c1e030040160000d038194040600c4d0a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 50316110 1250 50314860 50314877
    0x506070c0c030c0b0301030309061805060f1204050307030e01020a030504211203050f0705070201020c0405060414010602071d0112030804021906050711030303040b0f1e150a0806010b0a 81
    0x500416104850b000908440400f09001454000403001036040b01d010307948901811b6210745045a05031602c0e0007400040d90142414811480e0042c024140000258206443c041c1c003c420b4510f0044215001c0d11603030400300f590400d26410101d4900c65050901c06450f9860341980d02800ba40264001c0d900105142c0745030003440e81281e0103aa002c5078001c014425800122000180941f03800c9908180110060003c100c143e40030700140d50b40513605070080e00500007243d0600006143c0201a1540107844d03000c46814010540c00c1780d0f000e0510766001c0c100503070400380d0306101c0071401100d15203261103207001040004044e0342c00e49032960341464187ca071500c4a0000074403040208580c07911030f20000c0302c00a401034025004004c4148240c114410641d0202c1c205500c0c0c1c0000c070b8001d401751a65800180d03002401c4d0398907992200507440d40010300c10301200340301b0f00a0421514110301c45400502402c0500d00500400c0051001100070502c80d810100c94811902503a50450300b442241c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 50317360 1250 50316110 50316113
    0x114040212150f060f18031603140c0126040318141503010f15050d02030403050301060e03010b010914061608040617090d0c020f0901090506030d0c0506070c 69
    0x1601151004640075403603500c2400e1a100700a500d40504195070711820b40d40e00844038609120096a200d062054940c1d401e01303461440c6420f050000103c901d9160195a080000d402d083c02041c04c061405401802c40c55015400da0520380f801400c0b510f030500c01d07a1a405982801500c03c0e40b000d902240d826650107494526080d00d07200007003c50301000c11840700010851401d050311560a5900807100c41c81c0401c8240c1180510703101c00e0007a02c200e0205d00c037003841403070043c2c040c04845400a1a0140c5011421000b0313004a81066404400081e000001004160b80c02443c103034209800710020800104400000307400044507104524113000e4031003490000d03a0700c4a003951605e2105d4200030035401114680300c1d4240d4014020031010030b96030a107440e900e048032224144110752001c01030109002d6a00b082d5404081900c5c1241d100b80214050156a121065207500801d54000042070a040442c04c260400448245000c200007550b17081e0000301d6130020344513401403900d0421007007100d0325 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 50318610 1250 50317360 50317369
    0x50d1101030b09040b060102070e0f060d050f06010b09040501091b0f0e03030408150c070f031808010e01050106030b030a0302060f060f15070501140108060f0702010f320c030114 78
    0x40070b900d540c0800d1000c2000300b48401e841c0898403856007682510000c540390b594540d85ca2505a80c840c0c120301070300c80000e040d030606940c4404442e010b5030864900c6218940b0a514040c4243c00c001451400801d00b140d007070400d8024075000d0000003000303000000ca017040c4004030520744074504041140d500d10710240d15006040001c091840a0b0580c0c3d13030396848003425603941c6801c0c0d21031120b00c42c40c074001804600e1810309840d203072075000340d140c00c1d01402034400301c0e4400c19038504112103203c80b0200240e254030920500c207808200b9030011840e989405800390841d4003040805000c0d40105c9200b07400a03a0206005500022601102240d603d603800440d40102200b9a003e0f0442203450011907540f20003406400707198820002030112030b84a050707504240c0801c1c0f040002c4c66105c2d0010034590280e81080300c0e03200341d081c0700014070000b00c02803010135140310f60f4901c0c0503001c0001801c4c4c03605d80c0c0c20381000c4989558074401c07441c2e803c1545070200148414032034102e9983c14100400103a5a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 50319860 1250 50318610 50318621
    0xf0d06330509120109050606010504050901060309060b0402122e05060c01020c01090305180307050906220606090306050c030903090607030504031709180405030316031401090507021006050d110103 86
    0x20701034991490f010441070701a00805580748140c1d024415000040d00540c07080c800c90301a00c1001d400500300f40d207000d1090300581700741541292034a4503500c0e40c407040d403910702c09000041e06c00d19840c02d003410814000e1920302c4a124080030110311440e0101e000020b505440320031902c043c0e814964540d440380c2018024001c440380e2043c103500300b120003010701d540302e03024100c001c80485010744840e428004050b541c03003085c07050307580003004100000c001d8941900c0300d107490503200311046000c4808400403c00c82d401d07500090046910750009200340311a603c02c0652094803604414903606000103c0c2e07a481c0600a5118429440004c845081602c10000e4400455000e6040b56080002c45003a40c1300742c00003540140902d0160b04078075800700c00000b00c180180e802101851039621240004490392044c0d800c00010302da15019108041301e840c070440c82c000d200c0c54400103864200110001d04055441c0540941c0d00d003488801e00a503034904844c036030b040b44d10400c51528031080303100580180c04c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 50321110 1250 50319860 50319877
    0xd05010204091b030e070b0304020f0901060906030f050603070311031510170105040f0219080f030d050f0f0105040911040507030c020106080703030e040906020702060f0d063305 78
    0x1400840c1c0082c08142c00d07040a5821079007814800204040b4a804074100c41d48a03c61003040d80c40840100803100c03201c801580c0180c0050301c1403944904001c00320b4441e000aa11290000f00440b03c10000250f0510410b80c2c4010019810311003800c1c0400001e0386d40246e0702002d090070384c1028800c481d55800b048842400d80c2d1014003640103160404040031070542078812010003011201d802d403540d03030040c414144034640c00641204aa2400d1b0240020101003030707040e0300501000080801e1051081040500450a6800669458030303401c44c3c020503240c01a03c5807080608100511480141014900c1d041d034106850005000e151820611010341a910003190840d1070720050001a0741d0540008003140110b400034001c0c10396409480d0b0341c0e001280b00240010354080c00c030f1801458141c01c05d0000328081d08000d030402c1c1080d00007803915440410681049800051f0f920021146801404000c10b06103044058a010800c080c21024040c400b40030b08250510904d218000e01840a481c0e041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 50322360 1250 50321110 50321113
    0x411010e030607022805031804020d151805010305031209011409031b0d020c130e03120415020406050304030c020d0b0703020a030605040203060a030f051203040b0a0b010c0b01140d05 80
    0x1d050040c0d01a41768aa820348000e6484140540008100c1c1685500000d013a4010001c42c0707400802a44841c0d00803d13140c0180e0300640230803240d40448154051405041b8000d2110340c400ca01d05241551184d201c0500c2c008040d06080c01080820b07404015908290071240391020030b03035100d13030080d801030001d5100704201c014914180100c00e100000a810880070201d100480c030140c820030150781da401d68003803000503800404280d6460078030301d030703003000d03041c00010301165086004010794219007050090984a1918000b0041408000f140080711540e10400c11403400c1c0c10300754000c14520001340302405000b0b014100d0021902c07000440444a5000340b50846103060040006000e5402411200002828504041820b140038803c032802030308002d000d002c40354916502c00c201c40d102c4910a0301c450003a0f10b41c010b40301080000861180c2d03c5503041120500d06100341000321100c2c105803c0c1040b040914410008a221103001e040d103070351561001c103540d603100028280c1680100010001d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 50323610 1250 50322360 50322373
    0x80702060a0e0907030e060705071a07050c0d03090b0a09050a0609030203090406060e060909070512010801020403150915020c0106180609050708070512070c0602070b0709090905060411010e03 84
    0x1c00c0d91104050310010021100350480e51a400002c509035640300d010001680c04ca240804d0140340124000c2c07607030034480c24a05010340d081c0c45151070700400494044001c01d5001580c0c1203e1350003401703100c03420481424200240319207034542c00c0c02400000c24240700a5610f1200e4000e004081040200690f485a828040b0f0f00d02071038001e40380c0d0000c01603603000c1c0d0b013400c00115065000e09081e1704405800b41800307040c02c8411003041a54000500010f040c014208900e01c004014024103030b0182541d0400503a40f1461498a03840842c0000e034119001440d060341600000d044449400407000000d10160710b0312800811640101915401456100c41a1505100b01d4460b900034008441030180200090359419070107441d111800c481000c0022020411111803071844926203400030b085207010100c185a9580d40c100f2a8040981a0f984003154420800c920303500010751006032215010034007200300c3d0340c1d0709d80d0f9640e50041c03c0100745948492000011ba4410110b000d10410010215100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 50324860 1250 50323610 50323627
    0xf0305060d080a0c0b1506030a05070e0a080d090f12060e0c06040e0402030106050d0b071b120305090d2a15021603020c010e2b0c14030609010c09030f08070206 70
    0x204c8041ca4100c81e031080700030000e11200d54610024080310405040203145545403075020004100045c945410300c00d031901c2200341b0b6140e1421003005000d40c500102051684064090b111522a40c80041c040070300d0401400340305868980d121085900c0340010403406a29003d0700d0428525521994101502040000301901c0032508035004900030b9008010240c0c440b010301076808c510380806040c41e00682c0106d49200d1064206000307400c407800382031004819594402002101610407880000d480b1000c0c0100c0c0e50050049a410203840d003000c6003084909860110b4600c1c00710b80c185100d20a0303605d820107211100d002030200783c2080d1411550f070400107001d41c158110444040c0c0051084a998060340d50040850265000000340040700c0119141e00f441e50050101d24480c4c2d411501d0300d100000201119584805800c007004c103600d00720141c00070325103050002004425181e04000c061b900b20b5400600030015a500f00c2c40321100c02c0c00c68200340c201413040000003508820005501003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 50326110 1250 50324860 50324867
    0xe0103060e09011e0e06042009010b0a0305060108070206060402071a040f03180f0b0703021005070801061b120e0105070c0b07020f091b0a030905030c0d020c010f0f0305060d080a 78
    0x1802d003540c2400f440c13020b001100030116880c0700d0396800c0c0c951015005c1804520a0703028010050b040d88581c5030701030100c80200e803104401303901c100076140700422010071803601405a02d0307010500380f0b8002024582800002d50350f500c0500100c1c01a6800101e032014028030f01851900010800341003415070030b06d850040c403541280b070001d800150050705a0280400901155022600d00001188540c0d0900c041c81c40d41e58042002141544111a420904c0303410314040c00d449680c90707803035400240d80b4248026125240410140303400d810041803d400250584580ba0180700292500f013524034030140046c0c41038810f030100038000944a14000074602640c070001c00c1524400da6280321000301c0e580900000d8503007510003140c03030010021a1444441403001034140407006281c08904200f05859143c00c45e03000200d03500b5150464241019181c0d01000030181e440070a10f00f48041d000d0464000345a40501e4504808241e184c901082c83e655501c0f02d9038101e15000201950f80740300e170380302c040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 50327360 1250 50326110 50326121
    0x110a030c060e0a0209150103051f050f060d140114042a180801060303030c050702060d050a02040b0c0c120a02060a03150b0c0102030f06030d0207050918070807090f0605100e0103060e0901 82
    0x6d0340003034101400505450030469601d5031805d1902d900a640d9402c0900f040301034100b50340801d421078000d20042c10075132201e005407503080318603803960b05d861350412280c1c4045511100009019609040f1608030350a03001082241611010718480e402000d80c0c00120340550440c00c1c140003107400114007151440044d0b000030201c038802e803400c002c580721a40090310240076421010754850418000b8408815540d000164810448800146042c0d241d001c3c02c1c0140e000745010980682c040a01910b80741800390310403103448880e200030064000076a000034030078402c109207902010380301c00d40400201d84e6245500007410b040c5041c0d41c0c5952480c01e00a0007504202c90920000e80100e000c5030803820302141c850000072040e4043c00320390f82072030309100c0500b10103001460b660340ba01d0b031000101c21060286501801c0c4640242c041245082501c105840040c01000303206c9180500c200031640e00c0001c0703090410b205003082001c0a072844016801014030750b001030010000181041480c0c60f066200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 50328610 1250 50327360 50327401
    0x90609010b10080105011206170f0705030309060316031116051506061e091201060806010611100f0e0a060507020d0203130506130b0406090303110a030c060e0a0209 72
    0x8000d0940d04a08210350740b0314407003075000862072080050009501c140e0350700142e1210401d003c100182d580242c04400042c00e000220ba58004094000c0d40400c1031002d41c00602c0700310f000f5030401c00400b001a10350f1101400d18800a421840e05c2e840e942d005e80c001c40681c00c44821000c1d220403d560076005055000c0000326514014540f000017048403c16006000e10400f400d0719040030244000c0d44d20001840c540300d000d41c001031203500601d075a02d8201070381020f0b90030300204403180b40035843d07407910381d042e0400c40c2441110454400e8030f1000280004985092083c04144580c104122400a041c0c09032009020302450700240144003550b00564080d200c42d900700da01028000000b01d0702c074001c000385180c1c0030781d44003420441468810043d0a100c0031b070344840000569105420441c80c0d100b680854003041ea800401c0041c9a080724411030444501e03005424400780740c1e60002c250500c0c0182c0200300a0b41c0e55145410b8900070080040c00c150b01400006d42814001c40310440290741425 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 50329860 1250 50328610 50328613
    0x403060c0809060403030f0902030f100606050a05090108060f0402070609020a0b0f071704081b01020c060f12041b0e0a0f0207020114030901021216030606080c040b07020d0803090609 80
    0x303110062a200d200190b02c5607000e107002e44042c0d02d42d507800f00c0c05480032407091841c2c5a02d506141000d69801d0020600c5151000c0081180e2200741001c041a1015540003070148a401e008500d042a00b080884e510360109181414580c0d070b543d00016080f0003050446904184045103010030030a09034450620540200d4800080e140c0e0f4140d1000d8600c5403400c108011081030109a001416104a4501c245030784038400703040640303a50b0007614010880c402c0303844075a807800c2b00032078558061080d5510f20700299035203484c21207a10b4000c031042c490080c0c06001032203000001400d1162340c4a40301e0403040c3c03103941041000d80e2100c070031440c541c082c0c03a5028603d1070300794148140e40d014400c4a01c0243d041e110040c45103001e0a12815580009010448a54003000200b0319600c600418031b10a2441010b145840c10050744000c0480e0340e550010b105204050040c082d192811400340c800b1600c0f424112070b601e081a102180701c54502e00d00051041d10084140801c040c0e003c0f80c014880c030310150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 50331110 1250 50329860 50329871
    0x110304030c020f0a0f051519180503070f0b0d0b0a0b04091401120206070816030305010305060708010605090f04020405040f050402130902011d01020114090c10020c09150a03120302040306 82
    0xf010842c4650f0300d8854680004402e07102088a0304016840c0c210001003481e4003420b02d4424880c038200c5000c03441503600003403441340d002c0303c0d02d40c0c0780d038480c0700a014150010041c0b40e00300090f140d00040c09000d0641c21501c0455025400d510039000209d00ba0000b8100010840d0345001000d0181c005000c1c1d40003d50130310b0754060041c03041564040c10bc4480141071a02c0c50001c1d001d001640e8045a02511420002c20038880982035402c00075860a00c40d81d8001925890f501b4010b0420b040a080704041060300c000400c411581b00003907e41c4100b0441d03100e4440380791480060000d10a6034010754100741080e40110340c040955102a204038001c2d94192040b4140200c24005c0b9420340030000c0c080707015488040c5802c2803100e0f03600c07190744060000141104c0a2001041c001804681000d4075074098030300f241da07a0815540f00c80b4a8130b01400240240600c501c006840d107280248450000c4509480303400140d5100c000d04030007075400c10840107a440006500801a503c02c0c0010b0302c0103400c10303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 50332360 1250 50331110 50331139
    0x5010204170309030316150e0304030308010806090d030c020709050406020405120f060a0504030512090d0216050108040f1b06081b0903100b0604090606050702090105010801050612040303110304030c02 88
    0x300c101c500e03e0000801540c504500800515500c00742060281c0d0f0000c2000c0c80d01c88004054031803110311003411030045455510310720700288580c4c01604006102d03007104042c08102c003400a003a856118013070502013000d011203071040749842a00e07804128181e0500c4188028071865a0007401134417016259a04410304018080e40c1e1143c650fa5280e034154881000183d40000947c40190050301c20b02d420341c500f0028070204030010b04162a100b0498100f00a07509040b0380403c00446902600000c07400001c5c0741000107041a80e000700040d10322002d004003002040508a201011001d50b40d100c64205910340b000180300050869800550885600d5a850484805019600c07002e01c01001482104070910300c00c40506400c514094001805100c003040c0c200190040201400c1c9a81d075154540d030340340c010450201d406a101300d05100c4200014081503c51001301c48010440910030002d5441d43e02d02200100303001c0c03000160034070000c4203000c03c05030302c01d543d800745500807100d032040021078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 50333610 1250 50332360 50332363
    0xd0b040e010f0b0f09070807080601090911030603160803040902030402040e010603030f02100213180b0a08010b010e0d030e060f040e0c0d0e010b010206010614070803070513091404020105071e0501020417 89
    0x44d2840000300f000007000a8508e40f056145d0769000c0410b252102966945103425016541c0e00044202502c4010042181c907080c10880c26403241c0342c24a1901203240f5150f038040e03d0f403081d4011b40b0f2009400000240554a85800201c15a01c00000801071640d072401c0041c05282181107080050107102c01240054a003802501d01ca001d080900d03a80c0d540c9040c0302202d0722250200c1c081c2803551540c0903010a5500d2801d0070780100b509000100b0102d280400042c030800740ca40d411403280314501c00300c001107a0720241a0203001c0060b100b05588040000380140c1703030300a0b03910141d0f207043c5020402641041650282c825040450720034410540c01640d070b6400d03a1800718005005074014801080141d20440c00b0480c1d100c8140c29075484c1440030303142c0e017002707074000c94840000c1a00020310a60a000207404c01c0000d1200741030820481d406046c1e4075241d108043c202030304003d40071914100b07004120305d01503024400844c1110a0300d032686440750103500117101d00c0b000800ba0300e0401c50503140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 50334860 1250 50333610 50333629
    0x70305120a0b030708061510260114030a0b070f1202040306140c070f0305030a0f0609090c080604050c012105070e010201051602030304020d0516060c1209030201050d0b040e010f0b0f 80
    0x448804180040c7c2c2401c1840301c0d2a02101d500001c2217552200e8400b82a88801c101400386a404c8440160398102049071010f0300180701503c2c041e0f0710465035680412040c04050f5005101840e221486400d03240b401c42d4125442942c065400344002000010030403198000701c50401903603118145965007038032100045c05004805014502c40114401c0064403610003164420003c4200150844600140800315240f50f04030a07a120745c2d40e2100c03004e00c41c40e101d1040041110100501d02407500b41e036840d44810010b008141413010040740c844002d641c10240d0000e9079410441044a0320f0700ba040180b142e00b4444c9224055480e01010801c00c3c002240010281c640c1c82d002145561035039030130700409141480701034409024161800846110340c0d158503008100036612841540f4039070a00302201902e02c0004024001244010001070760041c0c00d64842915a03200041d1165514020a010b0103840d42c604203035510f054400341d00c1501680c00500000300603100d01004802134000e00540c0310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 50336110 1250 50334860 50334871
    0x10608040f0605040305130806010e090a080d0906060e0a0203100506030705041202030f0105041209140a0501030e010605030d030905060c1612030b0a0e01090b03060c0a05070305120a0b03070806 85
    0x12081e100c40000c0340098000a030860b11901d0000e1a000c41c880e40500103c8060300702c090160010030040000070a1444202d0f04090020090813621a1595a1103100d10840e51403521058940c0129000d00c5800d6000c1e5004004551010301d1506e42040180000e6000301d807003200c040c0c112071004c43c46007480d0b02a48c0c401e41c8641c4801d8034082c00c00385103550540b1800d5007281d1610601d42d081418510a00515005520421002070021008000540750b0002500300c40c038082e5021414a400d5a260410001102d00a00b40003c40c290071030305150240016030003945c4c05100b608459201ca9074540d001294803800344041c5c82c040d480e184100204d5215810300500469081795009012a800c2014521045208d060001d000300c048808500343c0642a8002011241da442c010443c0810b580100d44e60030204902400803440d003880c04d41c840f4020207403070b80304010300420b900e42003600071412070318080c1c1c481c3e120103904e14145010303c019040b0010060300074003130140300081c040000110a8081e5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 50337360 1250 50336110 50336123
    0xc0e0906060d0905010606090510020a0b1801020c01060b030108070b04120206030907120809041a03061f050d050a03020f0303042109050409051612170a230307030501060804 76
    0x140c031000200081900034202d51050180d031083d80c500001e0092241500401c51034640082c6645048201329680621030b582c0f07015500828083e0000844040e80182d105e400b410810403814074082c4014020b01400d00c100302c1c5580313000008105500b000c1c0103141264101400c5401c2942ca07000700c1d5141e80210711801c2a108a01640d0000614210000c2c2d68442d115008480c0b041d640d480b800d40708503600d40d00683d00740c40e000030320200b2400c0c1801a80f6440901102510f41d400700300700070a54030741e4002c0035101e554200050320740340780341c02d0800d00004040052074640d4030400f604200d9110340e641d1100710054800d4000b4a0110503010096900c2250461401d01e080000c8190820b244007184a608003000411140441c05a070707144112212280100001e182042e002203800c00851801c0d08280d080081202d610300c0010003024150040815407002283c0b581c0801006907030881504108801c201010300c201c2c202c42c1510000b952240300d40d56401d10460b41d0340c3c0700035200c2d48800d0300d024040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 50338610 1250 50337360 50337379
    0x9080a320d05040206070b070f3b010509040603030203040806090f070311060d0915050f06100509031c0f08070c0c12020102070e01091d0303060105030601110a0b040b0108010c0e 78
    0x1030840e140c2c00258480c0c00640064034003401c1d55502450a6011192080807070550120030340c0840d4030a030002038002e00f080b14201005038044250008802440b4200701c280703204040200c80d644194180c81d22000054010302020341c6a01d0302035200d4100c0e0040c0300c07845c814000000c0c0c04000000e42000991a42c20191010b42d01715281c0050f088086241c080d00003404000306040350a0910480341524000d0a0300d0411031240c01c0c541c0103454002c0d211650b0701407410284441c9551b041010300603080182440340c0d0b69000e48000c81c1c1000f0060104c0c0506000c00c01c440d0000581120001070b20041d0340d82c0d07101d0650358040056551100c080d6000c1d0003020b05007000e20200190720040c14a040c01401110041d40d5107000b01024081c00f604280c0c142500c42c5188092800100f81c00d030302d080c01c3d15016504525000000900c540130041c01d1074100042c1c15900482c0c0f002c240b15040b8025004440070401340b03068108414150070038480c2092075840c0041440d910383c89031300c5040d422040100110342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 50339860 1250 50338610 50338627
    0x102011505010813050a0c0b030a18032703021305070809070e460b0103061206050711010903050315030f0706050307030204080304120b010611030f0d09080a32 70
    0x138100043c0320103c1d00c1e032042500c40340203d2071007180300c0700415041700815036070700d00310150b007044c1c80c8258070b8100b41001480035a000a5004143c007207003d071991a050034850b51042c4202c00c40d84241d40042e4002001c550f1007402094035401c01880b41900352a01c4403251908803205682e0f004903c00e290074106014042040b581d0417200d18a80c0403000c0f50000100c5605482440075440603000c403000c0100700c03d00300700c0c291845000384002c1850034242003002514106250092000f40000100016a991700003040c680c0242141d0440d003110500030010700410703107009020341c0c0c4196010800e115943d800c25002d4540043c0d10000d04002c8409862010714050094a69070000351000040c55020302000c150600200040e00003402e5404a9509001150a140140c2441a007000b010090419921a100107000040b25030000340c20010940d1aa00d800c04c980041528880c010301c00800020710b00540f40c1d0258405070350602c078043d20300098103540224031010780100750000c41030f44140101c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 50341110 1250 50339860 50339881
    0x11030f0a050c04171e0304081f020c030a1107090606021005060f0316030b0c0310030f020102030405060301080d090602011503230105010303020d020d1b0b0403090801021801020115050108 82
    0x42c0c001501c0620340d0306141c2c80fa2400140c1c180d00d43d40080e001d50003154425070995a540101c000000d01e400035520385402c1044042d101c0904c040301c0d00c125900c4482e03000b06819560704540311032505100b56900d0781007105000341000e007510884412442030040102d540d810700d00c210012142d10b1340003800c08070340703459048000c1c01c4010000d5038001c1003441a045152824420f0700f050705144c0c10a0842181541350030502450f000e401060040c600b0301c2000441541409044160303504401100101030786440100e1542c401c54000c16000302c40440000b83d9008002074103000c204aa84885094a071181400c2f82215800460150803d00384003042010401c840c9048400d451a103060020502d034550107142550340030f90085006030301c6007040703981c0310f64180078182c401175040c82e15515400c901c00015042890150002e04a81e00703c3d80400c0c20540640943c1d0005c0003c40f0095480349820046c01003082e0a904819000d5404c10301c04408035402c010b0074030241e50050b1030b21165074454080b101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 50342360 1250 50341110 50341121
    0xf0402030115140405360705030102040f0302181005060702010905120a03020601060206070c060f0b10020c0102150c030c0a021e01050105130504030e060a0c06180611030f0a 76
    0x903a09556189500380c110b035446000c0101412411000110000c800e000340021200010100342da45c1c10030342ca0305102240401e142800440b548807040380503c6101b0011410820203600c06685584001000038400354000b5201049a00807140b011128010341c00c00c042c01c0b00d003210b03841a20b0410341e1041c4190301e80710000e0021030780103141540305151160049041c012841e501c0c0031031a44003440d110201740d41040303041c0c0036100c9403014004a041040c03000d4040c501c02c4100510b4240c540300c0d81004000303980d100003107520004110640c800c08403000a903c4915407490b0f01c0c010b024200c2c0401d03c101c04004a54020700582010758035540d1080e2030b0344e885403c58030f845000c5008400120850ba0a4041d03007490341c4d0070035000003c00b035152004001d224081c60080c1c0d0119401d090801c00420340042c0d905074900420340720725684040c1d0010882d404000f40d0300c010724040c6024031a214030480d06001d6031145109080421128142030341500140c00202e40800300480390344002451000b854101c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 50343610 1250 50342360 50342363
    0x15020d121a041806090b010503070803041a160516030b0603030702130509010212040c05090105040902060304020d14100501090606020a0f120509040c0507110a080c0108040503040906150e04060b030f04 88
    0x3a00346483c866480c0c03800d884070b122094a207001c0c11001482146400c1c40075034010b100200040d031070907190091410007010b4616000c2c04c03180d0007041d024000b0441000c5043c0b0503510034180c0c1e41501d01d445012441244500042e1044910000010a03a0030000201d8160340e40007003030588014024895540980001802001995002d101510903c0781000e1a207004030b208103203a0003803500300301c144540054140d04c0103204a0a00f0301ca41d01503240c8030100ea42158043d5404481e11805061011030301100b460706818500c036911fa55070048560b940000e043ea0b802c1402130103200c0d076540f812640d46190301800b51103218000d07110b2000582d40c039050754001c403203420064100b0210f00000b6086038121b061110215200182c1c1404100c0320084a00c101c00045801c10404c500300400030b40d60345000d40425060100030b001080c1170117410010348005006654040c41103c1d100d50006c40400031700e070705000c040742e0324000301c40303480c94580180415620b85508a80c00c43c0d071101400300030712202400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 50344860 1250 50343610 50343641
    0x60906020d0e15092113030804030b0705040e01090216080c010f061401021e070b0f030415090507060c0318030f02090709180207021c1113090b0c1315020d121a04 71
    0x35002004901c21b0303000011409034451940380d43c99410100b01d002e40040030071007009400c103c244107060090010f50b05440e294080141c866116501003003501e00081c034003921120000c261409107040540103c40350350340d051000c5c000c565668100600418034810386a001d60440d40b03080525a0040c1032a02c01d080c085811569031560700d41440240743e010008201314644008104028403170310001c0700700d84c100050010844c8030019110b040d2610030300d004000410a000c4090703003d052140854016000c1d43d000041380080e50391174420380e100d031503c50403402125400e0029408600842c0c5010407945c40460780b40c0035030b0700c40300c00d0802035100c417400b00c0e401510300d14114580410740e803903185054416180e8140201d41c0b0740410081c1900039250b50496801c007600c0d080001d41001c962a00481c0c4a045c058aa141083c400e5044000c1c5810000c0c200003041c0704805410343c001030b0b14207100724a4560040310040401d407a403d580d0640c0f2440040701c00c0c0e000300e20960805500010114503841c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 50346110 1250 50344860 50344867
    0x30309100c080403120806011803030e0609130603050d020d08040204090314030a0b010e040204080a02090a0615050403060c08091e01020c031201080c09040c0e04060906020d0e150921 80
    0xa4442c8036680094000341c4125549411002c0115000002250850340034203142190326000d040046210800340401801c2141d03480c0464100d0b2581810f90303191103c0102a00c6062883c03507440d41c01000c0511007031396903100707905c640600c0c14000b003030090405001c0e585059807542d0b180c09200240c0a2103100f1400c0080c540c0c1269289480600514040c424681c3e0124880e03980300001001c40b02000c00103841144100300400482000103540c0426541c15030761410941e50f40a0385100428031030b885681d0422034443c03141c01c80c55100004005481c0714a904000302c1e03030300403411640c0040803030325126541c0c407080c424090b941408628040b035510410000d460080000040d0f4216044000c0701c1c4130380c821200c01804071880511594030591070548081003e442c1c0358407070070111f203c540f14010700116150045010310490760088540c0d19000b190541d500d0030140d403800d00401c442d0044040c58010710803000215580c5034402c50264150b800180480c0242149554001d040c10807901610700040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 50347360 1250 50346110 50346113
    0x50423060c0c0405060603010609030b06040209030a0302101503020a0b07141b120a1205030a06030501021204060e0105010305030319060f080604120201060b0715140a020d0606030506030309100c 85
    0x50009000d0800c8480241c0344802d401d07028041690000f40129214810031700040c004e07290701101e02c40480390490305c81010340d00d5840210b002441003042c41c0303406000d40c880b00024190009910720444c200a00d04001c0342200301c80c4020041880d01000b9403000005000300584100314001c0c1c0f1034030b80100001e081404400c030180780791005140c10800d0325240010a24042d14007005102c181c0c254590151808011070790303d20030a107000d0354461003402000700c0440c44010544d849074002e154410003c654555040310750750710601c0b0032a011140c50703080c01d914124051042c042e45040300c0d8002c009506545424071201c090400702401c2d441525610100014000c032030910316001040003030060038003030800d814800ea0703030780c4c0c54103040e0117680c101541084110440403c5502064208a288004010f9810000042c001240000c4070120f0f440040c02160403041d030040c140309120b80010040140d5402068003650011075034658940c0007030101340c000341440000018158454a41002007004030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 50348610 1250 50347360 50347369
    0x1b0f0f090d06060906050411030402100908010c051b03070f031d09010306050402090c070b01050105090d08030a0b1306050310020304020f0a060e0f0a0e04150b0d06020903150106050423 81
    0x1400d0082d149240c80c1e04003000450000c0c4a001d01401c01a036091003454491060010340d88005071000740100c0421040e4a1014032840044001d80503010007842480c8107120028119042702c244c8000c03a00701202c006059550001c1144c070070b50340c00010b40c43d60940c680c80544195081500d004407130300b0b10b106144815941c40405038040e5114a20006540c182401803100c08600200040070707010040121101082d00d981c41c0c0da04440091a00c030b540e0740032141c0403541201000b40000d0915001100740b059440e5240c0069050400c195500c1001e601e131040c05606444092140a815400210b02c03c0c031780c42da007034000310b40c4580003512100303824000b0300c0030441403810744d0b0100300001ca011002006601d032102110325829011145403000d503060880006002a02a0008040c544050482540c1d6802a00681c1076004020500e40c12610f8506102c00654000d2681503c04c2c0100d072403000c00940e619004906882c1c103079a84034280f40c20266100e90075000740c030b000246218200214042b5136030303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 50349860 1250 50348610 50348629
    0x50903030c0f0105130213020a0c02040203012309010b0a0305040609050609060118020f190909051501090b0313020d0302070801061815060e0d1a1602061b0f0f09 71
    0x44100091050140c06016242100d401604034501429110801c901594a0305091040101000c07c010390310580554150303803400b10800020742103400400005178165540e0840409a09402c942d02d080a0484080041f010005d01443c03404c1d440c180000311426109038401076011344030700000142e00c051a01c0b0382c3c1c50f0590880d45c1d281107a0180703006024150685a080d6040c0341c411070158242024200c20340250300511440100021070a5096410306100302c640000401c11080c0030030060074459540c07040e4808124030540883c44402c0c00240107180c04040344e100f40300d074007007040100724183d00304901e07103145100c140e0841c82104800715480b0307400c0c411080205040c0304030000c242400f00320041914142160303142d031081540340c1008010340203c0e00010f40c0c10110b0b808580d41c841441c1c00c2c511031a82d04242101c0c0c18810040000760100030229280c2030f402e0344c0850b04a41c0d02e2001c1716090f00e002d0360314007078240d0b018070403401440c20b44030240104d107140666060a00d01c4980c0410300404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 50351110 1250 50349860 50349877
    0xa0203032206090605030708070314010e15030f0a1115040906090606020c0108180a0f050607020c0d120c0602090d050109020f0307121101020102091002150f0112110105090303 77
    0x101c12001085060340440e00300c0004180074100300d0301061a1010240130381c000200600144414000045c09481c80b90740210900200c0403110080c95840c1c2c120000c155404031a65200c4158110100362286000203842000341e140e08001c00c0d080c01c1c6543d586042103524411141c000e8003840d102c51410030089d0181010740880b000000c0ca90303140040500a80d980d962103081903400280d07919819913404214a40d01c06140314550308020340fa2a0380c01e261824008000d4420fa5010043c242001408603484d8005c041e00d608032042039881070100201790603691002004000c00760201c0c50802d0007030080c02c21613806030782c00606082401c00071070303046d80d000c2000f1912a50f40d0040d240451a04006221640c03002340c000f001603500b8016a01505006184058070034030900d012124207078401d40490b2083c09010b000341110b13603021940655030384191811518100c41d940002900c60004081460403940c860040c0380e132103592600c441e5501900342040a0401074200843d2a803602c040000f0424035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 50352360 1250 50351110 50351137
    0x302090c1b03070b040308060607030e040915020d02070c0807150e03101a0301050901020903070603150f120c080a020609040b0406032307050a05061b0109020d0f0b06042a020a020303 80
    0x1417030702d85001880c1400040905208000c24800000420390042007003414080a60700000d000700305040c5814544040c40f460000e045c000070b60b415590b4042e8000d010158841c1a4401000b51103050240c0c0300c2c15a03006180351408000c4070014900e00c1040000480040941074a07402036003003814406965024113141010045a44c00040904003440b41e03980c40b00489000f1410714500e070f0002503d0300b805114800800d51109141c2405070040700140c40100041100696015500c4507140714030f91500c20207071030109214400246040000c504041e42e41d600500c03141c9003102c100c0411000b0010b44200e95000740d5200d02c080002061030040010595600214041a424021120345401d400e6001203014000100c1d0400c02600c41ca0107441c641620b2995150203070502c0389460f03004003201080a90f200342d04180400a00003e50419021240600c4440c2401e540701001c0c4001c0e251014511480311400341c000d001800c44803600c1d44082103040c030640d44940c0007900041e145421a0b0f6610342e08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 50353610 1250 50352360 50352383
    0x4051005030403120c020c0d0606150225080607050309030d09051b0301140103060507020f0d0306090b011815050d020d0b03010b010810060503071416020f0a0302090c1b0307 76
    0x5064001004185075940840c0030b122405107024001d40752541c1c01038488c06040c99000500410510307802c0038019200e0704100d20800740030084025686d101d851034004500301841900d05242d01100407010079103010780010901c6448401d170489255000422804150100b4402d2200b000d50714003c10b0f84040c0100c0082c810340c03c241000c3c035841c002d040c40f400d10a0385403403200c04900981c00c1d44141103d80003680010146c3d10346009a0404a540454091500640d201c440040303030140d000d40305503004c024003042030000170001500e0041c0d921a00102e410320185d41004800440d85480c8a4000c152034420f09245000e40c890741a40c101800101602d610b40e1600205410709102c1c60340d04c54403d10f00507000c0d051040a40301045054080c0d1000c111002001036032050003503d000c500000c3c01c80700c0940c0c0300d41d44500030a02c01050b4208a2060800003544905850300301642c2007900e40003061403001e81c5aa2224000607401000c00584880e00d22103800741e070b10018000f8220f254014481c1045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 50354860 1250 50353610 50353613
    0x110d09030b18060402040c0309051e010515031b15041721030c13031a09011b05091207210605070323060d0611040911090105091302040510050304 64
    0x12442008140c0c0740d28900e145074000b29818001942074200c0e4040c0c0300014030b2030180c00d00b10080e00240c02c0c00f40c0188945110b501e000d6481110059a6500d402c0082105458401c0c1000c1d03001c120354040750b807550009814201d0501c4003a11402e81c101c3c010149040c44440e8a60000380d40c101c3d034044021041ca1154002882030240250a481d200e03c4c505514440e1440d40104440c0c0006443d56200841c040307141540c500300102c4039005160402c488481d0b00741c48645141e0103400854103540c16508003a20409103800d1a44942c1401d0300b646c4603107041585003810311615175895202034080d40710312200000c140300000c16581e21400d12404540e024619800c0c82400d59a010740320302d080502e4000f48104103880486841e0701c003400e5005100203502c500d00003079040b4100c0040030740341c40d14145040b1141103c0c0341c028070845030340c0b0006006070740048001c0c040034018410140c0c0411001c1102d0601440d08200004c07208040c08001030819450b000802c03000001400f0010224000005210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 50356110 1250 50354860 50354873
    0x30f0606020d02070e0403020607050304050a05010501032a030b190225140a0312020315100305061504030507031b1e030201080a09021e0103020d050906060a060906020d050307110d0903 81
    0x502901031710b4180d410a00300b5580081d5241c000070005030801c034010011908100003804802820b42c0c01000a002c203503109d0030301101c05402c40400c5001103c0c42c000301807403c04072101c0c100407250041c20110040e075860102c20420000000c403000ca0f141d00304242202c4171481c20703a00c004010003519071004e200207460040c441003c25820321010b40c5c42040307a8000203030310083d1700102083d40301c8090f8403511240b0f480303071000b8901400e143c1d04c0b92188800441141c1d1541c0403500c41d21040703c0b03020a804003000f074208144500c0c00060200d07080000c0610104030500240c0400c111000300925a2a035940c1c00c03490701d1160408400400001c046041040d581c0c4030200d25003000b5448420401024640e0014424000b600a0081c01070036141180d91640e0203641590304880080d0002e000074541160016220402254404c0c4103410300500411014070981c5004280c2d401500105491500a4816030b02900010603100800c06d4005c03001c80108418003000407100c1c0d59444001a4034114034020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 50357360 1250 50356110 50356123
    0x9010909181b0f06180801051806100303080a15050303070302010f0506010306150c020301060504020f04030507060201020f2203021f141c0902040b03030f03091009020f060901030f0606020d02 84
    0x28180148810420b200180c00d20b10f40710700700c640505104c4c103800941781c1109841125a80308007400d510740000c1048007100015800c0f8409016001c0d43c0392690341c0703035030525501000d0101500080e401000070f100d007480740c0c2c0a261003005540701c9103041c507695400280356511040c0102c0c0180d4690312014900b400358000c69800070801d080512038a4181083d00c0c0c0074010200c001070400000c100100c09544080d80010040d0401070400d543d07d0500e00b00c0b003542c1c1d6000340b00c115464800e1000001d00c0ca441032081e80c0604643ea05614688000074800d4140765840201030015040151000001683d860080c3e5009a045207000341102aa25401820700d01d000c00e0704441000040000541c0300403240d0320304141c10805030780011718003c1400800e0080145100541d0184070008020b51103140c00c0001d144a01e030503000300c2e20103180c0740c848102901e1039a90000d4102c108914070206510701b90002d400804010302d00050443c1c49010488107803502c0d640100c000d41c100200b03100c202c07541400719 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 50358610 1250 50357360 50357393
    0x705090a110316020f0a0206190306090e031804060f0e0705040801020304060e1603020622051c1209050604030206220609140604080c0603040515090c010e0301051b0901090918 77
    0x86d010700481500803444a210380500c028a5488551580d1a9a40a64800400b03802e00d903a040000f0404007030030590b82d50107031031a01143c22040d1031101c05860240500401c2d9680c6011041505250001000038182e0142040041c84000d00002ca9110b40920103188580e01034000030498400c440701c41303400d100401458001480c000a420309c05a155030044841000751846c15100705c240ca8500d0980d20000c60b003010354803030b03c0130000c40b080c601e101100500250007151901c090100e40081030311881301324400d043c0c000e00c091108002614100000e4100800d20000d404015040e821a6405101064020300042040d001041c400784044a030000388180094034554038190030080354070f84c0c81c0c0c040315002c3c0c07068100000250030800300f0304c440c00c0d03113031580c046510035800c20443d139688030302c0c00801071800504000140a0b5030724050040344c1c06001035102d800010003d03184007041c11ba00807083c403810301040d0540021007020b0f43c42540d40e4210b0484042d9003d0025152403403645100805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50359716 1106 50358610 50358613
    0x10080703060c0f020601060e06030411130501080c030a02010917120705010605040b060703050306040c210504060b06040e0c0d1401090b010f02010e0705090a110316020f 74
    0x2c200c6042110740c9a4400342005030720200d913250002d00c260400030301400040309090505000842d0094041c58528002e4080c4c00c005c9500c0c01800550201026500c00c010020100e05200501540108501920800c032944e00001c14060041c0102c0e20000c80a45255039100030802207000c0f41c0b9410b1070748a450303c4150038014000c1c90b0b00d1292034055800c0c0320a6072034601e440c80071a00d83c2981612224190f490b190140802098441c14107002d000c107081c0302c402c0620714030045680391044100d001c10035141c6840c0c4507041e00c2206140c1801540d06020a001b02140c480710260701c641d90b41080364403152880c0000f0054080140701c0c50700d404c1c0070000490521245c0c2c200504000080c0c940d547d9074200702d041242242c0c6142c8261440e42c109000c244010700d42808240e0304800ca4600229015062801e51601d991080d10104880b0003406442d400f116018095103004059210 = true := by decide +kernel

theorem cover : BRFrame.Cov 50179860 50359716 := by
  have h0 := BRFrame.cov_init 50179860
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50179860 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50179860 ≤ n) (h2 : n < 50359716) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
