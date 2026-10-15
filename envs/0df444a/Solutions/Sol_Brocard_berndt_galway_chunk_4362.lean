-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:22:33.838922+00:00
-- url     : https://prove2.me/submissions/9810710d-740c-40dc-af85-b508df09e421

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 784352517 ≤ n < 784532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 784353767 1250 784352517 784352557
    0x90d050f0a0b16032d090f08070312050f0402060306010507061b030c031401060507050a0b0403080118090b070e0a08070312030506090c0a0513090513031101020a0c0209070908060c 79
    0x28003d2140740586881100340b00e244881c0c81e1310b40f0f0b030003107001e17291480c0d460b40b2200014001a05100161422445600070329204c5070780f81402003040c02c0d20601c00c05601d1a003001c1c0320320311521284695010b0703411501a0b0780c942e100030049484c1e010303d103402000b0b90309000e0150790036407648800d401c02d40c1c0250750800020500f0041141503402c604915401c3c1041e079401840418031400040202c2c82c022021940c5d00343d404c0c1e44601d036807401142c05800003030114005100492201350341204c000404103003480203030030a4641418202002c0c1409041c0702d40417501d5141525030710901001488190140c0300000d40e64280720000c40102042c88001070f161500154191410521041c001d070004406981040c1c000034080d52198407420604641c135800510015070348640d405040e1003100480b075990380a845520b005000c0345209101800582d00611a40d1800c5620800b00312105404449081c1e007511100c80c00daa4900060700030321914001c050412582c0c40003080104401c500d81000f0714054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 784355017 1250 784353767 784353811
    0x50c03120117150411010c0c06080603070603050108250503011802030f120a1202091f0f1d041d16031208131b05040c09080c15090d050f0a0b 62
    0x5040701c520000c3c110400000070502003002d41e14000c1c4034601c10b0618000c20700090b00d9000540000da4000400158110108906410301780850780041c426801e00b4040ca5040c041040d803100720355090460000f55204002408101c07080140c0300400010380204404004152008104a0070410a034024841d5140a4152030000a111241d101c505081f40c1d06154003108119031008210800d5034986409200400c40340c2e40f03468202ca0b0b41511181c5d801180800c00c4400f500390780c1c0701200281440140c82400c80303017104110f01e05c01a4001140c1c00150b64280328404290005869005001031066065142ca6900c841030013000340e80c01500200344102c3c0a0300112074009003110000c0015552034007900c0098200d6214041070f580d51103600c0740c4e0303d0319480801e08071160300590b6000900d40c04010050034000380300302d0710044010f640065800d421300004841e28414144090701a1500d4040c010a1100c14842d00b007003501d4000507207a811502d42072690341a802076031000010a4500d000001c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 784356267 1250 784355017 784355023
    0x16060320092e090b0c1c020312070e040e010b0a120206040911040f090b030a0305070609020306190c0201091e02150d050a0f0209100f02030c12180102030c0c0907050c03120117 77
    0x90105a17000784550101d140241d590320000c4804a4254030080c0300301101400381c0c0402620522140d650ba41181d0200f504200903247c1c3d2a17404280b903454400f4121103600c0361060b01050b40d03c4040001e8444103d48041040e40c42254040c4a55920301a08440000b40c00da00900407180e5241d20700820366100d8440004480d000b1000c568160b201d4504680000d000c0c501410030b06014042c00500c00480350003281c1440b10855117440e244a1410f00d43d1040c0700311744110410820030388000c00015071250f81e44c42c00411501d00104c4500c00d4250940c04561720f803480d24143c40141e50b15a0340b00c1c0585144900684030540704484500d042c0201c400c100b503042c1c401e0b82c44c00d190061550080d5000c0c2c610a54280d030a200750341c1c003103000c10082c2804020040146010085070807281503610341d06128404680720488800303504540040000500e030a00015290103861000c4030100d100d602c41200680ba648a0301c2d8100040380804187c80100e110140400c1b812903a1102050b00058002c0c2d40b03842c2c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 784357517 1250 784356267 784356277
    0xf060a0510090e0a02040312020c03010f0e0a0f05010b0a0902090102070603050f1501110109031d0901030503030c1804060605120109270215070516060320092e090b 72
    0x800980d0b490020881c1d034802c0c40c001a00718401c004014506903c039121480e243c800c00d032001d00580e000008500302e6017006d200e142110000c401c01003060725104d8903125250f070501c0f000549031008400341c070340c02d01c5029400508481001880b088615640e081d07107002030b4114160f02c0303016015000300003d000d80a405158807408940600d4041d680d07030403581d088004c40725460b0318104040a0095a0b0182c803d219070003802d8000e888651100f149002d4800d4003c05962009026800c80001000000c800009494010f00c007500c9403a00c1354042e074040c0500d002c94040580e401814004001303103540c1c0101c0140700708403c914821442d40e8031101381805551070705628143c500c00c0000200e240c83c0c0c5210810b1100c902c000e20001c10180920780001180e008810706540c150800c2802d44c42c00364086107000014815810280f2200341250460403640202c5406a4042c4000052602082d075031450300007191a80a240c41300d003038084100300201c041010444001160381088042180701c9041c00741c2d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 784358767 1250 784357517 784357549
    0xf0105160915030906021803060105040912110c0612010303030c030c021c09050d0c06020f0610090504110a0806010503010c031806021b010203090327030d18030501050f060a05 77
    0x4481d65140c421295050050303490614100742d0b070b640e0ba1000003400f41c0010328000b24001c00d00082c0e502c0c80010503080000c1130f8000740c8101c0ca84242d0304001155001c840e0254813103030500340031030545854501e00309506141e40c19485540062404c40d031195038041107060741d001c0c2e981006504640380017a0104c1d1461441d6001603403000160404001803110301640307580843ca45000021740d03800c0452903030011002c04465180925106009143d810417103803a41a000000400042c10500340c0d00948441e0b5018090501d502e03840010140106054040d00701103010304245600c2d5550400292292401e0040900c00d50138580000c2450341300e401a00c0841110110060203004180e0341c05009500006802042c000030500c6510349441c2032010b184220402c90241d59200603040034035140654800c01c1021f944001c0304004c0d2940c030001001841f401d071070b007800c810f14501c50b4240c27103400c41c2c9984010302039804c000030842e9011403890404d00820065485d084602d854004010280030540400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784360017 1250 784358767 784358777
    0x120105030615060c07091d0d050a050322020904050d0f0c2f1c020108011d0a0509120d0618050405060a0b0402040e0f100503120901081009060303020f010516 69
    0x2c00b51807800d03800806010031103000300c1e00445da40341446801e0702d8071400c882100b10b058501c1480180c505020380d00124629107001d0740742c19200d8001801a00024044c86407000c0c4e8494003001880340150a03c4003143c0003003801926141c2440e0150b80c440403119580002504450b04101090140007400d12060380310031724140302032600d981c04403684d00d442c0301c00001d9110303002c1030845900c031154545000c0504580000001d100c6000150240700180e1203060030850300000c0961444104040ca508246d0200021030b96880d40003000d40b0300700035800d5188996200280d452500c071055849a411a1862070740d4140344458110501e0888404032000b0f04660400c0300058210a840c0d0700800d00108014070040c00c04d6224402507030790000460b6040740a2500340140412400560030390341c01410100c0051554000070103512015000e40400b05040c410458003207120741c1c4550987c038000d01a189010414103540c2c0c240259911381e0b04501c41619447c000c0403030513890001c98440ca80340354036291 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784361267 1250 784360017 784360051
    0xb0a050a05010e011d19030501051005061602030703140d0801140a060c050f060f27031801030b040507050304021f0827060f06010f23030402060417031201050306 71
    0x151080c41203100d44250401d8900801d401503664900320f080002c044440c4030311b6580c114682a4211100a48400791084004a042081e03589100c2101c0d05c0d0b10201000200c90300c401d1011034504841500000c1510801c0b02e0186000b42000505a50490071a034480d401660307181d88411845180500c0300f0381104201100b440514022000d441203e4407500c04c8801c0c2040ba070b1001400c040d001d036080002d0484030424000b10703000002184510041c00750007203083c134240110b40d903034074410502c00e4940d061074450080841c0c0e0180d41b10b1594810041e10910082c940400001c000e030303008807402ca100714014901c640d003010503403082c401c4815158803001940c0d280e5984001d10030750080c0c52a071115a4081c0380d9091201e050120b54020b10000d105403100d410a000003501200ba110300e02010440710b000800520020307107060f41380ca5142107000c5503407070300d40f400410a90f21568000007803c2c80c100302d40403005100040185241c840b04007a15240b41d80701c0341050f49440003a2640144a1600c0e80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784362517 1250 784361267 784361269
    0xf0c080408040e060111150103020f01260903090604090603030305130b010e040f020d03020d0f050f09040203041e08031509060609090901060f0b0d0609060602060a0b0409150b0a050a05010e 83
    0xc0f509400500504101da01c9103c0008028501036008403004070344040ca400410450800014861030307800242020030000901d1035191800300341d241c09140c2c0301000f07140272a005070b6081c41101d0008201410380341d900c94641b41410043c20051004900007850980082c0c4810381b542400903800d0f40c4914000c940c1d07464518a2445104094011344007080c14407032240041e52020000111203110f80c02910070b064540c0c0002d84848100c0b0f646005020b0100282d65040b10204125040340d04100d40040c3c80c0d884a0500440d01946005a00324106249503040148400780020303620030540002c5400c00386410400f8091031050a440c4c0b1a0010700610050b112460000a05540184000000070354aa51100c00d0311301844207500c0024902800100f441c0c1c4040b440c06014040d10140380180030042c07800c07e0003941c5a400920014405542d000d0b0220155550782120501a8200c0d118080d104240100d4070000e1904044003842100c20f0030001415003030500080b000c8450585840c0c401c800114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784363767 1250 784362517 784362539
    0x5151b0f031b010f020301080c12030c1e120a05041503061d041a070e01030f1b140415200d02030f0d110c01090213110f0a021c030f0c08040804 63
    0x314040382c59503c4183c10749102125201030b40c0201001801002c3c0c28201405106801c40b82504100c00c540003013110304a18840060188a440700d000400103994201e40012400c221541070445c81000300000c201c108940e01001800540d5409d07000c072155406c1d10002a01111000c3c0300704803990204190b80c0c04030b1011140340c10b5000e40550441607110b601400aa07082d08001c6820350b011450203e81d0f0b41c82c550707052240d40303454151894204981409260301c00c26034500321042c581000311180d044060800c8003003d6500501c0c04d00e02c18482c4000d165009008200250a11503d090040b006094070841c000b0308400c1d0341030160091490607001d1400d4807102e520240d1a4940a0307102d0f1240390300d41200a0042808a52031800080c0c1980ca0748104142076400000414485060070602017200341180202c07402e42e06180c0501e0781d141d10154050b402c00c4100031000e190ba41c81c12906c540c5003134142d000066a0400b070f00381041120855201030391010300590b07014000400034002800100011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784365017 1250 784363767 784363807
    0x1605011e0216060f020c0f0d0210020f15040b06092401090f08010501060305161b140f0d020d0f02031602040b0a170706090b0a0f030605151b0f03 64
    0x148142c84000140010040d005505a0b0040d070010f103515800f03d910590603c414500c0e0042200d0020303040c1c10b03440008501c0b00e2050310191082c0701d2171000d40d002030300801a001d03582100d4000d58001c842c02000b240120481210140d402c0340d44e050001e44a0700d050b810b800c3c45161581042640100030f0440c42401003800402d035414801010b402040813004540441c005100301c90010030150b060040080c181d0b00c0c00340c640e00c502d90040d11000340342d40c5c01003105940300103c4852001d09043c141082080056950700000d81d81c001c00c440c60441d590041a00001c920064003102e140084e0940e003180d00400c01090000160018000281142000070000c20454002400800e00004000001d02140395030342c808505091400d0344900e44140620021000b4006802c0400c0c01b903207002c200100c80d1140b15100d10410a445a0003400d25000350300c00d0000d408042d0411084c8106010341130a0356001802e01003428041c8042500c0000b800240f48040c0d45c0000042c509104000145803845c0c80301e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784366267 1250 784365017 784365077
    0xd0b060904060306051006051c051026011b2a050d0503091005010e0604020c210909011a072003011104090e070609140406030f080903160501 62
    0x8100068806039995000b020003540c01558005000d041c014160091100c03103034800c40a10800740a29403403164100800c100e030740d40c0e8001c082143e42c2c4601c0201460f07071003a044011590901c40e20704c0c074003000c000300d82d140d000c40745c034020004032010101101c989c030700c0442e1740030001351030101c0203907039612150746c84103410426140b0340180746041d40c60b03078100805400e2610001d034002c0300f0020080400c221022038420030000400555061000d90303403d20800520840c00b55400080c095100c4008200860591040d0706218250600860f144503903584007281c0140304c0d8562000114204c549111090000d40c0740c180010b28054840e618040e0024803106d102d1008804151040d903e91030070b000e540c42078081007407410340e02c50400d0416022650203400424043c2c5c41000240426600a10a83c4c240d80f902e0f4804006042e0f00c90008004e0041d0717802c01081500c001c0c0c449410410800301030428100120152028182c40e68890390282c00c01d4460300c0c1c00038507007018a04030800c92a40440880344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784367517 1250 784366267 784366279
    0xf0e0f01110309060711090a09030509011b0506010f060e040204080304050f010c0b0c04060306080f0d030f020403151d2406010c02060c100e070506042d12020906040209060d0b 77
    0x16401001400d076170040702d410f55568a0350720202c0002e103808481d841d442001c0d150300b000100c0803502c0003052801201003503070600040d9042c0440c80c80850304c8101e00c0c035911104540e095130f112500e441000e00c0c0c030b2150300086244407100400a10f014001d480c143c481c200000c50a0034607001c200314180d10300e90000340c144008181e50303001040280222900c154100d595042da5a031810000500b200c1007644040e2440e0014181c1141e6a14003090810031b0060f24600403d0605005203504021300c2103900042405900076203a500d000b14680054850094400e8810102c2140869040c0c80d544d18240c141d020840680030310480c081041c0c41036810010614118440684075030224041d90300043c281440d0350301440c01c1c102451940c1c01046003010000010b003c100c0d141001084040c01580100c0480c003807104008840c1e50982c0b425020300c1900a43c1403641e4540e9040344c0802040310850a078083d0400300006200c03410140220350448401618840c500801c41c041c80c802800024030540c2d10071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784368767 1250 784367517 784367527
    0x1140f0405131e020a0c0b060a080d020a1b08100509010b18150f0f010c08130315061d0408070c05030d0f08160801031506050409080a0f0e0f011103 65
    0x14440382c0000a660904650010308180c281183e4035260003454800a040b0380104107411840e98003101c00c071089540003d06404d10f03119403000a03a8890281c02800c140e200b4866948441075000804514041c054140c45842e031408991844c9040230394022030b841c907800f0307040c41c20303070101640d003c254016a10000010003600010002d1460000c04c03000101c43c0b0340d20014401c808032000d40c1c82c8a602d0048072500091200030b804102480f84150780f1606011145a0002c203003c0c0c01402c40c0c40350b0000c0000d5141c1c1030744a250800d04141d2440220089034901030001c102c210341040c0b004142e505081e00e24850740c0d5659241e00081d44026012900e201d02c244c1c00041c1501c04010108040d4450f807180e15840e503403500007c1000000400b201c42d0711100c21540b04140d038011102a0540350441c4030a00301c600c02c42294005013800d94089070300b0526090702541407220241c00b0f8002494940d468900401c5a0b071411500545030042c1c0e030b07500044800b07031141d140d80a0104010702c01c0044e0192400c2ca = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784370017 1250 784368767 784368769
    0x8010e10080607090302040e060615091f09030506010e130609020105211501020316110d080a20060411010305060f0a09090c0b1620091e0a0b01140f0405 67
    0x320009544020101e200e584c814411491b00d030042100390010f000c000c18441c600b401c00030f0010208502c810780d10500000300c0c01815213800300c400c0c00e0003000c1002c00700007400064005090081c2c2d07100030b4a003405403100208680848103185406040c80b514060007000c41911054014170410074201c3c1840020010305541c11a00100305d60010781c22503030001c2900d0608644400448412501d030704642040100148809850303c44188280c4c1024405845e11045404104d181c00d007a4005414140045440b5540650001a10f039402c008589500c10100e06003420503610402503400418030704080590a4665100c1d0703100c29405003009208108000b0a4004501403c00c7c0f41c11403800c441c0c07181040014041c10a480d4401055002c25062801121a040c05515200381000800c41d042c420003001d03003d045840500765180d0000c1800480f402c019800b0560007100000810081017114001101c6507003c1c480c101c684c0c58180c440c43c060050313030050218180d111441034050317400141700100346 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784371267 1250 784370017 784370023
    0x160e0109031728080105010909020c031611030303160f030603080306240d090c05190b07020d0b18010e0607211b021f0908040603021602030d02011a03070608010e1008 73
    0x143c41c95210280913505001c0010400b800c80c0c0c214501c0c483c010010b1104802e000011500b140c10fa0300d14541c2e07000c24034542644180304000320300354580b002009208400980c013803050400c06140d101d5581c003032058182079050b10341511024000b48410710020700181411a168001c0e40c9045040004000d401c05503481c59070040380005801c69038403000c01040002d00c0c400d60300079081c2229520724084403500e010321840254011444000808150f40e0115120008882d124680c01000c2e0070803071407d80d86604004210801d41c420543c01c044034a0081200881c84a020b05116550146800403627400300c40340388140310700782d228180d64400b281c42450008500e01d0400440d503001d4608a1800196020380d1020032507880e4025241860f0300300090740047c116021200b550501580f9058080c2c20710b12107500180c0041d425004030281e228055078194001c03a81001540d00c5170100030301c1d0109242e918000750180e0804100101e00601c00b1040039540e02d039000c21500e500170b080d19140d1021900b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784372517 1250 784371267 784371337
    0x1110601080309011116051504181a0406030308220c0303080f0703110d0c0507020d14071d0406090807060603080405010807050901020604120e09160e01090317 70
    0x4010b420105000c0295a80328400050040d0034030010320f42c150004000840c00d401c0c0d07210389803048035110381402041e00341c00290f50041c6003510070710440602e0305541001814550100030b80700c030802d40410f0800e03e81f51107101d0907690550b441e500207503900e4816421144c070094000e40180c0741181000d0008503a41812800b844c42582c030b02a01d030420003400303140600040e02c14000d15060140081030022004183c64542151003000b007800d03100000251903078810b02034080e4210000e84880b0050103041d40d42d5040c2c0c6810f00d8201c4101c56603442e08442d03050303101d4030030080010724817000c1030106046070815801d1a0141d080c07a86040d03901d5507031504480701350340704540000001c98104095030304108050341c0690541041c61410541d000000c1d140d11004000910803e0450b20f0500014410041403482840c064009142e900744207804010542260991000081c50b4150307a56455200d0f051a100301ca80c403c1c00090666009200004030740c008080300f1241080e8018003840410340345035104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784373767 1250 784372517 784372529
    0x6031002031e1803070303090314070f0302070803090d08030c190e0108100303021c090f0909050c06090315190501060818010615050708130b2508030705030601110601 73
    0x1050340c064500802c581124014161075440960403606402c100c1d0100480b2481036151400060110281ca41a122200c078100c00c00b40701c00b0b000c10764400704800d4584030003555010303401315040140c0d83c204041c1d0380d120f1410160380140196001d130000400100107550456030143c812424600c03034020104500341d4851038200050b001103c001e995580041c9041d41110700c110b41d000c007507411034034041d41d1142200c41031808000302103500c0d50154450728201000d0250440b14038000c0d0f60714003600000d041140000d803054001c0f40c0302c44100d480c20030219007944902602405002c00110100014500c00801940b81c2422200c0c03003082c11046842024007030b0119071546886800d01e100a41003031841450300708102d81c90000244031041290701c80d00300c3c10b080e5280a9649285030316007441e4074000c90311701880b002e140401c00f0504190901c00740a00c800b03100a407040e811540380121401450108000e41000c50030804584200e104200556005606040410140e4905150b5a02c1c14000764040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784375017 1250 784373767 784373791
    0x130801140a0b04050103031b1128080102030411090c2a0f010e0318010e190e070c030905010c020d1202010c021b0307050111070801020c0705040e01020c150603100203 73
    0x680c004103071090001e203240c01c0d40c3c108180c0d815582e000e0556000071510084100c1306403203040402c40920315800c0741600143c00c0b0120341843c422002c0500005c007061410300b4440708408070740304005101703880c031a07900074402c904071001c02014049503950280ca03131021082c2c1040038500d518029060301aa6040306010551040d48150204d810304807000c2e111320f0664102000c1c03004c49a0004242d4600352200c03207000452150050041c8d80b68441141c01940000c3c003c90031000380c4803805c01120440f8002102401345590f403031000c44034904841c4005011070411941070009521a201103031200d407000d00b501203007541d55200d80315400c1d0018000c2005079112000401c03150b505116201c504100300c0010350f122404600080e445036010701805042000300013401c0003a030760800c15540180f41c024021541c3c0c00700b0541c002e849aa01d0301895000c1c0307060000f204140b242c1442100d0440d00354501030400101c0c4030120f2500c0120203065203a140c401c8080740b81c00200c43d8801140580c00d5a584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784376267 1250 784375017 784375021
    0x40609082b0609090c050907090306110a030e0319230c010501050a060306030c030b0a020f040909020a0f0e06130b1306050414010303080703020706060e090c03100b0307030813080114 80
    0x2216068032080e802c451a0541000200c00001c1c485c0c0c0d58141c29200100c0d020903041d59408801c807541c44081d400506001d01b0125000e65902144008000c1c00000d55001c1c00305d52000420f0319524454449032244580c0030000b441c003194030441d8046450004540400300041c0c3e100030100c059005407075010300696586004000c180b4205100c4002480c0a0a0511090340b46403560030b01c1a000d4800505141a00701c0054001c141e540e0440f140c022613401190348030394888208000920301000f049003c0c00410030085503240c0e440310700720704559084001d110700e03981d4081404041568021081c0704291a000261841e54442819140b104003101001444510301420401900d080c00b02e07400d1b00400c00001440800c0d40801156031021250602581e645c2151515034004d01c0e65070300c0140b182c41c0780003c0c404041c0c40460b01c0102448100c049070f5120b0f844022102c1110302100740701e903040c0c3c00310800f000001c80550141040074014980080c0f01680c5091090940b425007243c50860741d007084c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784377517 1250 784376267 784376347
    0x31b03020f010507090f0302040203150406080d0e01030203240307030203071d06040b0a0e040c0503030d0e06310501020424020d0809150402130c0e040e1504060908 72
    0x4a29a80144c443c85c1c801481c51600354024401000760101030b005d19000130014000c01441845c0301e91400c0d024104124440d6542c400d242ca801c10404c80400140c0d41c144440b046610900a89000382c140000c0d038196900d484090086050054450a03010f0203504000005a0f8051100c0d200030446d10041411100c03000c824514807280040620b032050b0324001e051001900c41d28102000c0d140c0e040007070380d1581c5460802c1007003907040ea07019562512002448002c11030843c1c0040300d4a040c184110b407455211041000b4440e01180310142200501000742c129203006004450360b6140618001880c1613280d80703079081c0c20010708104140b200d485011540d0003a83c10007000740c007491113140031281814444600382d200c00c80b04002121072401200810103551390b6240c80300c9103213000c1c0c104010b8110920b030080c2011a440d40c0040c800e5251034a9560420b02c0411441c5440440d404500441e685940d5010300070722032090706851442c0b080c00340001c4401c0d403810b91600f40d114030b1803100080721842 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784378767 1250 784377517 784377521
    0x41e0b011b120e0316090f0501090e0c04021e030f01171c050f04051810050d0b0402060c01140f06100f08064605010f02030a0c031b03020f01 62
    0x1d0210580035414250020104040350740d160780d8a8441e01d00351050b43c501800085c5000c00c04003180e200c20340354690000b040a10b980c40801078048108007804142c0c1c1c0e40100c10304645600a488407142c001038055040382c6016401009107499200c200300801d4202a6a90280c0c0c03c21508032030f50101050050065400525900d407040071200000c010016402151540d084107000c03800d41801004107005401500b0390095a0103040050325181801280c1d40380c15240c0c2c10242e5100020302d1085402184500305404007807d804c0d00549011100e498540c02d210b0707503902c50b015000b59952303180050180e090500100c00c2c010304031103402601e1070502d03404001651801d2884002401041c00300c808005401009040e48284107c40001c450343d010090361460701415108510b0b2800310003c81842e0304540064500550010030710306c100c03540c5070340054030784a1840c001c07840903034000c1c40b207030347c00c41d12909510300ba1902c40d20340040d80442d0010002c010590291086015070080401920030b04024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784380017 1250 784378767 784378787
    0x1416031505242b1815051312051b0115030206071419060e0105040b0127110424050318070b04060503150102152a030705210c0f09041e0b01 61
    0x211021842e484400d42d18544c000d004d05c1000b4480c191104c0c00212441c80a070083e80c1d09541210000200d05180d40004201d54096002e03501c0c1d07142c5031841072890b00030512451020080b1418540035560440d000c2180710b4000302001c036a401105450445040e04c1072000c424005030220b50240e0092991801c002558145080141142e00d42801c02c00850039010003c2d045038400d12080240c844001080e070030741c02c400091243c9060038007078541c2c040b0216100030421500c00c800c1341200001c07001418888054411000340025505002041618244a60203c1180d4212086803440e6a4800c030400044d00258080d8000c00d802001300120f403640c02c1c0b0700c003055400900c041d00c000b01440410314003051003e043c0c110340d08144200b4045040705003070385a0348400d582400a443e840c207480001c2590340700015280c0c100101c4190050780c68224440c0038002c1101102c0281840c114540d0a00e45401040005a0003a05d07650740d52160060124603544860b640360002c0744a2202d080054060707018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784381267 1250 784380017 784380041
    0x1104080717121c0c0c0204151701050c0a05220f05120609060c13050d0b0103210503010312090302040c08010509090a021509041416031505242b 63
    0x104026503c014046100f8030b50301d910100e400000c0400b0407010480c0e0907440b0000080d0040e203041040e501c100c881604071411212618613581c840d4203130300d6800d401c1e5078064a036107454110a00c03102e5841800381001c0c0c01c00070b011801d0088108550103410700d9a81d0580d00801206a1622050066040c0141d00402c40c18103080101a00c2c28001c0e030465844200600303940440c940401c810000008068040c03004200007000100815624200103078005070030b110480b211a80c1d001b03000c1605100210800c1c41242d507856081c1560310f10345440544980340c105450030858400750100c01039031644611039080d450b9580b118500d43c1400c0c14482c0c0c00b140600703e407039183e001280f441c005039254400030715110412032641e038581c10848045400342225221200004000c0c00401100103180350084480c00c803159000d20660380680310404c40c80005009040e004003200508213010a004007407051860f800401a910b06034220301e1480c0403144080105035460341700258449031940a01901d241121 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784382517 1250 784381267 784381303
    0x1060c080a0f050904061d0a0504050d08060d0c06030c03140c07062703081522020a200c090109020405010507022101180b070206191104080717 63
    0x1056100c40445000304000501088a801c0201851621078030030343d04420009803041c4081074030307040d031021400502c0c141c0d0502050801c1c00105000000d01a45000c0c81d0000d000d0100441181003c90f001200280a90b03080204002583c0c0061116060340005112560300000c003401100c000805842d0072032005a00151094184001007098ac411107040907440000040d030809000801da859242c0c101c0304a0011003c001081c0c103045c0c000c3d01c903510850601c0340165804080c0070422000865541c003040840b03203c441801284020341c0c0c0141903080aa0a00f066a00284a1281d4002103402c0601e1000c9e08848800401c41c1410002c0c9400b5103100c6205504160a00c40001c3c440d000300d201c040d03c115004845242494074018103000440201d90090001008401c50030000c000700c0c5104a0f4030f0082a80000c504600c081942d9029480140b4055658482900041c02400c20341c0468820b003181080000381c030403001c01640340146071030061018400c80c0940058100049281c003410301203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784383767 1250 784382517 784382537
    0x50c09101e080705061809010801060e0a0504120f022a01030c08090c061303120518030307050c01360e0124051c020304050601150c0305090d020f0907170106 69
    0x70b800072507204152402a158503032038000102060b45d902c456a844e50740c1001c0480c001051804040d000b66043c2c86007034002d509240c990400301d004452044501404c1d042400b00c01e8000e4038854289804076554510480c1c42c11030301c00c880d1036a4150341c0003d00724149a0040f010140c0c1d60180102648007002c0e0500e00310b1407901c2d903c0a5100c00441d09500e11908001aa86032010b00ca032881102071a04004101c2200042500240c03076540f1a40010440445014001005190000460700107607030010203081814440030040d2804841150b40384500040b0715001492100305800c2c90141c0903074030b00c00350030b00c1d843c18841d110b42ca001038018520b5105a030740120400d03240584200050251858079903550061a1031405050700d1000034070b85450f00003c00c0c0418000001600e41c141c50b1060f40071603040040e10800d83d00f60758603ca004000c1103050011140307900c1c00c40c0c81d03400018009807102c03c100b09102d001480d860411500311010618100d1484024039481c56005e0240007103050040000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784385017 1250 784383767 784383779
    0x140a0c090b0903031201081006050904051e19030804021206090316060b0d0f0605010e0601120b03010204030f050607030b030a20040605040c05071e0c12050c09101e 72
    0x111a54040e20a580400261040d0983c604204881798040d00d46545002c9586900d180b81d180e601d0740b00b0f001c0c85242415804209803a02140355406154445d000b002282e8000210461207102c00720f004c1103500a007207850b803503288010f4a54014503c655500c5800d4a070600c100140040c482229a2040d80403c0401841d076030000700721202c4911303503246050f03620785500e4150050540040f459401c0242030400700200718031312409201c0f25200b50320502282c1e03242c02020180140844442d4005000100e5403201c03515154080040e1140140c0058641506d035100e00c00590091041151194801010403012590510406a80c45811400741c610202c9640b1224102208200080246408002040d4a96440340d1025009160250042c881160400000703031064001800544110030300036082c0e00400402103403240c2d1680d10911004c080f9040020b500e291014030700088900c2d100b07481c0140441d642d1001e541c0e1082c80348130351480c055403d00d444178086c586401c42c08035240c007070040d052000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784386267 1250 784385017 784385027
    0x914180705060f04080a0803161805040209040905070b1e09101b02090a020309150c16020105070803330a150507140d02070506041a03040602120a140a0c 67
    0x1112030803a140d64880301480320401d45032155a01801345c5204120340da400704900b940196200c0c0c1c0505c40c514a00101c1c0320030035286100c1c240e40146981552110038406454035501070040454058000110780c01c45035980d81c602081900180c030384850100ea1070540300301e04e81901010980d03411115007456109030124540c003600045803818051a48248180200722811460307545400901018680c213000010b1402980103454003601406802c4c100f000310090f030030380716024030358404030140343c150392072880345d485919030100f01d04100301002680301044002001c2c40c007406c0b80c1e640c1c0401c60340e1204c1c682254205840c0c1038092620350303014030740e0499031100c8140f000c0317403a032041a04219064220480f610310030a5070041c18039260703009902d5080d10000d980c24400b80c40b03802300e40c1a9620f82c020402c45005900c502541540c0007507503401c0d2040d610000c6c540041c0b2030500542410850f20300040030001c225429051160303030790307105803ca40c150060190400d40210041241030040140244 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784387517 1250 784386267 784386269
    0x906030c1e09050612150406060501170426030411010e0a0e040605060105040503030d06050901060206190b0a0302040e0a060c030510060804020d061d0c0105131403070e0109141807 79
    0x2400507661000502140c039000c441744a41c403208003d4840c0030140c10344140800300c0548040d5074403843c0000c041441d50090f035a2460018807015150110750319991000314140303007001d040300d03024050a100031041030344502560040c0c5c03091045001c0c40c0890400100a5003040341030910400c0003950070040040d401c2c41d815041a000100405c42c0e64a030801a50580302d0f076400f03242c144c800041c004082d00e03500c4c0c1c8103c0607180c0803201a40c150b40e907020100daa0f05001d5502d0054000c0c628402480c92a01c0d511540c0c030020f0207003400f00007554035000a000c42e4400c000018017500081140d000f0852144910360030303081c45042c10403c50803c0c10b518034440045005403c01e012604020030213560382c0c14400304103540d001105022941c2181e01c1e070481c01c81c0d14507125641d171141d00c101041c03560040f03050369a0302d00700044c040945403078603842c2c1d03040020440300260540207891001c6605412610110301a080082c00440d83c06180b8150400c11b4400916621182c140c1c0c410340001c2d46000b0030010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784388767 1250 784387517 784387529
    0x50304020609190f030c080a020603130c08100504150e0705041e051e01170303060411070f08190311070b060a0b13061d0901031e06060906030c1e 64
    0x9881d5001403012404042e00c043c03c410115183c00070002c0c0c0c43c0307012610a0107036440f620780b0304142591034828554804004900a600c41014000100e82d8403400d280c140050303024160141c0c02c079540c4d0100900748441c4145901450f91201d08200a200c05d40d8090001a0382440381003115202c010350068541d561030041c03602c5207484210489000008103580f04e502200100100032070b080880e1050400b000410282403988517140002401950348000420051540c101440c55503582908000007861a40805030f0032240a2000700d01240b40c2c01c071115820341c0f04202095503040034034564450340f02400085003c25043c245500d80c0c00d41c4807000d1383c81c40e81d80401100d9060b1143d00005405094035002800d4028004c128100d80c100b01c180c020303045400725281c2594032205aa2468040b41d104220160000103207401000010382d8107114480d0049010445551200596280c6099442c03e51180e214a612104107000380260075074281c00401500c0e840351190b04c00001040003506041c8146 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784390017 1250 784388767 784388779
    0x905030f0a02300c010e150f0901030e010e0109060506120307110d0512040f0e13121407030e0901062109020d020603070807171b210c030a0e0d05030402 67
    0xc0402000c0e007600f4034040d14006010314040d04260140300b9580c0880c0030034540098900c0d18000024140107000c08182d20718414250b1074104d03006030100d0680d0050707000030b04240c1d8034283c40b5000c45080c4115100d00f4000340000c501c0f07041500740081501d03806005541300740011080080c444c20000211551142c4c03104c40c0003400c420100c00100340b080e0070440544031707000315018000c1407803020b4010426514410080000705884104820184001300d541c01c055503101500d200c0840d0a50301540315240080c40d05403200d00050081c24180d400c50207040380404d285004501981c07802c012041c0c0505031f0361416080740c0107a05d209040509061000d142c000ba52416030105545401460000150b0083c08071950703401c0046000708100411626074002480c0126070b9048808804c0ca018011400b40442c0c0e203881da101111505241e01098415450340902c44003840a084010240f610076880e142d84151a807502d2880c900580e008140e8000e4290440c040c0303015811b07004401c2d00e0f082601541c01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784391267 1250 784390017 784390039
    0x40504050106050901120b090304050609040f24030c170c1221090103051609051302130602061e01152f010e120f070f0c090207060c0905030f0a02 64
    0x401801004607800241c4c10100c07410010030341c0c004402c070b0b202100e8454595000d05a442540094690085028140d4000d50800c04030101c0d00e440d03000000344110b860000994034440f540343c03003182040c1101041100900050410070700480c019000014078a20f41603c4030038940c0c281482c0c9459540d404c49200d6100c40350201007001080049540d904000d410309900d44045d00101c04c225040121900c1c0000d08000020f120503c50f400f08498080e030585444a826003400704020058420102041c040396003480760a03150280310012200519841d009072046042928840700c02405400d6180031040003100100152020b8007102011008a80703014901814581d1900c64110250b444e011003144151110400300071041d0320141130480c4a00c11038820b107008030074103034003405054000010060140311002c04031b000021300c03c1030fa5114980c80400d568444411504a03006848150340a40d520b0388a940b901c0d400c005060301800c400c034028520102540710f41c6a4036000c0e010000e000d0407900c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784392517 1250 784391267 784391273
    0x50c040b13170313350a0c0e0406150b0a05090d050d03050f0601140d050405120a0804031b0f170c011805060c09030a111504090b040608060601020c040504 68
    0x5503260180100281c03401c000c00600790429904d030003e08400141803a0142c0c009002212005551080c0c204c900a000d4602d00c0d10b56449075580c03503402e90140c280034100324000020400c00001024060b07a1030808814101818587d080b90b030f61b28030300c035115402c2c0d410500129130301074141d590040c00c034505a50743e1105007001c268990b14400c0c000300749206000d80100b00f47c0e05500072900c980a18448080a80e42d0a0b0046a00328120404c1c14007540303040002040680c0c0c590420340d80316000f00200c482d804110540005250700070540800010701c0201440105a844101200c50001c0b80d81e054038070f02481d440c2c48031030005001000b40b1403d08004038416910585040d1182041e00b080200112290960030f803414061200084406004800005101c90410000e031404154050020030f581310b1650b88034150440c00e900e150b98003140c0c820355150352058078802440605441d50303010800c0117001c030a00c016602c9640041340a070b00b1844c208035459900080903140075004460200d01521282 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784393767 1250 784392517 784392547
    0x1b0105040807231507060c03021c18051501080d020703150903090302130f1103090a08030711010507050405041a1c020a080604030825021207030e040504061a010201050c040b 76
    0x781855810603140082510494045130203032045502451041c8012120450704500324807035000044054a1141002048408994045104c01c070356120034142484039610fa8600c0c0401140006019802c203c006212400e820b100b0f0740420b80044c0020080c4504503551140c0c0e84a00045c2c3c00141caa5541c10030741814494032901008607006001502e03080a140301e12b0f4042c2138035050b448513681c2030141c10b24109074408122841050f5041c050207844013180d82c0d4020342c0d480a010b041c100101144020300443c000c0c411715004089580380c0c55903441c60a024082524121000c0c0018841d4070b020b00510781d1948040300302d0003944603a24046c0c0900600c002742c0101030342e0b000007039075125140030082016001084580202500310b040c40402c41c820601c400c134400c42c0300c1d0071001a0412662003503c4040e0300003500241d88a410500815268000498202c2d0802c0320152003058a40003200c941d460101c80ca04c038488800e100a020320301c0d01c25140b039040d00c80c0d8401d0300c5000d54009038080c2090840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784395017 1250 784393767 784393829
    0xf06010201090c08013204030c0302030d1407083612040e0604050c04030f020105090f090403021e070b220305070906090606050a0804020f19081b0105040807 69
    0xb200b82c45a1a03a02d0362072150003019a103150208100c0f0540300102240c11b07880d04034056a951943c45042544ca9a03400c0703500310503000048082d888140714168051400f4010301d0048080e01c120101c90b4545120001c0c000c02e0081c00031030001c49415400102114500d58481890154410a11141c0082c0c1c01c0203250143c044050f4505020100f000b04801c540100480e00817201250706106a8031180b9000085109611004009011262000c8010750149028062080c4000c19450b40f00e40f03081c022403130043c812a02200141c100302240c0e8400d04003071b40d0740345a24060741700600306241400304d041198400c80c850404c2e0912184408580c0e0700040142001660f4014165420103603200c03c0d0b2000350405000c0c542aa605002c0040742d502d1043c415038074848984c2d600c180e0541c8654082c0b000061480607000d42101054004840d4050b08501e54070060130000000d0414101d54030198109040d48224141001010841000000300c00a005026542d01841c80201036100b4911500758100e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784396267 1250 784395017 784395023
    0xa09020a0909050106091109100f120c0e090f01051012090501020c1e0307020f120a0c0b0c1b0f090703020d0507050a0e01022e06030503030405010b01021209090f0601020109 76
    0x42c5842e000821006421107022280000c000384000500342e42c9088050140310030310354100d40c003448445141807042840303d07040340c0f440c04c0c40341900b07401d001018265054001204041410000d809140d0b0611121050b8045002c44503d215541480c0004941350305840100701048410000503440210382e80c004032242d40d01400031035951140080c6a51103005104145480590b50b00000b0390b540000700032a001541d0052000100c0c0f901c4408000c030103220b140034910540700d25450000042c43c0c181041c000f520495040c11786032004500068a081001c690281240c520f45015840907210104102c40b820012640c4078500d03613900c20101c1c024010715007204103081c208024030020390381000080c400054140e40c0d2001a5010b0001607a41300c8440d02c0f509034920603c1c0d04d04008800f11302840400304c1c50660003190007a5243c4800c0c1c590b0300203450549240c3d641d0310710301d201c0b0368041005083c0c001c09000414104480100020510a0000d2103030f421612100b0020380b0a038800e60049104540c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784397517 1250 784396267 784396271
    0x70908062e030c0513020309030d0f0b040e010f1508070b030925051f080c0c12030f2203140d1d1f0b0f1003090c03240506090a09020a09 60
    0x9503d0800d6140500c00d03114041c059104200ca8849111941c0204e901c6002d104004601e09400300a4610040108054200c40316950b90f26920302a5158040c001c5030301400300c004201e4441070760700c0c40c044490410840d8270b50510b0340010071070300030085420011140800021038070703070b84c0355542c507030500c00c40248444036a0303a58103550920302e4140340c405007529015901d400308981e2680444014030103620040c40443e22031000943c07601041002044181c40c50000d840e802e286980c07902d2507680040c1d078000c03c594014020880046051008401800b0191010000d03400003910090a0312152400c5c0301c4901c607000560825822064001e07a0700c8400103c0d204205000301c1112586640c200b44042d0001110303d007141c100188103000c2d01e40428001040f5101100c2c13998100030000d010080c2040c149070321411003001081c41000d11070000c0d801240c0102204c03a4032048984c0e8089000911901070f440c000c103103e01d545580200c50340c4150036a00000301c4400318000298410305640c4110758641c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784398767 1250 784397517 784397519
    0x10060909210c020d03030c0f030507230f120a0e0c0a06110102070f0b0702010e0105010503030d0e01060504020301060f020c010207060c14011103070203040303090b040608071b0f080403020306070908062e 89
    0x1d0790592010120881a50383c580c150613230718100f2030540d10140e0755440040d048190100702549403100d00d040b101902c040c89441c00500001e4012079402c02e0b146d10303c002424504009240049009486030200c000d800382c445600f50b5400200e584207180581d60400640e04c8101110300025812940c400382c04c240512174520451403e4004e1003400c81f9140015401e1202490341c0c0c900500540b4181c0e10024050340c02c0500440035103004001201c448295503485040c0001c0b251150b100441c00303044556224400c0d1b61114101a160604417244681194844501044207660100c04e03507440c0703580050004202540d07050460701500c2c42e0007107501c0d85000042480031440c0c0000061044a1094565100765651a40081400d01440c422440070803c0040091200352145501d20075210300c42a00d12207a2600e0348512008123040c0c00c0440342200005401e10540c40d040022942c070450074504881c03d1400e00d142c5507282e00c4080c0c01040102c486024100c9120f910241d00c081c1210110119100301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784400017 1250 784398767 784398773
    0xa021306110c1f030f0603241b020304061404050907120b091005040c081905070c0b16030b030a0510111e030f060d050303040b060d080c10060909210c020d 68
    0x2c201540100c00121345440715140da284031500406c0b046070341010390218064000d104003803e510170040110a034907600d940c41803d00702540105902c0b465150b0040d500c440c20300030041c041e20401d8146c114280b20a200812a941e9032442c3c56502c034426191040090001612100c05071044a90503540041c0c2c100402c0340d001700c2469100d0072150301312014000100040c0d0181c0c2c14081c05d44102c1046004101404a4a071907900019003001e161310786100b2600490721800c405820540f40d44407840d412002000045a16000340003010300304a01400445080f0b03a80e540d40d50024140138800c4940395800103030020f1428040d101c2d2100303001c0c1c1d1313040c0514541c0b00340d1a0365070045a0710b654401e1160003140c2d150030403400022001d5404401940345442da92034800f4000c10003002d15034403240301c000401c00210f40401030081042c582e03000f40001e898512410341500c60680080c1861440d200e2020041541500440885070045610020741081190101e450f5420520b010390440c211600500070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784401267 1250 784400017 784400059
    0x3140a0b0115051c0b0f10090902070804120b06090a0b031504050715030e070f0b0427020712080609061e12070611070b0415030f09020918060a021306110c 68
    0x4105c1200da00c800b010090081080103001007030b03c20f0024402140c24844915154024080c250088421900307160b52003244004075204124201e940e02a280700307005c0d442c203040e0135054000c0200501400700f10005130220b0341c1d946072118003210700881d10780400c040c84814002c0c0000780007113980448003012442c8019000d043d449140880c580b00e42c1500103440740016481d20305591103610f86520301480c2c840746080155102c040340f80821a0518081150341385840200302444c4109292541e800703914401800110000303001074051400c40303040000c290b441c0c068044c9044003414a0014417400040402c89114541d10f880344c0c1445a201c000c074042e90040d01ca10401010101103503100340d19001000000c0c020b9104814031180d40044d05240c0a0290300305051200e00520000380102c1c00d0b40000d058120180d88800c06840c007a08052400716090003030b40e0344031120f40030a51500c2051036900380002541c4c803c40d010018614003d01e0210428848140002c000074040c0032220032082041007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784402517 1250 784401267 784401281
    0x72f061509090105060a23040507090e0f091c030905030304141b03070308090105070c030b1008160e18060a02040504051501020a1e050109050703140a0b0115051c 71
    0xc81407040000150696005018452003400c01806460049180058082000104440c148400340d40300050703030078540319441a18821400d0380e0780d0703541c403d11307140310380c04020b1010700f01c0c10181a052003003004034800096405890000400340a2800718114000c0b0020a80c2035801003ca010000900080c01030740e521048014117a07209440e1844100580203252a944280098054212a40800c045031703409000d40100c0506052592501409540c2d1800d80710860f0000c82e0410502e0050010500803020a4000361208000804160075040d440308a003100030b1042d41c02c14003225002a2044105080b80c80d07004000104691440c00c00e5802a0302941050060714001c5287c100040c0d00450003040c62401340c001a0041c3c0550701480e221410144446081181504860300b03c40001500c00d100e050b44107402000075084460031482c00e0301c000006021030070000d9220000d1031000c217118929a9044500d205a0003115089120042d2450b000b101400900680383d40b011005026554009007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784403767 1250 784402517 784402519
    0x51b10020316020a030903150e01020304061b090f051507020d1101170103020105310b0d0617030a030b010c02061603080106080c0f162a090203072f0615 67
    0x16696034980c0c2c000300c1e55034842c5040030700065034045080003c107001064245603c41c0748040820951241d0300807900fa43d0080c0d070222421603544205c804294481c0d01040c10707008103494019801c924211402203420342502a06200301740000d00d9594000d40c801c1102d00d525805480204400c0c0b1303a00304290106800d03021113010804200e81485070311000344003941602d034142c44080c1001c0402998105868980c06080190000c0c0c0c07141c80c00d448048054403004001c5500c040f951100f10002d21015075180c0d520034240c104100c000010105004800d6038480c812030716002408142241c0102d641e0141400e0103500301c0e50003ea4242d81c10308110324505603a001e5102d03c0003c1c0d90700d48044a108008075040c4036014000e0100c1c001400740130000340fa001c41c00f0751381003001d82981d07151404000c52400d2100c078000030340e1411010310480d03100881e0003401c80380f004505500e08a500680344150b01c1c1c10003900e10355030750020400300d0030f51050705818601000468003540b820035401c440c403c004410716 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784405017 1250 784403767 784403791
    0x809010608010507140c0f100f0605040501080316050c0a03060b1810210602040b030106200309040c03090b0906190b1c23010207020418020a0501051b100203 69
    0x41504001406190b0041c4c00c5130380d0715078034aa0380d01e2240c0307840c2c1c01c00f8a40c1e48a030701039039041e1903116034100003440f9071a10301080040c40301f414407610405c4030a680d0010f030007181400c00400050700c0c0807054408000b55942c1c601800c41103850310740e0918510300c00450b400101c0302c0d0040188070f440e6103c1c40560320151915182500a10f01c40702024404503450088664050303010310180742000104003020050145042c0e5510080d40c0c1c41083e60056000141104404030042101541c060843d00401c2107001c1c840c0302400354003c01390780728072403602280d00580c0c684000a82c098071030ba00103402c0c1030700b0034003c0d600c5050251220351291020740d0750075a1902c00b000f00750700e8000035201d450f400e039100034548081110b00b2040750a4507403508c4400c0c1e550007002040101103031030034500b01c5101d81c1d04800040e0f88070020320401007124242240e4103c40390a4080d400016102c948000c0d081e51003d007007898070340310303001e043c107208203541d4080180501031220740000846058002c1c500507401c2d106c039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784406267 1250 784405017 784405019
    0xb060402121b0d1b08060d0b010608060f030d02011e11031302010201090b0403031e02030c0909061302040b041a1e030910110d060e070c0201030b0f0d0308090106 71
    0x410080e406075840001c1506031400209450301c0c140c0b42072402d441845100715003800e22100030a4119075600d0005a81a0103203080703000c030194000009544108100d0f0501c41420864540001180050003580300340000040490741599504180e200081030040071034502c4194030b440203000c0c1000c000a14807001840d05000c03020405030007401007162460b00458115500c103401032441044214081c0c0c155565106020045090640201e05c03850085e14042042c1c04804000d00440c001c0311740700e82c01c940c070500c00d1144490780b09044071018007080703400d40340603190100000c5008500c40d1144406030303c00035000805c420803c0280c81166400305c048154100000d400d010700e481803014a41c081148001040300210520b405184c0244680b0304803440d5452000b944e9040707038440b4003080c40480001c129941816014009c00000d07004410790554541010300b00685240801d0700028145625444900019119007000d4141c080000b440e48106004500b40901044000e82d9850107950a1a0f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784407517 1250 784406267 784406269
    0x30c220b0109080c090606070206040f060f020d051b0c030601170f010204050d0b180610150c21020109082a0d020a080904140903031014060405012105130b06 69
    0x6190084800f004084c101c424911001c00c00d40c42d400070140c2d41d02550a00801002d40c4030704000e003025006506401c22140d04164010701590300d10781002e0119807050030303410000340d07102c130648400d54405980c4200980300703a0703e1181405c2c0035402082d018401c0344000100c1810781000d5005104042c4282c4a03084010865903081c1e1240340a2241c2040079240301c83c00184101c1c00596015403190907407070004007400342841c1041000e48011805050f803200c28488540760311000901d102940c1000100594142c0e03c00c01941641c132800c02c400c005885140c44658000c8d04109070a41d403004803160b955418031008805c981c10303601017000c0c400007070001810f00341c00021081680c40070346d001401000c0c40b0355038404856002c1c000580d080303034039520344054103607034408500e01440403800519240c1c0343c1000920301c90900d40c1e0000c0c040345e4a4840c0ca031815181c05c1c0803034090f500203103480420a140d049040c0c050182e4a81d68048142c640810041e9440c0ba000405440c180710b010201c9254035090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784408767 1250 784407517 784407527
    0x721020f1e01030b180720030a02030a03060b160809060f040806040b0705180603130209040c050411120a09050a0f0f030824010f020f0106030c15030507050f09030c220b01 75
    0x41340d0208001c5500201c2c05a5001c0e01400b09600d241d05620004007400200a40c2582c00c212709400159002040707082d45170360180500e001802101030181e007448a828072100000c510000302034002d1000080100303207905c0b803504a810401480c0e101c19075485c0d481c4107081d0707640300495007611000c9070316000c40d0702e4901c00c0c000c48000721081e020406081c0c80744400c11401d68005800340b101ca443c1140200d0051719454042e0b4490b6025524040a0901e0001444196610030080100c0700400300081d402e160b209400254001408040000d004d0f103840c5000c61902540d00000340c0300d07622075042c800800620714013000d015442540ca685c900d4981e423100f11100301305241c102410760540e0703107140307070f20f5100c2c1c509800440d8281c41142c8d02c0543d500c601c1402c5421030341055411901b1444248a0b1101d0300c48544c445043d94a800c209520308500014805e001d0b00071203a0040c040001c60b14001d80e01004a5204142c000b0604003440b185100380066002d14110100c5000b030406414807080e41c001c3c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784410017 1250 784408767 784408789
    0x11010203120a110426070f0609030f1406180c0415061b140d031d0a080c030702130c031b021903050c030d0207140721020f1e01030b 58
    0x20208240d25901c5900e00040900001c03c000d01c0c4041c42440000741072550001c0c40344004440d02c0c0111000a0711006107820049150012441200c098204000003036005c512102200d0b0031148118050031300f8506031007007051400002c0031a1080805008440c00303140700709104401040100c2d010f2064820030b02c01924019211001d03040c100030003c226030707801400100c0d011900f00034102821400ca9590108502d006d552607a250350104030010340c0e29070107228890000c0e00910345925421000710750b407070385e68805080081800724041050b004003074003003082c0d404951f40103007400c6821106280700383c000c00000c1c508070000b9041102d04641c0b5412100c20010351041076000e011840190b090b44100240d4000c1d003101001700c01c0000b5440814180050500111096000b50ba00c3c3d200341404203240390120310302012a001400d0800241d203809105042001508640c80101c500034000150000f19000403107403c000142d00e08440e400c0300c0d011524051f0000d8030200400c2c6911410710000341c0744 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784411267 1250 784410017 784410037
    0xa0608090a0209040519061a01052a0a0b091f29240306090f0c2203050a06050a0f02042d05060a08070816170705040506120411010203 59
    0x1c45005810321044182d03016009030202c1c4c10091816141100321100b40c64280c4076a0350721401c0d0112001010404c0390a9202440c080b42410508030079214000c1001c0c00f44280d0010414000000c0a000d100d05001035800040003841880c00460194030b540604400c0c000303094042c4107580722510135205800000071800c00c02c015502c10340b0959110700c03010004440c2d10400c4101d8071503022801c00818582e0744c0950303402036100d090000c18421242d40c080c1c640c02520340000e08004a4141c0c000a81350280d00840601d120400d9002200281c1045908007a05501449481006001c00d903004207010307a282d250100600e540c40300010080780103d004460f180166400c0c500703c1d0141000b010701010003611484902c540d0303508002070700d55007c0d205040201e0b25002c1001074030b03504a10b2040d40b2251915204402d41082c0c040244140e100d5940000750540120104800511410554003d4071016290b50323507500d60f0200c034112808048400300d85049490005480395440801501c0d40785034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784412517 1250 784411267 784411273
    0x8060c0a0c060c030b120a020405070f08040f03180803030402011206052d0a060f02070e010614070507171e0a0206030c1c050705040311030a020307060e24090a060809 73
    0x4042e0303444401818400301d1110406880b950101e44650f1007418460124a00d1b4000b41505c01d45032041c00107030790004159809010312110100503568201a616030f0240d4042040b4100d000b051800352500c00c0100c0b0001d01e00105031801194042c4d0000013140254000d8813020713005004200c50800303603a260b00642d0380020000c0200d40d02d00c00c0d1800001c91114002c0040d0300c0c140d924601051100d82e450380244001080d030306200203c1e640601550300602608090381d02203604041026010f409a41140c940e100b00005003001032040038040000500f221003c44010030840320103807695510a00b5141c128410007403072041160400062244015501500e00703800d60340c5801043c006604004211440328100c02402c0519075098490f2520450a9480e903075222829130900884e940003440b42c1c00e01071b40c004031445015aa000402c0c5c0c0c2250381501d0406019906d51001c1a4440e042124008003440f00004403100c410044001c0c0200c0b80c5e0682c1c031801036554408048130300900559141900390 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784413767 1250 784412517 784412537
    0xf0606111c020309120106030512091507020102031902011401080601080706030b0f0d0c0902131703070209040b0603070503070f090e060c0d090f0f121b11040b010207080604030908060c0a 82
    0xc189803907482d1826a1903c000242c0700d5a07601c403070b402e0a0400010035a64ac03400100c0101c1072404000b410980c0e0904d044413400c04009a00103035503446402d650036401c1d001c1c04611004940b0035040544041e0b4070800d0350710156580e0004a0f03a4080a0003841c0c0a405035010124059102e44116030082d0030003844803240644200510100c07808900381501e14040000010545141c13500090094105650401c000f40e403034103680c28100204420f000200d130304108035200140c0d450940858205400000b00340039521001c0c0042d1a10040d64055038260050b41800101160854036a50450750312540c00c0c01400700a00a454551700200e031500135440091101d96400061580110501d9200b10034942501510b078599211450215104032070001600c61022803c0d58080400c4c0208141d0050b0a4802c0503940d8030041601c0c41c03420914015540c03009284102e1307200300a080d0050410b40c080c0e4045080506008007240e01038004d030b0805200b03140125111300d40140482c0c0100035240c0d1081c03d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784415017 1250 784413767 784413769
    0x13150315260f16060905090f06041803050c07090507021c09050a080c0414071409130504030c0b0f01030b16090b1611150a0f02010f0606111c020309 65
    0x2441da118040c01c0d41050444a07403665810410944015401080080c0500441a10b8040c21660290007140030001d04800801c516202c1405080e00440c40e036402003d5903903a0300216004146544111040c0346154080e541070541150061011107284029640b01e140c0700e00035001a11401d4418400607802030071310881103078003549841143d503100d01e0090300c110b40d9100080c030403412a40140101d5040018055142c0ca86480307a1001003400e5219503c2d02d01c0c0c007100150400b64242c406c0f4100002c00920016140d5035a0020101c101042c60100300c2ca050504000303000000d01c0c0812600d0f680d41c0800b14412200840c1c0a80c105c9a000c00c405000b0b46c2d0385003080c070044c1e80b9401c1c0d250500580d840d01142e1001c544000d0a100e858400c442441ca5070f41d800d11410090154a85c0c07406902c03041c0c80d40700000010401c44400d919182840764080c465108100d005004060701c460a03949044804602a580030400d10340e40c000c988201d03010394415039003031200c40342030810040242e071041001c1103032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784416267 1250 784415017 784415039
    0x1d15030705120307060908220605040b090a0e0a0b0a060804020f040b012f0705090606090f06250218130228030506071e020604151113150315 62
    0x2d800d109001d807414880c1e142d4031034003503034042c00e400c80d01c20002042c0078010000d451030380e20a142c04212a03080ba81c2c0740000123441d5204901402002c4100017500340160b440b8001d18100404215003c2e90403071030710005401c000e00d40a0401482100b901d8000180c0794803404425010741c0d0010052030702081c41104000040c0880189181409441c01c103103c0200000c1c0c01e00c840b00540b2840000035010510780c040d08081c01504018071602e0041b0070310500d52500c0c4252440a076003900e000094001400014885000c0e1208000c41d81c20030160b8880588090817805800d54801c1d1400705a14041d17410b40500781c9011a150454002c6005541c8050703d0020200307181c40400e51080c180328001e00b11145242030098200b5034450340054140f081c5240e0101e14010b100720100038240c018520084000d468880140000c0c12004500d4400b000b0b0140d2644054480081001c11682d52110807400700c02c02c0310329100702721034001d200c842c25402c180207019000150600d44214801b1906080c22542 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784417517 1250 784416267 784416289
    0xa0512190c06090b070e03010b03010e1e030f0d02041410121a030d090f050607261b16050609150c030d0c1106010501050a1403130b011d15030705 64
    0x382d0305484405010216003d51181800707030902d9944d400b90000b07080b0a01d07003074030300f1080982e000344e2600f10a00c24902001c03994403c2521405500e4028801000a0750302e5401104d00441c4507100000d01e01500700c1d40c039070080c0126084070280e00c40f201d000b041040035141c40e0016003400315083c0b91400c4500e0906a0062041c0502c00c0c0c030521440c0426030100740f41603004250080400c11070b0f2024044094018022402064110b415614108850344d64400c0a551402c0402c110007803941d200d141510b000b4103450000703c440a003e00034450b91190296244202c407000d201118402e04041483e0403d031017140c86d9000060404410442034122607040d962007600032000b640814403050071001254040e005042c0c00555a00d181603140314101405d01c0010787c05103050140810104045507000b04004000c01084c410203030300ca40d20b41038513840440090f04001c001050700e40000c14602260760010320b501010f5482050039503104260040c1e29074010510950580c0300c1c0104000d14a00000048 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784418767 1250 784417517 784417523
    0x602061e130515070c020405010512030f0c150a05040b060103050c180105120901050f2d070c0203120c0115030c030206071e051b061611210a0512190c 66
    0x103040b1400d5550944003043c055806600103810745c0b41a90540c034082c010a409800211400001c00c501076004507030700e201d02082d090400b83c0120710f5603100c00c410f00c51101c0441c100121603646280400c04c05c0001c2404980c00c40703421068a000c111507500ca449280c1c82640a03094a03403514030b1042140b004540d40100d81410807404000c50404180e81e250114010b44c4a0782c00491241010908400c4030a0b00400c51102100314000300140e0350590703050f15200c400451100b0390a500c9456049940d0004640060741500c24104000b060100d440c00404030030309208000c0000c031510094052901401d44006812551440001e202616089008100b018132441c142400021200c00b0030f144100c003081c1c01d880580006000500d036001070140700802040440381e0030b01d808456903104031031240680014010414403081c82d04680c03250102c426480101e980910140241801030366582e81004074202c4c2e00f1700810744800ea03980300b540c007550300c0400783c00c1c9044003030301c000d02048a1700100c030030007a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784420017 1250 784418767 784418773
    0x14010f05030a0216050a03141602060a05090607030806191811160501090506010b0726090a12152a0e0a14010905031c050f130b03010602061e1305 64
    0x9070b200f9203400882c0b244130600c110702030103010542d0704016204c5040411450b102060801501d00d16000790306024407015411140b498482e0900d0004603114082c03a4900e40c5c100400055540506400110062040300c007243c0c900b408036028825899032080c1c0e1700c5070072000340b00032484000e031000035000045ca00404007009400d1581c0000318284000384e214090320b90b41d64503c40e003000d100c0d0601020340500100756449140100d81d075900026900f405074409820b03001e00c0c07400d04407080002c080f6144500014000c2c03610540f80e01c042c2008004801080b07031a5000100081d210304114010190301180031002c400b584015660118048040d44c42d030f800c20010100c11b030110302e50702c072003031500600a565074260002d042c0364009041c0c1916904512b10a920030156540c109015400b0010303941c49070700e06039444405204140045010f1020100d80755030a030704010070104000e802840c101c41e041d6003121080d45808190001c403030300301d10b4842000c105080c001490140407091814600d4410001c07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784421267 1250 784420017 784420027
    0x60216050a03090f06050315130f11090913031709030d091a0a0b06160c05060a02010504050d170f0408071b0510030e03030708090f030309011514010f05030a02 70
    0x303032810079460748000c0300880e44520060241c1302e1a159424058160b5003880d0f407860500f45400303d990f96007107580c0e601c201000c24107610200382c0d68001a01103511030340c082c40100380e81c0c1e140300c056401c40c400082c01001c1020015040e1440035a920300a00d405485124070b441000e09030242c1c2100c02410003029100401082114800c18400d100d0003d02800f01515200c401694a01254002a15013064141000714403081a0349003001c40d24089850543c030901a201c1d86402c6400500c968401035100001080e0303600e5154040d0000c61240344500256070024030500e405580042c0522100b80c103000d003103c0000c410421400303a450b00300d40030305076140c00d100c6070742c3d1005848071110306520500003c084040200341081e90984600312010b007400c0c0100380c14641304584d41c5c040182400304000880c0b010420703140052044164141d41a81500c0d603920381140e000e0b018101c2c0b528041000308582c42d000039407040580031041103d005030341b220f40402c9281c904841039080940000041c66017042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784422517 1250 784421267 784421273
    0x112031b05010207060c110d030b03070f1211150d18050d03090b0603070320040908070804050a050402030108030a030e010e0a0b01080d030b030703031b0c030b0a05090706020a060216 80
    0x32020500e610450001d6610642071600c3c44c25520018030060900980682d201082003001c11031510000040c41c000550f100340300c0c0002e1400a042e4010102405c0e403500104801082109034000103022340d1034a2807054520040c084020807580f403c0ca2405018030981d001001681c04c0010001d40281446102030807e0b10f40d0b0307061017a03c00400011075510300100c401c022000040700ea01c40404c4024020043c03840d01ca9900d0340b103441d04d298403903002019444e413441d61180c2c031407030a40d03421248194482c055440c00c42c290358414060301e807040854400004041c038103402180c0c140c03520a40030f1350500f490040140c025000403290300c2d4165480720744951400d90104040d02d15980100071002d56945007086007410115107a0840381011300302000303500d254130006a076900712940b6240ca910041c040d613139002024101d0440051107441b0902001042c044103800306406074440c4941000240c0341c2c608016601c2110340304a0b005038100700106804250aa8007422494003410750410002885903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784423767 1250 784422517 784422557
    0xa0804060b12030c060c03060109141f0210060504022502040b0919140112080c1501150f020a2018070201050405060f0c0906030408160c15020a0b011203 67
    0x20b019081980c1c0f012826070300c203440400a141d003003003031040420704d18185800002c00e032414038041c00854445640c4500c00035162581c0b150000040300304510700d00c1810140c000d4990404401e203102c2e40e0308100021680d8a890700c2192003410f00c2e080f820369480000501440b2181c48208240c0e0b0042c1e56030b68110a545030070118500c220950a01110402c041c0d2000364101c0386101fa4202c0340c01c0311900127101c20303140402c0030310900750000540c58079007022115007032418a070400043c100081d450000180c900100c21b0000d01e00130715496130040c000010f1000c9984204160000d4803400150910b0200580402e9440581c0364010b0038082d0504520034240303004860a680d08401070395260308200600505100c07044d0403110f40f003910034240c18248121505402400020761013200d00001150400045d10708640041401503440d80342c102143c24201a0304800384a00704015404101c030300a61440800c0c01100580c3c00340c03000241e6400c0085490a030031500c0d20031001d003c82900d038043c03408406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784425017 1250 784423767 784423789
    0x150a09050714100804050a08160c030c050a1d070f0e0a0f091d0607050904060518100902091302090303071e170c1b01021f02030906011a0a0804060b 65
    0x60880500301c001d0318060099400f00015100108880380041c00006040419403008840e007024041d900c912800c22070300780076140260003c03c039000700d110000c20031a08600243c100e50048401c001c41d240c2d52000000c007001c00200c07001d03075204044000b0300c0c018040e100884281c034080ca80b00502c222a1800b20b0f80644450304148404180c0f20000c1081604a00036040c900940ca42020102c1066044595461001501c00c1062203000314030303141103441c1d07540244001c180042285141c50310603954503071400344c140d440702c038010000340001c02d400d21103000f210111300002c0c04500600346110f580030000c0d0002403205034036020402c6000e0219144a00304c6404d5114020041a5644c1038504813420314807004140e1405001441345565802000c6041041349040d400c50b10440304022004030306004640e0301c0295107102c00108844400c080794042c0d44a40d004004031030081e62501810f5504090250324101c00810800220048a20400103d03801030710880000c5880115440007414032007507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784426267 1250 784425017 784425029
    0x18070e10110106030b0f060a0608040305030705070c030807050c010806030c0904080f0c1b0414040b0901060918110a05090106120e01060b0904051b030109090203033903030702150a090507 82
    0x4030814820301b01e00b00c03c107250700000200d40d04a5454502200a80b003401c009101030f041c40302c04000118181d02a00481e85150b9004500481c115241d2420300c00f036400110040d22581700d00d0280048550040410a0040c20001d00606071750012908000081c0002001154404400c0c0140030041c2c81c0880038207040a80380c00074041c001c4100c0d8410403840c0704198014450f60030b10f01814844035580c20882d4105400c42440380780c07540c1314800c2c2400340c6442d50120014a16001c00214021741d0f4200c550b1901744240005040c00821000300a6004050300030345504c106400f004100783c0b40920707500d0b6074419440a011404040350000682154043d80c00081c420100064100e11464103108140d44082a481c81c5000d000c240102c0101d5800140a400030f0241c4d2181d24000b5941c040065484c0c55080b2801841d44040040f81940c64840320b00360756881803d0b510408188001c080182e910413021070f0b004101003011403612482c2c00380c001c1c014080b015550403040001c194240911006424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784427517 1250 784426267 784426283
    0x10803180f121c020a0c090c030b0909071a0301082d0a030c03030e0f1b010903020918060115140738010b0a0c080c010b0603090c18070e1011010603 65
    0xf8168283c502158014045182150040f1900038002542e020700d0324250b0380c200c4800500701d800c145064004014004540d0f070300c01c07810010030080c902c0015481098030185a0200044d404c1041c004076640800c1c0603010b942d40042c0318156500766140b0035260001c0c0c44100c501e84c4003030306001c1c076414001c00d04010b0740000d10b015403080506416000342a00b031000031004141c0c0c0e4800b422940c0e1070b05030080c140c911480b8503401540e1541e201c2d010942c040c40d001001c01c0640c0c14031001d00e441d0175514500944150082c80c00008040f529140e0840f40c201c00c0f601d6842c405a107100f030400340c907400120221003c907842e00441050382c1c00003c01d03640110480a2801080080c03842011141034140c0c80080490020001e2903011903011091100d065030010466454a8407882100e014000301800c85170440402f00402c1186078000400c0070700c0300c1043e0b1311041c41d014072242c1f02d41d0390700045503010041052000c0e40720081c20b02880410070f0b61141e161180c2854912560142540c0c681e07030040c0c030156 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784428767 1250 784427517 784427533
    0x7092a090b31030519020102070902040803030a270b040204110c0607121b0305090328180b180112050c09010e091303051315090e070305010803180f12 66
    0x64115a9580030342c90700300305402c000c0c9540e071070a50380d003100300350390380013003120302d6200c00316402044180c0145c051410150740b80d503290100c080d582c2d0000c441d0003c40c2801c082d27070890f07501c5c81d030085a03005100c080d034a030320308041c10f0304c9004650a000d48100e03049940c80c402410801901c4003e01600c0e80b181c0040c0c10507040c42c130390041035400150700442182e0710f000e80f002002822030f4540078403a030036410301148990310464030030304601070008900301c203c0340c145200c81107031407412072140c0100450b185c0c0c0049024a90040c0404c1c84c1c28010040003107410000101510418030b03d0310340307401e014500768070000305d0140005c081c4c440998030920b01800106000d1507541c3c01510030009060143e07110750091800c841134070181803002c00040e06212000600c12404095035000002501c0d00c106803078160603030300a009012082d20311803018482103a0001c14440c0f0f1103402228100d034003000c001c50820404003030380b11100c0c6d148014070364058040404a441500d42d85254828502450b010381411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784430017 1250 784428767 784428817
    0x1115130308091c030b010c140a0515071430061507080a032a0503010f050f030a080a020703150605030c090906150d0615050307092a090b 60
    0xd0070010784811010f030001c00d100c600d07145207000c40300f480210342d190101d0550348aa0050300d01c07529550000c1c211007200d03206070600d0000083e190703c11a00c41c0d811990300d00c0100c0b400800c0300c48151541c000187c602d800403402c4215560103411350104c1640703900d4118011815134291391003184460b40c03200e50303048100060b40c41e02402d0703500140b8100d4003051074802c1503a9548220301c80c84c00900b00b41a90380d81e4188242c4013082101c807841d00c048520030003410314204085d0803508244100900d48a29103000b050342e04001740e41c10400b50014004002d44150fa640da9451504a5100c050452040803c0000400c182c0507081c0d44401202c2c01c00200c0a003414145801c0c00313580510075010356200f0050221546000440c1035002a03188a680c0a10b080100004e40e41d00440e8405000d6504024178000442203440d01d400450704118116808950349991050a840d4100c41303010004c440680c02604040e9181c1e020741110b400c0740380942d20b444d102e00c0140c0c059003021880301e058420384004400f01c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784431267 1250 784430017 784430027
    0xe010c0206011802070f0f11030d02030c0601050103060b090409151811030c01140304020d0b0a1d0d050a1101110a080103051002030112032102041706101511151303 72
    0x34000c03183c0020361901d4003d807070f43c0c40b103d48880001001400010507404c10302400401d000382e9508010305075100b5000c1070340003d64a030030000cc107800318007440d0000a03082d0b002c2c0c810712084901d40040d0300c0c00c24a2250030000240103145003641c0800300001c422200400500c00d80110b40c1401c240c001c1100390a04162030b070b03a80c140c3c51460003076204489144050f0380003444000f280000000b01940c030340e030310b00c08a0004c001c4c0c190001c1014501106220106165420614540b0718a80300054164503031003074696500403d000400c01f2900c10410100d100e8401c440c1103c1070201c04002007100c804e4080b8a41c9a03078081c02504000944800c0140200607003440340395803207900280150308550504c0c001400101c6440401010b20041d81c55040d04281c07480044d020304170888400f1034440d60b46001401d502410442d18085500954000995600c01c1d8032614080d04c50544c42d20a10311248242a1348410a149858200303124083d1007002900f018141584a909403101401d03a20722540380c00f403c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784432517 1250 784431267 784431299
    0x706020f1e03030112030306050607060609050f01030b070e19030b180a05033a020a0f0302030c0a03110d090515060d1511090306010b1207020d020607120e010c020601 73
    0xe0060701900195042a10000a03039040d11418001440c00c03102c680390a400400031035009541024010800d80144042540000700315500b00c1c0d414010b954800c4420004090309001c000c0120800a010a0000b031050751001100c680240104000e000002e0641900859035031040710080b40c09410090005038042c03012012101d418010004e402c0f40307036940c0d138a0b40140c450b9a00b240903200307051110202c041d809500b07580c401c2c0b50b0000c0f011a0036492080a0b60004d00c8090200d44203260f4003c40394401c3c801c40340b02e030403d255200e08103139106100310090701084074030444051007444039511000c424440c074014a0700c543d0040071500445074804603003c000905d003610500c0d030741e100f01020404404050380c460401d000b00058540031458a00e007180202621142c15118000002c00d40c0b02020004082e850700c200d04403107a41e543c824040b81d4510f03002d04c2c824016088013001c2080ca07406928030882c500c00142c40800c0e8042207000c0c46084079035207160100140c1c0400010841c00140142a403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784433767 1250 784432517 784432543
    0x20c0109150c09080712030e120705041a010c170403080a020c19060c0b180a05150a1e0e15150f121b030304080106030b0f0a1404060b040b030706020f 66
    0xc00c3c1545802507064460710144174569010b95425469010184a102d070740440901c020b28a1418181480d501580d600c0103004e500d0141d4501645044110881d141d654100c000595400c843c0a80c180c1d40c0c054400425003440503110018040030001910040c0a40326214142e8014a03e000c140c508200743e081c00503c00a9001500300c505001d0300794441c404a84054100c0c1c9105140d0f141c81d04040c0303004144d4030311110b043c0942040041008000309554860031280c01c591400d945a02000702c045802210500f01c01e1203a9070342841c4088240e030072100030308c4445020b503018407040c04446680400304031101d0100d141403401403d014940511f516142c0e10041c0d4003e00d1a03000449060354410002040d51551400c081d511600c55408100b00c81c00342c04039038001c1c0900781e560700c0d0001220000b80e516654545c00000000c42080007407241c0c141c840180c41101c0d02a817107a403110801003466800741c8da0810381300c4a0314280703070310708103d03a00c0200075a600400b4024458011242010b2003103001c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784435017 1250 784433767 784433777
    0x606080103020f010302071703132d02090a18060f0f1b1d030d030b03101503120e0a060e1513030b0c070b0f041101080610080604020c0109150c 63
    0x501c00350320b0b114181d152030038007800c0040e0340344031505107461322243c2c0034a4031252400004c20801c111454507a00703031150f4807030b420003010a904401c010306c10900406020300d9460307100081c20f01524001044642140c00c1301c0d0006a5641441e030303811a9681242c42c00d0341c0050301e40804021044551040c050034000c0081c2c00c011061035218651103001901c1d0040c17081010150442c0445075950101700e007800002411900c00085e820720203809170603114481c0d8401d0040c0c000c1940c500e01e9500411007402441035403060900d0841d910b0f5403548402103407840401c540c102e03030512036464018104d170151106845511030729150740c041101c0a0125003813070010b0034090144006507003111440c4402c2e41d0340025244039560300c2c035024003854012140d010b0301c41030b042010b20664040e5148020301550041d031049440114030707001940c4e070001c242e51454101e21548204203400e03224810300394109030010000f515140715044024207585500344c0a0381c00807500d00001f404001d0030710440080d5809803c1c0303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784436267 1250 784435017 784435019
    0x6080906040f0206031005041409070501051201091d100b041104050a0b1b0334050c04050406020c0d05090414040201021903020c0d030818070b16050a0f080d06060801 73
    0x490218400b5050000d004050202c01716113124000341c100d03005044007030001c000d02d0407a041030685c41401580c50341800d0050721004980e42d40305070300710791606041c12900b0900780d184c4107042000f01104038021104c4200416001161201804612800c80c0300c41404a00b0a080500700000c07108501c03682c00050704100410441c03525a02c00c0d0700c088841c2c0018164589010b8144101c04103003002100c0620301000a030000d120203110076000c0d08828080c00040000744455000810350444403000e0241e5002d050900c8651425400c010360003845544054285410069403a1a180303c7c3c04828011071b00103c2c01a4042c00d02d4071890b0401034001400e802581010f0b00041c2d111030b00e40300704c0d9864a6030f6640007024503000b000208240d540c09041001d074203e140c1002071040b5800c1e0784a4490a03030040308107154800002d000c0c000e03114184415440e103641391000264505d0b0200741145c441c0141c2e5076540225682c006040400e81c040e44800b1f41e1140c0e4003190741c00b19411900010140700c80e13400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784437517 1250 784436267 784436273
    0x6140a06290409021c0e1902040507021606230405010c0209040f0206070b061206160e0a030c09020309160e01090207021306090b10030e0a02101b030302040608090604 73
    0x4004040d2000c2501500c080707010300c0520340310740c800e40d00f10101c0c4500003c0d16000d110001200c2c0e07035680300c4c00750302003103100443e00c02030791500b60100201c0107030a03110308070401503d040d17844039800001e0307801241d120200d018110005440107920100109840c1a82420b41000d002c1d082d0300000300000045280504020003e0590010307010f0181c098249200001c0400808842c426150303600145050785624540c80c0240c803640084942900a140300500c01d0504240091043e008200b042e00512204045040480361112440c0245a110980760000404a0260210000500a4010096941e140000c031841c908081c0f44030302250221203560401c00c983c000c45074241504c1d050840540d5507507050000900a1141e840c40c681020314007400011101d9443d40040d405035016541c3d0702a05c0c4102d101581103070b10914000c101500080b102c440149402015251510709904100241c1c00048941c0d241180441174103c0100754002403d0191542044e0b40940c0100001c00409091500769 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784438767 1250 784437517 784437539
    0x504090c170a11071a01030627020f0f040f05090c010203030c0d0c0504030206030702061506160227010f0614030106050a0f02010b0d03210c08150d080706140a06 71
    0x2e16561581e03903608002c028607404842200d0810382c009540d080400d41000c6003891003a001c1c03204070355042c6490306066090850603034400420451200c8900840f00716024000a245003800741c7d43c1c800502101d6256650301d0340b0074440394824120300020a0301d0814400c03880c02040c4508203055520910400662802c18002c40303800d44645100491030811080c41902d15003c1c58000960020340401080480c0c0e5000699501c51300c0803003020707040b07100d000301446460f00c182e10b141382c64034071041428005030078803c000c2c2c05501d01040031404038440c0d08464030f44000302a00400000308010904002269210b404087c0f5065200141855549000d601401d0f501c201a440000d01030000c3c4c1542e01035000394407401040d50082d005100f40c94861500400e411500d0183c0000309a45d5684038800300440e10511400103d80e881c3d018107a2500e00d000a250a48601c549520602354030300358000800c4071014188a61040c0c0010074400002d203240c1448031380c01014001a5071401d10200091050a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784440017 1250 784438767 784438771
    0x10090e0c040b032a030312010e06240d021809090a0b1e1812030a0f060905041101080a0e070308270102030301052107060f12112709070504090c17 64
    0x803074250a1001284d8020a0440c010702954116400e076810001032003011030041144201c601719a01480500044100182c000030171900481a01080c410b81b43c14000660041040c000e40486c544010240c81c00000c5060508684403442500f11548c05020088907000c680e8000300c070b19405426100c42c01140c20f48151000381000d06070490a03000d12008401801600c40403401a000c0307a980c0d1600d90342020143c039000381e140d8405031408030000307800b000310302c5090b001e1540183d41c1360007115820300450721203001030035403001d01c1d50303507400c580048004200c031000035072003070b000c103130712110501c40b0f01904d00c40b08a0074095940c80901d400809071f9001c401c583c15180300f221799420b035900c4062000400c01900d04520024403402c50003184140e00f0405410707003507090ba96040300080d0200700000c243c03241e001210803121014850320041c03681c1010302d4080712840303c810070820150400003910651040c7d441c00d0103d4000a400d010b00c440c0d0780100c40318074a031410300003040091008503120032100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784441267 1250 784440017 784440073
    0xc030f04030e0406030b090c0103050108102a0309030306050f030601091e061214030a081501120c090f0510050d02160b0103121209020d020910090e0c040b03 69
    0x91400000d00701405840241d00000025004200c8591645461010207105030307080c03240d41c8902c60600310303698070074003807103040e60103c0025191344419840c03018040c1034246c61403001d20400391040c5132808030380784441d0348040881d60003140007091400e02600f00d82c031940161340102e91020344108252000540941120102d25001559444666019000c0d19039042458402414102c001820906110744050f00a0081c024420300803468542c00d682c07845040a003138040780054000441d1700850702e003480d5000700d0604000c1014080b04a200080320019039034900862030089050146010303208810001c1d00d400c0d94140c0f98907884030006011030003210500020b460300060000501c9243d40d4443c000300794003c40c102e00558603490300c0740000c250f5000400c00510002084000010f840c00381900032a006401080b040c1c1464081c41003421000380b08540307094801200140541c1b062040082d0f034104000500380d0041c1040412041d06d400f0942648243d002d15003221000e01ca011f0000800c41c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784442517 1250 784441267 784441291
    0x1b15021006150f2d0203070b06010c050a0305160b09060723090622080a030e0d080a0f11030d0e010f0203010515030403030e0d031b08162003040f0305060a050c03 71
    0x694003c030342141c01c110800c001e0300a91445991200190004064591f56101d085290001c1d91480011141841e5403040a00664080b540c1000400d0080340100401c03044841c442070280b00c541c842044031401601d10001d070354400401c1013003c55010a1680c0310060301d840c820b030003800070304516855005a03080e0b50b02c20100028401c20208240d04600e002403904884e40c1c00c0d140e641c845090300d0b1540c00c1c405a0200d00039001c1003013039150a10619140c1548003100504090304e10004841c0603546080c02000d204503084484200e800400c094490080820341c0816411100d09010742950444904540828011b0006200c140c0c0e0b02e0200c602852100101940ca903501c83c02c0403406084178101108081c05200b03a2a481c2940c59041004121281034100c52569611101186c190800b151241000c1514045909225201785208098511041e100254107924607101c0c0703055910640c45a9003600340d110040040100034410070340d01216400040009140c1481d05805610009150307020343d20f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784443767 1250 784442517 784442537
    0x3809041107020a0905010e18060106050d14040c0807091401050409050a0f0b010311060304021005210c0a321309020315210a1b15021006150f 62
    0x140c0801600d0041c0e80042c0841d11055881449400070310f02800340040c0342c0d900c8000541003a030b2243d000114982401c5c010b2075182e1070703d10102ca1941000001005083e1030f40003c0301c454600510160150740158500c0303152a20380302a60749401d102c1d80c041c0c81098241010f21465000207501c0904581c420340d0301154000710381c5031960400b070a0300c0c00140801c3e1488040010b01c030300820341c40e05884c03084207072503115120340040041b540412074000f5407000e0351040c518400c40c46600a00800110040303400040701d0560034004c0b011104540280807154049001c2045960181800301c0c0806c042c280003646020350014000982c0c402811200d40c0074000520089141c2d22200d03036402814122000c41d00ea003008960020394079401036030a8487d400340c0e24840245001400840b0720908a00c0003003005e80712036680e0001c0c0314064411241695080703400007840c00340e07001e58603010125950151401d402c205904004480580e00941200b82404130400401c903013003180001c1000c2c060526040344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784445017 1250 784443767 784443791
    0x9150d0e1b0904140307120306090c1704110f031209040b091009020c0c09091b1009030b0a020702060307110f070302090c13081f0b19060f0e0a380904 66
    0x1403198100c0140308104003400081074640c035034016410b46125200a02142f04005421100d001c6080e02e041d0f401c03400040420300050740c5c061020514800900b080b1148808800000c1c20184d41c00d14400c181300340007615080d41d19084c4a50040e554040300d207401981000c11070341d103410b030141c01000c00d040e60008044030004000c00c21079480803c0100600190701d011349005440c0c0283e241000c0342c2e8040c01402419520744050f50028110865a64210551550b2200c02075200c000c1c00e610324640e403c10800c00941c507008001d510690090300c1d4070b918ad42425400c0c521305900e514501002c0d8021b03442c20300042c1d039080c212541281105c2a200d860300759881160b00b54002c02c0c0d206240c075108600c07042c1e11040c0d12407c85c4101c8410082c007044421502c1c010f0040d5032145a2183c90f4141002c0c0b4203201860284501d00c0129405141c1500c55100c818003088000007103800c0f006042c46032002001d46507030024140c00700205010340300801012024040a22801104c00362445140c4410550140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784446267 1250 784445017 784445023
    0xe010218060d0225060f0c270308040308041706060d0f0201110708060106030609060b0a030c090e130c1202031e0f0102071b0501020304030b010b09150d0e1b090414 72
    0x7403220300c80040080c08524034281c0c00c103044c0c00c00b021a049030070b00c1000b4001006c54851055980225110701007108481c2086800d1251f400d07020712a009003980c000300100e126000504040c511644126a0301c0b814036400c1c10600340030703040d4412a070b4040010021541c5074082c0703203844031354808120704c501186440180c030300005150160036248161130b400501050300051540c126843d0303803010005951240e1041c42524140d01800040010800444002c0352180c0c0c48070503c0c1c84540380402e5215162011401c1110064800d10f401d5040c0301d5500c02408041b01d1800c0042c0f132404050a03000c0d4440c1d01091f191745056071a0032a214070121103080c080400d100d50b1954002880007196120000c1c9400c81c00304081c000641c000c03c01030203000c1219400002210143c0c1d07000517a80741282e180100e81040c2d0340c411400640c00c242e00005400c10844401b002e008880e0001101164400418100515103d01044150031000000d400001c0310b8440d0081a5009500301d0703900201441e5140003685 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784447517 1250 784446267 784446277
    0x20d150504050a0210020a0503043609030801060914091017150f040b011a040914090105250e03030906040602061b03010e0708090a060c050d0e010218060d02 69
    0x11181030004110401001080d00d40d4058800c88188076201c04c00c000880e580c4c142080010b01a600030131041c44003d03012040c54a629075500b120003502c111031500c481c064500b245900c60f4450b100d480d2401007680260b501805002d41d440c01b4003016103064414840b107510510028050303074030a0b0102e040d07036254000c5800904110301d0160031241525086070340d210750003560b002c07000c203d03000824224030410400c039008607044183e04010b6404e007810198007008641c403020740c00e842040001030140742405000040c0b02c08004628080c544842d03440e00303564000f0814a0030b440500c00b00e01c40e8120f444d91844600c01c1d1440c14000d905141000320345503108058a4a41c89500490b0000304140d000500300d20600c03100e04036584154a41c1e48803c0e0750b000030700511021550610006000c035104403001684416001c04942203002c031740c0c40b035404031440d2001000000b0760004401c1c3c8181e905e03018203c83e02e00184021031034201401c119401001d515040d0610030b141c0003c18861001852301610307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784448767 1250 784447517 784447553
    0x15032b1419121107050c0a06080412110613061d0d03180f080702180402010906030506060d111b1f050612070e06040e0309010e01080c0c16030515040c03020d 69
    0x71503000f104070703069202c0e004014101c1e500d20400d10032101604001c0b0004c821500c042e1100c4d80d080c2c4881d82c0c0c0e100e242d05011110810845006101c2e061032100304100e40c06203214104080000365a410650191000184010f404030441c80c040c400301c4200103010001c0d16244c1c500055901c0e50452500003548c44018041c000e0a0728250384401d1181c1c0794003c3ca9803038401c45100942180300e0340c40140c000c500710b40c082c0c00309071010000c000c180e000b0f410241c2e1051005018a1502c00c800100d0002c55600021115511038040f60b11280000b1641d240d11402e0080001880c80c80c501512101a203041030314034060058a40e8003080301c40c0c40b61003140c501c0c49002015a070174141c8490340361464140072501c640c0701718100b20401a003e10040b0481d0344075801030b580c4908806440b8015503050720040c0c0880c1d05440200442c50360480188118540740c281c43c507900b0b0605180d82411440c10180c0c07102d03031440b003040c581840006004104490704407681501c0380040303485582000309031840c10080075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784450017 1250 784448767 784448771
    0x7021c0e0303030115020c0a120209060607020409140708030408070915050d0506040308060901051e1203070b0f010b040602190204060f0915081903030515032b141912 73
    0x415101d2030350b41c001004605c40d1342120400e05020081000b804a14440c016000d0a1a58010003508200d1f880303540c0441d0117000d007032410702283c4c045801c40b410210240c42009003011039898010042c415640280304540c025401c050401381042e84840380c52003800d04143d90350120403e90100d0075100c41c0105401440e8403107400c06410459191802160204c002500c050300094203840c2c001074240c140e88024081440b0135034032002e10440b2071504000c036944083c1c105031506240c40100000c2c903d641c4141c04c009428201001c000c80c40e0380042e0040c20b5141014402400100d0b400500c2046031a02031120070045882070003c2002084107401500c11000c98141c0031560000325080b031600c036018000c1400312140e81e4401151103060103507a880d8000100c3c1041d0300424841d80042d60040650b01d12501000c0c01100083d14044482c0302007001034007800802d403880c400800603402c19074250f0400c2e02c900c200c0c0b030a40c01d0700391081031030013a035900c40440c4240502c0d00c141c00c01c0360441d2143c403003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784451267 1250 784450017 784450019
    0x402030a020d0503070b0106020a08040501030213030c09021b28080706110301061e0503060f130f06031401090f03081801241406090126010303030518010507021c0e03030301 76
    0x2043e5220ba110450640c0c080c1e407280c0001668a20010ba4a80c03110307003041c03007207081506100c0114041d5014940750040d160303000201001148440e448400141002040141c1c0c0300c10110b0100801e400c50481d00100b600705100c160756480742c0c80c00c8232001e4150650301030782083d620b24001d05c075030207160005000c0f5464282c413022100d009000540c140d0702e541d250140c646006413009002030748100ba00ea00000c0c0c09101052241c01c0541030b82d42202001402d40300f50f5140e881545003150131411078a205561200c0c410000e00c070381e2400c28004910b41000900800c40c042d2281c0030074110001c00142000315240004d41100d10300c1c0c26084900010364000e0008040c1c1c803411b200000550b4441c40030191a8290001c2d2001e2102405c100541c17000c0c210038100700a010054800d001d034200d42100720101c1e01190343d140740700d03007041d140a507110362000107050a08000e203441d03103c1001c0003510b06038504414400101d0300004d41003140c0104038043d0106400310039046545541d80b00c081500341c400400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784452517 1250 784451267 784451273
    0xd060c021c0e040b0d0f06050c040b0f07030f090b0f09151603082d07020a02030d0c061404081b0115120210050a080c09031501090e0606060a170402030a020d 69
    0x1ca00602c028080310184000480d000c104403c00e1100c4c40014111080c041103640001d10030707000326610007104a4850308040e40c900c40e00c01160311682c00d60f015000d000900c64200b40d0072040d0060010b9040c5001e03c5100d041c001015194403c40c1810004580f010810407d29600c40517042c0f00d00c500000c04540315003d8030b079100101c69001d070003240882d02020008040d4094070703114100f01409000b60380c200c540c0c01c0407080031561001e0701000c11401051507243c0583c90130810850084004e568601c8526090306006048400684146141c1c2c282401800045440070050751449010002c400c00c80c2c000c000d40700340c0141068000b0b0a1000b22152001850500d4181c050f45524005c0d11500e4001c59440c404641500c541300000c1c002c40c1d8107a010036544480c503406404510805000c03241c035035007114084e0b04a503d00341c1c800d01049840782000042c080341408029081001610400d05103501c0110282c0701c0d034404414004031290307042c006010343d0750400985903001d030003816820344025281 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784453767 1250 784452517 784452527
    0x121124030711011505090603152a160b070315060e030c0301060e0c03040507031b060e010206010302010e010c02060405040908030609010602190f030203120115020f0a020d060c021c 79
    0x455030000700b8103000100d40820b50600444440c0314a4070b11542426090400b0042c145001605194162040f1556401d220f014001503a0040c3c1d80c00c14a10100b03500da0b4902d608600404920404a483c00d2040c03074001d01410900c02125a401300340d40042d9074070b60740100d000f0440d001010101030070540c000240d0a401c400203111080d004e506a0316802c01c85001d042c02c0e00e445100c0c1001442e110800102a00601009550060300c0744043d00c000940c0c070b458001c40c0700d25980031240c90103841001000000e41002420446060a002400c819807564001811035500c0b50030040c140a0400845011941c52104840c09040300410400001c580c0d4205803509400442e01980149401c01c00840c1c00c07800041c24000f104482c072070060080560765500d602006014008805502c03052085100341845914002d01130601101c010f140103c80c218000d01d0103080a00be144281c200c01c2c840300c0581c4400504c04003040c3c0100b8045000001c1d01412450840c4d1020035030642c0024200001ea6540c1c08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784455017 1250 784453767 784453771
    0xa021302041d040c0306020702011e03050105180712020a21061e080705010e0409060e0c0901060504051f050c19020925111c02070e010f12112403 64
    0xc40b00303000100340502e486001441c8141c038084c200603040c000030400100d140d00180003952061412090760468009e455811880c061700a0000c240c4480052140d82054845000c2c0001a020034420906041030050500b02d156044890400d8000aa81481c103000d032000309501c12450a20072807030207a0b442214020225806504403101982c8032804816910700d030120141da0005000d0b000c081d1410005491400c94400040d400c1740e00d5440380d2001c1402442800019040440900103140c5580700300300c080003050b0000014003400740b00c1400140c8031480d9601014141c2801d008034241c00c84000d890901441102103260304c690091526602080101000c0d079510035182d03074007251158043c10080c030502c8030710a10742e045100702d80a4803c0c8214140d00c44ca00e550070a9a08000701302c500500c01d2800c0410310000340c0e000b0081040384500800415004203401c2c1510058241041c2c40f07008000c1c42c0031405445082541420100381e6684440491413042c0e031050f03611090418120800d0039001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784456267 1250 784455017 784455029
    0x40b040b0415030204150813080304050303090607031a0f03071a0c0d021f02070c0e0a09020f090c040e0c1c0605090604090c12031403041a0705091003020c0a02130204 73
    0x909403811031800c3c003e00076101a02d558907241d458103904041304481d42000107203454440000103420801107074154004501540c050b00207140c0c5e81c50001c00d0303207140100c050560420145001c03803000d40c006c14400082c5400308110b840c81040072003040002c1c034003091504810809201c40541c0095036102c007000700310580a18003038804001003450280c0c7c07180745904000d0708207054902c10389851a01607000740764451103585601c0b1102e440380140b06140c0d030100c2d1044240340ea03442d81401540340615400d18001d0080b00d0f0101301c2e01d041ca800741c910740918440d0010444c003100201301c8250b464000d883c4620384c00c10080220301d1240c01004060301c0300d4481d1500035066103001c24582d0905000c0c030100782d604042c10030107580c6406c40903030003043c28500a0301001224070040003071581600096010b1809200500d41050b842c1c84981c40545d40640343c0000e00c90200585190340d100d407801c1140c245602d0400603295680112914108000520003d601080d440602d1480c10f00c96070290013a525 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784457517 1250 784456267 784456289
    0xc0f280c020a0e0403021c050c060403021018080712110f060703060e250c0203030f0309010b0a0e27030a0908010516120b01140c01140a020f030a0908040b040b04 71
    0x80c3c2c2e4807500c49054800c4c0c90140040c0c0244410380c80d0b01e440850141d81d070390b0003868243e19140e88880d00741c4c10104180d500304c0041c0c0006c0210300171071100d80900307c1d02c048819006860a081e50f51810b0346403040e00f000802c4081c00e800440c1d0005d0107010f43c10f50300030f411400e69250140090111b521490b00300c5142002ca07207045408205400c240c692248140d000349030454550008900c1900580080d044a10401082c2c920150058800740098218078000c05e056070303140d007081c942e45821748441010080c05454090020885000c0c070b010103d41101241c1032010241802118000c5c1c03516448003656440c0c40b0004038444029440340d0381e042101d0740c02000f003007161129158100d007070b022050410001aa09000c81d198120143d00c000042001414410301d4140e145000c11400e401c81d04090703400c0d07551012220b88032050003402c40d03030080c0c180b02c0440c54003000d03283d090701700d02025001c4c40d00341303550b10038800400c8944800c4802501c0c0d01840329869640d41c8001e441c09911902420b01442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784458767 1250 784457517 784457519
    0x61d040206092e1d010e1504090501090b09040c1e090908031621231e130c1e051504081c02150903270f090c0f280c020a 53
    0x14840e41072131603102e10b01c2014410300000f40c00111640c0c0ea140480c0743d40001020748124250000c3ca0082c401804030382c07408600c80d8902200141210542142140180c0c01c810420000900c1100749005030341d03c1d80b2001030300c0802011302229110041d00139201c5503180c15000341c14041303020061441070300005000504000500001c9a4013003c600c1e6520010f0f144500f481c03a02e03905601711442c030714a500b0115060303c4011981080c948403d4907002d01c401c01130300c0c0030f00c00b031141000e00a03804a00c159001411035400c0d075602030311400d644100000c5500313a100034500741540994000c002c29004000c20001443e40c41398203429800307446601014880c4030841e80c0106465044000c016035160040d1801400d541c0c0d00002c0ca490003040c076840e84c0401c02501004104071902c0710141c0d0070300601d40305c0c00c40c01c60083c40016072801225500c140c2d0101c0801040d05900c03c126021009808002c41d200c0c960504072070b515181c8441161100c9a1107070101c041998809540c40c0e071309000f100e241204d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784460017 1250 784458767 784458859
    0x90618060501050904020c0307020913170405100f0201020702040c0914030601030803060105070519051501050405060a0303120b0d0b070905120303040b1302030d0e03010c0201061d04020609 83
    0xd0340107205603808104240704010b060b280c04d9014107022414902920f01d443c402e07500080350b01408560074403c0c880001120720500c64804070f1000140340030280c0f01e182c02c2c00e0900040e85030080448620030031107a1441101014030079015555025070180040c810000d006101828504a0b030280c804001c464201c40322003031a00141c0e45d4103c0c1d401100991450b1609001100d1650000000b581c840c0b003044503003500d4001a161003058103004401034140d0452440030b0740c40782c03601a032000d0b00ca18144418400b143da11340d0700302021030342c0c0750134000301444c805400d0308094010001169808607000c214035040c80302c00040d06110341c0403079a5640459480301c2c00c0040c0c42c1e200000340c0702a51b01c1440040d0010b80c0344250503401c00640c441c1004641c5141d80080e1414880e40303222800100c2007020046182005d000d0014203080500080c0b2203030b42000c001200f0b125100080c0300050401901150640d201c2d4000c07510440d00240c10200c41c0d255403121410100792410750000c102420341085200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 784461267 1250 784460017 784460021
    0x70819080904020306060c120309010609141603060b18040f050f0129030a09031403060105460e091905180d0e01140a0206130309050a090618 62
    0x1115a100e5280c074108a041400c2c04020b40000789519084001004440800d004c200000c000a03c5000c1866684c1d1070014806030941d4007640c8442d054a04114901d0b0b0301c503c001c00600e52054007145540c1c14000c1c01c14045000d0582988032500065002030780301645041900701c014107090580701481681900c042c060102c1e0310480d4031007020500d940c010b000c0031441030782200910b590001040707280c144040992030f1a0b44155101031145684110070b030100364000d45251f40440031040d18504516042001800d648100d23051f00805080c002c0a44000d92400d50031405407491210114920b07125040040084203880c0305c900010440c559039018981c80c16044403442041d04a210391030000564403090301903c00034051400c040e0303040e40f0700b040e4110f007003210800e07191007650f80784841110712001514002140307800f9030b000e40082010021540d00010819000170000300001500c09090404032901d00761900003e601c4681e2083c0002d8880a90700400c06858804440881d00366450b8000e0741 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 784462517 1250 784461267 784461313
    0x60e0306010807140d06020904022709160e01110703060903080c070f030c11042f071a1801060605031503010c02070504020d1805151303080105240c0708 67
    0x100c004d00d02090400c07030342808698042490712400c0054140605040020166000304c041900d00d0030001c0307000764003000c00b03001e040f0496000355141c0c02d9504021001400c4205125400400c0c044840500c4125034070a10721642a541c644c8280d0314903070f84a103031000c09400014401d800081078000030622140d0400704560009512586142d040e012541d4191400e21030f029094640c007091700c8034159a41c449000d200f002c0a003200321105442c440c40c0c19400b0f030082d40b40342000100f400340200c0c40017611110030350f050190404d4002e140d035541d01d0300040c061142c034410b10f400313542807100c0040d04c0340e0030001550144206101c0d241511544034280b608840001c40d1100040e880400101701a00b030650041c0080e208421010510000d00d583c00810303d1000c10003160300d64407508501d003d41401c1050203801030706800c1d045c810b000301074170000d00010060003424401c40200c40441c0300105a85580d02840c5103604a241e147c04441d1001502c40a0510811750341e03010722001c48080da241682405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 784463767 1250 784462517 784462529
    0x112063b0f060c0325170c4e18030405060a110c0607020102100c0203210114040e120c03090a080f160f0605180909060711011404031d0a060e0306010807 67
    0x44c011b0914410349800e8203802030700302103145000b0448102608031708240c4070381c414125101c02c102d00787e01000e503001e01c2011201031602031540458140802c02c040b907407150000c60008010a0031140b000c4111300314452540b04990000000494140e45500006c2c4480c40e90780c81d0085d1248112410184540c5100d4400e000b4010b0700203500c0710795060344960082c0c20440c158411207041064003050149a4140034030360511001c4028010410800c04807410440b002d0305940138020390700700c0b801d815036400541d000800300d964003041c686180141041655540d0000510345034895940c0c60001e9101c148a0110f1b07401c0e030040205480c0090031a0b020030089411044c0c4020f10140742540485030381e0041e40030507a034070701e40c14080f204c656640c400c95030151a0500142001d8186150702070005400d0307030180e10003641030821400c200240f500d28503500a0b01400d0010f04600c0703e000c000340d80094090385550182c0b4445011800c01d034000442517002c80c040e400c070cc40990700c0d0540c0c2c99442e00366220322 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 784465017 1250 784463767 784463777
    0x1d10090212070503090f0706030e16080a0311030904060e010e240d020303040f03050f1e0a020f010e0d05010e1002031311060f030112063b0f060c0325 66
    0x2041c40b092042e0000c1d42e10240c0c0c002561031a60b440c0d40a1820030003d64000d00009468660303a08603ea0180712a0304d2030242d1002c0527049916110345151a00d401e514060280600004444441c0106004843c00128000d01c2001000e4031040724294100e000e00138540103c200800084c0d00031030100c0b802c402100b65556241821a82c40e0402085400510040fa094081800b0001da00c0301c115a5490103148120064000201400c01051500c101802280000325030044110501d900c041404034000350162225408400305a00698162101c59459500300c4082d080b40c000b400300640c4109030450000b0f0941e41451100003418059010a50f0481d01c80c900304a0800005035858031000d0036041d000e01a60f00b0840803000b10310072074009078410b007180916406140100070b66072145860041142c00780d101220013081e08a95401c6030140f4040241c01c403425864620681040411b81c1ca150100850315149003140c51040a50800d498141e1401d1034170b000e10f4800c809080d0050142c44c0640d0361 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 784466267 1250 784465017 784465021
    0x80606010c060b2220070c090c030b12010c0219050c06031302030303010305070f0911030610230d06120b0a021c1a1002030906221d10090212 62
    0x114002400b0f007210303140d4840c4545080b0f80d4a0310160f5429425a4441080040c00c0603402c0320a0900f00c142503845109540304011000029245145800a51b100d00800040502d1304200940003000243c000a920541c2130040c41895038054000000c0400b04d98282d858420604c0302d0751580c1303c203080d0010b140f6040041104644d0620741e001d10390040c41004030011200312900440d003140d00a81041c1c42c10b0700842c00034010036600d90920b100901820341e04100800403245808454003000e4039003480f40300038155403240136105584c40643c1a0007043c5041c00c1405000d01e8181c0c1d54008003028200c14101800000d51143d05110b0300009500550060f00550b46e90410900035032124480240c03100c850013203c2212804c078483c00240546502c100f00740c0494074410081c0301140d0814050440d802003194404948800040c0d41205240580c0d1000881002d00310920100d01500090164042d94104003048600130b9811806500094024000c041d180e035050030680c0700f445402100d00d040b07500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 784467517 1250 784466267 784466273
    0x9061d0a12051309050a06170a0c0803090108040209040311071805010b041a1b030409061706060307140301090b070203040501120b0306150d020a2312060c1b060709030c080606010c 79
    0x145d80e216550000c00200b65807107140640100100c03103c10007a590240c006603041020721082a0041c090b010025424840e0307020000307100071700c001c00017030180a41002007403c040c092103000c1002d0000030159080d143c0c40e0181c04140c400c1c0b0100b602c070704c00d0401c4000100740001d60122415030340e8035500b6601c2241c140d01404aa60b100f1020b07144200004001c1056406042c005400501204a0003144407482d1102e8100c5851840003203250540010042c0142954000f503400f00700e804408a0050342e0550313000203401030494402c081c0c04800d401c0104503026a001c4028010380e40241c8405200800420500d01200c00b02c0c4001c3da0143d000002092000d8400001700524150007402d0042c1c00da01c0e5030102d03940030b001d41e0200c2a4038840102810307240c0300070a145142280c080e02c030904002c0980840d035035241400740010300076203000102c9071900c5407840301034100340000c0c608461070350500c180004c0400b84a8807068070030b03000b08040851000c8010485074010b801c16582c0400d4030909031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 784468767 1250 784467517 784467521
    0x703050f1c0b13021206040b060d1401031a04030e0112061502070e130309052701031a07050c030316020106090c050702030c0f0d0609061d0a12051309 66
    0x2035200c038450348060001c01c0007244114589003510111503000b103010240402480030f40c1441401e1040c81e04e005000300c80d0402406154640d20100c12034001c01c40392152070126203613201e8035400d111102d00300050b0f030350300601400702c445c100d03849411078426540500b188010160800d480c0140054408201d201182d88035040c100b9846001000003d003841d5945200b1034180303500e10056015800010003000900720501110390300a080c103800c41441140c03560028004038031809002d2040d44001c5401140020b11071181d002c0c1e9044000100d155612424100001d0b51240ca40d40c040c242c11170000b5440b1031282c0203513040c460b134580045003143c5400800000e4000f22560542c11503583d9800042d41c015180200c00201c512521100d0741da15450040c0344c10040884003082c0030350303005500298076440d84c4480204094011900050304030303841ca803400c060148441080501c4005481c0100d09140c0404c0c88032006209030b044245601d42403106540d40d02540c0b41c0d0f284030703000030782c4c04001000300d60b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 784470017 1250 784468767 784468777
    0xe061f030f11090405160b0a020d030908070503030f150f0a17101b02010b060705060612010f2310050120010b04020708040e010f03261606050a1103060303070305 71
    0x26003110042c200d040300100d21030740c808503802d88041c1d02c404024003503981c04c000c001c40074242c04089545040e406c100c02940c1c505131082900c0c201551503541200303000d03005007940c2d11543d000c0143da40c0c0342000f044800e114607055803140d4021191420004891804110310b60f43c4020280c2001ca00b28a01500300706e014032004481c1c1d05501944101d402111003034402d03061050f10300443c0d22072803030440c50000e0840728106442c5003e05030410034040401c2000071026401181129004120b01d50441c43c14054803006500a02c61801c00c0d00428410507a200030007404606d0300e0070684680d0320050401e00e854800c1c820a030200d040009002c1900ca002070451200b084a080089034128010f00490201e900502081c3d0b58084040b8050110741620780a01e40106110300244000900750b444054140651202004a101d42c580d03401000504c0e10081c2c4003c0c4482020f404100c15090078850003800c4103d841d51445441c0030501c44080303010200b82d90190b4005001542040c3e0140c3d0103a41542c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 784471267 1250 784470017 784470023
    0x90f0406150303081503120301091104031205030105040e19110a0503060c0a03630c0b12041b0e04031d010c11310e061f030f 55
    0x150300c24000350400854841c03004600c80c4d601c030700c00307881c4c00080040d1400303a00d040c05200340c004c40141c1000e641d401060b00d040d1101200c00052018900620503141e225603070000701039800c0545d04d544020703084009141205d000307880a208184104032865103444000024003524084031560401040c50055800f4041901500d032000302c40d210360000b840c3c400c0895200c0b1004a00080c1c0b01c40e1140d07d4080c030242160100700300c8840011031205407203000201030041c0c0c03104172550116656011400318000c8043c0300e0074080d0041c0350816461002000101009130b030b2600300440d0003e080c04100007258045c81003220314201c1d60700c1e40c1d43c9260400b06003524a40d4074001104011a9440d592100a409180f01c0e494080c205001500071450104200132407078140084031a000c80800c01d24034206501e444100d500300070702003089944103c1d2040c001049094090111182207080c8000d500007101d044c00c42c1c0c102c54280d900d40c0207006d4030142035008050302504841781040014500c020610f00c03144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 784472517 1250 784471267 784471271
    0x308070c0c081501080f03340c0b0c0115050d06051e310209180f0609010f0f02090d30030506011704231603030203210105090f0406 58
    0x40e44481c0c10340f40ca401070440810315469500104a899820041880401e03003580107141000c000d02d40c240040c40103050340e0060201c01c6003481101140c00003460f000103600c10354031400c01e6190f0a59007402d40000c0e81640300396180540d47d000e1001c0041d00b210894100420800445035241d44501c064034016000b112702c130750300042910300c030f41c46403071054405d00c104c030221030342004407650100c030b8417040300c040d4030821036441c3e03580c009a1a112511179200e250825501c40c3c03002501039140c90b104034507508459500446043c08141403064205910320780844a003404240750f0306401e4812031264901d010341c01074402d203507500010b020180342816032043c0c808843d12031041a00d15000892440c2100000030307911300400c040e642c0c202c107240b003100411a00c101424507080c0e0b0b40c2c0010001e401040744400141182050110808100456885804880d0300500136038924005c1c0d03036904459920301c0404183c0c1c0201041c803880b4410704c0d040b100010840d40d615100c240180030034400180c01a80d10380d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 784473767 1250 784472517 784472519
    0x316030828180f050d3002161b0603060e0903071103100204060c02040e010c0c080315060c01050a06240f0e041803080109020702061b1c050a08130308070c0c 69
    0x324606410350f801030082001e01680e050590f4004c09508510340d44022600700c4800d08161076117040c03500803089103140001070342e49507038600306001110030b65801000032101860003a500e00300350252004a4556480c1072040d2600c80d5484480000c04491035801c40d4400d001100104504009176082d81d280501500c01800c1c0781c00780c0505aa1083d00a040458169032040c400c5080a06ca046400d044080007005990014500100030000704c58010709181e2020001c14940f9404045001082d076004220f95a151001409a8003911048a403100060701d441c07000101c880b520708100c2c440200d10814000c3e100d10004041c0d5070800b400c84d0100030000424180c0360340b41c5642c46101181181092051806c80c241d18000748033b40c205030041c058060060200000503111501595440407130350f008454008441e07641c003441c22000581205500c13641c0e0410034003103608030f002031281c9001562000344aa90306070284048201300c09004000a03d040c0003d07401c0c903c59503010ba220340c4983e01c218605 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 784475017 1250 784473767 784473773
    0x50a150e06090a05070509010503030306090604020408032a01060b0a0c0507090227060a05120402030a050610030c060c080f0a11100f14040503040e04080903031603082818 75
    0x1c144100e070300c002d10f41e000301d03c480240902080160018482100c08100d99070406001c01d44900001d03000c14041c003802c00104a047e83c480d0107440103042150110f9485261002040314504820f20103840302a06255075280c101006005500580e410250224980072901d0344c2152680034055064415004515001c6440030703080c0010204100401d43e05078542500200c10f681480b4050b203420320612041200803c82c5802409807035840d0b400011a80b00703540c3c0e50003c00c1c145642003100420500540c41040480b84042d0b4484081d41c0c000c02030030906c0d98541006a42281c1b10500c050a048018001d046c1c64070042e40c01880380b40a1494401c041e5440c40310310901d400400c40010848175202c84015603100690b1290380340400c3c0102c0f41c3d0740d15081a441c0d1035100d114034014181090399000c005000d005c0301c5422a58440b501800f140d565072103148180b841c1410308001200010b102c072022400d004031104000302d000070404010101380c0d220b121400c0c01031541c01d0001d114102842850307008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 784476267 1250 784475017 784475023
    0x3051309151d15060705030c121b010902090c1815030718031a1b0d090b07030e300d020915040f030201211e050c07050a150e 55
    0x100750070391001c214282001a104903500550000607102803802d810005090f411580c903a036640b02c00e03503003980d40d4102d070304001317085104121001c2501e00c2940c600f001800043c100424074410300010f400102c0840005003400e07200c804c0e402940c0400380101160a81304074100410a58060f041ca494901d5411008240340c0400140d40400d002004010000c40e00d0b00b011507041c1806004900c0880142159204a100042102d24000e000d980100240a07a40741010390030414580d01412a10380d506251b40ba0041d00e00707403004640c5440000c0102d0740f0300d0b00a009a042107010440900807410700c280090007103440451118040c0d0500c0c000c045e000001c1c0308001d054110107840c001d0390307686c60700c01440030141082581862400c0e042004014105c4100171100c261b0340c2c246040190170502d0080c07401c60748850310110220704e15040c0d10400c0d98024901d56064002d1034082404166503d401400d003d008a000191a03504445041400601c40011000d8450310007400001c51840e1507491520b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 784477517 1250 784476267 784476281
    0x30306041a030109050a02030c0a05090109050405031e070302011512060b0402040b0a020105090607080405060c0310090c05130e010b070b0c0c030703021e1f0902031c020c1c0f03051309 81
    0x505c9420208188055080901c04803641c0e5406982070400c00345410040785010005215003044266030b580443c04000040c006c036000d180d409402c0441103003100c0307404402580458411009507103000342e059010384041008804542000a84031440415600c900025010742c40303905600c40e0b401c00000c02c15000c7c24019000ea0300d210f0340001002e2500a5000345829006070104050215000030400056000917000c4d0f07129454402094894076000032400c00d902080e0001240c0c14108500081403c0d48070020b4045070000306c071252200340d607460410128040a000ba400340004c204001d41c00310344800d440c180c00c140d100c140d0300d140c0240425102e0554010100032001078101d220510030302030b00940705602c0703043d0500190945507a4000c1100090030341442000c1980c0e26480da500941d6400d000901903c50304461384155552072100083d140d202d040c124074491112084204041c0c4480e82c40070ba401d6a1201100691503801d48040d107441e045561650822804d00d080460b07408a680a589 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 784478767 1250 784477517 784477523
    0xe1b0a090e0a0609050a0905031617030a0e0c04150b07080702040f1d0102281b0b090f0c090f061504080a0b070e090105010f0302041a0c070611030306041a030109 71
    0x40e50f5003010822800d6a4024140581c114200002c0c800403400100c00c540d44401902c0030880c1c0201c0d2840d002c1c00300b4105100784041745401000700a18090540c0260112407140c2c0245e41a01025000300300c12540c440304400480420702000740011803c7d003005041c05400b80c1c4600d03081c03001d55030006050751810104040950385a81b10868403462183c1d401c400140080025810918405600081c00c0c1a410583c1009107408240c030300c4403406500c4140240030340d105004c000710480d041421101b0016a4600070f00d21030060321800c04840841c000340e403040020020121a181d032000000b01c40d5010b400d4a50240903009a00340012200c0c00810081180d0b134094078141449040140c41010010700c0c3c982845100d9181d8111a40e600341c4450645109003880f4010b400400c8040300240140d8109446002441c481040c0c0c54444e440a80100e0700d80800322480c290b100d55007200d80c0801b0f0100c0603050f62091000c07400c2032416400c44021040390b0300c0140000c3c0180c40000342034070880c034029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 784480017 1250 784478767 784478771
    0x4020307170c0904180b1b0408100507020d020a0807082209050f0c251b06020a020306070f05030f06030102071a1e090a0311011b0215010e1b0a090e0a 66
    0x4503403241004d00a179000c0040040c0740030400d4071240c55050103003034000d01c0b0100055040c5114281d03c50510140c82c06040c4603030483c0c01a0000349905c60050005894010140c80b62180c41409035200152004c071142d48408002e080c005150ba0300c0030680c000690346129901c0c03d00d28150840700031131120f80100204107000c1194100950074088051000e084058003510401c40a100c4082d0240c01c0400303409031280c584006003190500440264a0304030001104960080001c0c21b9a4001043e011150003202071360301d552075040c4252a84400200312901240e800e100083c1890186186560320a4001d000549008103603900c0c02c5803000c00344a00750405400c6400d00003650500c4202e9034cc5035150030b981c0380480c10102030a43e43c680c402c0170000c2c00c101c0720101568202c2000c0d008089001d03240d22070803050b5100b074035000c0d440d01e0031002c0c0075080a080764000a40c41e0081c26045005020f02d003002000c0c80340400d020200e99100204940601800d603200090040c00c110740325100b40303a1700c0c0d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 784481267 1250 784480017 784480027
    0xf010303030b01050304020a050913150e0c19030308130c06090602010507210207030504080a060b1206041e03180611101a091008030d0902040606080403090504020307170c 75
    0x10250803202c0034000c480c10403106000300310060700e8010b20402601c00c2102c0e00a013640c0ca00b40340b003202034519200208504a03254900b0940f0a40c1d400801c0c0001c2d42074280c3c0c54403440c50b010300c44c180703040703042403a0052514034040000c030340100c070030740d40040c800c01c10b04074103002d00d8484180c580b182c0da01c440d0015178138074806c0140075420701c1410380211852806818003103412030550782c2140c0c2002012045a4001a02810035028100b218002c0403070300103961482085040460040180c009030b54001e0b44c232186c40da0341200d40490301ca440750751301a448603103110415500c140581800407003101400320030710120355125004034010340188442e0b40d9100e20300002780d104c607091074860024004541c0c1446002000000c51815504070040c00307888000e40343e519540d500d5000fa4841d4403040307013030000080000c001030041d040f0f01007250007075600703001c4030f95103203000c8609840446024000507018801400705103820740066801558602d01811840f5130002b41b400100741c00c0d00c101040100004d9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 784482517 1250 784481267 784481273
    0xd02030f01032312090d020d0c081501080d0e010309150b100207080c0f0a12080403060b0d02011b110a08210f0a050904091502030a06090c2001060e0f0103 68
    0x90205aa8400b44003c46a03420307450507000e5aa207050103841d1131500001c129a01c0d15150042010302060b0011310602d42d802560030a00e035803010a004103409401a041030028884072801d200c0d0481d19058001e290280a04004a6241c550320302d0440c10980c607904148041481b020030341d2010b03c40d88074000f407051900030400c41007010307480180d0300395008036808100028010409911208090b90301203074400e00d443c00100601017a41082100c203d5189464044c80a0300f4017610950b48602d00403c01505c2100c104900d000c03502d040240010007900468001c0012805440e0034148540c003500101d450007400100c0c2034041d83c121442c0d40e406000b514010f440d1303c0109014880300c1031103032407600c42440d00005061042184181c240310f0000f442500f80e031117942c0b0024155821404102c1c1c00c5125681a6010703500684103400c046051100201d030020003446014000029a2580050b11100036000354024400c00b034011920f55813800006050314035807507900e2044000c0e10300c440556055103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 784483767 1250 784482517 784482533
    0x90305030a0f18261f0504050f1204060801080102090a2702041518060903020d0f0c0609051311030105010c0503090a0311010210140408280306060e01081306020c030d02030f0103 78
    0xd040750500c0d4441403032580c10645c01d1482c800e450304030800124091340d90303007001803819220140700006441244081d00903c600740340500306a9081e0794400c2950f0b640ca5454034281d010b00ca2000340d120340700c45010409060b188205901002682c6820a07409245903440c00481e0803651140b00000c01d4095404d07001a8050f100004c03200e590359480c0b40c61410701400500082003400700900681c86900a60144800c0c0b016541015600c00e0318a0007058894400801840c0144911801010700b46034483c01505540502036a03802442c0c42d8900303603880c0c0801122083d580c3d840a81d100e000402844806884e400c8d2941d01540c05019140c0c02c40003101c0009140c00d50409005a031580342c25180b0001c051118580c1c1c2c0c2180c0c001030550744516402000303201c10301a0360034203850803a0076183c04c00110b801d50481c03001c07a801612001621410744005540442c000c682036010f0000f540403e000045882e4003618210f03001e50300300c1e4207040304140703010102c1e88107070343d520300c108140c02c01001088100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 784485017 1250 784483767 784483829
    0x9370902070f14030d0c031e0207150c1101020d09030e03030408030301180b120d02060a110f0d11033303031633050601090305030a0f18 60
    0x204524010480d02c0301d09800000708070080c080e0f112907000500c03041081080e00c0500c45450400c00c0410180701001e4018108024146000c2c494840060307524500f034400c1c1c41045810000408070001c01440b510010f0064000020500010001401c2241000d00c003038400416081c1c00025101000d0802030103203104005103078800d501c2040240004240482664110b90300c190441e903045020894503006058005130032500011a1510b060350030398006410401f50801ea0242c80c50307500c508240e84155a50780f81d03241c405181c200480c101c83d040301c200403c2c24005285001880d40c1605050700c1560740155020754200010f8500e09814403c2c00400300a1480c22910560395540800d010a031039014000020620080300300302842031264440e0b248443c0d5466240442c03d58040c2883e0800880e240107003c1451442d280c00100154081c61102095a4000000318244504001c040f03460205500c400c40401c00110090601005200c07107600240c02d80c1d86c00541101d075441c1c240c1e6820012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 784486267 1250 784485017 784485029
    0x602091201380904030c061116020603060619090906060203070201080112060e0706050706140106023703030605190e16050f03160206010b1e0937 64
    0x15080720104010000801c400d0107900d5810054418140020b80144814440300101d4112802008001c201a8404079000c655485154200444040c20301400f00e02e00031002d100141d640720202c4000503181c6800a10341c407500003860b06203460a0080418a9003000c135460401080d1000e9007405650303407038040c2c5005090035200842c10540540c0009103070801c18407031055015001341c200c1007403080c6134018480b06640e1000304c90003c8c0e61103000a015900c0756105496031880d102002c00c451031108509412076000d82c0c010802c0e0303076078140300600c0c061404c0000e840d8540410007205c6c0d1f02803039051400441d4020b1f100003421901e00700c06d00940490b00c10b890001910302d03450600c03008a4a802c0e0540010b1446140c2540c1c002010b0282c074a4072400e034242c00c071781a0210400544004820100e41151309540c00c2e5000b99995907685180c50042031031041404542041c3d2021201c020000b81042c00b5005003440e0319035000710402d071010043c1c50440005800010b500c0e0031b80340e10b002c803da801800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 784487517 1250 784486267 784486271
    0xd08090301231f050108090f010e03130e041a1305070621020a0f030f0b150705010605120d031a1201050405010e0f100b032506090603020711011404120602091201 71
    0x600c040200001541e13001d21414400650080340806504020b041c2e104580480204103000d8101e04050f581d0304949200c06600d13848043c04105410600002401030ba0b02c0552105003261541e13103903c10580042900341d018440d034a020012403000c0090500419a40d15010300b8101e111604d070fa000540c0d5030700360b4045801041000740c1d1540c40501c50100680a160009240c500c82c0901d50240c0107090a941c1d01c51007418809001070300c00d10041513550300c110001c0040540d503500780300c2c0b284001840141e00c2d41001d041d15084ea03000750801095185120050f0424120f004001100c080c5241c44400144c3c1d9039008000401c14248294142842040001d0004440c070018481da1074600b100181c2c0241e48886c4004001c3c0c40412130300707070500b50034884101882d101003c0d101010703450384503100010b06c50b46800502140a0f1084403262504002429403c000c4103005440310300c601c0d1401c0c1e01201c420400010810380c08101e44000510410b005030360b401e108010018100642408070050303034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 784488767 1250 784487517 784487551
    0x905070b1e1b10020316230408032a07091a120f0106090b100c061407020a0605130807060b0d0501020f0c010b061222050d0e0319020f0d0809030123 65
    0x1410b0400d480c0d4049850303140400e140706054034179441c0b9240b401e8500d01f00c21001b0a01191503000417015002400352000d100118200d400c95203d1920190421140d00760440c44013802441c0f1260044401552850910420481e00b0004203e03001d040c140d24222079040711000600b041c10038062440102011002404203108210014143c1c0c20b1410b1404180702c043d044100410840743c201c1c1c4504078515908850a150001010f511050807244c02ca51040c581400113001600403148480c9150304010800c0c288901a900c8600820301c0c5800640d015408c4c501003400a4000d000500c003012401c000c140d26480c0c1c81c80f00c6401e4400d0055079603c00c04044c030203c03281c0e0720350080860780810310100c170b007040582420080c0c00402a0302005842da002d40074900800a030041c003010b00242c2c06808503890030080607034000600d24001e43c02940100e028140c2c024a02c1d14854207082035005540316031814100c200040d003103481803201d1002c45030300200300745604a4070a0a1590200207000045411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 784490017 1250 784488767 784488781
    0x90a02010f18030f0f141b1005070c030c0513180b042919020c0c09091212040209071107090507053603010905070b1e1b100203 56
    0x5000aa01e10104120000305a02010418560500464100e400e42c2a44183c1e801c0225000c52003600a48440c01b051100c480448000514000f0072004103600c148101548401c0003100c50040d052401000740130320180700454540765045004600c03c00e40b01403803524240902c004295107408c030204d040d15112600b040400e1414014400c96449051001c05a4507854014031840032002d0416552452510003581d0244803000d907402000d04d607440040802e0315600c150240e105840300000c00da04200045086801c18903c030b030760401d441c10305a0741c1d911030411040e15190004284400b0022082e010f000650811140232900022546024000a0706800907281d64140500c00c80741c41e15035030800540d140c1d220720b00b5a020104955030350b52502c100c500d0036000541f61215400c205640802c408112458140b280a4146034008090035409250105c408a0b41d0080490058003602d210303002d20012141200806031f0701d400500004028284502e150b140099451680e020b1070320400500c410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 784491267 1250 784490017 784490027
    0x31506180b0f0f0301020c240a09020102030a111c020304030b09061b090d021008090705100f03020306030309150d0b01091a0306030a12030e1005012601021c05040209090a0201 77
    0x22a000340d400080c03403c9031402090092150410600c00da0190310072400c410021607500012041201c501808151251205482100c5500303174000e01580c800c000d4081c40e40d00500c072041c000058001a9007180d5819560030f910740038020160001030708006010f008102400000030703044140c1d40c2c010200307480c24580c4220040010f2405c4040c88d600400d2000c41d9a850340c0c0b5a0040c2035024009041071003000c2e0002d0a2900e090340d64081c8c90280b54004a044e082100001c01c25540340da50b844c41414412a0a0f8005e51002e05203d030140401c00c01e510b4a07440e00880c646c000c0100c81e139003990b59140051100e08851090240c2c504000b111501040010210000464000280b5100036901c0c3c8501700080d04c0c00c00b10790030050078480c0017041d100e019601030744524681400c1c0001d039030303a144413440711000300c4100f401001c95010a56600010003100300111107020300c070200c001481d00e13000035144030140041d0040ca0707042c00e407507808010450400d1519107800256000c020300f00d50301c141e400039203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 784492517 1250 784491267 784491289
    0xe0304061202180613080106030b011502010b030d0e04061a12070306080c0f01020309040f061403030903190f170a090506120105060d1508150c03070804080310031506180b 75
    0x201ca107002045442850540714044001040007000130400182d0702d0ad030030074403001d0034899131a03030007080352044440c2030041c021b000039a24004d01801c4494851001075070951740030018240c000d55602c001180c41170710440c03408100707a4113403100d0703403105118480c105005074000c12880405003480020002100b00054018000380c081326006072004041004030314500030340c02d40542c068186540c1001661441d40320f4403e48044464104810242a040c10b41c0e0744103150700c82d5016070100f0000c01014100c00c0140d111540301e803001c14802d0000f9101c0d414201c0410810450b060760014207507640b80c2d0448000c074018403050310241d050650011303064a00d4003052080c0341c0140400102226806070a60188a903188205038215201762503c01e050399803180305500d00b4801680304041101d001c02c2c41d040c0e0340f10789000d650b40c5980e03945580da4060617800c0900121544c13002c064010002480700d211703002d902071149600107080ca14200e090041c0025010307141c101c0915110030b051180d02c1d9245000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 784493767 1250 784492517 784492519
    0x103081914040b1c09060b1005040e150a030506090c03070e04020607030e01110304030f060b01080118020919081c093506040f0b09011e0b130e030406120218 69
    0x280d1115404126243c0040040707013a41c0d109850511408100041680031301c020240c29101d28846080d003c0c8191241d11440c042c11030b54588010004d109200c140100c143c0075207014240e000400d0366543c88500e84141030721066681d4021030b1491081d41001c1000b070000302a80e40f6484041d0409401040981c0715080025040080d8218902081c1e400384e0581c940c0d0000c2d1004413a540d035501d0034000044882140d00b00d85c402c8c1040c07800139480d03100d850103a05841440040003045c01d00b0091060081d403143c0c2c4000e40000d03002c602440e410000317018290042c09000003421141c0880310100d06070207511201070060050040c800d10103d452203c00e00040505440400102c591010780c81c00501542200301d562440303480e00300420050800d00d0003120a1007403010b540c1a4681c0c0300224241c8011018550101d0344007003010350301010940000c030703d03450090803403060429450864802da50850b00041c1050780001070400c51306030b001641000a1084484c113705201c3e5022002c64940d14030803d503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 784495017 1250 784493767 784493789
    0x10807120c092601060b0306060a110c04050a0c110d0e0409050c090702030406091211060304111503240a0303141c09030e01021c110c0306010308191404 67
    0x7070050107010b5a4020f031400d140840d00c028111040d48103c1c1e030003a24404002d500702500099000e00d070f201603c1c0030f0080148880e080c44901241210b803443c10850251545c070611020300c4090b1104d11419000d5081070320042080d603e021030180200743c080ea084099603004981c1201480d900072802d5490070400c41d03000c14040501d0603d00d18051904542d160702a054074184290190000001d1003107404d56250080f13900d98a0700d00358040540028058001511018001d00900d090310007583c0c0503220b4040d80680c40d0b4110041412102005200c10041000006000d12125290300c1c4c00801c8101406035603030100910003007a82401c141c84000c05100401b415030364030042235400c5d102c40213102420340200740c14481103007010f0320b811030080e400704030500000940f952012a40b4500c01c103203030b206c45150703482540040352041c104260440307040c029001181c0c040e80d0280a1580214001c0040c2da480d003481c0b0140d4030705041641040300920210303000b1440c0ca0203000d02501c1c00c45080c0645 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 784496267 1250 784495017 784495031
    0x506130306051302040509010507110d0f050307050412050f1b0f04050c07140c0a090218010c0203030f040e040b0c130315020712020a0b0705090609221e0b01080712 72
    0x20307483d0641180d400003580117040004100082605600c914401c080c15501c1d0080d1a00e4810700c0b944a841d801d032600300080140c1c840001340350046000310303045911803906900d071584e94000708035031419034181110380e074001d80d030a406030030310411840200100801400c0d982d14600c50028520745400c50001c1e00894442000524585995050380e800a422104810100c0c0091704800d4440540d2035542d8480c580307640c0003143c0240c0f03038030942d900b0310056201204184001001910552580301c41241e042c4404c010040c0d01c1107403d0b01500040c084115000c56500703003440c0400140a00500740078a10506000c480c07054000d00041c002145d0300b010070102c1503685507006a0180c451198080c1040851888502400c2d500061440c0001e0180c0b1011400b42c460440849080c421069100e51040c03060000754a03510300919401c0d81d03a2400030b510b003612224001c41909868001c2c07141151040754004503440802d460003103e01880c001d2802d0105441d0840000d01444614220660a9070355400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 784497517 1250 784496267 784496281
    0x402030703020909030301081b0a0504090213021902010e0a02010e06030a090f140c010905030619020d052a03040b01170a0c18060f03080a0507032c0406050613030605 73
    0xd1400385030003a280c98018900300400550300d520a21030b844017407055204204090700075034041040c940e0000c2444030300918010401019000d03a40d0140c8c1e001c040c2501d010211040f51006155240007130010004090071000c020742110201c00394002d95404c41070f42d840050703031f02c40d2841400c45001c42c2d10b10f403030f900c1d0706140a0042c011a10f008128040200d005014400c400f00c1500070008000c0c112040074040300d00442c3ea8507610310400b40c0550080000c110200c00c3c030f01c2440c4003c240b03d0170050411208984403400e03140183d814448142d1102541100280d000d51100c01d003101050000740755043c00e9031095600700c070510540c2d01c183c072910041d01007201d090103040700701a000b4403190081500d40d4031600100c00c1a01e400d2001e64134202001404188001881c1c084a42000c5010300305405607000350b0301a0b021110840800601f120040d000064050203050141d4020781e015982541920520046a40035005903101e40010300c130701c02000d000c042c41e10701078a034010800714041d11929 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 784498767 1250 784497517 784497523
    0x1c090e01060807020715020102070b060f130203070315030b09061f050d110402070c0906050f010903020f0103241a25050f03070f0501061a07062d0203041506150305040203 75
    0x1030494003811440048001c10180c7c15000ba103101401076001e072000d51100c404024801280c2c560407904844050014a0b411140e58051540030103036003400305452340d031105c1d40314201c445900210755455030030b42800481c541c10060103070301071310410020380c20025406811300181c0c1680f0420744108241d40400b420490181c940316140b200181040d9100d14030b41c5028601000701b070045a82107880d04100255a281c40e0800c00e40a842c103031a040e000c0303030854090200343d65a1030012030501d0b0301d40900400011000345042000b1040c1540c0448032070a019500b10600e104c00c104032003240e024440c0500c100d031501c010707921221010740c01400c0140c644c501541010f8103100c0b00021400301017240700500000c1120421b146114000130050359803582c3c0818140c000e0343c8201c00700d0320014444a0b0008480340e003e0800990501420b0004001c005019121300341c08411000c0f50355004030a000c2002000e00740d038210a14018400c0c800f060415500d04003840c54850210201600d07030000c601992414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 784500017 1250 784498767 784498769
    0x201090803010e1b0f0316050a05041802120903030a11090114070303140c2a2e06030609120306142808011b0c0b0a0f0b030a03021c090e010608070207 66
    0x10407140d40c4551507078a080071745400440d07022820b080f03103448050352a4881c80c1111400b0030b09484240c20203082c0306203801010303148182039140680c01c010244007000742c4245180f00e801c028004690381d14104a041080d581a00b00001d0007140511218040e80e800c42840d40850804a14103510341119003811005004d6950341d0504c0c1281c004140841d0240c4ad100510304403c4100d0ba80350071040084800582090301c52681c800c981020901d21041c1c400c8050b070000103841c1c1e68918a0f000c011524082c12244079500881d00581e550075404200070648060802070f940c1801c003000040e207800b14025507210306000b542e10810543c414002040c1e000b00006404104003200c40e000613403210810f5000b00900310300071400c1400d446420143c41c5c800d020707030142035500c05241701e50345e10b0340e03085a03000d00340d1025480c0c09151198245081c9071800c00000f0451030183d0f005168059240f1840007503004550300400070440540024001c885c1d40c0c04031141115101d2030001e9543d591130100300d0600ca82c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 784501267 1250 784500017 784500061
    0x52a01061802031e250e1804050613020a080106080d171612090f110301150b2203080a09050a091404020d0204140708220201170a1d1c0201090803010e 66
    0x920f02007042c0c495408050b00256110507034081c0d00d844a03034901c6507040d0074115801405607000ac0f001528101d048a003003220248060310300058103442d04038007070a403610354100103100e03403200701400c6201e03910035903509031502c80c2190100740e81801c44000701c424800d4907480040c4141030040031504070580d4800c2d994141c00140d0f20080c9901c2c1c0c600102840c2c00300d03500134400d40c01c150305040503501e1001100c0803180c0c0740c9046407500144413034240c450200b0310120803a0804c44400040030a001100501a24140340d680c403661f00e040508020380c00c0300039000760f1364541c90107034490020707000b400105421540407a045a130116482c8006009440c601c40070a54078550b100c184184550450442801191b9103140d02010116a6100080d1280e05a40190020b04289040c962a2001b48041038001c1c2c0120f4010440d40040d06142c901c00504114070890303580440801d0ba005041e0490401c48d00ca2688000e00c14540151116401408180079a400d1015501d02042d032a0744103000c0001c2001e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 784502517 1250 784501267 784501321
    0x9040908190504032306042a06020c150309070b09030319080403021005040218041a130c0f0515030901140f15120607052a01061802031e 60
    0x200403500600c5900f0511045900e01d036100380d25018014402c13030180d07a0902000c010812641e65403078400302150390030001d80300d1800c004c040c880d10420312903c0c000034040a40050006030303200030501c950455402144010100c050050241882e804107041d4101c420942626454094180c0000d08602c18062501d11182c079442c66117001d26003001030705100b58060b800707460001c07000e20b4901c0281c44080b14001e40c071210001d0031201c0000028089900640a25203582840e940a181484521010740c1c0c804014107041085800300a00d00c18184068080304030708510b003d2401c0042a807840800c00a21549500803001404003c001d40c0a44406101103c10290398141400c4107184400292081c40c01c54240d041840417508154118908814054004003199500c140b4111200d40042e12605174541c003804c541804800c5000101085944a40c00050804d15180c62041c205803180d986d284100d0040c000c00c00144010001002400c01c03803246402070b81c2d141c4021010024680580c002200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 784503767 1250 784502517 784502557
    0x1f0309150903081f0308120403020a06060621020f07080f0c070620012a17090d09060f020a03050307050f1303060b06070b1303020a05030a02060702011802030309040908 74
    0x15078001e81ca940600d09808104081c81d410780c1c21100e009046000180001008201f100340e0341c0384000040740e02c28040d1040e034008040a40d80d40040d00c0f2582c1c40240020403000e44402d42c264070380181c807004148440114900fa41034403070703041540111103001d041c1100206d0020031110846089030341800c0c3c1e01084d9108036071208409410764000f0458018000d4154421420202b014071a0007070044400d5021240c0c8805421440104d0f404009903400f0041552251400ca00e051002d4501400c2100c002e8060f0100d41c010050958056902c13042c10000c0c1040c00e00f58058002c101200a0383d090319109035241d40b0b01038191020b210702040a14201c030000f0324041115540c0e8640001c1c0c030711401c018450072071a003041102502420102030603140c825170105010400380023040509600c01d005840e004200d07611482c2c2550805280040560040020841421341c20312440700091101c007001003400c0520b4020076500c0c011900b5260045980302000000d101a2009554060040c2c200f464040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 784505017 1250 784503767 784503773
    0x3032b090c0603240e0a11090d0602030610030603033f0c1107061413150206010906270c120f0e06150f061b07030b151f03091509 57
    0x80c401c240c850b00013100902c181d00d50001c48000607504036508203200c940561110304504000b0f04966402c0c0c0c9205008108004064940c001941c0c030840c002c2c440180c59180280512480e140680241010503280200500001c1e400c041c0d00702451151030350b0041c2d003125007902e000350340a20702164200742c4440769244841703e002d90010340085541c1d5503101031100391860807550740c401900510f004a08912a058000d001c4034019080607418a02c3d440e100a5075101c4036855034524820b44801a0010401881550500d000d810000d0060f108405646420702003524040c0d5898581400140c0c0c44e030540501039881948000011f503c0c071442005100c1101c2c030850300500000100700664000e09000510403482c007004009417000141560450b40c0090701080390079802603040200011441040c81e08001d020400680a18412414840d40e1f00384924030103481c1081d01c004500c6541c103680c074206003601400075444580c0c0300e400c02042840044c9800d6004d800d05004039089545012190018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 784506267 1250 784505017 784505021
    0xc080408120301170c0f040c0210020a0905090f04050616020a0203070816141311040b03043e040c1103031e0123060d1107030e0f03032b090c0603 64
    0x126100d28030a5404c5940000d10f80e03440d00100c0b04459031050700072412000509282d00a0308039690144191180b0348035140d40642207030404a80d04e000240030410a01240c180710701c8440c3c002013410b004143c540303000d079202580e424006190101d40000700c01130f0f002d414000c01041c2c111a90040239a03500c291070b007400300d80d203107401007102c9007940c11002c00040d0130f03e24200c000220100501600b40001940c2c2ca644060008070241b074010b04d10030000043d20201240c061b6006030300c140c0407403100e46003040d0340000700c001a212000100400c0030501140440402100507035180949020464060803a415a0f00342d00c80c148003442400008100100340c0082c0000c6a82c100d080001216503980b203901505030801d090442c0d03014000d403100960f0a914100b0040c14820550f02c03000314600d60500d80c002c540350400c410480c0460301c520007000c9a450401c0c441c900317561080d4000c40c144a6100c10040b00010744580d11207242c0c242c0001e62401d031009d604002c20050f001241c40092555604000300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 784507517 1250 784506267 784506269
    0x804091503050f1f090203030304021212040b040515030105060318010f0f142206050a0b060a0f0e010e0303040e0c070803090f0c010903030e100c0b011d090d02030301060c080408120301 81
    0x180315200c04c82c5036041d0544c28410401c1c2e89401600540c11960340368240301950045170b0400da220b2203404014110b443c1910001d0025043c2d010106443d64903213020701142051070100c00d801d4000900040c40551140000c3d2640303d2a0f240072031003048a1300035a24014102c030050b130f131000340c01c0107401100a10150003a010b0312074403a808400e99601c1d9141088015400052410769005102c503400100306150081500414294000622842d01d04c00091440e4811902100841c41220380d042855800500e000041c500a00303010340d4a904180c0083c0c0c41b8840c034000c4550800721080401c3c00f90325010181c8900036444007640e580e03410030102d095914094850b0070303042841440100003055104001003811a80e050b1603054840140304100002003011103007400c100140400707101c02003004d0a0401e4028207800d811070401d903c5c1e250151401c15002003d900081d40030400f2884c02c10707400001c40b8111a001e2070008181c2c011444c02100a11403980212480d214002d4510b0075140342a000398 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 784508767 1250 784507517 784507543
    0x11012a120c0513210308090c0d0c1403010603021c1104020d090b070516030e0d0204060b1c090c05060f1b0c12010c0e090c1e030601020c030a0804091503050f 69
    0x26603a6599042684000038a2070b00c8003240d13200d140401000640100085500090044191f4034180320a0020410254148606031a00b01d652002001070840d4410f041250340410340c002d004c1235055801003034207840e0003030f402071200c041c002c8050140480748c602c00035504c10081c002c0d580d411300c05113010007030000610140d0b030003100040030514007401881220440b004c25074081070845a0b64400703584064580c0892078001a440c100100180d495120b020050500381c802140c813482c411032100b0202501003460f100b000c1c0340401d0711000c102445807d0040310021500566601c240b941101c0a600854070002c03188002884c0c004460640840c030301c1c01d42c3c94199450100000701d00c070701a00345c0b00c20340d1002e40070461506070440107080403022a68456075540c50149040b00ea8100d0303905140b0291382c0c208884c4c3c0c010041c48540d60341804504031820049000740003884164440c0d440d50711691080d0f000061b6107550824507042e000345e2490003140c0080681e444503024001081d00c44907603040c81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 784510017 1250 784508767 784508797
    0x90c0d06140606042409030204020d0e010e16091a13020a14090607030f020c1215060907080a0e070f08100b040e070e10121211012a120c05 61
    0x3901e81c2414004d81d070403900c0c00113101081c1d00103410640b100b0b12a28000504000b20200d012016840c0c41c0000c1c0030001083e0000141040040416403c6509800d41e500e40d80e0070107001003030354a5510744603609451100c03000088103403144511241c40c1c2841d02c0349035000903c181d1304035003405180d03016044405558a4800801c800400d051a480c410600383e541d000506010381000f0a100f141c40c1000811240102d5070300c2c03111100000c0024602080c220402d034044104242112100300200381c11410035070b010b442d242044c1402400b9031600400d00301c00c46a688c040d070000d00c00c0400010008000c42180c0243e096207a4070300c0c5440b0404204048192801c011621200381458800c0100c1c100100010300402801c0008090078800c0181c42c1c194881007803040416120200309640007807502c681c45811480340c082d81c014060342c0c007401d40c244d0540d1525032606035a401c0014060140310990403080b4440440410035070303d041032400c181e0f046d6803514100a1a207900040103050400c110765134 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 784511267 1250 784510017 784510021
    0xf060e1608010e0606072012070906120309031e0f030302031f05060301120c051804051b091b1201091d070f0605070c030f0f0b0609090c010503090c0d0614 68
    0xc280340801060f513410340c0115007007001c0404030707084032013055481720301024225084032110005000811650080702c10b540151008101883c064410600140540041c2000c111400d8902602070040c2d8800a80550002c00329800d152020105140a09520400d051107140343c504008000f500200c1d524803092840c0c4000241c1d44204a0207074040300c0006104034a03613801d00701e0305210b424407803070f0807241002c0c0340102180079070f0b41c070250360710b689c8402e2028a072502c1d0a0a1161900440340d4001c144550400c40d9800c0f11385803800e805520110619444100100019080e0710620070003039176400300c0d03203540e00109030922903403c02c410400414070b42c80d2110013941602600c6441a1280c038a00c40e10b0000b00308040d0b0f004c1d50190000501401c52055030710b503292614010b100c8256000c641d0b29040900c0c1508001c1c5030301005d038103c0004d54500080780740c4124040e0381c60801883c02c505110700800050300c8107030f0400003070800c12005030003020044945d25007a0090201241c4403041d000306c07000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 784512517 1250 784511267 784511279
    0x607090e01050d0f03180f0e040606170606040b060c01050f180d05031602120c2b120b06250204110909070c0c050604060818030c030901030f060e160801 67
    0x2030210081600003805003125413290307a0642c2c1114402c00c00700b1011100420005a0000401080700100f9007842410407600c0d0600c3c00c841100c031560041600305c50f070500240a24900005c8040e402801a80c000401c4040c4100064450160203440321603907003028104440c1803241045140903021650940c21161001a4402d40b904089080400000ea0520006110250a10b03034000c4122460050750004060012018241e6120416400440e44034068a501446004141c0311110a544000016801e00403400504140354591018140c0d500e56100100c07980e5940700303c500d0940480b41258140d55080d13a51007a03661a044141d02c55450000c00754040d92002007140c000b030200610b407503520343e6040d8040e02c00c2a41e0b480c080d600144101004101034807242c0081c8054109621351810303610303000b0341c0c4c1224414001901e01941d0014032078001800400002e6403401d072401d0030003188842000a04100070300d641d5101c25404103144003840001e06140600301811080360303441c804603071303290f0b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 784513767 1250 784512517 784512529
    0x1206170a051e0a030813020928020f031609080105161701030201090e0408040806070518030718020906070609080a0215060d061112191406060f0a050c0607090e0105 72
    0x2c01c0e504050b0088910140028442c10b00c140e130180010301284144481900841c4410501f19415540d84244032401004a21525114884881079407410f51601a500d401c1074a640800f1b4000200401310020284241e409581888050000c3c00000c01c40c130714000c00c0c5440320058031050900030896180740e4a00c01400c0007519410b980d01a1241741c662441c00c0a40e0895207002001980ca000301840007180310f200600c051070083c01c143e60781d00d0315019900d040c1461003201c1403001c1c2c800d81c000d20f4100990492202e840b15902d00c0c400d401070300c908c038400c0400d04520810200420080c80c08a10303c080024041c0641030034140b83d403c6420308140e5840d240085441903800d29809a640211400004d4243c5c02080560202e0880719007440103070301d94100312035000c1d5803280785a4805031003c1c108041900c1018021200040781c61164182900407910301c0c030800c180085d5200340050781121143c040c104941141a1282c121010b924080400911500281c0101028007011400004043c0390071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 784515017 1250 784513767 784513813
    0x60f0605010e041103010b030c130801150608040b010501051804020c03180a080a020d020406050d111002010c08131b0608160c24271704080304061206170a05 69
    0x9029003807841e400c0c0012144030360001401200300100400240c0248510ad1900e80018603026001141100004d00d00e0440c215598100300c041004031020400400c80941e080d0381112001c2c00c00315540c44003036009528550707512840769017286c00000c101902420020040460f4000380003604449442d00080101c0c0345203511038000c00c0e5001c0310644000d403a200e015090701a100400014126940e0000300390940b1507810241ca01c41c9102c52080d0007400c111034500e2168105100030480c0c0010130340081c1a02c030000e0440700404502d205c032041000400300003000d4010389950000c12640c0d44107401045441d0868403000da07000300c203500c00790b60742c002d26140503026400480d800a44003180034403030311b401001d01101101602e0f03050140312031802240d8070408684031035522400d0300361800c29041c04001c580450b02030742c00070401000700f00c00101c21f0360243d0b0460300d8130004116140090002616164000e4112a045c00d1b41c201c45080380041c040c1c0d030b0548030718155080c4483e1a09890404024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 784516267 1250 784515017 784515041
    0xa050a0b010804080919060f081008070b07060f0203010f031e0c05040207050c13091103070303050403031d0a060e10020d08061507050a030201020a021501050328060f0605010e04 78
    0x50b8030100f80042c0780b900c050720030f14001a019117000303070042c080c25402d4002a401000464480d44451a546134030051560340107042c1080f0040f460301d050245959a0703414481c0c04264000440c440d404c02403203820000742d0701f019140964482d40c64804503801d100c090320080b500000d00c444d100303a00021820090441c1c90304101d0030315145251a083c40081c2d40700240c100c40a014200b1160642d583c3e01241805558034000c00044005140c0307040c440e1407c4a48038540f20b41d00c801d004000085c3d00c00226010380390b2502e41825180289401e1070b02e0388401e5950154080000100401c405030300180124004030125142061454811002d0ba2600049444c40c00040d86035000225241003402000614160b0815400c0c030f030024507140d140c2800c00c0d0410840050f50005004a201681048008614064100d00200c194502000665a0011590704402002c0b42c400282981c10034050610280f81c2c00010070720040e4195010f000c001d2040f40200d80c0481c040700c1c0000b005051030711401c640021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 784517517 1250 784516267 784516277
    0x6021501060516050a110a05120c010c03050d140f0a1a150408070b03010e0f15010c02040603051005040308010b1e1812010209040605040c02030a0e270a050a0b01 71
    0x100742441299150300142d41c10f0141940340740d0400000b01d0801c103c0521500880d0350095180e403000800184c0722940e4032151250030490100d07407004e1004900070482c5038003420b00000c29011441c09903082d010303041105010515001000e02c08040c0d00040b00c1c8201c415410314100c035540e800c103d40032280b01d00c1d4041d00b0929a22001c1007030b030800340b007510140300400c0480f0f820280d0b00c02182d0300d41b48d11900240103249010004021242c0e141000d00e411031010400310200e45403140500301002003d40007241046101181c0b40c0a5445a90104010713542260a6030200490701001002a050a0b6011800240c0349000020605c2c011415a15118036170404826140d1880c80003d0140d044110061005e18201b901d8000d181d6a015412007000300900000d80c841c103004040200301c440b9940081d0045d0304107815007084640c00720858038950118140b40981905030000b042c140e104039031a0f611300b1418400c420f0890140d00c94441d115001c1d01005000c0c903030f1102066401c0d130340d441c40010b0120b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 784518767 1250 784517517 784517519
    0x102060a090b19060b0c0a1407030b04110d06020c0105181212041401020c0a0b060919150e0a0b120d09060f030905120d0b0924040207050a0b01080706021501 69
    0x15603c161020404040c0200101d2903686803141000030340c0c050006540e40780c1c054031500d003c110064140000042a20b40500398052460712031180c031040042004045a54200c0c00c0c2030f0540c0d0382440b4121654000c0403c40d00d03401e000f00c14900070f12098030124464000303802110310712500001c0e100480c684902041c0d043c40314001c0c00c80440d00000c0c00c200da80c06495032201080072405d1000e00704ca620104e0090480300c00505203140310100160440303010310008020401e507202c40c01920011522203080c000b401c812040c0b00e5400e114400c0d04034000100c403840c107100c590781c0590071001c00104d08540c40f40c62258600c00d410390b80c1c422039045c400416444507003040701a000d4a502120f000040c00d01044600300e40d990a82040700010000200c042d01295207000c0d04840d02c0307800e0078500140d9400304141440707c0305a5224004036170003280002035100362000d6840d103030161010707198403004481510b01c8c146050798003a14240180c508071b00c1203500015600348005000b885107002d010320a0711503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 784520017 1250 784518767 784518781
    0x70312050f06102a0b16050a050f0703121d070602011a090601090b030705040e0c070201170603030f07060f052206050727061206081c0c0507080601050102060a090b 72
    0x141c40361340301d050248a400b83c0d50070300022510200e245468410b184000051400400c1e80a050340400c0b106010000306209203204160490102c038104240f0110050b00c8225030329003100c20700d900310b81803140c0509040507200c0e40981d0000c518151002241542c600e030380c0340c8004900b00c1b0181c02015070799071003850200010b030601c6280b003a081601890891041e5855500100c601c2d40182c0e14203000510009080089511100425030045040c5400c0da10b007601d1900001c000385905005844054800c3d008a400340d6010400c0b1421282241841c9440e1015070074104020940c2c4201c0da0f10b4207040c507000504100d4240c000c45201d08521131410380d99000c2c2e841c1d01004000c0104504148100c0c081c0103900000c42c03e0000c0398aa444014400845043c228001c1c0410546000704c0446804c040040c0404000841d4800280e224141d072440c1e20040d00204030740c80d600040d000303445400f410798081140140450268107854080c0c00300c603802c1c1c55024913501101e180d0600038114001d0403000c9207075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 784521267 1250 784520017 784520027
    0x1e1a0f090a020d0e03070807020103061401050d1d010c02030405040b060304020d06090201052104030906181413060806070201060e060904030f0201110d09030e030a050c130f02070312050f0610 84
    0x1250424400050b0100b1300000c45441d60b4003100c1d064403400008a000f108660389401280094080da226103810103040100191031030003240d650b070030001d488440e91503411485400c24401401944001d00c4003000b102d6000c0d40320380c040d00415008030b0034102100418100301e02101d0107280c1c003406403181440d007038481c2c400078261404101d041010400c03410503119000d011201a215070081c0d000610705142c80d001d03003201010352180c41844582ca03002e042002c00c10b202042115003c41c0210801c416210004010180110440c01c1c82840e180d000f24a0060014070280b00d050260020440503031242400c100d06001150303a40c0d0300015000c00540000e01c12548048542d4040c000411341d1500c03030403205d450343c000601281c10240d5515980c0281035103e40407415081c015800b41c0b02452080c0c03549e988609240403128050385040c1c2d0100e0031503e4550000e0019522440b00f15107800c003034130780209643d401c282c111a0880c02c0802181d80031400301d41c802e0250b00010a2600c1c10001e0310000c1e50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 784522517 1250 784521267 784521277
    0x70b01081c11070306140f0912090f0a0b070615060c051002091c32060604050702030c101401051e040b010e1e1f021f1e1a0f090a02 58
    0x701800f88001c0000060a036005860100b00c0c180300c1c8164900c2c04281c09030341c0a070000d007911410b600841c41c6080c0d489002c0110f0b00749600030b45410060754031401c045201c8038250b500040f50340e500001d100080c030545074840340d040c4000302d1042104039070312081100e40b6a244000688690845110b041310680507900810701410060910200d00040c1036800310101403605090f00d046003d66481c11180544d4118024080d40e004c6400f2141c030600e2440031761b0b81400401090065507143c0222380c01600030026291814070100c210b541103048006480701038846107452031083c264172400820b581c81e1400c1d007540303203100c4241e034117140e41c2c030580400001d060207090b0300e8103103c44000003e43c2c5495002d0b00000401038101485001c40d50602404003d0051000c0c2c0019040d035154400d840603400f141d045440003808070b400d210800c820520701d00804070900c1c2070311648541e14203c6410706040d005469034100319040c2e400c68110780014031242c0428041a181d20040101c0010b07805031003940506 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 784523767 1250 784522517 784522547
    0x316030501230607140d02160803040e010b0315030d111504021e04060b0a0504031b0506070f1a041a0106020303100501110a02030f0303240603042015070b01081c 71
    0x90a03c0705c84500582800c01101007400182c04c0001407070001c2d07002c049080014003505000310300d0646013413500d45e242d80041c060214041030000200d0035003100c0c0c52a0b1a040e6800806907040c009071b00d000a06844d2000003065054060031080805c1c0500c481c4d0828420344d0003604541d95a400b8040c0101102d4441c030707095601c01c3e5100383c0801d0303500300300c009042003100c0754441c56941c9046007000c040d85c03800c0c00000b00340c50820314414003184d25030340c040e202c009070700500c4503141881e03070300d4500034a07400c3e5a420117070b0b006181d0810042c450b103020502d860b08100344a285150340c0750001241c032840201c40d00030845c03a00003401c00c03080d40300300b01507100104000142c0d1540138031030303000030305182061002075042e0340040300b03224003040070a5102c000b052690040041c21030310003001c100c00b408001e0001d4284000c40e601100704038883d100c41d18100000501600000402c01d0b540685600101d60680381d000c51980017003090803000446200b01c44103443d15114039180c0542c00c4413050b041003594 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 784525017 1250 784523767 784523783
    0x260105151e0a02150105191208161101030e010504030813050f0a05060106090803070308060105070303140109020a030b0609031914060106121a0a170102040b0316030501230607 77
    0x80c003940401d110140404407a80d5003c0c1c0990f03e0343d081c803003042d02010303003003c0e22800b282c2d04c1c12407210050342540c20868131340c08400c2c07060035001c0c00c15140354080e24440041c08d56040400100f0820110b00c0070060740000d80b420054520b150808a0890384d00300c40080c0030540704400300b114540880940301555200f072080340e40f164071819140341440303e00081110b681d84020300601801c2d4001c4d04800242204100440c2002c2c010388000304030160180290b0b0501800054100c00d25120360040980884400740d61641542c1d20001e500081d84803100c048006490002000164a0410100d5610640040040c4000300308004480c402d2141150100c2e2100c0884501880140b000d0090034001d007826180e407228501ca803820700c815213071016440e200c48594600e0400d100d644107600003041d0b50038054013811400030113039814024440c68206000e503260101c00c001c401304008030340c1946403150356024000e40c2d0b6a204c00f00d810014070700580d400d421640001510a0030700c00e02603d0014011800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 784526267 1250 784525017 784525057
    0x90114120c0c0f0a0501050f09060903041e080f0a03020c010504260115080106080d050c101d100614030607020703060525080f070807090b070203031926010515 70
    0x1400b881c1210012017101c030350751200c1c01c115460350f41c100450341c00154034014007610320303100320610340f64822405a01d40c200320185041c0f8850300f20502e07940180c1980310464401d4904d805581c0c3d81c61074000411001403255030b0481009510a20a560440307803074580300300861031012408035402d03010094a040c290343c0c90101c0007042519141c1603000306554400003d6903420911000d041c145200d2001c0140403007041240310b8501c00180c00511044200e000140744e164118010b04001e01664800245d40320348000710704a0401a4019400ca884221540c00c120b000c01080c540c4841c41202c1c501e0240c1c02440382040800c4498200b0756006c04e9020a001c1c7c3c54100701b11100d803080100700c000001a40a004111100c0260b49a4980045540c14207000314505201d004007a4412405100d407210004508802191410001c0d2000700c098031080341b040ca40f1150700144140b480e424040d04504c4113400c00e8000080004a02e4142da8014000744855082c031035040c0350719441584c00307591003004202 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 784527517 1250 784526267 784526293
    0x403060b0f04051006090506030c07030804150c031517191703040b06010f0e0a150306031a090d090b070308090c03060115020f0f1507050d020a05090114120c0c 70
    0x458140b05130030320034036141d1607410b004004054042580103140521801c201b81f0405859000a481e08203606191044403a640d9150240c072040c40a507002000505103809000c5440d010740017200014054020b043d9060350302c0d01d80b42800201c1c0a09003280703821842ca030014422084655100e124010021040c020780d810a0902c2c190b40704036030035160059007000788025981d1110b33802c2d0494119141c05a511074007400003e0301b030311342c0307101e9503c54020454003a2710890003a04403c000796000f034088001c240c08a580c10400600071501b0a03514001e14a500140b580124509000c0d50380c107003507180c103040c250380c0e080c0c0b1103407400f808404443c03040000b0000c060340e0821a16020340041d00a5071700754001400041e15040350b0340c90b1944281c101003d21514000c001620148008040e91400e1031602c80c0c8030240c0b810320480241050701800015481260381d04a0010a0281400c2c0da610040b02110f00d00417402d80101c116141c2c0c55a40200402c0f15400701901030101e03c90840c090742c07501d1030780007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 784528767 1250 784527517 784527521
    0xd11060c030a03050604061409070503060d080c0a0201021e03032d040c05270610180e04021807080a0e030d0f140a09020913110918070f0b0403060b0f04 67
    0x6940b900000e8480c01000303000c1c2401d000c1c0b24010281c1d008001c1c884403031000095019840240580c0130000044001451507490310064401240c101c0b41d100d50b100c03800b8180a860b01e0003280142d025102d03001040c2d00c02282c8101411042c08030710040d43c2540c45000c80c05912a000889964085c0025484440403260110354180928031603178107052214545801d2021840e07490011304048901c0140802110403050180c590000040b651981405c4d444d503025208490880c42100305000d03248004580c0c01100b0000038091130084481e1400d8054a480d0700c1c3c00b60b04111001000508030b034022826101d07460f0460307926200404156030070322008034141c208450904100d07030340441c5c81e458810900303c050288903410400d00d000502600c20940c0110b504420003038400f6201c0b440014843e001e003c0304820a5203000c0c0002c18006050400941a40360381c3c0400d401c24501d40035009000480c8507103041e180d4100d42420b80c00710300340380c40c40d1182c00040c601c0340c480e150003c940140c1c2c40030943e500c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 784530017 1250 784528767 784528777
    0xa0e07020d030e100501150212040b09040506061623030a0903080c1f02070320061f0e0a0203370e010e01061203020607030605010801150c170309011a0d11060c03 71
    0x4048400300c4203071440c1f00034684140e089580000800400050220305180001c031450490107540120347c544440f00464014403811861200201c0f80440711010440a020000450311081140160300380c505c20b0383c2600d905c0b03510300c03c1d004078070812030400008e18640c0160003281b501c130301a074145940400000768800b41006c403400c10203600190b8082095000103c2258900b004080050080d4059511660350000a07215002182c1d101c0740e0303c9205d0303038508106400303400300081105241c104910254081d4105a5001080c43d00038851800b01b07845000b01940e2850340703c00b08800c26645011020001d200e20b0760343d00034554880185900000007405801c0080c40310514150018005007402801c00001500030030400d030030301c5004c00c401d0317038001c1060381540c0010a5500b1031652611050b11009284000107082d08071300b030742c03036030340c0d0040c010185200f00e00040003031003001e1031200d03158070b0104810200c940c4408070610041c0411452a01c00c0200c80010717108910788549000614690303001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 784531267 1250 784530017 784530029
    0x9140106240201060b090904080714010c0e19050108090c030f071a04290702131508010b0112020a030902090c030115030c0507110f19050a0e07020d030e100501 70
    0x4601c0341d0000c11494440d2840c8504103500c000c0040c2414003100507074501c510083c02d8410000c4002080500000c4000c5645c080c0d4480b030030030109100540f0f480d0180030580180c802143c6240140c491034186210798200c03140c001410b4400139400c00b0015103e6034805403069070584500b202421107070310208041401100d00100904401c0e1511940841c4041e03d0900c0c054041000d02040100030001810b88443c5c001d01250340030a1500f038002440c1a000d444006540500140d9070b120f80e004850f0b000c480d00941c5440f07a034132440c1e01c0d10800c6098454200081d400541031005110280d981580980007140741840c000c01c1900e01500081d20f4800141c6401800c00b01c000300400125003420484401c03850107043c20301c41c401c40e0740c4014065016418001d08284030100c482081c0c6e54515000222980d802803a08404c0c001402004040007a0340c0912406052a01004606080428091071044040c4d5004201c941a84107046001d8800f0304a070491303504c1000003c2400c49614012140038200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 784532374 1107 784531267 784531289
    0x10305010b0a05031e16060806101e05070f0204020a08090d03110906030a0e010518010f09080405060711030607080f160816020325171c09140106 64
    0x10018210072284051007000811f000350007500c0c040c0a60029107402d901c220004c50f040d40d644500c142c003c0481c9050140d00e020b010311810040c031255100d02c0101a02c7c884030350226050f0b8000341c0340e03840800c00c01410094404010064041d001c01d0034034041c004c2d1005c0c040b0083d0a4400c04000e00d0040000000080d004a1141c2009040f0300901000304401e141c0f1341103065214141c41320f040259420005e0001c41100540a660142c0d504018921b10b00b51501e010001a03031b1014500311010058201803030003581d81444114424016a1a8441c041ca03140c01c04801940000745881580c0743c02c3c0802500341507011440c107070b1109130345134858620a440b910503440c501812000b5441410f10a440c0382541c440303c1401503107039204a40f413951080c504240310035903016500921060044800c08002e0580d52504403801c00d50180c4410f08010f04c0400c521800d581e0142c2280c0003280e = true := by decide +kernel

theorem cover : BRFrame.Cov 784352517 784532374 := by
  have h0 := BRFrame.cov_init 784352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 784352517 ≤ n) (h2 : n < 784532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
