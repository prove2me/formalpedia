-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:16:21.890641+00:00
-- url     : https://prove2.me/submissions/0ef53e65-0322-4ae7-b9fa-68d0586b6e9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94604316 ≤ n < 94784173 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94605566 1250 94604316 94604329
    0x902090604020712030e03091804230703170705010c081008210c010204050919050a1b030f0b030d0203031902160807020a0b040806061005090f1c0501021902010c050405 74
    0x90500170705584180c1c3c01c2505009200711900e6103001807822001d8941070100b100300703800c2514280c5a20038140030b00d0a80c0c101e0249081c0c000030aa8008004d418510b035100400c0610038080f09203002000d114074030024a0034014007907042c1403911491072a2820303110f2280302200c0782d444100164442c00031803c0355030b03102065207010507100780315540d20a2581c6159001e4802c9a1260b40c101010702d0800400d03a501c160341c5941c03603c01c0d802c01d10094031010b41d00426203000c5141551001000350040000900a0344600c118450302c44000c280342c00c00600090500e8501d160040160308000308001c001c0e070350a0703203800408212010450512300082c00100310711800800c02000b1000002d011415540d8150903440242608115175031360399140c4054031303112030007031b103d41e8090080480241c98080c018410307601c03020303009011044000012010844040c1920707181001700103070300111801040c400c1c0001c0c0014200f04140a003c0002403100900319422038280a04205040c03100303200580d100b6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94606816 1250 94605566 94605593
    0xa0501090b0705010905060f100915051c05060718050d0809120304121202011407080c0a0c050319090b070c0e0601110706030519090c03080f07060504030309020906040207 75
    0x7158041e220b40301441c18034014143c0c0f460150151088a007082851305444540500c6400d00070100c40e292540d403405482600c80300f080c40c000744103c803802441942002c421447c8180081e4211030070072090398540b20b0800009a84a0303001480d041c2c901d000013039072540394100402080d038007500b6400c0d0f03a41300e100c2d69004001c00284203201b941981c9249030001c00c240c0c2c014103120f001c00b48202e078441ca01880280c50205e00100954241201c94030a40700941c04d440c4102416162414145e5920030141003a0f44280d0000080c00001314102d03000c04e070104098011114000c00342400c9a5100340e01815180c515840000d200c0c800304000740002c0d0096108900311190a02c0981c0ba5072116001a07881c0380c1801c8009a1500c654100064080d61582105019452070f10b0341201500d2042e46000980d0003445000d011140b040a0401c00101840001d04c206400404801d00309400c40d9210300540c0e030261000e40c00a5115070481096183c4890000e070411011501145046080d5a505a8150a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94608066 1250 94606816 94606829
    0x301030602030408070c0b0901120b090a0c0203130f0801140c090418080c070303080604180206070f0b010f030b07030504050a0209060307051002250503030304170403080a050d0b0a050109 82
    0x702c0400d00704005003040d501011703880420b030100940c032044845016080a804140014100e083c03181c601c80c00761007240b000341c00281600c8140d94845180308003034804030b6043d504520040151141d9200e5040c1000050b01e645140300e1599490b000c5032509503851250180c040e2282c25083c8001c0d811040125590410306036004654003003010800c0b440c880050394040c0c0403a50006040c80b0040002c50050181d13442900c1d0400c403030310340350140421102401c00c01d506c000c0030003039540090b142074405864132134421205004039007440d6542400e07041742a032103c14401c1c4020014010401d1000245521480702e2404210518040e1036580da29610820301a0003400c04001154150f05c00307108980150101074420f40d860030490b10005d50312000300940368400d0228028100c8442c0e402020901202d100400a50860300d03691112030001030074140411440e0801c1000000065845015103a0119030380c942603100c100f00c00fa00021765136401022403081c041d00c202408160f820013103c01c02c0d03a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94609316 1250 94608066 94608071
    0x70815040f021f0f02011401060504090e0309040e0a06060602010903140c0a061b08060901360f2306060d09060b0603042d03020c010f020c0d05010506041503050303010306 75
    0x420380085514000306140d400404400d0040b110f21103608050002c040340d1041c2c1c02008003803c0da401c1003440601c01e010701800110100420001d40c10290030210041421034280e030b00d0b180c102d40c00107044402c00300848206030000803020301401403030322a10317000b451540001c2c020442140c1e8020450407802c0c0850005100104014505100402030074080d20b6100e04208884440c00d048661050351350084400000c02c3e0030f00141d054180880344904031030841440f0988520300141c2074411078002076000009180500e00720340907682c80d02030701101d01d00d0020001155441010300600c1c0240c1e03500d1071500c3c4c2d41d0380c000703101e441d032100c4040f600c2000c40b0300800580c0450310f1401c02c02801301c40341e009070300c00b0b40031052000f40150303101c00350f42a001e403004c00c01c440108043c503000b503c0c00d4001c014015811940f074966440d4000c01006007100440c0c410360341903008600010b0f60a0311650011b980c0c03a9520001c00c002e508140c4140405011007402000c0d4072031540e0303600c40d030b02c3c841404003d00c01d81c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94610566 1250 94609316 94609343
    0x7050a02010b030105070519140307200604030903170711090907050414010510020622110924180103060c0e030f010506030118020f010c0c0803040603060807081504 72
    0x24800c1d40b140c425100024000c0c8554285030300000c181d0340040c0310b08806070b03170a40050342000e8040c0b282c060182c03000301c0c18581107503214241510044410b0700e0781840052203171080301c030814080c80305a10461083c2c0317400c9070341411414005041540c88044960100c1f04025100c04910a1405003009040c100d6107a452559040f00c143d0419032107600ca150000d0400544c0a082c11080348064180d40e4292442803020004500482c0d49210594581c14540101c9149034800c000b075a081c610000d00911400022103509004139071000c0381240c0d080c3c2090200d00c0100014521603900b04060f0404585940b0509000e030016006010103100080c211555180c5082903a8041c1170a4051244000c00340c80f1408141860940038003011100c07580700703518292000e5800400410035491554000c1d1060221080c080c0041d80c0c44502c040c41941c1010044000140e0b80b9010801000503014998001c00d1075490010204e00c1c04031513800502e2950807a5069840740d0704418032066005030820344505451 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94611816 1250 94610566 94610587
    0xd0209100b040b180108040812060604030f06090203010e2410030503040303020312010e150103020a03140a241a130e07030518060405071205010b030d09060207090509060705 76
    0x4040d903110100914011a000984140290141c0003a480120840c50619040310044407800350480d8000c0c808802402218039100e0416030559005002802ca245425125129a803a00c00b0154084071480d486600070b004504003805503003a5500c08030014225044c00c0c95102010291210403107004400c1100020b40800301000600300940e001000e4070f580316141d040017900d9510030000c1a08181580c400042c100344082c800d64451203072640c001031810007107001107002c0c2d841480c4d000c08054650042c007040c0071482103403038018000c081000821620312211441100040c110351031410340011400c006148500600c450302151803464203a642c4800180a02d0b1030782c00380c0201c140d086005003000903554050380302c1c2d8000c6084016000101e200301c0740050382d4440484004000d0b40001c0c20070400f40c0c0000d00702e029142e200700008241d0800d07040c0441d2416141180f00340014249442c100301c801d405002500203000201e10a004900e02420305960740d074009000202000b20000d80038044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94613066 1250 94611816 94611841
    0x90d020301061a0406140c100908130e090d050909060f0612010801021e090a030303020d110d0207020f0901080a240c0206160309020f0d0804080d0f030510050d0209 72
    0x180c0b01c007943c105100d9405004000c2c10f60082c0c01307180f000c100b00d5150340440075814416070780b408000c04001d140082150141101800801c20215203a8000740510311049400c00b01c048064a00014046110301c0e0000040380703010028011903051240410494910f0344800e50104d610240984001d9044015400400c5140c41442d840040c000580000802d0118040d00107107090745501601044954002051040d00d210b0200c006900505404080000a0084e000703070000171201345001031212a0002c8203c22580300540d810000348e070009480d8110328220b40206a5414140c85080507503041100650380d6034081c0c1c40140851511140c030120005075942e502c8407040921a007444000e00945000e959030030705568080c400c030105160744164034030910543e490070743c0051444040212450078080d03103440301401030312010740800003c43c0d5400c040044643d104041d99030340c5070044035040018202d82001c0d1038422040c0c0c41c0c4004100a5641c00c0c2585007031a0111400803150300c41c541d00391203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94614316 1250 94613066 94613069
    0x9020a080303090f07171e01021303080d060b1e070f020604090c0e1014070515040b0414012a090503011d0f160b0d0906090f050f0105040206090d02030106 68
    0x2080c1c0300001c20400e403c80c000c0341302c1d91425481401c440d11162120482c0041e490210150340751a4440c6002002d008024105820b8869100000600e02114841078421182c43c1e504107484904000651449150032071150f18000e103204040c07281440484c18812518580090f1321a030700e0030021881d0414000f070924400100e5038002c0c1a02d80d1543d5500399103021344034094609010582c08940401c481c104501104101800c642e140c0d1017003040408a05120781003a1030070f0300c4034894641580c106c1c522282d4414000d030301072040b2660524091520301d020820340080300d00742e81d0501c2c0c800c0c08030408031895000414041403400e101c0d0380507824211411410303903202e55031640c20035031003110242c00481c44174910802d20094480c580560022247e44004000d40c00e9100005490104034140e0b403440074000420b00901c001c1000140b5848520640b0400d01b001d443c0c409566080e036080080801490080781c070780341c0080c482032030680c00051940c01619000c9000c0c8008426400441d9002c1d8400c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94615566 1250 94614316 94614329
    0x10b1207090b0d06080f06360106030516080d050708030a0216060527060c030405030403060c0f0e090708060909010f06080a030e0108010e0a0c11031b06070e0109030609020a 76
    0x281c503000c6001c40e0701c0c007a21551103100d00f40d02810038401c81c0c03068045400d40c030858068440400c3d03013030340369680700080c00140c0c02a08c14000b405161121024280140390007103005030001c21130302d10341105142096a0590100d06c0e240d002d074a01c2040540c01038165500e090700425160307100d40d112076810010748103c804d41d108400343e9000c1d00c42080002e40c8068050011000d07980d12000c1030010101d4820300b444800711507039101038000b070074656600c0d00565019204406480c1016a25030b201000d40d0000900c000c0480e0051030310075200c80e03000082c542511421110b410b01400c003504060501000500300c180189100c0000a500b8007094104e4000045ca81e0310400075030f41d035405003d0301c90030b031300130102d0005803503184101496200781409030503940701443c206a551600d00f13041006000515040d401d1041c80d440060b941c01c1c003400500008440c0b50511900f0868001e0380c0f500b0000f000b0107040500c5405032030f20f103407a68080301d0501030325480340d800501c141c403a00000e51000403651040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94616816 1250 94615566 94615589
    0x60712020918070e0402040302150a0e0d0605160504060f081f03060218040207050304230a0e041401020c0d03020f30070e100f090302100c05070e010b120709 69
    0x180c1e0040b85000702c42d03200d00b565980e490f545004240c1001300340d1007640310181d4080700b441c2c6400721102d2030000078044007196091500304030603250085003500c5440c1c203050b03490990791b00c1004469aa5803018011104c01031810915240c1000c034040c00e80e911481c90a401c000c2c11f130002924841d50b00008901103840e4103140345025959180c0780010303600c81c54117000d01d00c141c9000041a400d003070003940c0c0d07030703540c0302c8050f40c2041d040c00d442c2080b000980b41e04644e90481000000706944854600c00058161820081d81a190500344180c401c0194581301e82d4aa10410000058a90205205401d00c81034035004d0394a40140c105900e1030f0060710002801710742c120700d01d0303454040c005151a907807010f03940c200300c41540c0d120300560704201c20f034041c0e40e00030030040d0445800511418811300003004a0400c0c04062340c8980100e0703044803000403c11b010421800120013030000c01c0148100804060341c15a165604000000103070b4020f2821540d1401ca81901041005024200e020058980c4c135200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94618066 1250 94616816 94616839
    0x902070f0f240e010605060405010206041b0506070f02030609061b0c0304030b010906030201021002030702060109091a091b030604080a0302070305120a090303050708100b09060405030f010b03010e07080607120209 93
    0x6050080030501600f81c60342d0300c0c0007800646410030005880407518160017900b401c1c3e66685130201508101c40710720708d5140403403101046913500c600141c10140e0250034114035041c10742c4103251400d10040d106460b140d10203001c20141c40581908941c0600185464586440c0390b2a00390745140a150002040b2969880020410300b1403a842a800c9a000740e00701e0b4502c0c42e030f0081d00c8080b41300c155034010060b00000014000d503851030300100d02d29881110445101c050300703814410200401d0700e01800c2034100004907081c88601281500c020f800031805400346040179a00c91403180b103001c0c0350000b81500401c00005043c09541900c0301c112280942d000c0d03602e001c2c05150010701a08004801082c54040800c051612460740540701e14075400200c010f05e41880704500c502d8210b0404168041002c00012855032800d00005889032914070010490000300d401301401d440103000d02e00303060303408040108170080700048c84c03607044449801c2c1031201e90030022482000c2e2082000054210040e601c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94619316 1250 94618066 94618133
    0x609030601030b0907050d0302030d0c35151804141203090105181009021c060204080d020102090105031812070b04050114070c110607170703090902070f0f 68
    0x2c405124900100c1501e5401b0303100c0c0d08000402c0350906020740103910900095005034000e03400355402d0405070a10804190001c00103c112416845205012400300c907290301d03030400d04801c01c5401c07020401c081c40180388988041200c0c0d540190032006250103c40c00b00741840541c80003036101186860540d04082a0b00e6502d041c1d651081e10440025864100090720015007405046456010384d006808166100f02210700a041c0d214020b0781e200d9408070180300802c085020800d0058810380025855a20784000c0d2810300750242196402d41e4010403044800381c2c0e02c001100d50040e200081007400150886a2519020340a00406008040024500d0038080c040149038842c1d841130b0001d0140c2c00002010a07242c000549031030000c5500d031150100014042c8020707220410004c2c203042d0901b855512060303803a0613655400301c00680005044810705500c1440c00b4060496008150f14124450f6600e906a0015035009000351079950880002c0201502010050001c1100302481d04002c2c0c92 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94620566 1250 94619316 94619333
    0x2180d0b011707120201080414060106030b010e0d0c030f06090807080304020f01170106050f130f05100302120f0402030312070816020c0303070303271109180d0509060903060103 78
    0x520340e840480c284500b0a120700009041c2c098038409014080300c804a5401510b0968000d4022254100800c0c10122040c1082002c1c50007402c00360340120f40076188000240c0f0b0200e03818040c5000c0c144022252011a140c03c840500b2a603000820111200c0c003814450024801040000c0c54a440040c1c65800d1000540c090743c0a00d000300d0342080710144540064a501d28411003001040c03e00e1001000100d000d6006400030079180c0054074030382401317610b0707599503000f458100000c05030000200741300f14184140500700c3d48059040031464600c40328004101075000510b242e401c4080440045c0031924107200391088030703008040f000003a00303043c0e81c090900c0341d0844000d5540e8008440310501e144c400612400d21305006005035203400001d45007200900003411418818202201c1092411000c0c25100c101660244070380e101501d0700103042060540b000740a5042461001000301c001d02400b1851000c40307000d07400c1641c2d80b43c801c0710115010b8000c2032080d035414025080000288500748 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94621816 1250 94620566 94620569
    0x11040302010e03030903120f070c0b0a020114010b04090911030109061b02030708071e0203030d0e0d05270a0512060a0b01051201060c05160914070203090f0402180d0b01 74
    0xd803507404090303082d4024150b070f901402c05c3da164142d00400c0c40740200390b42c040c010f01c1ca02c2d00840801c3e241005030344550b405d1003505e5014605605000a160503001e0b820b00c56a05104148003181c425545410101260760080380140e8100560311691030040050406031070000c208041c0c02401070030a6803d00d6801404044080c01d036a2000846039a1058030102c11031f001141e10240305801c0c070501d41c903100046014039030f5007200700c1601002017003da54100f000d0905200041c501107020854a80c0d1281420700c0c42c1c01050070310030107100905050558001803c08490184080c041c0c02c03070000001103080385241d00503a00300302d24580540c2141004186248921940d05081c4481c4121500455040c840c200880c104126072100602202c0e100f00800038141d070050341100c0c240c1e001e000581b00c424210781d001e41001c503615050310308800181210107a028150b070002d1070804041c1f0001c86d00e4000c0002c1003030f06c1546e00040c8031001d41c003641124456548040d001c1e001d010018540740a960794207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94623066 1250 94621816 94621819
    0xc0301110408150601050d2a0e100302030405010908070516050d020a0303030e160b04050123090907030603060c12140103081c0e12041e03020a0504050a09060c0207050a0608090d11030d11040302 85
    0x69607281800300e805a2010112700a002e801014001d0403e00110000d400103403086905540742c015070004588094003400f070712401940902125246903011903000ca007207501041c080d500324840300c0b015030740d40421202140c1d05800d010030100d820789039841c2031403030010312581c0e5801c80c2000807408001c00e0003d00240c1c0c1d070a032140701d07401c4403241e544070090540030343c030703410584082104603d00d040c1010401e81200507030a02250700c548030343c0c641060710302074941d050010384407551040203410380e0b004803203011b80c400c500c0418070350440c1c44545880c0300e80b4000304036004000910000c4400b084d400005005141019181000801841150b55910600c03030032100007144131400c40c0c043c614a00c0c00c2d00b10395000b410a0720351850003040c8400381900800080f86155140ea482012030414040d5408a02040d8040c0c83d001c0c0c03d00c0d0070407200c102c841d000031081100a8040103081d40e40003580150b02800d42c180814400389602460b03140d44103462101c02c0302401d01680c1c4005c550341d0700284c800d80f0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94624316 1250 94623066 94623131
    0x210c110111030c1813050106031506050304020f120a020a0305060718210201120e06040605160507062c15060d0b07180b0c0c0301110408150601050d 65
    0x2080c1c480018001600e54404500d410001100c1240940ca095a2080c2000d00f82000c00f000340e80302041181d90903840000400c0d122a04801509803c100c0c0001400c05070900d24114100383c0c0200d5249010b0781c1006000e01690500b40403031b090708200c0c5c9010b0503401850403e02985a2520719120941564802d011451518000e8280781c2e074400a2000d4070b41642c1d81c1c1c400c0b17072403400d400301c204003251074140d06010a400d0700d61108802802800d610b0107081e80100b0b400c2c00c0618084003100c6004014008001440c0030300b405440d8010708881c05a07400101c080741010101e80c2ca15101c032402c00e09200038064529940d113070a8004103005060300e80c40743c14104240d07181da00303008840284950091400d0a0040088e01407402010b803403007040158481c05040342c0e00c07194014510303406030503280c0c0d403030f40200c00c1800c05290034003656401a07030346541c05040500c1d095606540d08000680540784040400029465074482c40986a081e000b050003440083c03a2000405c0c5151343d0320740218040031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94625566 1250 94624316 94624331
    0x40b0a1d030106180b030604080f07030302090915010801060201180f080c0312100e04030c062d060305060a06030203060c07061407030902100f12020a020c190f0e090a0201210c1101 79
    0x6d00480c20602c2250001e091514011150b1024003140e4004101242455404e0102c510a61941609180300d11036410001d00c03940c900c10000740c101e620580c0a1006c582c100711440701d0081d100310b8040413403580081c400101c2001441c1c103404500844603c2c81c43d070302c4042610140c038a80c001d201c0d4042d02031704001c0c1415075241c0d0010f0700312010403034018003c01c5407a00c0f0300f40018a154440e01060781180e4103440c0303d00d60f8510b20082a54680507100a05484234001d20034081e05204450304664034507010081c1390702c0c1d0790100c6d4540c0c034000c10009100d5004144101841429000551959402c110640301458141c5000d00105a200c10580c002c0c000da141c2c1003040c5018040c84410381c00c05884200030b81060111743c60180d4054240311085001e01440452281c88150b0740341d004691a0915019103400c2c1194101c0070701507503000018104845041c0b103e05c0f480403860b5440d513902840d0080d02140a40c001e030388502d002c80d414040749485e0401c03030b400c10b9a11000e80f009071240d2000900045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94626816 1250 94625566 94625569
    0x10031b0203160201050d2c1b030a020d05070b120406050c0a02060f0c07050105040b09010c14090609010c020d12020606060405031903030603051c020111040b0a1d030106180b 76
    0xb8003400142c0744a100ca40b000c010050340c012000707000b20b102d035803401143c00c0d032002e82c8200e5015042000940101130305442407413045414451648900c001401d8003420340300e0303100080e58584103c1e40c082e0180b80040c0c2000180b020a0081754050580e8070f40003030352647c2d4405c030b10100140c210f80a445040c6003a0100f03a281801c00c00f1140c046a056005081640740c5a01011400d4000360181c080304400704100d80001c2d03800c3c0100d600c9940503111060300c034504035401e503094800282204007000305041150311601e441106861101109070f0382e00352105807100040c1c40d00c0450220182d0300400307020010007000f64042025038100303266401e0315601d44548040c00102d0140307000b2680d060b000402d60843d09541680700c2d148060091401290007036580d184c0600b0240300c400f2551114408150445d44d458090003016252a00d900750f0920b4140341148d1004640038041d00e086c04c102c94015103000e4000c40e000c0c00103007040c004008120280c3d0322040420380c580750012240c84a410300c00c40310983d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94628066 1250 94626816 94626823
    0x20c010314040807060c09050d06090c05060304020a09020306061308010f064b032003060c0912010e01110912030304050c010f02030c0601030c08010e0c01020304050d020301090210031b02 82
    0x320f6200500300c1c203022407640c690014007407101c0442c1c1003007500040018245e540324506082c16000b410b00151580d8141001000300003a070b0080c030700031075042080c0801610342030030500807185154401070720381d03e6140009489100324400d003031a00e0802200414103080650105801e00403018041000fa540da00303442c24500302d42c43c080d016440300070a080c260700c0c0140b1241d01c00e8002418205080031509280d00711000d5050300260f41c800301c00b000404030032409044014082000700c0081c441d0381b07040004000d80e0b1003500140da01540d003802c180d0060040941107028030860340802844a0320f11050540b920f90808007103207105c2c0d06502a20340c0c8000011040300d004903002800342c04880c92071070054880304c2246071074100b103100c200030241e0703000001d111450186202c2c041201c60315103040344c041c0c207403000c450a80385203400804181816a80000444089a5041c2c50381c805034416400080d00508404102a40101c0c46101e2280041d625030720200025025030269022480700d035104070ba8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94629316 1250 94628066 94628071
    0xc030b0a0b0f090901080303040302060a05060f0d020303070606032109050307060e12010608060a050c030601080103031107030b090307020a17100b04020f0c0c01020615131a060a020c010314 83
    0x4100c00940d00920400120500402c01c0540c003008841c50070b0302c0382c0d0208040c103809174030075403c1d5040030050008066041c40404d421102c11001402142454000540d41c0180b10b80c0c4184501c00d10851041152414420744501d190000800c02002c1c3d582e090607008118003040c03480710030340c244140032075090254a000081e40c0001c0c0003407020906080c4282d0b031181c41080441e0744800315403860840d6000900508010784500e001400e03981c24458103010554001822200d061002030042201c1c50340d1002401e41182c0c3c00d4506040b0340e90121b2141303401c08440ba04080e03c420b40200800940640c0000104415403080c1e583c2d00c940d80d41c510207134151030582411802c1c0c0f90400108401007806a0b004070750340c0d0500078001854243c0318007242c1050340c4035640740a010b42009441d40119038040c481d070b65003c0303070100781b051040028a000030034100c0d01007e01d0450b165a09103c004049295081100780c041c084c1c513480d83d80d50a0b8030080d503111a0107681a002a04010b241070711000171199650 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94630566 1250 94629316 94629319
    0x3030a08150a050607030e01120902030a11060f071b0603090b0a0b060d0c02060a050c0a1710030c03140105011d071d03010501060c050c0402070b130c0b0403060f0c030b 74
    0x24a600c4807110380307604100c0400d409030b2110300b50001265681d100402425034920a0700d0b52452812564005001800d4024600d6035041c0792048000140c0c50100300312a040e5480460415543c607d40300142540c003403100d44492801d40403401d88100040c101445004001500b5101001c6030f8804003101540d22007040141480110000b04000c045039800c5400100d00007440c00d4100a20700c001c8001311400c0350b1f86d04d40164400014400c900e949441041d4020006a0b00680b4000b501d403809428052954101c65903a07044c807000030b4400403c0441c1402940c0c2c030500f4014003696a05140503401074090f410862540303400c00009102031040b40301c40f0741070201981021156280807080e280c40b400040b5444010380d15079859001a0b0b007e101c0d0034003030103154507208442d03e11030401901d403220032000140200e10401650003c8bc4a40441c0c1c0c0e44150b03221800081b00001d441d1031000202183c1c010258008007080c080108410740c2c100ca1118400b10714100110702c1c000758100c081d11031103429107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94631816 1250 94630566 94630577
    0x13091104170c034801210c03020301030b0a050106020705060702190905100b07020d0b06120303010e04031e08010b030903040503030403060e240a1e050403110c03030a 73
    0x4000034003000d0500840d1520100903140b05121142c0400c2c2400301d10040002c110783c01e030302c4240803045072646504003a0640d0002910441d185001500c8640044c1411410302080341506201042e2081d0040c08084c0000418480340c41c259001402940083c0000c5420701100c1c2e000032288000e622500c1d049641660060081524000c01e018541c0e0001074203913000800038500c0320000400041c160000d000d002c000168a150502110f900450190404680c9400400c040c1d800350740c1c0c090304144507030303000072420640b40c8401c0001031321a0798003d243e078028040400001104c420000887e4401c1b4000d854010902c070385281c2d04044c3e205a1108200420150401071220540843c05180d100381c4d903d0450b4a45038450001034039641141d8011261203840b10b024500041042c40105c90b051065403510b000c268080302645181c04008200354905a5030b00e84001c15010460029010011000c1e0100128102818020100072040003202e20920610350200d07090304001080742e40441d5642e450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94633066 1250 94631816 94631819
    0xc09050a111201051509061603020c01020f070e0901020c06010e1905040b1b0d14060a060513090b03071a0c01050c0405060702010c1a0c070b0c0f0d020d060e0c13091104 74
    0x80007031000034002c40200c0d44005000046c46500c920300101104546074405200c5003074640b500078941480b486210f411500050610f503000c0600141d000e042d112031000601059807400002802405054160792152290200000740c661252003980c0c010a81200c1c0401c0c0e00070170803110780c00d950742075800a1004902c440020785518800096400c0401c0b510300f05445c1025101c846416100e520741d058903c00000024802d840c0307840c6801d0002800e85050072403d003202c5c5030201c00b51604034800d0795010341d2a0030201c0010f0b03401340b1110003d004c00c0c11100141301e64000d201c00c1c0940000c41c002116600c0c1c40e0125000300c0f525415101200c0d0018400c51500c0d155038011034ac10490070f03600b02c0b00803069503500d00403c0d0100703481900c41c661081c201e54850160303082202103888080c188070040c0d030f410420180300303c105104a400c00c82d91a080940ea1700008445100102000c0d8494403180c44a803051241d507041c0f450003094002c0c504410981d4507500d500460007196000b49000240000c100310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94634316 1250 94633066 94633069
    0x10918020d1b0807051c020102070e040f0c0f05030f010b03062a03010306020a021005010501140f09030f030408120f04052103070303050106170405060c0d090c09050a11120105 77
    0x1400303401c500c90402d5800110000c0b020350b41d01c20468000803100c0c0c1020340d080c45242480d81c004590710301e650000503815005500040d44a40380d0340101c049420780e500014007030215090000c0c07070341584404100b080039a01d540d100524140b50091911900491a0104c001d400500604002d244002d01070305058840d1441c41c074416a0001d54a1641c4c480c44a546d00d50b01c40308800f13940214080d01c000f6a9940300c2030002400d00203020201d201b071a10748001401566402003000b81010302d0390800030f540b4890300d03803040564020a9030f460b909d48941c0d242d040741c2c9200072003d8800c07180404229404080d50045a0102d40148203600a8800080c0801c10817854150045124895407030343c4800e000754490b00032410f540c00340e003040d400b00c1d4480004010f09544140d8849401c1480140c3d00c502c2e042550390952120b074050502c101100c8081506c440e014495842401001d5200400340b0ba01da50301c041d0a80584012140043c003280b07840080d0706041c0c2100219143c0108840e80f6400b16820b000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94635566 1250 94634316 94634329
    0x11a06031003080c01150f0b07030e010302090d0c0504060602010b1e0f0a12020f0d0f030309031e030e07050d050d030203070e0405150a090216020f030a1b060801091802 74
    0x104401c0307444000440000110750888000c00d451a03000c4008596609084402c4024558590212140e030403209010400801d251084d200c5940d4145880c01da0803040342c004078040c0c06a9030460394440007025a000401c00148900b208560082d42d0622480d0351781c075005d03804c03540514216030300311429202c2c043c1e900900c10003410156400900e189031664403040410702c9a8042d030446d0b40d0884031507403003805514041d10881040b00d000c43d00380e0781e6403610340c0d50320b503000c03103040d100a05042e2550300c6c810400d400ba07000c000400c0e030030b1014145003980200b00140644400e0001d106035014007000801e05040c040810141c141d0031100a080f0864000c5c000c500942c00213014008100e0f0f058080308103541c407400354600602903020500b0368000203c0030000781407620f41c458800315104200032423070000240e20070748003150102d0351601110b0035800071a04083c1d1084000b07040710380c0da0047c14001d841d0081800161016969028800d0f03807101684000c40d18044007030b030b140720000c3c660580103181a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94636816 1250 94635566 94635571
    0x607030c2109050d1d030c010c150b0402030c090a090c090e04080f0a0903110409031e0210050408040e070509010210020f1c0e0c010315090504030507120c14011a0603 73
    0xc80000b4294640352a401d041c0183ca20300703000040c682041c5009030700614003012608041c201c016118103031004002800460030214001c01c070130b03c0c4400d00c0c041041da42e4000f5400f840060025907032458180008007960303220355802c500c5860641800300701102c0901c50304001c0307556134503440c2c04541403e03a00044507600070703c2264103e80401c5401c442d02d03440c1000d840305500750b4903141861415407614065000f10100b40b41c0c001c40c80c2c401010003095110400b2400c049035101c1c2e0156842e200c19040b4100140f07200000c6106013014184010020000c000701f007240e004081c8440c85403102c1000302c945200303a0102900680c800320740314055511690041100c07000b1a503a84c1d2900103400120364014042a81c1c00d480c4542d1070300710b6004840244180101c2c01000d190070032201200488250041c209030203003240d07071a41d803000101014020340480e81d41507048030603080e400300b207280300a190270b250030380484101d802c594006040e19014000d440180e10580d0302c860104c0c0354041031001c00d4000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94638066 1250 94636816 94636877
    0x6060403060e0303010510030c0c02060a090905131e0510270303050405010501090e1b01090b180f040e0c01030504110d050c0a0f051c02040b1503090607030c 69
    0x10480000020301c1481003824015082000d5603c0c0c0d0f14060410001401c4000c10030185800c180d0501c070580d40c02150001000da040702e030b00c1d44841400c04101d51203c1c40d03801400b0041e2070042402400c0d07003411244150148100d6040d105c4d41c0001c1c8110200100e49000102950b203c4000708010941c80c2d04885102c40c181b4035112103036403900180f650301607000d035400e0340841c1c2d942080c002444404e000d442c0c0900300c502810301c200e000c0751800c0756566104200507481c0440b12f040380c2c500c60380b0035a0280d0040071f03150320031512805100b0b0050004241c40d480944100364081e540000d03428107000d030703c60702d202a0025219003144403006401501000b881110034500c0044506015618104014a080c1c000c43c010004090700c0ca00340151101035411101c440088070703908000c03507525a01b070000110030048214040c0306903440810042c1c000041c240c0e42c003444260301940480751b0440910702c200190000c5a4507521002002e4044501440003e400500520b10410403100d010b10310f107001500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94639316 1250 94638066 94638079
    0x70b1305030d020703031a0102060108030f13090912021b06040b0c0a021914060c03030c0c10020712021006050604090b150a08060102061015030905030c01110a090801021602060306 79
    0x940b1030204d0340940c404902096440b480140701064040c0d03a6041e5002c00e000900d115410460030a03074a004414078805202c80005003d29080080100c00d0000d00f070001040c45441001d284c15010400109481ca0052240035180301f20159261619450341002420710351902d424280550825400841001244e100c2d064600c00141c0380c101c03580d07444c0844020400461030401500404048201c10003a118080034451410050703408022203030400941c481c81c0b86c3e200d54001c002d0f4200382041602880341d51006c100f0109106885010501c8400310b82e09582c04061404070307080c101d40c80f5005254101d1000d0106102d0860a503000e164585802040b9284403491200001210b9114a10040008030f4203c1401041e5804100058012455601d845241420b107000036128040e151240c030200354540602000780402841151030f003203503074002845540175800903e01d00e513001c01020400140d0050001900740018800c0d03c00d03c054010034040300c661580c003048450740007d05102c1d880517 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 94640566 1250 94639316 94639327
    0xc0702060a020c18090f01020309060f06030a05100c0906020105070c0204110913020d0c020d021903110609060709140d0f060b03100f0f091110031112090c06070b130503 74
    0x40c1e50f6a141c008400c1c0fa040b880000d444e04411305810110410f01b412071982c018018821800d10103d0300c141d001040ea400001d040c0e40e900c001030701d003c400c000c0103029401861441e48811109400540c1485540d03101c0b4003105a94100882c02c80d04216400d80000d51180e0404005140540100125a404000703450a002c414030020320002207800e021051242d0014000200c24030f140101001d13414580050504440d14440180d150829001e003080c1c0c20b8040c0c0c04a1080600541c960694180070740d0840701e992070300d002a00d95401c026194030003c103000103000511500b41c519507941a9001404c0c00b440e11815039541c0e01c00d481c1010741102e080e61035082c04403454404005a18042c0880100450001048800c140c220303807130584115410b50501d40301c00089440400030f0400202c040e580081000303c0d800b8228010f2010861041e6007000014a01d80040001c0c20024020300d804d505a40c03c001e94807040245d58825100700910300c8081d07000003400f031090b152000c04428040c50544e0b10f0403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 94641816 1250 94640566 94640569
    0x405060604050403030222050a090603030512060109090e030921070303200a0f1e08040302240a090501090902210a090501060b0a0e0a03020108010b0c030d05070c120302030c0702060a020c 82
    0x4000c51f000c0908001c0d8603100b0440e51500c109a00700906546e4020080702e0304645004005200e080301c5001c090943c00d020691591048016070001d040403002000f4251401106649960182003c10300c03800da40c03410040318042c817110090b40c10b0101750041080e50300d5a901581d00040302640e41c0c2480788880d407d04452042400b00c22a024030404003043c1040d01894104696424800b001c6038645c029904000020284002c4a0550703804454006a0361480030f0309012000c00c0f41c40f2000c00000c04141d200e40f1907000a408c1041d500f0907220345c3d4085444031080001c900525054081030218000108042c0e5800311541e90040d19100300454101c5440e1142c901f920800d500c02441e0300c000107941c59581d98003100350410403600302c44c460025465038000030000901070140c09091a00041e60101c0d070032080040703510f004501c484c148186c2c074100b100502050007021003960080030286411903101e03c41e2080700e11034030440344880d040056940900034250415013806055104503880c49105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 94643066 1250 94641816 94641847
    0x10080c04240603060812031302040f1d210306030703030c030c050601151218030509040e0a050d02060705070c140d050610060e0105041208030c130602060609070804050606040504030302 81
    0xb800c00c9840c0400c00340c1c9001d800a151103140412500c01c2103080c8140160f25821a804142c0700b81c048030003094696480c5140802042c1144070104105c42a1302e442d040c522020038121403220042c0c22035515100f042c1501b1a5512040790340c160b054001e5401800041e000394012402607010780b400280420b480d99450385084002c1c2c00400a168001ca112581c0c80d62100a658130003961440600c0845e001346585185603000890003014044003048100c1c260301c03207900200d80003407004c0490301d12824509005403540032502400d40140900310011740704a02603011945140e910040c0307800704a183c2448441001a48461140d01081000c007523004104204985030040c42d821403008256854000041c2c0710b04800f9080d00d05010b000d1004021030511101d0340c09992b50000220744d40d0350344e0720601083c240b0802000c2c40c000300400e00e002c10500d0340010402d208040680300d03d89940c85824080d69400e10480d001805903000c0c1001842c1d508091308095002482403c0c0035041c81140e0241240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 94644316 1250 94643066 94643069
    0xd0b180d09080d210506131a150405030319020a08030106020606091027020706020c060403110c06090103020a09051c020a09060b0a05070c030b0a0501090510080c0424 73
    0x10340d00700320a00c00c00c07205100c0000003286a08000f00c401c0c100c01036800c0402d000a207500300d2030707075208006012031301e80512207414510080020029030034041d84001c803040b0200504c5018451845198908a4000046a0a03100c005000711300701107610b0701282c0502003803001034045024039415040001d41800195002e031840f5000350035145481d8003403045280004242c6000742d82080010040110b0682812945c500640169100c002c0908402000b0303201c5c15030002d180c0d62000070222181440420076900983c0300341d45600340c8001c42e840c8140c2d25402403036440d0380078a04000d903140a40c000d0b801042c0500e03007828035542c540d64a0000032180d0070f400011449048081e031181085240107802000941071440040007a103082c01030821542c00740e00c03c054140200024000c09208940c504c501c000d40d80825003d80c2c520b41040c1e0f85004d0842031251003003003805e02c0c020442d400c4140307050300b00381d07840000100350b43c2c03a41a0401001d8500003000d8402c2600d4400800c80c0000041281d50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 94645566 1250 94644316 94644343
    0x1c0c05060d06030204180309060e0105090a030c210c05060315180601020f010e060105190801060906051c020117060607060f09020307050a030804031205040905040f020111010b0d0b18 80
    0x602c90303c0d5005010a0700c1d8000748030503168491708042000a600180300c441a285145406030040d03800c41c0c01070361305200d45040300e6884425000008200301003079550700140c45d0748401c0c605030b440b0310842408215503eaa4001e04000c1c45a8081c0481e00303111018562000301034900d0222101c1500200e580c1b9200c2207010b1504800a4003007148a50301040a40b4684441900800840c11910212a00c2e06018040d0500c47e11216030700003c01c1c10501c2c124405044a1300c020014141c1c0c8a5280e0010502485014060500c0c4809800591031080c0000d15207078060f16001c6207090b4100d41000909402440c0550050f41805040302080140c40b40d181e8084075018001040c0d211801018542043c4c0c1c0e00c981d114480c80002031000035183c4082e43c040300e81c4104050308001802a09444500481d0021625103180c0400c0109000ba03010541c11064002e885000810249404c51400c0c1d40300b410700d03240c003c1c0c5a030580000250424502c40da00c02c00c161400540441d087c5070039420302c1e08480702c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 94646816 1250 94645566 94645571
    0xb0607080c060a05060a030f02060d020906030f011505030118200a020c040b09010f090b03032b0606050f0403170c030723010207020907050a030b0a0b0d0b040203061c0c05060d 77
    0x641552140f2809400845c202d84010590303196030b03555212481c20002c000d00070000805c50f600c500c201034040e601c19100040409460b07180403240010040024841c440b22507200b0032081101c02c1c050f40403207041e10b403030982d0001d0450b14030744103001500700d0491180004001215035215001000301604400b5000e90242c5404201002007105462410840760320070800760004202e0403902c40040022900c028401040e00306205000030b0440c0902042310500842d03007081001c2c008140080501081d40c00c4001708005900e81034100c481d400350000010020004000500c04900040000f18044412048603851300d040d443c8020300315004404100c40c680c500e5103c03200b200e80380c0c42061560b9541c0700021414515241c0005200e410003400c10014054009111109540300313400400150101514040384ca030307500e04075802c19602c407840b0359146914203810280940303054001c60780980340092208624812100c0d8a000e0384c50198000ca40c60100001c000039192250f0020b040403140d41c4000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 94648066 1250 94646816 94646821
    0x507020312160519030e030310030b070305012601020403061505011b020102030f0304060b09070e040c030908030127180c05030607090b0309010b0607050c01020114040f060b0607080c06 81
    0x10041e03004054400785091003500100c1061560280980d128141015200e00f00c1031301c03541c0e0550040403466030075100e6000010401252441c20103003c030460f031040201120700d03510880124211902801740802c1c81e05071940240800c68082c13183c22a20340700c240014030385075580e42c0c0c1c04102c6074540c00305051941c2811042141d0368000946640801c440c83c0f041740d0b0300e0080d500013500e0b44920940c03c6184500170010400b4032201d075104954100c80508100b00340d04004c40c0140c441960416542e228508020004501500c240101e60403240d0200f0054250f90038921011107050340460800ea40d07580703e80f0700c46801c15683c001d14040ca48011403214a0680c0d5080c90b62500410350400760080d440601030282e000e03230120009044a81c10518191a43c590100040c0036107829140e039940700d6000f04e00282400030110f8055100d141c260020009080035500500340380742c00300d07400b8000490341d00b502ca022950582104880603001803c0b14034228013655414216000302c0c10012a40c1e000c40c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 94649316 1250 94648066 94648087
    0x1050a05040c1502030a0c1103010507030f0e030a0e06090d02150a12021c0b0402040f060e030105070801030b04030c0516060c170c0706030f02040e130c05010518010f1205070203 78
    0xc05001600c1404200003c1003030104010307650380b180074242c8041003880c3c4520400c0c4008098041707a2034000034024445411321010040241c030481610030b518500c0c1c02561026618004100e504035241344d25040040c4007050104003440c4c00004c000b0303070090000c503801401a6118052a40d1a0f010740e40c405455030311020f0010800c0d980541d84640035881000121105018501c010150070349152010554140010200c1c0290040d54000e104416001001040302500043c0c01ca501070001c0d4000c01941d942c092046500d401e080c44040c1040600101240c0481e22075412802c11074004c404030340842041c200104101c41d4154068000a900c651400080040c400d80d060610041c3c040711a0038884200941c98480c80d9038810b03032090540d500350548440e100c1c1e80580e00140403a0344e440c00a8901400301c078401c084403001c11035841191900c00314541d03016030251900c81c070700c50362082000c0c0c00c81801550354034228800e40d001e00950b6408003044103c02c5c01128401d001c16805503807200c42981 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 94650566 1250 94649316 94649333
    0x6040b04060f09050f06070c1a040513050708010512030403080307050720060922020f040608070504180b040e010c050903213703050609180c01110f01050a0504 70
    0x606904000c0109020800f41e6039100e40385c5c0aa0004440c250b0b07480c506464042d449003e584d0000c4102180074030046590039140d000341040321000d0320302503c80301500d03965404484e42114800c0111303c81c8401030201d0308220400d065040310100440b85003a48039201c550050b00112100000603c000424408021041c0103a0b0403108000d41103074004604200001c0d5540583d000782801240c2100c01480b88800441c180c0000e01001402190350790740c440700c004d4165002d809114081103030607011a6100c2d100c2e0003182c040b0303105105000c1d650380c496408180038240081d0001d0f032080e10703000300b40255407080c030030440020b035a62280c41c0d0f00c180b0001410f051900e034941e100350f0b02d07040340c54000070700e0494011258840c00f030301c201000110925960528214140101403400901c00b102c3c182c03042d4041d84210300030281110100500ea5403a0080c1c1404200103900040d00c0e0441c076910203903940105010f40c007500040c02500c414660004150b82115021207000660795218824403042c46240c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 94651816 1250 94650566 94650587
    0x80c04030b1f05032410090e0616110d0c0c210203010c03060e0c07050a0c1d0f060d0b070918050f060306040515150901150906021c0c08070206040b0406 67
    0x9601800c5000317640b101c0c05503801e074103695030307901604202c000401105464110034050300006d141000300003841c00d643c41d41c920044510111290b4102c5603024103d0182c4054540c03d03010b603000700b0000c108402d0444056903210412034110408020105402000341041c1440f40c02c00b1084a00b1002240100341c2541c500c0c45131403040c1490001e0a000071104880810791055454440a075038108500c0d10a141441003175026009e460708a002180055100503484040b4000022900e07070380d04c6000c501c00501a040c1c500c04c0e4042c240e150120700045078205600e51024903800c00811056131450544400f883d03209000a10a90320320401403104840c80403903400c00d40176401000585407550382c40c0d5031045182c0b07035460360400c0760000901c900c1c1c40c4001c1e104c078028090510440d65a482c1d82c00610354440c100c040c40480e200400204540d440000d644004030841c1c0d941c06c1c010740c815603050321450a138040586619604001502c05038071054020002421160744150384c2e18500780f00107060340c016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 94653066 1250 94651816 94651819
    0xe040218070203121806010b07051614010305090f010f090b01080c0f060c01020f070807050c091b1b1903020d0c05030a030c18090507110f0d080c04030b1f05 69
    0x204180001e8a600100b43c1d035404201c1000126180c40381c0c41c1c90400c90301c1a0400c020303688660790001c0344080041020300605c900c55000c40c0c41d5200712580c03c00b0400d07502c0c01520320100c1c0701c2c24401c1c4250703c41c0e00120b80210ba22001e03100180c0c1200c045a094a442000b01d500340ba8440c6052010450445400ca0040c40c94002820301446e4100008195028030f150541c4500700100708400000401c0d41210340b801380702d0f40d00a960b071100b0f1903c0c00068000c2502642e80e0b0007a420048414140806002e1140c0003040e80c10145902004500b01e150708002d448010820840703031410289103040000c1400e080340c1c0c00c0309034904504c0f0320703009280c800c45000390400c208140c08540d000030000401c0c0c2d580814242404100118111000c45d222aa940414010504600b90004401941c1c1d13220500403c2d00d80c0c0c680b001d14404d0510340360348441145a0418690220300e840c60128860304030b481c1c000200c40c000a25140e965106e010b40400d05694080f144810250001e4000b80650300703807002840d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 94654316 1250 94653066 94653109
    0x3041e0812130801140103231e1905010617070f050d0303091a0106030f020703170403140c01050a0b040b0904020409080c01060807081510031209030c0e0402 69
    0x10045015120000c05010394061240450b010600c810000110000b9000c0d07003008002e0254091002124084203100a4604140071100207900010002d80140140141e00090080d0740d0302c4c40d01c1a9000c03001341040c240038003038001180a40103401180307003070081c01040040741043c28189203042d01030442c0c1002146912402c402c121000d4192104411141e040b504501a00c0041c24181c014003054040100355000d45500c50406000f8407983c941610455a0100003051410380418102c0c484c00b0400782c081a65203441024214591102c1944503219284c8000b40080114681d5004e80290075050490f9441d032040141e841400d2043c00e041d0081202d041c410b00f2105008201d0304040504083d016a484080d08028400d250084441e404c800000800c403a503a2107022503140d8a5a0040c0c1350a80140e92400020142011840b8007a20014110200d00742c615aa041c0c90001014584e40911400d180d0000c04103420b600a60020551aa5203884078907052042007840b29401600301c010a1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 94655566 1250 94654316 94654319
    0x50a05070804022115070c14010c090b030a0e01050708090c030d0c0303020a0903140718020c0d05030415150e0f090304050f010e06070302010207030908030306031209010e030105070203041e 83
    0x36214444c043c14881604090a9251454416036081880081d030040c50031407036200b072100d600c0d48051543c00d014010303401144007010010104e426140c1780e60828002076800304c4240845200f05d4000c54100400032400100030819406150a4400c00c48042002c2040c5034108149800b040c0070302442071902324050200b41041d4040a0060098003001500705980072030b00380e0040b80038201e4000610741142d13040550201400085943d0681c1c0d000310840e1022081000c00c84070941d0003a1022410700b000509809131020f40100c400350401841914480b0110038094041c0740d1500c40c016001005c009495521030034290f1905502e20060801c0310640780000c10400500804020fa03029188102c81c0c001c00011760000480b00d00f0a60b0240d43d07413020300083d9607420181c055005084003031194443e00300c8156108040d680340e0104461080d015006120040e1000d0121801403c24800505107000802962408a800c40724204c4c2c2c0000503130b00009050206072038841210109102c0140381002c404d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 94656816 1250 94655566 94655569
    0xa081b0c1011011e1b03111602030a0b0a020301050111030307020c0f03030d0e01060e01050a06090306090201110604060f050903041202060f22090612110f2101050a0507080402 77
    0x1011544504002c01031000c2105240320b50a42101381c500340b621600080507441ea0f501540188022400081d20700c0206003060f81c928000d00504000080c1c244400d82488901c400c100b1307a1031484003040b40e06004810340400001c4118080d1030240c0c24042d40180c60358140400540502c0441841200c40d90090080018260340000c2d0000ca445094070711201039200100800c1c510f0148264030407030a828401c2c2c01914010540c461400c4454602c6130032280e90707a403001e00000d00000d0181070002481c4a13420300101e1115005110781078410324041441411b0100c00341c0c181102690300310380c6261515503507403024032140115a000b0351502c0185280030310340302141e240c2c12084c0300c0081c00385401051a601016000b4192303400316a5201244403031405070f046441c1082c5c2e480c0200401a46040030110368044505540502c1070750203003403403c00d043c681c01003041000d880b090450b4803c000e1701c0428440b01c00041c00c501c88801880c0082024140b04107500c0607214002d00b202e08001e007140400016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 94658066 1250 94656816 94656829
    0xa0e18040609060e01020d021e03160807020a0204020a050c0705040605100c020f0307030b0118110313060b060a0302070309050f03030304030f0c120f03050f0f0105040c020307050a081b0c 82
    0x70760041c000110701100d841c10340c014003d4091450240d500c042090b54110403242c00410810043c0b40112110034080400718035180402d0f18004090308025846e401d120303018050310707500300c280303801101e01c090344c9580064241d0340140c030340301c0000d00302140708200d040d030400410019250848060020500f050007241c00740e04100a42001c22015402c100159250803070f6050320b00c90081d01ba12400d54882c10032005a240130300c1400461115a2000901900b00748034100d4480c41c05010f5620795207658200d81d20a4800c0181680c00580d40c000405a0b5030781c0388010080b402c61514003684803030450030050500c0301d4940c04030b4000c54410f41c4e50400c41c2e5003c07044a500540c18104011201d085040407940c41d40ea1000c010403408011404458003504a070600500c40b9283d9002e100c81d0b80c0e01e529000c000311040d0307000c0c0a01848200148401d01e0603802c00b0800d42c4441c812070b4103203003003502c0d85444c01d9040d510990390f01e8800281416032038408240143e140000c1001030058080e0076002c01d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 94659316 1250 94658066 94658071
    0x4051209011704140607050a02031b1903080619141903060c030911030c030601061b0519020f0105030f15040e01051e07090b03010302060a090b0703050a0e18 69
    0x252228006002240c5a01507180e15040c0c401150b00c0000c41d241c2441c218550b000c440d9000701d014810000001d8031680704808446d50301540f9030103541400e000e0490b40980c0072465070820018000ca180c2c0e80c402400007610742e84094000d40c2e030b0004501308803085c841200408281c000000d21940001d0007000043c0030890428107080d1640c0c4c8143c0000c1c0c030321221240d9107030002424a42009400501141d140e040f503040e4034021913961030000c1850303041555468101c03240c2e5801d50007010040000764050500100740c220126155920070a0907034a550914800c4c441a900d480e103807001040c01d40c00e03c6000c1002c112402e003041d034698288144c4075020114000c1c0812411088010307410302e0b94495800c0149071001060091006003801084503545481c15049541007080040004002c11710480c0910101e5028a05240c0365034219000d02c28168440d0f0035800511070509000910207004a005150842c005e80e1141d45504581d840100010044443d091080d8000e038001900d0b25002e080c0c1a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 94660566 1250 94659316 94659343
    0x1f0e0c090d0c03050a1b18090503090a09060f0501080907090e120f0307180f03030305090c030601030803011a040e0a0905010e0102030c04080c040501030314030703090c0303050703020d080405 84
    0x40d150035468001541c08804510018100c41e4094800000c00200042030650315116410100f01085009044031500000340703d0260010308554510803860100c1d40b2440c159401081981d01d40204840490031080443c1c1c00011150340d240d004110700e40181c00b10401810091909070031909010124036610169404ac80e45210307502e0305040e0304900c003004100e5030081451500d0b9101c4040c1c51680c40c0750b4004075a0000840c60202d803048490034011010010b4901c85842c0320886421334070118003c040c0149071004038031480071403034100d07034040009600941c0711b80f0b1556601d604240324001c0301214442c80290502c01840f09106c0d000c01e00c2c2c0f02c55070000c0c4c0b50000182c0300b03a03241403440c05080107a01243c50740d440042488280c003c010001c00546d182181180c6940c0004410300c07088031000d00c80500010340c82d259030494010810b0003550031241c0c9190218120246458115402070b0700d0740124082a000121071003010703010f00c441a400c82039810030443e146410b850b41074a8981601201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 94661816 1250 94660566 94660591
    0x2010603080c0c040f1a210d030b01110a05070b071b260601030512071515091a0f150f0412020a06020a030c0303020a140f0c06010f060e150403021003051f0e 69
    0x409003d052010340550080d8040111a10102d0190009c2e004021740404580020205c00c181101050700150000c2101d5221004050032443c0918141441e000001c048511300e001003040d1043d54121084000903104418101c16024443c0071811840c0b083d004609100f034005000400c007082d40032440085611559a0581e50756a0903d048801c030903030156110b207a00d1900c26241c00c14046072080c1001d45507114000c0104021120101c0403400303201c2401ca52000b5941140d10690401c001c518091302c007a01c0c1c9244c100100d100f000240d540180e04046c04812044082e40e00350302d00340c0426001401280080c0298142c2074900601e007129190020382416000503070840c06c00d100300520411400034031201d83e00d8014413548500d4507444040c003007585104903000419070b410740b2101d00044441c0e549403d80142840003e1100c003041c0c1c4846441c1000f400d1000001603240d610000c8400c101c86e079400181887c044458008004010300c001d002540c130400c0521281c4402a960781e0041e0280e82d60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 94663066 1250 94661816 94661839
    0x2090a0f15120902120607080702010207050606060724020703180302090a05060316030305031603020a02031803010615050c0709180219081207050c040b0105040b070302010603080c0c040f1a 83
    0x40001c1e100083c0c1c000e4103e4261a50001e4512000c5603041c06200c1551b1944d9007515104022803c0c0c1c005c220014240380c1141011a90900d0140e00400c202403183c00c502103c291441040d4002a0408e61981c030015000a504c500b00b60340001e0b0315404e60311140c810700301e050440c0c001c10780c80c2000510307003036082e599038004c2a46660300700305000040c04501c628032580b9450349001042c07904183c2d903031a408040000071049842c028003d442d8a07400c2071f40118101411641074100c0c202d880d00ca01e0382c255580d5000411455884c0c0c0c03496035801842c0d2521071361802040011403a00a090380f0044a01d07181129007140160f07030b4649030020340d404135402d40c0d418245004c904000311469216881074401e105102c0c0072020102c000d0300d8400d009906403000380146105100584801c00c00761400500704000c24042c40644030042d206c154040c0c80001b4203a926580c0799440c9601c808905151584014200e003464036040c001c2002c03030040000705101148483c080c0048021080d17480e544030300b0840c0c60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 94664316 1250 94663066 94663097
    0x17040f0203030c0a03140403020907201002180a0e07030905070503030a02010c0207060816030f0e0610050f0103060b160512030c030411180f0a0209040207050102090a0f15 75
    0x1106008140c0080680c0daa40d105205a03642d940d605840031008111400184c41355882c1c2c04055808882c1c02600c200700c0c541d00d00c4801c803809901900c0841071402d00004200d20303520104941404007103002001a56280c00740301240044061100240c4918a0018207200d000c4070011020340058003801c020400180624010741802140d40040b074040c800030420140071742e415001107011900d00c1e001e440300c441e06c40c1000c8415040465901240800344001d00d484144130b5407215020801440700019054805c84244c1e08100301501c503c00601010300c024490340c901013406a5088009007002c018540c81d1000d410920302400ac90070030b03c0c503800c943c405c0074003506202038404040342100842c0d803480e2204001581d500140c405440358001c402c507024580c01c0c6480300c1c4c400c9012900d0340d61402d40d507151303000c125400014a8501c4540c0c083c00700c1c07022610b40c0d002800d10a4411400562191110400e00554803510352190566015140c4101f042e040769500d50240c06030b0520f450810651102d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 94665566 1250 94664316 94664333
    0x20906070611040f1508130303060918050123060d020111030d0e150106211d0a06110717070201170a020d0608120406031d0d0f02060703020a1704 64
    0x201904090400740b0341200e20900b00014070607a04405118503505413110380c5c080120b00e240181102103400c210101e0032844008207000001440382c5404900152508169029a40300003500038440c8180d044500400030203000340000d0844c41c400390b04681140d5840d42000740000f03488035014103841c140c02010359224202402210700c9e001d080304d07680d090400c800c01c0104188a21304020b4081c0c008144100c0c2c802c501c03024101ca000781d480c0760780740b0b184003480c042c54000030320240ba0896991402e13508c8590002d403810380c690162406080e0098640c14044151103d0400740801c00008000440c001080e562920716403186000501ea21034001d03200682e060240031026184556610040002e00105a00101a440942c90f01070102e56940d2070a16580e46011040d100d000c603060005000343e0740309600c802e0500e400c0d010088116602c05140b1810b11410014210003d1185800282200c0e010000107411015900d4110310340700401d840203155801c49185a524050071304041070500000701c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 94666816 1250 94665566 94665577
    0x1020c0304290909010302060c0f0f0a2d0b1008100c120501032d0f0c0515040506030415090c0e01150305090d03020a02120d090b01090905070603020906 67
    0x1120781c0e0307a45820101c600e80c000c03541c81a981d01c100c000e0500c802580d60066414401000c1c01e841113590850f4200320481d004401080320f40d108400000100d110204000000c82001101900d5140450700304407180d114160120084041d0a6400f24403420455103400c028940247d000f04035a295600b55070160029540500c07240c0c4212903000001d03042135440442c01062544501a0b91803254100c1029940f00748809030000c0740e80341141c495116440c207040e81c90400c95001540540b5550380750030a407003880105450b40c40d030002e41440141483d0824034462640e101c403407418985000c00140640c030000b0401080d01c48010a805d040c0c03081900a0f04003140d0090011240c2a15644502c052500c00d12400e2412894a0045041d130346c020700c1494001c040501c00341009080300d0034240d01030f60100d41c0900c21481015a940341549003000a080c452140305404a5480100e041003880c00f6010f800074028545452a00b00c00113400003a01d0080b030b4090f05015072140c403118001041800f0300e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 94668066 1250 94666816 94666837
    0x203070b010602070e010905090d1b020312031b070b04060b0d0210021501050f031c0c080c0d0f03020324010908011401080d0201060501210f0204030f031707020c09090102 75
    0xa00d400450750319004a00d03881603400c40c440c0010203aa89803258002e031142914145581e030403d61442720410310408048000403c068554100c11480b640842d20303021551602d550300f82000300038446002020580c907800382c404d07120301e581060b140303888100c0a00340240006140d145e844485903090f80740c40010005c0c0c3c030f03001405060107a913045000f035180e13413024500d1b20f8101a01c0001040501e800c110450840d4009402488103440d0400380404c046100c041010034452488083c400148111004003030401c0c01d540036103d0315600c1c0d2000b0b40061503c80c545400d043c0140104079032000710f0640e1114101c1c0f800302c80008000746500580b4079800d00d8002d05042e500b0001c070620a0035889003d541203a243c2d404660307091015250403800c03031b055401440d00251040e26031043d021940f000316507400c210301c3c07000a070010042200b281207920607401192011041809403040c550007880081241511400302e4200e4900940000c4d101c120140503a4403035607030b0034081515180250706940e400490b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 94669316 1250 94668066 94668083
    0xc060b04050c0d050f0c07020607060b04020301080f010c03060e0f0415020c010b1507081e0c15070215060a05100c050a11090108150a02071103060109061802030103120c03020307 78
    0x914a102021030343c003044890307a00a042c600415040d505100780030340300c1c05246500d9400d005c016800c00419034003800040d921951242c044144550300c604c003d600829030360700204a000c0c8244402800c4d42c1641c11041c05040c03600340f04100b0f104400e042c480e4000d040d02c0ca215403a986a00d401007200c1ea941c840384d54418404a2121031400f01580105a94001241e042d0310340d10b01c4040300c0010388149000100b000b102403101e034543c3c8803520401e040580c1d110070701c10f081540720a8001d26249401e181d4201c651840380178023449940503c40074150a00b24000840b1070315007030011528a1185104040c0900c6007070021408051141e40310681481c0d014040d0790b61500103090000c00c0c1044485641c1c8100f11400000503d960f0014519804d1348040d04600c8050703650b80e1b40c1100035088070764140c8082984044a2702c5a079418044036001e8000c2220005034a82800b41685d60300c908094a203030090305c1080140003181000708922040031b040c2ca0a800e80c0c0600d440c007281940103200d0000c01c400d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 94670566 1250 94669316 94669321
    0xa020f06010308031509090c01030b0d0f0803010315051e0c0d06080c0301110c0a02040b1f020d1206030c030b040809060409050108280b100f0618140a060c060b0405 72
    0x2030f04000314015104140300700341d21189642045600b0409031080e41c0c080e403005141b0301c0300d540250014008084014191500c0300030399210500c0105403800300301c030b20140010052042040186800440c00d40d011030400980c640150309594400c039149880c00b4941c482000601c50000c3c100c2202c4481207010000c0c00100d580380109036440c0d0140310140d01c01d5082166101d05210254140e400010201004008449090702884014600300c0012504440c7d07a0a80109684c961920980e0f001c1496009040e40c01030349c240101440c0d41d022924011505266040020456215000040d05c1c0c02c05c40000c43c0b5102d80c41c1841540c4501211307030303070800d40c0482d0000b20101180e001c10304031980c40c03068032040007000310a05a401060b228194105840c031000700041054840ca15521041c440e6001e00b19a8640d00c401054440d40d40c00703000001c00c4c214106e07c2c100c0c81c107071464000303020900014a040b107408002641440450142400700140c0850080601640e600580c00000000e48200602e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 94671816 1250 94670566 94670573
    0xc090c090a08100e01090f08070609120f03051006050a0305091c05040305060609100308090102160816080f1c0201060321031a090a020912011506080f060a03020103020a020f060103 79
    0x20780c581201520f101d840e06880030009141030140d20f10300d5512406400600b80296646e40254001080c15035110fa92080c51400140420301c5100d075900103600c607040b0f40c428150380201921030040940401c420141c80400019810000350707a16100c090401081c6940e90340e030142c0ca400340c90641050003810800181c54202d80213002802600c0c042c9041d20f4250360b501050002c2c0d61030640d034400d180d4032007901c1040407490300d401401040e401441995440c0c907099400400d5885160080b55464102c0c0d54440c1082041d00440781c000c0041e0302c05046041141d42200d0380ba42c0c0450f104560304484800002c1c0300c030740b003035101102440c0d119103000740403042c445000c0b007080c04ea803141401007444e1000d509610341d000c0d00d00750304103d8001c220b030325a07940c0c0c0351000c0040d42050f204c11350441214860041004428000d90362207a09400c603154181c3d24010004203000343c00303080b00014850b800e090082c691038440080042e00d8080c20003580d00d2000c3d8208902c3c15048060054850107031000100c02c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 94673066 1250 94671816 94671823
    0xf1c05070e0910050103110f1c080c010c0e06040e0c04030f06020319020702092406030921040e01050f060f0307020d020705060429070b040f0c060806030c090c090a08 73
    0x3501e500403c0b02e1030b490316411488201c074000c0c04054100c50510306084020700d000007107140b00c0d44020b00a20302e0f055511108282a072041c81040b16050000f0924100410092240141c0d0400c28540740c000c04012502003107072481540100b400444000c000940310a42041c200c030000c1d5840001c640600c4200d06040000b50019a0316128041c9030302110040010349000b0b6031200c9400400451207511031400080400d41134441d944c3d80d408510114000a0741d500028501c0341540c08040c0c182d80110700c05480500c200c107900800303051170500050102c0c0b42d20040b4541561401d6400c0300c0383c401c000c00021624050300c0300061042d600001084001540031440e6824a01242c084500d003544440810070b05006501030001d010b40541c0d801c0020020485800d00c2c44081d001c0b4551400c805500ca80b00c040342e0456003901d100c4001004001046030522018006040610f0301d00d015040c883c00107900c40f0132503280548030b00d030700700040f541020b1482e040b28940700009141e408001d9031400030985 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 94674316 1250 94673066 94673071
    0xe010c210908030c040303022b0f1101090c030203010b09040f0b040206070804060221041401080c070804030c030b1e0a020c070504060f17010b03030417070f030303090506090109020f1c05070e 84
    0x41c082d00125003d0300d0882c5643c502c041c144c8901c0271407840e080c084100c400c3e0345c050b01480d00300702c001d26480b20810028403078014024000c01000c2036040c20f60041c1425150721450325401804031008110108032141045111141d000d0340c50011500c0790300004105028500b4007820314007000a0000301a6000642000c1c070303180014200380b64242c0e54100004501951103058040c08100c18420303103941c82450a1940000029602403c2105648a40b034464102380c0040350100ba92807024001d01002da48801e074042d4240c416074118500d5008607130440c3d2005011600c040740c02180301d400411040c41628007a100103041044101d59900c0c00d64101e03500362040c41040100c3c604149022078040c00380081c0410058000c519251400a034105883e0401581c02d143d80a00c0401040000e225108500203502981e8045040c07005414100d0814001030254085a803505401000513110b1969005203080129520281480074906028000a1102e4010f04500410740e011807102d000410090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 94675566 1250 94674316 94674323
    0xa03020f12090c120607180306060801020a080c0f070f03120c03020d1a0307030b0907090213060f020c0306010608130f080c010b1909020f0f13090e010c210908030c0403 74
    0x481402d40c2c0b9003400400305100c4c12105094104000140c0c100340606012440b0709240c012943c9400d50384e840718400c40d000e03500a212144d4001400300c1c41c030340d44019495040362075800721510344505942d41c0c0880e44140c4000806010a612402d41418090a0003645a5800c500180801c150a00004000390b110320381c80c03204145050315403c100d0030341080390300108038041d00400c000ca0446d00c59442c8100003c001103441e01c11208089030382c81c060300103001d2101c0c54a10121003e4101003000d40030410b8000c941c411540200811082c5a40010307001d411107016003480442a200c0e89545401c01510700c5001d0407403040340c80c0c4241005131034801044071060724002005a801c51a0030440c107014500580d2411000441c014041e400080d801041d549155a40c040c3c07401047c04203241c010303008400f002440b2003204600b001801d4190142a0040b00100020020ba11880b540a000030010821444c8c0710364112a60f220b800580390302064089400c1080c1545a2500d00140440c580c000e003c00c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 94676816 1250 94675566 94675573
    0xf050a12090503100506060c0a0f02010807030c0e040926070c090608030d0f06030b0403200606010c11030a0501020f1c050105010e04020a14030a06090b0306010f06050a03020f1209 79
    0x20103080c0c46856900152840107010f84000300590386a00c000d440060000d41d03101c5410803202e01e0240c2c040100f01e26a80c03240c00d90250190303140c000035207031030402401301d000c1c0b41c01e083c18208115408150900000c40460f00012448618104600c031940c50b122a230000044251401005c0c0d40700801600165104001d004501034540e07000c2e84c1940e20a1084003119070090145460b449119040003a410718200400980503690f500d030703040c1c2048151409da01282544280c0c03030442c601072000d0b2a8440c100300c020314440c100380780004d104904140015050610240030075070103541c140306514000380c201009544446894440c8440c50f485001c0ca20881844407949514100c0c05000f000d049a80503100d22031003803a83c60500001c2d40c4840d40013030800c003000544444240860000c3c5002c0d8018101c0000c440703042180c03507021541e0b05da100301d200c0c0c0d11800041098040d40c1c40c4200684a0b44d14201d61034601100c2c00f42c0180c0151504001c90b2000803035410801c0c807114040d988242030001c200c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 94678066 1250 94676816 94676843
    0x1214031005040e1b06030703020c01060906050f03070302010e2e0f110606030604030305090a06050a0e010608120d0c0207090c0309060b09040b15010909140a0507090803180d0f050a 79
    0xf943d1030444000c0491194003000d60014030f0300d003c2c0065079111840b8180986010681c00b0200d0850346180c00c18200c01e03990701000d108600b015811071503016000c1c0e008107411401d50b0006000004410780980c8600c202900951040310700a10550340e07203080b0302e00e4140001c1e81360300190079021080b2003207002a00d40c400311105440001040c0303001d840050050001d0740c0791501c08401401c00200070f450203118030400c0100082c202c1c40384a100303108008000509501294070b03d030942d44a68890741707895000e03100821150409108451110088400001d03041300480026400c0041c00c1d8401a12186490200b01c00d498054101c0314459120b4003040003403c2928081114070202034601510300614100010007180d0948640341c51101c0505110484a0380c400c800425100416654505160f040303041c026012428020540c000b859420038482440c102501203540e8003803600c00c0400c6a022072440c58007a01e4600f2032070000c0c1c0d0010403240c0741d4182070400e1980c07002050701c102d03118180c00e80b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 94679316 1250 94678066 94678091
    0x50601150c0c05090406140405060103110f0f060c0a0506010e0415020412150f06060306090b010504050904060504020103090812090c01091d09010f02070c140f060304121403100504 79
    0x2404808203074840c550300b29803810101440681070005204a507407943c3c5118406002d0026442c0c90301c03603071007100207040c0340d811480c0451a01d100c0380c1c1d2050098070f80d036410503070350740d40e44054811907181078036a01d84035078480000c58030f4503007024800751040c0114400454407000c80e4036164400c50040091103a080300208484049120b50300c0b83c40c074845500355443e07000401e000400038121420b0040448d100801640d070404031050340d481a8007003a9140410040c10110b0300484030502405d0030081c2c14540340502103000680c00403c001e0030540d0b0742000800f1a8020f51100d8600381d0080c24040d11a469400c4032940ba02007a540c45c43c081c03103007060604030740d840740584100355102c8844140ba01303110f080d200054880e000c0c1880c10304e9500e80d42e00c1114900c0ca13201424459006083c0051070500d4440c0303007150034180a6203113014141110040d600754442e601201d40240d030140401c55180d00b124000c440c100d0025590401500001040c001c951141080c41810b9481c1241c1c200300784041602d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 94680566 1250 94679316 94679327
    0x30c050f1c0509030114010602010902030c0a03020d020105030c0d050106031d301b0a0b070306030305040509091e01060801141e100b040902030a0506041415010e0603010305060115 79
    0x200c41000c5141c00c044111200d4441c1016204118000c0c00115400c0501101e100382c50000343c1210380140c2d034614240c0154642084064054001030f00d030000c20a0550b00070038a29131a212001c0d05010000003c0b584084980742120100c0c04581c004008558407144004d003d400f000d0b6120010341c140034001034012a01040100f071a4100c50304010003440c002084c0301743c81004a09098500d5010702420f0f0010118850601450601002604100340d0900c0d1110102001800c40c03403c140c585441070001a4000007140d0545608460b2078001e41d40305101613140091345000a10085c07840b103112201064150803403001d4450100090104920702140c086908408444215000010960341c0d14008007000071070f9080401d9036644c00d2205c0c0c88140700c01d05075005a009030180c941c00020050305051500c07645030841d004850520000b04007090b90844408060b0990542981d104c040d6040c1d03030f00414408045c403c028090380d0b160343e50f90800640390b5201b4421070b00000f0b602490441c0261080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 94681816 1250 94680566 94680583
    0x303090509010e0f04110a030209040c060221030c0f1c15170309130b030601081011090d020f041d0303190c1209080d06030b06040b04110d090c030b04030c050f 70
    0x1c0d01c2c8134000d0f03856460700d0500e181e01c0000341c2e40108034040e010001d030700e906074540d104900490b00020b0b028507002000b4a80101402442048050b01c070100101c91410340450303400c501038900c61500c0e422000b1550803503200d010240b95400c07480541200d914103064101481c0d00420320440d000b072503600c03044d001155188040640254100f0080d0b0005494486008180b00340710f64400100034440802092601400b0380040d5840d602c80c0c841141b1403074243c001c5200f400320350741070030b030900807860003080c4068402c0e80001e100b86140d001000c0e098a55600c1744002e00e100c0c3c807101580e0b80d01000707999102d500035038410b00c0d8141005001d0809031003d00176103140e13a4169441b0f1131541e100c0c02004005010b0280300700ca030403100300f0001e101507441d4011407000c3c50007210054140c0c14150200022901e0310040e0034010760a150b07079120341000c0d85003580c0a0b0700c581480841c1134081880e04000154268000401c0900c080c0e007404107065004511180003440f890480e003208405070746050380c3d80d254 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 94683066 1250 94681816 94681831
    0x1060f0e06041109060715020c032b0603030806011d27010b030609040206030711031c15050109060e0f031002030f01090204081f0e0604030806030d03051522060303090509010e 77
    0x10040e0400003400c40c1f14407035220341100c07801401e002000200606503800340e0914600d10382420340b0403002e00b0314080c1a1402c8040489e04101052540d54050304101c07000300544c1c1485a00400c4680181006c0250b10382c140c002030461408110000380000300a190803c40e4504904600010440c403c1c804100c0340204802840c540c01551503900300000d60307100408003420010554904c42040c4010009044404040c1c0101c41821038001410740c02c4860012038003a001d440b0781030401140e40c0008080042d501c0518085d2210b42111b030103c1c1c45c00060402090b0103200d00c40e844001c50344d4a902450254240d111a08490303661494100103070301460183c01441c0d04030900c20a51401c1a241904001d010244007148401d400700e405410048110350640110344601e081080b2460140039080d8040668241048a414103100ac103140140324200180140c801c05200c2941b400c080401038250f07101080700313004103500d0f4030380103040b803070544503c0d401502c0720b2001281c0c080041d604107100d201c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 94684316 1250 94683066 94683079
    0x10e0d23040b090d0c030507030809040e0604030e04050604110c0a061808040608131a10082a031507020106080d09030809220f051806010303080c0304020301060f0e06041109 76
    0x1c041e007007013020500c07160704443c00c8030000000000100f0a0202d80001c50060000c551900782c1c0c4420f20054840758540e0b00c1c01074024bc0d08000c00290070010090b020442500c0001d44c42e03403201c1c0071230000d046440300c2d4191580003041c07a1004000000e040d0282511030b9605120304501040d0300945410940401001140b00340030a001103841400000d621035109a40c8281a006caa10f0b079500c207001000e00683c10410b041c040022801c00b9500010040240341c000305034402d243c85142201c4104582d80385081402c030340000c0340c940d50400a440c1c4190300d003c0368105038148a00041e008154505c02d659040c01140540c903100b0b401046842c08807500451041c2c5059500800c008140e50405088a10205a12200ba00c00344062140c02e0440c19500400101410001920818058441c1505c2050341c0010018400a80d1240010b0b811094500015481e80c90341d10001340034205682010015039032030b6100061508002d092640540c109031000c00c1040020122459117200303002c1455000311 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 94685566 1250 94684316 94684327
    0xf030619020a020717010b0109050307050a030609140607090311060f0d0c0306090606090303020709060503030a0518030a120809070311120309040906090318060c0609020102010e0d23040b 82
    0xd5800801d5181441e03c1a504499140e030500c20f00310301768000c0c08220703a5444088064070f5800841c2d04001e02001c800500301c482c6048000f4507803c1d00c07404014240343e03c40d4a45010808100e04074008540c0701c00c2502c80c43c1c9000c2c0c0c001050340341144016100c4941d40a20a0101c0c100301d801c4844201d1401c0d82c8ca882c00010341e410201600d00e03680c0c10000c059071a0b20000b1503011a00c00c21010340741650302c3d141a2440c6040091400107a604031400451400f081000295400001c4500801050420700c0c0c4404011104c00420701800d94119010300038216210b04100401042d0916540240c603150466211080526591803207404024120947c0d00e040741c11078540305440071491850442100d10749280c48002c102503810342c00d000c50b252500c5803510300805400c503449a41020358035021480440c0303001001803030003442010241070326030b0301c44012066900c00e422078403d081d503610486138403040c0150010f041b9003907001005c038401d100903000700c5451060401c403022120700886090425 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 94686816 1250 94685566 94685611
    0x30b090708010b19110a080c0d05040b09090c1201090c030e060709090e070308180901060f02030a140c0a0f0308100e01051203041d07020c092707080a0f020f0306 71
    0x160000010041030041106480c0c1c17a0802c02c01000e143c20344a0050251144140203806103840707003034407501040c401301340014088000c6110964400a001703d800d80c94a84501c20840403510070b44041c20f226204007000403a4138a000d401171810004140e404015204203041c01a85417001a1000340000d4100d150401406407940c00100303109401106565805503130390f9510f001030f0703c5214042d424005910303c3c0282072411440950040916041880d462860814001d44a114100d425010f2140c00154042a203a544081e5809180c04804555600c042414580d04c01151360400720001600e07980040c411030005075140045070380d094045542c603400d00041101c05c45503075400d41031500c0140b02c000307400d03060986c004d000480e964610042e1800e1a000090805107004581801048034005000c9100000d101000c03d81218220740460080d0040009050402d50b42c0208194441c03045018140010107020301d022620880b040800f0f00c0004c6c060580300c04080328a1311129a01c0c04480701e65 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 94688066 1250 94686816 94686847
    0x8100b010c140309100e0a0b070b010b0f160501020903160807170a080a0809100603030f03020306041401080d11010c0e090a0204080d0c0605150303040603020a02030702090403030b090708010b 84
    0x30341c1181d5099138203120156000c00c8010260722243d000181c43c0c00317030b14401400d010428901400d44500070b140780000e2501c0b451100326040c40740c41c0c0b49442c00544056449075690903519100518042e503005070103d410518043e4110100491283c020f1250500141b07404101c0c1400711002c4501a045252400c14418080c410900d44000e0034001d54030700c50009020708000303083d008110b84524045003820800b061802c0c07140b00c14040000d2030140c0c18000b00b500401d40c07528080c400e1501603965a0b440000c50050040a8074040c2c0720700500b800401c500310045440000c0c00301584d1801ca040d441c4906440c03e8030703210080f0070041508070030000603904007034001c203034410240c21000d850541c3c2c0784180f03890100c52100c1c000000b20800b08c3c1c0001c018050240c0c503044426008811030010300c4c0741c0007039240d21403842380303009050340024080c03001c6000740f003552501a00245400c10034645400c018001d0104150260b00c41e04c0c2e1400010000380c0a159880d05035001551800c2c1080c504130361f034016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 94689316 1250 94688066 94688093
    0x50d030b03070e130b07020303040b0112030c0b0702101a0904030507140a150b03010902010806011206230a08060103080d09020402090904060b01080709060c02090a0b030f030408100b010c 82
    0x8150141e44004501024680e00e00350090541500c074030030303113050760034240e44800700a005441190001c100340008204140000390655040360402c0d850420302c1d1030f054400310112000103041c01d2003481000207240d0085020100c651800400744000b240c1c146400f41b04400d030040c031507440b11060005c6408030744901d016145091050b065a500000004012403070584140400c840165641581c4a07001840d13000d081c2c0750b5081a0001e04c507940490740068a4010300401060400459051003104c2034803c0e00000010000f02d102c182c7c0d50810161840302d00b0445c5008240182889000041c001a0001d20380f812250010501401c1c01d00b1348540801501c42030030181da100780c0034815030246980310311002d405917100d903034000f488811038030025184500050240091014040c1c0402c599900074075082e06903681156000d41565444c0c080760001c000d802ca684e6011300c500c1740c0480d0711020020081095880704021103c0020403400751f0410343d41500d24907400610300c8425000010704254a280 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 94690566 1250 94689316 94689319
    0x506090108011520031c050f07230c060405060708040b0c28080604060905010503120d02040f06051c0204051003090f0510060311030601050607080a090803130806060d050d030b 77
    0x1c4101c000c60013500350380071024015140e00006901d106040911070381032080310504800f4812464815541401303000c000b4021028805802d40000841c13038401d804507003000700341c0f20840e100c2010f1122595070b64070480b03046929200f54008550304a000c4c103080d41c0301d25407201c2c2d0100250740d403c03200c2541750406000602041c0340c24040c503444080c2103c9900d034041285c0d07114401c0303240581c2000207580e10f070b5201c144041d00d4080144000d0f18041805280302c1400303040720b40c0e524080200500203114a41c00840c515203c0b03040131a6242d40080100750520042420040720160580102d08a11451040301c0d0b010303c4011140901c28040e80108690300d0098848800c502035a8407910b050680d00e60705075054035643c0304280300f0415002907281c55894190000c0807158101000700f66039100d020703000b40404070f000c04d40303404041c45066450040c00d40301086c4e139280d00d0708841e002c29600050107441114000ea07030000b020303402c00c4001046120342240041007480c811f800c05500030801c102406 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 94691816 1250 94690566 94690577
    0x1e030702090c0a1d1003110403020a0b070b09010501140904021f02030301090f02040b0909040c0f0b0d0b010f120c030204080109050705092d062b060605060901080115 73
    0x101507614488403501c02d20950032140e81c0d81240d00ea005211960590300045050543e128040d0f2503195a84042c51400d440c3c140000c070449003014103451070096134402507002c49441004500d4800389805800d15a00c52410145181c8420003450f09882003400740b14042060111261201d2605900d10b6410074000b910140b1000c0d90951004041c00b201d1651030050783c000001040620f1680c4107411288130385d0b520440c10241480101c500500c540b4503524400d10110010806021074204100010042c0c00c0030140a290303030752003030401c68100c10b040d12061441c014420100d5406906000c00030a0381e43e03203584000c240d182c1038800401946008004040d424400406d0b504c100b44200d03042e490240c3c0040c0700080c640410010420402040d041f50301c01000b078500c00b00000030f02e48400c1118505100c003095a00c0a0114075050751740d02542d007507503a600c0b0004411260f21006a00030704d0103014240111a1500180300e0f040c411104d040b030004c0c04140c01042050306c1d0049845c250216890407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 94693066 1250 94691816 94691827
    0x105070210080f07030e03030109050a061e0509010f0e060405072a0b0c190309020607080403110f0f0105091e0916030507020105010303050a0c1b080705040501050d051e03 75
    0x31075409058808a440800c016005100c008400c882d05580d202c9210b1500384065070210010a4990006108480c011303500c1e040414421107140d00b1000180020040c0300d44d200400303d203824114041403060600030b404400000c524190304003400410380303110040c0481681c07100d00501006000c02000001001079100000303030f2002c5805466488041c0c110305503686200039080150200201602c480c03020310040010b0212600b062170b0b194866101d5060008403581c50b400880c6041c13250010041400303800007000710030000ca0300040191490256158150340c0d03001c40074422004001e40d41d031401b280d8144007080103403501256119604045022040e03a01500d180403507a00a820b481c065402520140c2d42131400743d02d40b1505920001510083c0f00c40c0d403550314040e0048c461803220a00700030b13646010006000b940f1050203081c0d803071042000e0609036203010003034403034000b0300403035105500304000003610349800720010b00001c0e00270001c0c20781004c01024000e5548038555641c030050000740113 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 94694316 1250 94693066 94693069
    0x907142b11030102030a0b13050702071203030603060203072a0507120c0306020a0e09070201050411040f15060e010f031e020313170703140a021c030b0a03080a030c0c080304020f01050702 82
    0x2646c019507042c1c40c0403440fa94800c041240f203c94507161b040b0b00c00c1c5407000f00280325a001031214201c0d5554000e4130f0101405080440140c80035802c0a0909070000040c40752040d80420894008090010206000000350390784003d443c040d4030028101350b1040d2401d001412001c0801e0700704034810002e00003c550380340c1e2000103a810070503152000c80c41c1d118004246041c517004160303000c0d80602c003c1101c0e01c0c0c55070341c00c54031004007205240220f40d22071001107500c0b41d80e807003040d0301c0c2d000881001c44a581c2d0540281a40d03070042d08540000c3d00d0344075004205029000b60b0032071503400c52014481c1846001184000c0d0001090090b01070316000e460740214907841a0fa1074203c82d80328505580d0540f900b40504030121840788070300010800c001c250b02c9590301040b09144040b110350311044113031408a0480c0034080400d00300e071713001d100350f00000100240035000b440c607541192401c3c0442100380c1025628498001000f900c02c950070030020700186000c0c0040c010785001410142d040a40b580c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 94695566 1250 94694316 94694321
    0x3060a08010f05040b090a05060a18060e0705031624020c06070602070501050705031302120c0a06020106090507030605060a121d010510080d0903060e0f01050907142b110301 76
    0x50500b8001d961034090105100004605e1940300c1c0192008011102c81c590f80c19a489c4401828030003000c4c0c0d074541c0c509805103a444280003580d0040000e008034040074200da5140d00080c420107201e4802d00c504114000d110074040710440e41040c0e9910084044c011a8845032040c9d6028181140508505c2d22960340d202c0002d029031038040c560042e1109018607086003114005080902804000d2013046002d29100000d598155415118070404400f4600c645141c0b800180001c0ea102e8507164010407104c1c0d05501c440c0444e649000b041c0540c7e110108260111142c502880c0d070050ec081190045480c06410010180c099919002507601c080c0641000d403000d61421010307559460f2000d01c12000c2c4520400d038003814400020b01444022410007820740039042c80000c02c01a182c2040c000650024004c3d1040304000b88002e010515126803510f07110a030034080c5080a2262010080950804100101140300da48011001c82a0102d01c610051031042404961441c050070f5506425202030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 94696816 1250 94695566 94695581
    0x51e09011d0706090503070308090d0c05040c1116050603010e0705120c190212031b0909070903020a0f060507031103090d030305070e18011502150f060901050102031e03060a0801 78
    0x780007034910141043c0b0020036016041d48068400d500c8000180040b401403422291009001c55403049030301c11038500010703241482d9210030350003031078501d42d45c0c901500118210042d50340b910603150101d51001c40c01e1000503042c06001d400500c1400140040c19030140000d4010020307081950810303481140488440c4001c076000e604100d0041172210115100140a461007003681c000750003c100c080c00c0c280000d000c000e0540744043c10344900f8071a540512821900d5480001e08008038504c2c0448014150203402d1104074090301804400081c9031112039400c43c00e0350010356131180b81c07a2003501c0c100c07442800300181d140103010030081c0148981d00c030047c0719001482030300c2c0858507203000c900261a2298200324540107100d1a41001d00012288003c20b040d01d00350b0b00650300c4c1d454503620481c40c042c1059201c0d08404a0142840b1507802a030518a201d540c1c110b07810f200380d80c1c84000483e02c80c02001301d1002f108506950f507240044c0707080c2c06194003100c040c004d90521540c0e0301c0c8090954104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 94698066 1250 94696816 94696871
    0x703110a0f0b070210020f061504021e0408070b030f0402010509041407030c0807020309030a0b130f05150a0b010e040b060c011d010b0d05060708070302040e010b0d050a051e0901 78
    0x142da0021410815005d035a510068005400b4040241481c15191000180315001c175260a00d12419280d03a03d42c1551150000b080c115041c03c3c000d40e56a800a071702c20300130445507104000d40010303548440700c11203101c2c0c0f54440780460580c41d60f40c01034030160408904180d20039111170464806500800b50540b062000359008502036080f010081e141500240c40b007001c640040141541e152400140c510300341d40e100b01010203646e04d000c1950400100090700920380000d2500d040180000000c111506d140a440314075084d441f0300c5000001c40d44001705850104140b482c28000f1443c1990201841142c050962464020066015030071104c1d03192003220050008ac810100b0050244a00b08102034140c561219880d00c0761a056507401d00201501e0030403c803240010090303446030b010769006004010030381c102541c43e603281c071100360000b00c038180c0f0040c41c144c0007a80f18009801528046c0d48504110160480f00c5044042c50203070040032203010359228948040021244200344601844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 94699316 1250 94698066 94698089
    0xd08060a18050a05010806010b0403140c0307030c140108040f08030601021507090801050f010b030c0d150f030b060901031e02030a12020a151401060509030c120c010905040e0703110a0f 81
    0x3c280020004440c0c040e086121503910134030041c00f41102403002c0303405481c2c1058101c1004e03014001020325101c40c03c180940c15000b0b0140002c00c01289100e4182a0b40d80ea22480181c0c0c0015401142c1d9844101c0300500140c0141d205180030444090085800c50350610603a0103102107425080040c81c030589503400050009a41002414000e00c20250002c40e407561100140d40b5106004105010241121020120010300e842c0540d010b680100615080c4c02e50804401e6a0394040c01a20b00c107a100c00d50b40e911102c0c001031807a240401c580c40c107036036010711010028044250150303991000403008980610a1180d240d0108025a0224032182416402015000e105203030496088040000c02190303181082e0b0b14490956030103186038152003a52400e03986400b4a0030009203019200d5550507048000c2d01040c2c1c207036a03004107603510200d0081e00d0b2000c00070350320028070040f50400c40005956422403002072000410600d090002c48400802c840b01709a00e1b5003071000c5410f07083d0b204607603025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 94700566 1250 94699316 94699321
    0x21120a030e121306020703021e0d0b04051605030303040f030e0d140a050f030c0705220c09050a12020603011a07080c07030516120b07110706030515120d08060a1805 72
    0x40c030362070032040031304560b1001d01100e9145038045800c16010140c60180d510003100002502d03281e4100b01e001c0150800500c1c44d003801d09040c11a158448480300f2103c0051240c400304040c140001224041c86e4041c1013840c903c005610210741200b00403241d16406400d524003c0042402d55225041141c03080015207000e02c15803520610749004a245200c0d2a0401e01c03000c1000e0401042035000c441081d624012540000d100d4140514240100105410314280580300000c1c0d0050102c01500c005640b00d135042a15005040c90340000c1e01e00095009008100500c82c80034110000d050201e00c40c0405c0381031040c59682d00000c0d0304000d00b500c1c032a6021441c10014047c0802220811402511074011a1800c01305a52104840681d014100c20f00318404194494450031746500da080078601600c014a840c0c000c01009080161340502e811a6162920382c014600211014404c614240040c1a2108020340035101004c0040030558030410071807001500ca04103811404810000200008052 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 94701816 1250 94700566 94700587
    0x7090c020f0f0c01080109020904061a0339160204110c1005011505070203120a02071701020a020d180504090303090209090d020309040209040e01061421120a030e12 72
    0x41c0c40c206012081c0d11602c44200b8030390b040121740f81524500700e40540ea0740d1480000c40c010303190381c1e48a20240d8000301c03403031100b00c034a00c00698003072103082d08415034020820502d0f9001405814150a02e5180c900c1c000170101c003840b0007448005920368207101c1c442442d0700090100c07002c98070440000c0c0c80c006001d4281580500081e40040b40d000010001075050200c840d0320b850683c80d844060000010b040b0040d03640c03c0050720242d0840c0401c240d0b440c88a82c1c00251940450303c602c1e40ca0345a404101e000e0780c0011300039500e6a0000e540103003c4012482011101410004994516038504440110f420b440d1805a01200c600949000c00c1d00034035441481010b03e0000c2c803258480d0001030b0b10319003203640402110b1030401e040b5000342e10742c5101e80008005000c104d00420503586007044c0003e81c0c004048981418143c00c950240714800c9500502d20088420318540b48650080d00c28911803140200c0500300b00880c5280002e580b8842a50311890509944401210f948011030707840c280 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 94703066 1250 94701816 94701823
    0xe12011506030e0a0204020309010b041b020f0606130902060f04031b0b090a030303021b060a0b0414010e0105010c152f0c06040206301608070509040e07090c020f 71
    0x1007600e482c2c00c0280d0b12080360b44944581000c00001e20580c1c000000c100010007d40001a2803000100100a1800d40c0100c0c4442034503109824009030040071940c0d5000c50001c10781c203104002c0030f01090303120626249e0720300c010310110340100c1c1c1c420024003820007680840000780002d98400d6240d0b43c9400b6018900b0441300300f0a920000688908114848881e20b074204264212540350801607111082c0c070702070700040d03041803074243e1491042000300300c0b840e01c40341c005241348141502c00300300d0360003001d44c04061a030090040002076148000100081c0d4898603520182c1409000742c40340e484540e5425070251159030315629200c1440c818000d049905400030175441c2142801c9640c507004d1001d2040e51166401403020f48181c1c00403a0002400c66048041c0039101100e680c00c2440c1200302d00f827001c082c1d00542d03a014000740a14405010280643c0d03145000d5519615070606009000c01048058210b003c034004160141c07000004041001d4054544050b002c1c0c2c0141900f0030700c8030001883c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 94704316 1250 94703066 94703069
    0x30a020a0c050f180a020f0f04030b10080d0e0d06050f061f2109080f07030305060402130905040204090b130201260415020405060a0903060b010f08070f0e120115 71
    0x3c02d0f6100c0749080c40c6607494010a50412452510702403040d0f580c541c108000b4000c1c07564808030341030300080e0400040c440f1030040c0240c070f115008400c05504d411301141c080c20050f0045c030115600c1940c4401c03003039001d001424403009000b410f225002c030b12740d6207a00c1541c0083d00c01c0c0e100c8481e00700078450382e4170b0300c0d83c11903591007403000c0b62009003807848000500302d0000240144400180410a04d2007004540224000d550041c0c09140e0301d05030f0701ca400c0c036154000c101c107070006403a04000c00c034a49407500844500c002d405540c0650103080000c410300404000d08100c0e4019904c1d400c51000035114444180b158924101d40314401000703000150400d20700078040406000e039001401302401c46080000c2e085504084100c02d00d04124803210002c0c860b80d00442d60180010401041c00e603031140d00441503038400e035014000d4185850055445440f98030411001c5041180000c0249101e0500030300110400d1500485030701a600200d1070b40385011a80e241340d651214100010504084003400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 94705566 1250 94704316 94704319
    0x70f0c0b03160f20030f030106050a080c0901122301170c03010902091b0c030301080303100b0a020604150908040314010e0a030f0503041a09010f06050d11060703030608030a020a0c05 80
    0x1201e080e5180000b030191003c40c9044d540c9918403241918a88010825558034402d40002c2d00d80d01e586491003d4042e0300820f099900003420140001d00c03112440c1c09a46140c1c0d81a181d4803e14103202d130540015001003551071455407101e40072140c3e8a0783da202c03405c0c020204480164140003a0035021030030110414910b0780668103000110005844611269a00801030001a1030038220781000310360500c40d9062255640c44044008240084048000c0d40101c1083d81250300b0b140d513800220f2460f0151100c0040580c002e580041e001c00c1c2c0d8040408008180d420002402d24025130300c2d410b85030010307001613488c1d464009685021075024030529010f022030704000c244551003560300410a0020070210000c00c40b0210100701004181415001000000030504219203800d103003440c001e00c19007403090030040c00c0800008171414450a0380c1051a0065800313102c124100c42070284a50041d0350840070107a469500142c000014006441484a583d000c0d011140c610308107101c01484542080307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 94706816 1250 94705566 94705577
    0xb04091505060a0503070909050c0a090501060f082502010b04020f03010906050925030f0e0a170306030c060f0f071b0905010e130f1211011503110105070f0c0b0316 72
    0x14443ca5400040b01030440307c3d40c40020420318158a0301d541806403030b074071441c3c00000341e040202c0c82e4909a040541a5181541c03442c2e51003d10b0700046031101c0f0180c520b0f5890141c0d03580c20b41820f03049902002080c00041c000072400208003808a402ca80c460900032208150102c0180111065401b42000601d4103d07469071041c04c10b120444d080000d003110404041445074500c001090203900316540c120120402080041d400414444e01d07500201800c8818521174440c402c1c4551110781524041e101c060300522003108c2076000d0004943c4407140420f4180420b01502e8100c6c80300d04020100306100701c5ca140c012200c0607240300d070156116007250341d00034100b100601810f14092000f03a407001c40f2501210916889090035030b50134500c0f00e00a024001d60784000d5001c1500711080c0e41d185c401181c000c10003800f600301c1000c00e00c0100d00006001e1404c8280c1c0d100150310500c041c2c000103018285103a10240250360310a1011000d40c003150b100807000c001c201c0120340115070301d100e02c080c40c00c0c075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 94708066 1250 94706816 94706819
    0x70b040b120c3a09060b040b1e060f130f0302030d05160308060609040e0d09050102060402060a2d0906030b27090a150e0f07030c090b040b04091505060a 67
    0xf10481c100d82e400c5401443c0301005809401e10224000c080510741c4000340410075a0241e0820001403c4c802d401c50707000301d0400301600c40070b0904061140c200b40303442c1800e0401612581c10000355a000001003c4084018003010005500c014000c13802401c65411042d0540c0c514414582007006d00405142417107028000d0b01c005800e543c5283c605c3c036a241c540041c29903104800100507014048007140c006260007554002d80c5000034181c0394012580e09c5403460740b03541f03100490303589600312002500803a061003640e0b2014090400840d1007940e00c141c408402e1007480c289800e080c0e400e4180c40009003101010808180c05104030b0040302003d5403800300c00c2c884610481c049504085201c1d418641e000b00240c07040b24140064070146034003141000300b02c0c0820824001800d00d256045a00340545281d4500040e0006014001c4070362044040880a01d41030484004010303024400390041d4942200e40c4095a40303202d060b04080c42a100604003101e000060411540010300301d038081c0c0d110000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 94709316 1250 94708066 94708087
    0x1a09010e06042c2b0c0611071707020103050c09010f0e2202031015080c030402010201090b040f0605011505070f02240c06090a03081503070b040b120c 66
    0x2010741e00c00070954000c02c141600b0031903041c140c61094000001c41000000d00074040601103054403c601c007601e540349495404103180d020f60b0030341c20f265801088150128000088480d003188401d640607040c0203080c0051521404d5400b030111840384242c907800a045801c40d82c242c86007a0300b10307078a60300c180d040c2030050b40080e0081d501c2c52150780c140060100d40c1c51840e81d0300c0b60303241340020100203415860825014150b000e50800c1d01c504004100d008004600e00c15107051600c0c0100f015590101c0035200e805041209620203801a81195282c0c0c2401d03002c5003040d840c440c0160300c41c0c1108e0b440c500c103a0030403808851041e0824003121942046032203099a00005607016185c000c910012000c010740300140040da09002001d84055000310000502526000a412800c070b0b61801e07aa5580c2c0c2d005103050310b542a521004001c43d920501003121005050705c03501d2103d00142c219000e503902ca0900e2602c0744c0269004980c00000051503141c2414160109034200e80c1ea48607480c1060300041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 94710566 1250 94709316 94709339
    0x11413020105160c09060303030b0303030c0403080c0c03030304030e031009020604090f02040923090303040309091d0a0606081b131806020406080105091f0b03070c020a091a0901 78
    0x100103070400c500800c01a10803000c04124402c210342c007994640303046540d204824080d03c8244801d0f0301092404001103103904021007200e02c1400c1d141c2c040703850641180d40381c904640151101401a125900080c49c0d103440c10801140900e00a840c0c0c1e0642e01d05075402c00d46025802d00070007007132a0034403c084005840d1791060b981a02c1c060940403035040b1061900d0701c024000d0764002e402003420521880c1c07851542c0b42500306000400c107805440d99441e4490983d0368403041c0c60040008035030100401c49500c4c1c55016200e040785001c00700101506803540c192800300301003800c4e1031090b0b0303445040183c400100800d031150010040c42c5804c1d030b6900c10004100048420b05101011f40300d940100c10003006981d00e4400c10741c070080442d1601e0f1140802000001c007401010301800851003c514029104c0907403001841b100003680748614240320b180582c0e41c20160840c001d0200c0558600010f80c0c070202c40c100507100381c00c0700260801c1c80070954040381501c00142c6000300d010000600c08015200c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 94711816 1250 94710566 94710601
    0x90b0907050c2a0a061803080a0507080d050603010c0309030e04020a020c0901061d060c190501020d0603050a060b0103290a030204020a110c0f1806060d0504030906020114 75
    0x5003062a00c80382c2854515043c40d41e0304107034400c2186a0010090202c401d03124421084406a60180780315444540a56024004441c880003000c0100002c00000d4001d10091a2403840c901d085414150941e6071a110764001f80e0010084175200d03007c01c0400c1c03c0034810720030030020919040c0076011541e280a032201216001c0070740103507000160820464000c0142d88800b04000c0d04184066941b003400070081801e9010184680c0705030420401d4502d00f0500f0b8070740340d480103000341c980600120006e41454a1004080b9039070354007801801a18010362080e14002c500443c05421045003910b49482201c40790609541490302c1c00406034400000e00c41d901d81803102454202d04ca10400100056100d442540000c1d88140001014a1200c0e03015414021341c80007841110302c003d40b150f041048516100c1203c7d504500d040c1e021122911a2411080d00300c14083c206c14a802d05809503401a20340840b01a008640d6032070007000312941c24440c403000f1503208020b0700071a0500c40030b1134054004a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 94713066 1250 94711816 94711831
    0x20c0f01210b180405010509010603080406200f01020c0f0a0816110904062a140a03060306020c010903180b040317090a030507181401050909030d050f10090b09 70
    0x50074500c140c60300c0e6030740301d4164a070340100030009590046030701a00841046400325865401d1070301041110780140620b10a4945c01a849401d007410003000310340d00c1842c0728407070b41141c0c0b42440e10b452543c1d0501440400220f40000941e8801004030920b26151540c0d1700404281d000d07080071030104134030906448180c840040c00300e280500e42d0601000348201603003d694010034060920081000960040c0118809110f545800811124000800350703c2c4011640109010802411074284000000c204002e8582800504c040c2c0701d458102c01c1382c01102a94075269541d8411b6014160000e40c200508100c44048402940c20054108443c1c00f952000170807290748a00c0314201002c4510940308180307009400c05101c6566418001e40e01c1c09948580904030511260042008016004820001c84041056030240e4604400e0029400d070040a0010703074002448035514056250190318082d450031380207104c55050102112030780d00c04a80c00040041d02c0d01850400603100e1036030f003076400f404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 94714316 1250 94713066 94713107
    0x9091413110109031505060f06090f09060d0b011509050603091005070302070212100b030a03090509071806030e100b010f0c11041104080f0d0206041104021207050307020c0f01 77
    0x94400590f010895900001d020303104a04030761000302c08540c0154802c04080b50000881e0a070242800400d04c40c0c1c21986800250f00814000c103400e10300b407001c3d0080d4002c1d110010b8400d6584030340e22560001c0e0015130001030000c140b4542c49900c212000050502162000e1440c1400c0c599150707200b03009401540030f00e403a24006400c150081c1c1c191403000350090100254401240d001b15142d58800c101c060f24945001c02d08450382c180000d809600340da243d21503030b081c64103102c1040f0300c1d014020900000c00002e011a05000d140d4041c440004040c25103011401d025402c0200741030006034050018224034142159105a038010000d0403a0134550610310703400b00c070b50709003109826221100180c00504242d0f0800300494028002e104403100e41c02520036404900c0d0901d525142c0a00103880164048404a808502142b6a2181501c0c008000502d03040f80c1c0d000d1504121000c443c001e012580110030400020f40500c0001e1700340300100c0c2c00f421030082e00d50010b444106041103002d035140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 94715566 1250 94714316 94714343
    0x1141018020f030106030227060702120709090b04050c09040b150103060f1202040b041b11030705061006020c2e0302210103031106150111150709091413 67
    0x80c0320354102c607442006040031940d02d60b110100078000e540050310302104800d0308031031500070404940071810484401090145001000d800300320703101c000c6502040950043c0400000e8180c828443c0c0d544003407007a400078050b8605420320a0402c092021828021450b00c000c0100040c040c0c00000c2d4486440c012200300c104404004038002c09281d0400061142403400202c0c5141545070030300d142905c00ca6040c40002c0c821000e000036601d0042000280208800e1043e82882c003602d07000c032034400c403001103a040c440c0503201e65180000c00d80710715800c1c5c6004503040c04040d0f414010000196030640e44212040d4110344448400c41001587d06c8440c055001c01201c1c0c288280c0446400d00603040e50003d0003d00740300b400003000800c0c4421400308070100e1220002078400300e030301882200c2e103558035803090005400541301d0303800100625540380155843c1c048071381100c80d10a4041c40859072840c1d20300342801150300c2100d0700009940e00710410b0808010004c01d14404180320194460304581211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 94716816 1250 94715566 94715609
    0x31302040507110f16090b06090d02030a17030403080105090708220227251409090709061d031b010c050d0201050402010e010f1205041b0e0405011410 66
    0x80d9050b1101c01d80f1340a0040524902180014207080c000224031034000100d40d5894041d08461100240980102041c45000d05034982044442001b500140540b00090318a90b00c5d214186504060180311f804003209100a0591140c800e501500c0140c910300414142004041c00c2200c005000056001480380c40c080c41c220a5543c880c1c8907540a80b00b00300300c07074100c07403121324281c0110605480c0e0401e5800151128140301048031a0b801c0001c00341145484c0410110307001c0c00460841030440c442040340340f04980b20960004d10460180c1d984a2019003400001824400d0000240d00103104e02ca1075040a5900413488013015606540340034500a041801038412034a800c401410320f0103002c100300c055680641001d44924400d81c0d600e00c0c1e0110740401034450380c500c4030b90301000404082040408000690045e83c100c1e008105441c0301c002c903954609441213141d006448040d0840080c0010483c00340034209854255001c50030051a2810003a240c1c4000d5100740c602c2a18444100740d0b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 94718066 1250 94716816 94716827
    0x110409021c030320120603030a1e051605030a02010506040209030706110c0301180b0106020102130605070201020c100906081509040f03050d060f0501020d02120a050706061e030203060c031302040507 87
    0x5120340c0702440344d040b42481140702103410540c900381441043c01e000031558640481243e607400760369115030304000d45080710b000850031001301c00401e000e02005000a1455003242c10a5a40e201360000c5548412040c002400d4070000b500644c0114010b0081c2c1c4690740d00030032402c09640c0d1031328001b400e6807403da00c0c4900d00084480e455805518000c95641118a00b0032039010755800340079041156680e65004900301d00c107205002c204520401e10910a00b44104c0080442c80d00520440d020040e0380300c00182403050440c018004144801f204002c82c0c1e40103070300f1583c00660040803070a200d60341c00c00b05005240c01840202004244a014001c042c0940e0a40344110501401000701b20348880c0d400f41ca04a89000380b5015202c1c281c2d448104910001c0e810316038204200400d42041090f22060340c99400011044502540369003002c2078500c1b0100a0403010308070590703122455465801032508040c4007801c10310309a8420020405820481c054450040e0b50503240010b40741e032940e004545 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 94719316 1250 94718066 94718081
    0x2406040306090606030215070b28060602010b0a0906080307030503190e0d030f021602060a0504091401090b01020313060c0819080907090b0d120912050307110409021c0303 75
    0x185450314a160041c010380303603c40c800340d80c801d68030b4800c811601c28805020303008c2c5d414010b01d9050200002650480c04040561581242005501c1c038464900c0e00c03907003910400e03040300005030340d1280040030302d02c2c000900c90010302d46240b04000090800c400d5603264400d40700003506002000020400203201c80600c660301ca00e0350b44041088a5a0242054440d141b103074841000074107000060508142610885007040403614409141042c142e0910906801c26150201842000e0000081c0c4030101d0091143d02d00200d00c0f409190742c1000301e00011a0190030340d440c1150300c00c0c884614040003080115098644e40d05008200314160b103401e050521a5000c042d0b0a46041c2009858841d04001c0c080e020340c84041c240c0e444c1c0b0340c0ba00c00d4201100c5840b004194000b0301d030f4081074082a49030912185003055481c0031440c00b42c6860212421650b5a02c2c225184d42c0001040c0060003401c2400d01c00005040380e082c80290307540c9d000200b024001550142c4043c40000c00305041501907400246c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94720566 1250 94719316 94719323
    0xb0a050a030501090204050c1c110c07090506150316030b031009080d140c0904091e050312070215040336080105090f0312070314010b041d24060403 65
    0x400d158aa1034a9406452040c4d0700f28040c1c0c2c180000b1400014000e4280d8901000e8866000140c03841d108481d009410403482c1d01d44000010040014104000c6c003030a0064240588045050700300201800405191041c40701c02c030b003409000b402980801d40130b0781600c28081d885c3c049001c51440300080e061401100f50904501d1800c882801081141c1001e4611940301e0007003049100b6070100c0903119003004a564086419003048030701031074074243c0e104d21a038a0240c1203844641d1914041e0a0ba2207100040a03202584041001d035a079540304002c4550181881c40980500d5187d2940c61590344e4018200500740051111803104009120700000300c1044000f003290350559070301c510310180136800e00030041c0179401c00002440c50320b00080c0c0d180c545561013009500e08088a4034074112001c0c042c040301e0815032220844228440d007002c03054080c015001c40740340d0b01d5140400000a0202000010381e00810741400c200c916140c0a000c0005102c424100324000001000015100c1c400da0700020f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94721816 1250 94720566 94720579
    0xa021e100213151701061b0203010203100810060303020a17071203050603010b0312030402010e1206010803090a060216090f110409090c061407020d080702130e0106060e01020304090b0a05 82
    0xa408800c9402e80b050300f141e08090201241d005050f1044034103600d106030016039406180300400c1524481c151075602402e90030065120148103074002401d80e44250f800b100c000443c024103116aa5090009401941c502c400411449203035580280d15401800701c05048005490f50951038407002d0400c89062903803040a611264611010240042c4416140d10b8040c1d841c6c841c03084914100003412a0301c95201c064114156503d0360700444201040c50a0142c200300d0500003025400801c0210340e0203081c0c03880c061074903009444140407070044d481d4010400c40d4464003580051640c0e01480000780d42c1041800325881c00220485405000540c50b080c604410018001855402c513510400d00d035403040380d1055a19a444008a40060181281000c640700400c9001e0051800c44a01c0d0a540c0c4580065410406260000b5848110450b06516001d8503000c98404182c1c0030f02c102c2000c0c00d494141010308450910000396203001d00d00070301d800a6034880013039200e41d842141c100000d05009145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94723066 1250 94721816 94721827
    0x40e0705090d0515041e0507090507020a02030607090e0f010302010509010807111204170c0901060c060b041107050c0102010c050d0f0905060702030a020106060302030c0d0207150203150a09020a021e1002 89
    0x101401c000219800d840311802c80e16200039000c03621030001c6c51079030002c005203070303a03030410b4900401407201422a8080d0b01c12808600c0060f14107005183c8101104e49601c052140b504c0c42d40600100d0050000089010490041c0010303a004000e49000700000c1c60312080640e2030540940e50411008040309141c0b049603494040a90f40c40d0062054420710400050104030a81d0210703601c402e0400c60075405141d031401407089511400c3d03a4200c070f5020b0040854000d100c00c000c02d084034840c0e030048000820010342101400010440d0380d010a0f420710003004030070703e5000c004080f40240c00100c981c0d6500d0701603010310340c41150000005903400c4800c0d944c0a082618010307542ea4462460080954200980001c410b0b000b403090f00c3c420a48080c101b807600031440350b41d000035449074400b02c03200c800ca80150303c2c000e101813015601c144042401c4203540a004800c20140c008107078002c1c0a01c600410482e208941d000c5010103501c1410707580c41c424a0040314100e41400301903048200168030201c0c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94724316 1250 94723066 94723093
    0x90209040b060d060501090e0c0a0311120715030e0d0908071a0d0c050307080901060b04030f0816030e040605030a11100207031509020120150603120d090201080c040e0705090d05 78
    0xd0285400940120344500d50140184000101c560bc0090417400000d00710941e181810020050850b4842c0d0658446517154281a0306110725102c00100095131080c640917840c90030400c15403460103a08220f00c0c0d15103014000c0345c0e0707645a40261f000b0b090300200c2c040c660702c015800fa142100c9001105101641c008403004066810854500c4000f034071000100711516410311807081624110354005241c2410f5480b640d1240790102801c6030107940030016003d003c0c42120140d0520fa100e17a4488135900c4038a400c10003a900da13500b0951094002003101d030009105440c0d030607080b06043c1c82e2110408078200b01641400195803024109009003421062407036019402491014400d80f10f8500600302d2801002070010f0321012242150701c0511140d41042480c5005648070070000c00721101c1081e044d10241068000c8400c5070078594458040404568102c050740ea401000040e141c0c0c100340ca80710541c9101b14020300400144500020446040d49540002c0c0c0c0303500d0703003000840e0b144000b0b044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94725566 1250 94724316 94724321
    0x21e03040f03030b0a0b0307030903050409090c03020118060507110a0f06170c0a02060a09060608030c06090f1c0f0c0204020304080a030b01021c081f17070504090209040b060d06050109 81
    0x15000c82c0024a02100c0c0005454030309141003d81c2c02042c941e605640d540d0300e05600a05d4038a1041d003d000050100041c0780f2071134041c016103288582c0d9242c21140c5907100140403034508070f003c4214100c2c001c40520840754000d041e1412990041081c26100840704041890b02d44590030903102d81101102c08543d55030410049140d982c40c0f450054555078401100b020540905e244500058000c0808680800c40076004501c0715070040c140055096542c0d001da40c515807214803004629000b00c0d04000340100e0a0141401103424240681008125003442c40500e45846517a441400141946100b01510a83d201c005296028000315580c0c10203041229503070308118003200009040017500c13810741d44045001514481046a05201d0b0814942e040e00d0b03101008110381050340310703072021018407a403180d610340041c1110040d03c1100e2052010044c2449041e4004e503004508020032440141c0301d06051546c41a00080c02091301d0301e42c0800916074a0031180c0251101c0d007007200206010703c0700e6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94726816 1250 94725566 94725593
    0xc04090216050d0c0201090303080612010f0e0601050d11060d0e0a14010b220b0f030312011a0703090b0a02011517070905090705041107120806100201050f0604021e0304 74
    0x8400321120720124402c100c5130242c803100003d000484170718003000028056113144e6000035005040ca051148a681c4003421180c01000380c0f40c071207450b04031142c00854140020742c050b1001b80c8020160302003030749800c1d42118a01079203601500d00001c9081c40c00401da801085510300600c1520310849440c14183e043c240040d0441540303510304941c000052405020203c40960b00c0110742c2c18440e444080f0400078080103c1c0590003188003461101d96660034402000c1841c01d0403c2040c7d5541424080c1a00c40c00290b548110141c0400c4081f0200b5000031484049514a08485a072031100c02c4049014110740030390390070b10030000d05002c50417144002002c80f0046101040303540c0b00c0d50f164590390568105945411858204441c01c3c01642403507007210300400111144c2d549840880c0c2e0b604c5407800320f143c5001d0001782200d810b029aa217000181d5a000ba04544001e01c00c1d42001003007507a4110001d084a482680d0019419044108803d00c45c01500030031034545440f840c4c2824100601c2902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94728066 1250 94726816 94726823
    0xc16050d0e040507022a0d02041e0c050f0706020a0905190806090712021212031008071d0f100911030f090706020d08040804030b070201090b15010c0206030c04090216 73
    0x70240002c4801c5d10000d101d0192080c0c074024030110615448840f104c01c19031418454000359020302c2240903031107601401c20022802c0040e030086101c903c45001c122001056483c00304102003021042d00050350003641c454035044440142e540c000500c00b59030f031024550142d6040f0700662000e9240a501110030002c4a4007075041e10382030b5441c6030ba010348420341c44c00b60a5403446400200000b50030069040702c109903160003200e100ca071004c403080003541c0007203540b03140c2211211414804105c00740705410042c190243c0304040d5207408400440200300007840d080620390a240040c3c2d401c0d00381d228801c01040120300401c40c86600601820040e4400c41ea44088400218081011154000381c81812580300d80d000d040e201c0d40000c0101ca002c00c002e40246c0d1104428403012010844c20340c10240245059000003645084525050b40b86500040c0151039040b1a22032030303051070360480410610f40340d04a8480307039250740301e545e121054091500448801e03840070800400c064080040311040500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94729316 1250 94728066 94728071
    0x60206090708070605040b18030303010320010206060f04050622020d0e0705010203220305120d0b04060803040603090501180f03120204031208040f0f03030b0f0906090c16050d0e04 79
    0x101c81d84440c1d030340d030f6440c8070306000528108001c0181404820103820600704600000d0b801104040000307103035030000c1c1c10986035001007901801000c3c01d9121285808032003800505082d16000d0009400c00c42030f0080140141e446034000b55031031350b40c400624020075084101580041d540c5a40d43c1c02500f00d12070b0500010726084040d6070f0304000281000c102c400590040d07140842c0c02d01c0c40031800441d69419000c0503c08a004000036105000c240d01c1c1c8107507502140c0e11007000744503c5040d03401b00034000340035601d81181445080c81c04001c55055503220704020518a0301450010300504030f031400f0200301805035909000700060b880c01e212180b80a82e41e6041104080c04c5684105e00c038034400204a001c6a4003104c80c0c203802070701030b250300c00e005170354a499211064451009010584108400181d80c92140d40081c1c07600e10038143c00c040c2e00b521300c01f8443c500440030600c858405852000d02100200750440300c5552260184400c035804010355111003000d010140c01200c1c020802172080c1e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94730566 1250 94729316 94729319
    0x60609013b0f060901050921010f0b0103021e390c01110304140a030f1505010603060605030a0207020409050304030303020a0206070809151f06050d0b030105010302030a06020f130602060907 83
    0xb40c00718903001070440003845549403c8100005650903402420519008040c0c40f000c13103604030354070001c40181c1804c14004240015002003043c1100c04801401d81854414000b50010410014130300e10308165500c181984c9018074105003006111fa4a492600d0345e4050114a510111103424844103010fc101180e00c44105100192201c501c0c107030810f03400b50300c103000c01c001511184110281070700707010381403900240c0c49071034000010880c0d82055507808084c00c0d80700c0100c0414403590740141058602000b000c2d0600900425500c00a008040007a2b00820799100f9980c543d4001089183d106040325a11a0b03280303000f4002e9040b00101201600510740000e41d0f10f40543e0403107124a50030006003120380c241854201030400054074003000d0303840301000b1206644011504501500940d15402d4443d80c3c1005e202c4142c03101800c05902a074145401003006890014142032019409000940c881d0815840c03106180105030b94401c40e02c3c0d1000380007503065004203000f070041603440e068a03240e9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94731816 1250 94730566 94730569
    0xa0c12050f03042d050f0c03060c0f0c0f01060f0e060103050103170a030f05011403120705070b030408070807030905120d0f030e01020d15150f0503060609013b 70
    0x24003031601040c0a0a80400005002440191400c1d40249260b40c3c0140c4818030345241c4d000b4034244040449085e07000b940304000d046801c10544001d41002c070300902c510301d001c0c1c03412126801540b40981c1207407408100c4040340242884022000c011810081000700c3c1e9420a28540d909035100d1044a4404030000c60155486801510306981e08060034507080e1280b4040803090f640021030b1203080581c1c40802d40c000c2103150194078000c0202c41c4010650381c48800403d0b04020f1880e2040b4401141040b940002640204d19641101c2031303174003041d844c3d6480b824004614892844018543c1c0340000305203040642004002c000c1d558103550f107010701c041d01c3c04000d5075440c00840940128046d04144104a4031070741029101c1585200054140400c44a286c0b0903650038136890000008507010a0180041024481580000510f010318030221480d01c003410701d101c0a080207000f80300c006042d240f56406440610030090a03000d01c44010912001030a80c14001c9030340b01c060a1460740c0c89601c0c10b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94733066 1250 94731816 94731827
    0x1502030403140a0c02040908191110050417040305070e1501120c120906050604050903070b01030210030e15040309140a121707030314010e0103080904090501020c030a0c12 75
    0x11580342e02d50034282c03803a03a015040c103034002d0503814040001c40c00b510801038507640540c4001d113205d07880003034640300d240c82e0702d699003041d00f0003010410403080b041d8240440c00240100044210340c000242d1030302c5605182e41000318010b110400c501002a00008011300000c1400854007480b400c200aa15080541004a4940c1a80a0001e400340285400000c0f00e03901c5203e03046681c0c202413680507030034101d4006583e200303241595115034844c100011070410303000303081c0e01c10b030620091340c07030401c05546201c04101c060001a000300503091000070a580a90b000354034440800c01110141080c0e05942d090110040b80d08400003100080c001600c4007401c2440c526460700101100801800c0006406103440500d0046c2c8101600b05901c0304050000c000625440b1b00907a00441d13001c3d5040c0105203800c078103074048040d00e180c1c0d0b13004001003101c59050f83d60510040307a000c02d580074241041400ba01440d012003269010015030b41c104150400d2030600e02900c0b03a02c0003280060034070015203c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94734316 1250 94733066 94733071
    0x807050307181e0305060a0203012303012c0c060406020c090a09080703080106080108060103020a0504050a09051e06150102030724050a0204090513050c0d170c0604150203 75
    0x81401840810312807401030845a00d402c0a941180c0d1030350f41d0768080ba40c0d0b000810841c002d00c101e502c00d0140184503040c00130550064000f1025890f55140655402045001c40a0f0040c00d49828008001c190b0702074110121740b821140312901203c0103007a0003a508041081c401d491741c407445d1110400b60500800b500c1c102c65017a0023818a0307007002004e1003405e6000600343d0003c40d070344107a0107002030038100140055034041e96800c40300e9810300c0f030040d140004c1a00003040b641c1c8030500400044c0d946110714026104259004900f6071100840c100103070049410090440c01292058444409030302580458001024211407041c1c0710411041c850003103040d902070040c0c01c02c000d00b00118141042c113075900d1f40c2d6650514080e00c40c035030b00e61003180d000799440c1c442070380c0010701000501214010203801000808070f02403840031643e0381554541a000d5000e006981e078007070007400c0c0f00389081703200310000000354180c0d9260f550298050b110181110200c980d8400944e403403030030450901c25030b803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94735566 1250 94734316 94734331
    0x7110907020a0b0610050c070906180b100e01170a0f0b011d0d0c03080406030f060509060a0326030a0b10090303120f1b020106061e080c070f020303070b011508 70
    0xc10f81d150001404040d00c540c10202044c860200540c2d041f1100801030348005240c404400685e580c00e24840011950503800c07510303201403d000c2911091f82d036010901000150310306082003801c00c020010fa92110f102d40401840005201c104000907000d904000002c0c605c40c40d04000302c2170741c0e2006495404800082c4000c0300203018110540342004440380c11428090320001004e290390b69908100750380170b81c00000000c0d1312208410004a124003600001c0c007811640001e9505d41030000c00c510155030312001d0981040c00411003030092820f8810305018103219469a0b0340d15007080c180d0b000d0b0280408042c0281c40c005541036802d481620613409a9506039224564410101c60340406010b022001c400c043e07641e0072140818114643c03101010740c0c2250000300b515858141c0c054a14509079440d40d170b00c40c0f00f02000b2201d9541c80801079a103c03d110246a48800da50b0501408032000c4030002034040c44002a118227004078503a00074100c8180040c0310075000740c800d50480b031f1105c00756400fa = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94736816 1250 94735566 94735583
    0x10080a11040806150d080301030f0c061419090f09020304021302030613050a02040f03031106010b03090309011112040b07060c0507080a1b050304060c0311030711010c03020c0607110907020a 83
    0x1403140c4d03075204aa04808440101140042070040c0c5030181c95500a03030044070103982000c901c9003081354011041004190034101406082c0a0024900f4144600300303144d02d610020b035032a00380c00c600991902c6d0160015002500700c864071140f662000754025182a84102003801d10403880884600803070b8481d660103000c0c1d5055100100060b0058440a4000200c90350240000700b59204071a008000030340c040ea0b50030180f8001c115440c3c0c10312006800c044c00e030003820010441408000011a8040c0c0000c3c6051030b082d0500c00c0500b8202003906200222b80c01d000140054000c0c01503000d001c030780c0c0c003d0303804118041c9445002d6555108048000b0001a001c4c07166804550060405030544401500203c10f1581e9a94943d411540030f0340107200825040f2000e0002e0540c09020441c4400b42e80e40110711340103450302e0f01017000c1c100391001c504000c4040500002c0500c28404002902405041251143e0540c03524000c0c182803002414046c4007640c001a0340648000b480ca80142d400a000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94738066 1250 94736816 94736821
    0x40801051f1a0d020f09100f020c06070f2001020f0a05060703020306030c150a031802131d01020c0d2703110102010605030a05061e090d030506010306030210080a11040806 75
    0x41c6500c181141c1518807568000d0240c0e80d550182400100302d96501d10030050759810703006c0c0800540f41341c0700d02d51104015030203c2604805800081079800d40c8801c54080b910303200245000300039841c40c10300c014442490b441c00506120403100b08a440d44070260290341341c07400d01c0242107644071140f02d405000382d8400004585421b010b036008542260026090710034140340800030584d44000c0843c1f01e0114040002c14440050341846100c4ca0301450400080f0b4250094000603c84d4103101d1003560700b80da54860145261041130700e6070301242e4240000390746a041c014201c6441d805c102204c13801158940c9500d94140c1151040c003120200d200a2500c1c0490443d140e2401d2a50030068650541d0350f549800300c0c0c2a50200080da070581e1084000340304a00d445400200102c0c0c000400c0496486040c0500c08401c4010652505801c0303549800940c65884500403009803895910294000500c0380c840801658840192445581c1d480c2007030001c0c80b54888005050b11680c820f43c400d82e08030201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94739316 1250 94738066 94738079
    0x2150a050a020f0307090302010905041802060903010209030a110307060302030c0d0b01020304050a090e0f0a05060a0209030132010f05010f081e090601080c030606090106030504051c0302040801051f 87
    0x941c00c01d04041c0014242a040510b01405900a071030500210300e1240d020030441d80e0000c07110001d0601910140f00c440c510440030804280c05805c000d2040d803022480c00309940342503042d00c0a01000404843c0a42c0660602000c59112114100e019000d80100464501d01a000f140c3c0a00540b9285905d0180e00041480c002c7c4010190b050450108010004080d61100990005040c240c20005050405251a107103000c03102180c040c00d9400103c0700d580031502c0814410341c8084031401c00350f034400001d0002401003603408405a002c03240301901c0044843c0c06d0409800e00e0000d64200c085590301c400b403040c1e80e05568414140050000f1940c41c41c0c1510900300ea90700040450118640b4808405410004900843d041d451079407050004004041c4200200040301006601500141c01d041c40820f45c0b01d50140110703424551940e0110381013280410207119090704c2d50a400c14241180700c4003e02946c0580b00f02e10842d82050701040a010b184250f000d040c00b40411b00c52000380c60940c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94740566 1250 94739316 94739321
    0x1605121302120d03020a1205060a0308070507050402030a050726010504020d020c0a0809150a1704030c1406010911040e041e0c091b03050f0a11071b0303090602150a 72
    0x86040780c02c82d0b04900740c41c0400c02c2c1040700d401e2800c40740c1c03005600d64181c4036008244c840301c5c0301040c2c2075506010500065845660940c01503e4000b0f007007550380c0a003410701e1403404489900164025100000708588660b1650000340200b01d02d07039030b08421040e003040801381d00703101c91310b07040360366115070300401c1580381c00e500802c050009160301500b8414900300040c100b022081d4140c5000c040010692020702e408003000085c0300303290520506042d460384c001000040700483d190082081100880c0615006502d50310340c0991000c1d003a0101c01d034003441e05440300e00a2040818003030505901e2441001030030103644c15038004007000900c9030341d25285c0301030f00090485001d600b070003c038441070045000380040c5005841c1e2001c001c81d1011140c0d0407860040492502501014541024859010b1210000542103c18240c0c081000d83e01c00100e5035682c403071000001d081108164070f0301840300c5c0c1032405408480c029100c621045070344890590b1520140c00e40b603411880c088000400c540640d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94741816 1250 94740566 94740601
    0x10e040c0e150301050103060e151507080d09060b03010c1b020117040c1e03030c02010e030c0a030c030501050612030301031b030f030509120d0203070b0613090803160512 75
    0x7403400700c0010368070304003081000311410b2882804520010041c0613958250103890000e003005982090075160600c40b95140000701c102c201c0c820303c00c00340d81e402c4001c0d2042c1501c100c50341005200340c1d96041d10550301d0040026650460301c45041c26166039035031406118030001d00322984c40d00c0c0201c907114601c21403808001901203040c85150303013135403060400c81080a0700c940d11403000d0005040c2403924101c2e0f200d06201258190825003681880026800f15074500c06950a003004007098007410002400c00308050b00c40ba4008603062000004d10001c00ca0010440340918003c020680b110380521040903d442c4101e06103600070030040000920103240c0320448001a000d0400d8240c403070f0f072002c001c4205a84185e00041e4040b886001610740400c4100c081c0724044014620803110540c0a9247d004c0c080005c0c0640d0074030b900041d07594075100c004500c010017143c406c10442c10300c0c2c90200c03101d0700290f9a00c0d44041101d05007010b04c5025404503440140a200035910302c1d80e600c4403030104ca203801e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94743066 1250 94741816 94741841
    0x60e0609030106030b0c030405010608010606200f030a0309031115060904030201060312120c0e030616020309060412030212090f0625061a1e0103020a090806010f090b0d02010e04 78
    0x3c480e40040031580d9060858022600034901c01d650b403c2600b0071500759071094200c80516450032104010381500811000018184405058106c80f0071084441c10025801c3c50a8401d00000402d4020a1382c542d00185c0321a100b512144140d030000d5a00c2ea0399143c00f54480080c019a40d0003045043c9030544926521510038400810038235125914030074142505000e90010400c5440b110100c14094040c040106a06207850310091b90000c000aa0355200504034404000701d007100900918030a000f01c5014980151001e541d07690f40740004490b5000e0070310103074018007944807400d84036100e0700708440901200621480c070501c8114100601c0d5445081182480e20300840e58448940c28440c0240449009160000305540030995000c40c0c14110403026104001c070607000b442d0f008007560b00324886a42842d005840b182d558000303a070460565080b828a511a81c1300001c0e001d000d0310300c400d00340c9072042c0f41806079a204409002040d505010024081074810f01e00c8051400c0503030141020905 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94744316 1250 94743066 94743071
    0x1030207051006030605041505040b0718030c1503050c031302011d04091208010b07020102060a050c04050a09020301060201200313080d020c07030501050f01080d08090a0803160306060504060e06090301 88
    0x14980060044030421350040720403944178030030041800001d84800e251018000020f2166103007036602c00c4a00b0070001c1925042c4086001480000701842c155180619440020074042e00e4a505010b101c0c4d061007070b5283d00107400d000002d140d0032094010f0301d0041c00500c0c400c54203006540d00640b00b1348040b4050210310480006042e405954a0044100070350240030400d02c150b1450b40010800a816008180c444130200600703801030340e00003107083e8402c124a500060710f481d0140050710310701c100c0c1e000075031082092801040e40d540d07585c021412604550020032003001d00c02d00d9684070300e02545410040420600018581c94000003030115007a200f000880d2030110100380e15412078000c828409600d5022031020b0040100c248039981c0c0141c0100400704256241118107079485e4030500c8090108051a00810a400303410800b0199450f031001404d030302c1c1d18100301d429046c8440d40305820300082c00c2000008019000f04100d8083d2403081d03481041400d455018050103600c011642d681565 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94745566 1250 94744316 94744333
    0xc06020c01020f03010b070201080f070c0b2208041e050d060c02070906080a171303080a0509030109030c15050405060c0f070804030501051b0c031218150915010b03060103020705 78
    0xf10007a000350701812580711819142d6099000050881c000241040b0001405505016800350080c1e104007110707901503291070f00c0c0ea4400b6090014040000d150b000032140091012040100010180c002e0390405030421840c4290a0500614084140b0500e174001541c0003c80c0046001c40d000b9582041c0c2d0350045942e003036918844a0100d454982c0034000f40c0d0041e407071200400c81030700148680c6105002e4114203000c5407108210340b9006501c801880c0100015076654858090015a045c140005008000110103420060300c4604d100d9421521500f20138402103802121b8071030036000c0ca4110b0020590b07a550481d4617111395102443c13201a003c02401a1400945000000e001031072003007001284c1401d00302d600d4040e05115850614440d181030049a40303a5200100351038499a081d04116140c0d00c613112400541001e0190704401400f03180c500d04900b980c1418030f6801191010708641c15001c143d42d07542508003007030041c203501040c2000800c40c158420f8003d001490300403000e030355425 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94746816 1250 94745566 94745587
    0x40f12051602310c170108100902150d020a0f020604030207050f01050d0f0b03010c110a06020a110307030908100e060c0912030427020f0324060406080610090302010c06020c0102 78
    0xa0b01d841d0f40420301c035407100e82d8040701c1980280400800030300800328844c45c0d410300b00c8940e225904e010010800d41d03507846200c0155500c801e42d07055100c140c05a16640d8036808a036200c00307544030030b000344042040041c08628040c8009140303485640c040d800f03443e03400e044c4001c10042e1020091014108030040c0011301d00421a441110710144841d1130000d079440258040c50b0071b5900d45c1d1540400d201c0d09041c8201206400715606540e00c0d4007240050b40c400041400703941c800e2028081c19040d2202152071070801d600122481d082d551000111040c201c400e50603c400d0319070490b182e280c140c004d08045512004800c001e000241d500500d80444418215501c0c0c1c07844d041a070000c1e8554075254807201e801d00a0340301c500001002c0071000e41c030301703002c0000e00c00c114400903000445030031a1045220018403501c40c40050a00010a582e542d540d464100a00504098440601ca080084600302c940c0e4007442c610f03002c0740ea0603114903451400640307440000350000010015195020406110761 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94748066 1250 94746816 94746889
    0x10f05090f040222050909120a081306060308031509010b040e0a090807050607090608010f050f0301061502010902010815011e0306090c080405010e01050702060c0c0312040f12051602 80
    0x6051441160305404d03443d0000700b02c0326600103003244055030883d002005684a000044a0410300c1c18100f0b601c0707940320002007002c03102012070080c2502e0b00d00340c400700820610500450007850b490440f1041d1020507000c116105038284103c0801160030030041013a020306040441d4004541000000c03070b40210f4407044d100b03034451f0700121039541100d0200118243c00211002c0900140c2c40c01045641c18601001d031741c0b903c030b4040c091259851440164003580c013500404081e00c56020b0301000b0460368403019018088101e4200d01042d0308000280c48010600819528000d05070340d107082c2d480a0740704a10f41d90003540c01e01ca0405460380780105494034075000f844488500c07961403070721516040c1005030031140e11603064181a41440e00707000c032903580012165005000e8440c2c059480c407100300518614815a403200285d4110041004280304420040e0203406000c0c9070740d9060b80241c14000c54070740c031030a5400d49407100200d02d020301509046410100d20104101001e42113141001c8600d031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94749316 1250 94748066 94748107
    0xe0f03071208040e0c09130203090c0103090809041104050109050105090a090c1b0b04141b120a061a0a05150f0315090f0a1505010c0f0515010305010c0905010f05090f0402 75
    0x817003200042c40142a08141c07403141109120740e1411401c5090203840c280d103407018800fa441c101a110210b120a02900b6401c0300c19003c801481004003a400e094401c0c01d50b086803007168049144088000b985500907400c9944404004050781d600302e04111003103000b0407070f4100200c10444a2070103420030300300b460505d0304854051003031500289070501d0640b6411310300200c07800c016000031f0100110b205250ba441e0305c429404440d07060307144000c1005546407403520907020700901e0602a002e0200c95428010000942003a20307a01d5500751144c05002081d000320840f480030080400049105c810000007842d00105840001c844546900d400200d0207101545c0541c043c802c10028021450342c00c0c4038402c6111580d20001003000d15180004c0d205410140c07002e8800842c0c00388501c00c10005000e10b00349040f14440c080300c03650310b90030002d00802800c080a0301140d01094046a6580124200b1015030342e6584c0f100d01c6e0500325003d1110340401c00c01d0b0681c11039024852a08000202e064829 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94750566 1250 94749316 94749331
    0x1020703020a0e180706050304122d050d091110051e09030c060f120604060807050108040f0b04030c0501060602060c18010c050706030e06010f120f030e0901150e0f03071208040e 78
    0xb40c980c09c0904010311001d01010030308041c05412113107104400c0d00001c4220030900c507042c007000b8034180c00405440d14494040e00044e0710340303443d282e002088100c143c80e110103802654020006000a0710689240c85030310030980005401240c181031000210000b403100410145c1995802003618001c01d0313040d0802c0c81c1f00480c0d00804242c09924103240c4c0d11b01548400112001d20803d4500f10704141c56000784d0003002d0401000f840010305211400b2560819542e114040d4140d03841c01d824010038404080c4800c0383c0b40d500304a40041c9152002070240d024441051403503103801e921006d0150481a540c50281c103002d003550b03404010407001e1049000a003400d850100b888800c01304042d0400505812034440220400420300690600280000700326910029104050b4010b050075508104601142c1ea884081c1c0e600100d141203d1b01c946200620007038a0b82502c2205190400601040d080000d940590050030204210841e05d030941d02214001e00d001d034601515444185907081c0110381c1c41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94751816 1250 94750566 94750577
    0x509131b05010f0e0f100908030309010501060f081608060112060f30031b0f050c01080f0906040b0a0f0e0f060601020303070c120905181501020703020a0e180706 71
    0x10000341d40c115040c601d01840f1440e240c2c115115140000c0c03610300c92080014000c0303482c0669522403038000c034191030190034100110780d280c0c90829000c501a100c24040d1a000400003020514264060800c407401108492160154125000c00843d6600f03401400a0704221a02c2c501c1c6090844503c40c100203000c1280e055408242455941c035070381c040000d04060028000000905600e9400300140b40300341e07151401c030b440d4404041501004169562018100c400f015001c401089030000d07410b844030000380c80d081910f50f07a0036202c1c5030400c02200c0c1620340303030410b078005130006805101c1d46900c407141c9800000c9205176a0300880403a030301410007600036408100d0458150004001d0694005800d1005501d1458440401002920a00401003460a041d00e04001142c015400d00c0080e003409041480c0a01e009540c40381000780980b80452842c0340541c51042035440030500b0300640390047c2840c28807524140c82000c02400040240e404540c1c0a00c203542126000d2100301c00514040c1d584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94753066 1250 94751816 94751819
    0x10806040305071106190e030307030801090b0a0b030a06050901090e0c010c02010201020d090809040614030712021c0b15030c010f0c170a0215010603150509130b0901020a030b0d0c0509131b 83
    0x1410404d1241400d600c09c0d4401d100300c00009030300c002c0ba40e055605086000c541c8010304804520350800c01d4020700a244808410010a0b68079944407008440084036540000d903a41e922030030459101c2ca1450150350849c002d038001c40d500a129240000e803040c800146409a5503031010304940300c003081120302c0013000071140036070f1600b8041c07007000d030280300541144001c14000007aa212058845c40300310380b10400c9840c0c15992900c5055040d000c00e000700d15058051440c085042104c11a0107070f030210440480710b40da500b80000c15051a000c1a124031074416200c4c2404d036000d0f420307040b00300c851030100e40c00d4844c2011007078003401c9a1450740c0c006103429502000c8042404005810000800d86043c04d8014296045001c201c1126801d442d07502c0aa243c801c0a1070101c810204040c2007461503200744820208154003c28a1001070341c0c08201d012900010400c03c40c000c100041c007814a105410f01440c034207651025005044004d440c15200102c1c4d030781c5480100d500313150384041d20b12001e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94754316 1250 94753066 94753117
    0xc0e030f01020408061303020106031e02040f0920060d14060108011205031b100e0d1101140a0e190305041d0405070303050f04050319030314010806040305071106 71
    0xd518140964100290b00b05400c182c404c6035210310003040c4281c00220450b40405160003035004402031500300d461641800c0c424002d030402c005400004078007030391421182c1481c0c111184550081c003a4800303501c100402018907031000120903407842d541c0c409000c000013041e00070107110f888032140b038090b505c810300c3c940300001414103070050b0f004618241101c450200069404411150b03040c043c1c00184910844400c500e5281204400c020502c5621f0029012000e110008070441016125030760142407980e18800795081e15400440c45607080040001726120381541d420201d2405d01040440da030040a4054840020f0f05151059001c91400101800f0b48009104240c010410155000e035140c1402c0d07132120b07941c2e4106e20024041200c081603070700c00c0303407402d100704c0c0d00270701000701200c2c00c1481d5403807904c0070a4401d03076085010920f806180756000040e01c0c1c0641c100c92500c0050021640c403910301b56216800350908895082c6403a028007800c1d590741c406448150340300030440b0300042d84101d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94755566 1250 94754316 94754323
    0xc041805150616031b121e0f0509060a141b0c01030c0c020904110d0302070f090c0203070b1b074b05070801020309030a0e0d030507020607020f040c0e03 67
    0x114460184070100040380c650b0744a01c03543c484072945454030340362107800c414952102460388800180510b1041d9613000000c2d6104180c00701c816000c00307083c0c046050f1908182c5614000b161040c0c0030410074880d42d110303850076001900c2d0000c85414082280c01052114180c0ba0740414105074078070054280d4404042e40c2007180303120f4a003007800d041044450700c4001401403402000001d2081c058113002400700014246d42c0703050181c0c09000341c2006085450065290480da000c2c074000e85018520000d82c1e8040d40c002d0301c0748180b564001e1441c06c45140c80784070700f04c031005000030440310001440714110864040203000c0c2e0703402800742d0344032080072240e200400c1e900b4125030b941084241411087c0141180c00000820b1040d106204200c485850041d051041d198080509548040f042160100300400185408001d0b82d0303c1e00480e4041c9010840e568840b42d0004d00001c0c424800340300103092000090060600091105c4204081e0b2400101500c101c055948009010f4403041091828100b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94756816 1250 94755566 94755601
    0x60a2d09140f1006050607060905070b04091d0c0603060904030513030609050c0109030c0b0c0c060a050406170405060f090307020a0801020408160312030c0c12020a020f0105120705030c041805 84
    0x10f01e0700b400070078a418005070703603801140005400d15a90310348502c1040810270180d4024018013441644590703951100d50005d08040c01c0c00c1000b02c05200d1038046000b00803606003044c400c010201d5086417905002e0146064008108a0900500708080904550051421f81c0114402c1c040400c1d4041d841c036040742015954000380341442948541440080c2e00c0714003c10580d6205142c25403941e0442c4c07803007850b02c2a511701c05604550001a101c101c9175112005106407896034650803501041f880381c071000703c2801ca82c050000d4000341c010800d000740c00000c0642045000c01200e00749405500000d202e10709903400400182e5001908001e080380c1400034126034000019030301e0304149582c59001010051001100404d81d4444040c01d5080c05030701c21090158000c1c45802030383c600104007958030001c4c0e0600b0b0340f04014543d1683e65943c441c204403000005803603004016603c0d8000b0540d0150006230800c03802c1d8006000108842d04500031826003030390003000208460521001c40c03014034051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94758066 1250 94756816 94756843
    0xf0138071a0609191113030c0b070510020304110612180f0a0f03020111070b01050a051f1409062d070201020a0f08090d03050705060a2d09140f 63
    0x40d907041000c2076958510941e40a11403001030b4038801c0d02040200c1c0280502e0030002940039020904010028040c60310009a0b0711a80c3c0c03e040f00c5d603c90080341ca6138025188010141e40c04002c21a03203241207500070f550003500c0380089041d086a9030300064150340020480c8468920f400003000080003e001d2030342100b90700c01e4040c2800004580a142c0c039413004e501e014102c006900700c030004141c401d500680300480e6074005e00e43c0344c81484c41c0c5420030200c00c1c4219481b0360f10045d408586890017213800321f55000342b00b61000e426124210f09581e510365481c017002c0d44910900016042d611a1b030001c0c0703603040045910709280c110901ca500f5107800e2050000030041c20521a110050343c000035034100c0240c00100b200c081da4000d1510340c850340b2500707500306d820000601a44007015006006480102d200f60284d400f1a0717a0200f03144200c071340542900b02e100082c01701c2c0071420b429a80541402e82a012004202c210f0303035844040c440c5101d001001602c3d80302403040707000b070748050041410a090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94759316 1250 94758066 94758113
    0x60f0c0c090108030f030408191709010212011415031e1503030406120e01020a0804052a040b010201020f0304030216060903051c0201020c010603050303060411030f013807 75
    0x1415050f82d038030300404003d04a1801c0000c042803e1010700415140c810604501d103c05030b80c900c0000900c0312500c0f50507a50b40f0010800802d510300e03418001d54103103c4400301d925609a00c0c0400c14200480f05e042144c0e080710400c1140940060040c00031441181d0207000c848008400c1c20106480400091204540161000040400303a5011040b80d04841140c94080503114000c012a001031108845c0240150720002e210803c2d103030040c0c8120b1199010b0005e40c2d8040d50511013116001c1808440c07041d0340d00300300860507140d28251f80004419401032000500f002078040070400190710039541500913074040c00110f10071100c5440c090b0080d201510300312020321b14581c0c44039550400700c0c08600155602e5184040002d20035415180e03250340180081c0080d83e0349081a0340c07281e20541d51940280d003410803a48035600c884040701c3c041e01c43c411140c0c2c0680e05e0308900104861061a2204a07098a01c0f0326404100e06e513106240104900440c250352005103140190522581840021201c0d2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94760566 1250 94759316 94759319
    0x30f04240f0b12031c09020a0e0403020a140c0a1a040e0103110306060607030c0618060c11100b180403141c050609010e060108180d020c0f030c0a0909020301020405060f0c0c0901 78
    0xc0f002050344880c0040c0072400300d43e40200c7c3c4002030441000e03070011000704e00070100300000c0c143d00003442d444030ba00609088c80003008004005841780484442540c002030105400c0160750484e0340c0036820418131180640c2482d8964407000d0581c60280c1c4282c9a40d01c4a00041e420b80c607051100c1a000b8030102c0b0b15038a840303a40c0c3da01500e107043c1244080c1440c1c1d034501010303180000107004150100d500c260f0420206030f500e0400303001c04d56045100c41151003001c1c8441041e0b09540b00d40c02c0700500040c404170320b488907038208514018008008804110701041c0d6154074128040291001560460405643d802084008400c07110002c10091003030b510300c00108001c400c09039805410031130030704e4110340b02c1d541d4030f00440344000d00417050881c511482c1d200151030365010400419800f811111445400c0c042c40c100b5541301c10f4128041e07440048141c00700003c212542c00000c000744058000344c14550b03580001095500080c051040414000a05080d03010052000300c1d16584125000301065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94761816 1250 94760566 94760587
    0x909070305041a13080705030307030e06090709050606040504090308011a070b0a0e0a0206032412030a05180306011503050a090b01060c0213060b040303090803030f04240f0b1203 78
    0x10080000f500e900d040e20303500440c3c0e03480c0f034608211071100c2c3c0010409541c3c0d003283c030701507580e60b004442c000000ba2030700e50320300c040c4000819151b01882c0030070000c043c168149040c103401442d002c0c1c203440d031040c4200000a0280c4890091005490094540d07a0040d8501300140420886d46020244d0f806810445440060149048a80c101da035000b40041c0b14490088100d1410452078400b075440f450201c108904405400340d41c40543d80d9004d80c12007502e07000c0f4140300341d07040b4045001c500c035001400420000b501c0b400241c001135132004124894542d600011034284602030300b160442905041100b26502e4050007040e41015003240b08000b9aa15501c1c0e021140c5810b001e0a0104540240c090f420f40d503400380c1021001180150401c15150f44210818071540030b03110880200f890780000003162203010068900c10080030442403417980c0c0c3c135070b1124462494542c81e2090302e003018001100d0520705101301504500348000000c1c51150314001c224103480380000c0da130b105900c10003004488 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94763066 1250 94761816 94761833
    0x901180b03041412040b0304051f1d010216110a030b0106030507030c020d0206040204020306040b0405011212050a0c03050d0603050d02010b0f03010c0504090209180901020918090316050102130b090907030504 91
    0xf201c121586d407903201c0d00c0d20315045041c00c0381925170070340040707602c1c507694600711650b4041403442c1e00001080e0303a1003d407032038600c0c240d008074405010030740c0e241251400030940840d80c2c0c4462800080c030f1425100d48943d1080f9010500380c1010340042c7d0f48008009240c0e0f010b11404c034401613107000422002c1040e410003036541c140144028020794003c0007140f0541c80d075421401030610b00620521840d03864019008090f1035003101aaa40b450a00c0001e00c10b034042c0c2c044510001240c0e656000f81103558030103030303000c4d40071005480800380c2d20070000021520601c00a03d800700ca0340e001040105080e42000100c009044009209074980760380460000d400100320350850b02120000350b110080324000a10300300c9001004216558074204100421106600820f81c0c00710480300c000403840c4010010100c0d04044508404a0b8803c000b18040a14924840010588200d0002d0b01d4101841e17851180c0d80c18540c80703d060408085a58a164540185420b6020013685806c100c0d40c54a41c564942 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94764316 1250 94763066 94763069
    0x105090d12090503010c0c0b0705070b010e19050a0b01090824090111030f01030308010801020906040302040e0109321603020d030905150714070302010f050901180b0304141204 77
    0x6060700d400e003400c1d0319030260241d80d0040100800800c505050b6010117810300010f00001c9401040396000074981e40d01800946902c250881c1596007543e00b86440c12040e07240240100c80109000c4224544031206800303201d100c1c0c800080046040b800c0000054400340e1103810108c080d0300124105499510480c41c6001c00c00d50180610300c49440da03031030040c010101401400511200001008110710003140e070581220f200e0303521a04035aa81d020401d00300e0050080a03036201104100810261502d031704800300301d9642000010b54801a5980c049407004043c4e21950b60907610701c0c10300ca0341042140c103001d030859500c018012150601501440240301400300a202c2c0011300b00b42c40c00d01d4860036868010f005c02901740440703c12681a40c9155401c60101101e80780c500241021010002165010869a040c1c484032a1045898425102a04101e4540e410846940c1c1d10340e451100124240000f416004c1c20641e43c0d0800d42080501c2c0e908102e920f64999004903070040020044504440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94765566 1250 94764316 94764323
    0x60218041a100c02181e01080d080103290106081828080c03181507050709021803070b0703020106080a0302030702060a030e01050a0609050721020a0509180906060105090d 75
    0x20a00c0f615100189541c00282544400551075000b0000760101d4003880e4584890154021081a030f038034802c1d15581c40614030810b00140324003004100092010002c6036034204024502d0f80b4441c0031007910300c0d40c1c48090740b0210000d4540780500200055180582040051003009000980e1080c0c1d140c0c401d880074500c81800040d04202d44a050100d0281640d80c109034550580b5956240d0522008000308500d030341a1007584c040c42c89900031050704007110445907100e00034129051800c11180f0094004070003d0105002e901031049550382c00303029800180601c04c405607211101820000c1c02c490b150b8102417001d0303100794840d40c04250000280e910040e41146c031f0740d64a00030349000300d01038802810542904d43c240418441414082c6d04a10180c5043c804d040103681c1d640c24040300c03000355266a00d465886a691f4100101c00315400400141046060140c50100f0a00200708614841c102a10307240c1d600301c2c140103480e9018450190004000d01e006428815600000342401c00c0d803a8004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94766816 1250 94765566 94765577
    0x610050903070e0a0b030607090e06040207240e01020406030504060b060c0a0b130c0e0a140105011202070c030b0c0403110f090612070305030301060f02060a06140d0609060218041a10 80
    0x40c0111301182c101ca0000103028040d10242c0c00c02080143c640d0005010b600101c000715070005100b0f091510949140d00c0e004502501e2242c240480c40721020700f141c0c1040320060701c40c1159a813502d0240001c100900440da000140d030324117030400c18210f41c0740030702183c07068504005004c1d0501000860900302900400800103a88801c03050b540a450900341c014281401c40c01c00140b0001c8044090344141c0d4907003000e0024103126000c1c2503a1120034029a4085962001c00401040c40c0b0b40c040d010342c2d4410880c007900030307889845000392600c04a6010800c40e400040030300801071403d01c00140c82c6000c0c0c2c1d28541d001341000024000550040485008003036016801c100880c04110890095400c241901d56030b50311103600405624000302044090b11884010940e0030745203104e804225040034048220300c86d521410030a60000e211400c0d41c085484040e0300c804506144024140e0055070711282c41c5d110015800d10094956600c3c51120034070301c0240d05222900c4000000e0180c00f02840c1c0b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94768066 1250 94766816 94766821
    0x304170405030d0f02010f0e0628020c07030c0902030f040303020c03070b01081b0a08030d05042d02010e0103090b0402040b0312180901050628050409140610050903070e 74
    0x1800464040c41d8001d95042c40750035005011540c01001c0d615804030740d540203108494804000100ba03c1c0300f4003003405c465011800054291188541414100259a89028005c0040d41c0c9580607130304000001a10b9810403c0700708100644d900d00c03a001480c03496804d600f5840c09261102c5500e90040c8050103150300000c1ca001d184c1c0c230501c212006a9842a0048282e503141c1c01d1712540e0702a941e030964170078141c0d05100b400f94946040c0700d00c2190400700080d480e0900000d40341d030107008050011590040c403135450b0000c0b102e0006001103000c102801d1407840f160729000040000250842c00c1341418949449480401d10032401c3c1a40540c0640780810b0f582602c2e00400e1034000c010300301e80858040448c1c0a0000345c0f038200c5800e142641218040c020f642c80e08100a16407041c07a2060200310051480c10b0100d00c216990000d484c0b48a00f031403410300f681c80708d5400070f6030080140e0344039020b4a4001c000c85850940350802da40080351806030f04180c060000700e642d2300a140102079040103404d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94769316 1250 94768066 94768103
    0x604120c11030d08040204050c12010512190302060603060109020c0a020d0213020d1b0207050105160c0e01290418050a09020a08030a030605010311160f02060f1201050a03080304 78
    0x40385400101d020341101c2c259030480318000c04010058404a10460074a0003003416256000c003a5409985140d005440e16464501006444401481940705c20701500d00c4164800441d600310840b000e010741c01900c030b6031404000b0513007082c0c8141c0008160318414032001002084c00110707184401e9040d6214491516940001040500c410403100102400000e1709005414150040020f28503c140042c1130210110b030240c6e02c5042c00d0062900050040c005400c49050044101000c036000d100c08142140e281d8070b003005085800d0300f04029524030046409041d901440502100c600746031042d80c01c007400c1100311140c581c2c01c0009544825141c40200340d0b2442c240e48090340c003690003062148240da40d112540d8898000002c0d01c80440e03d00358001445500a024020301c035140503ea1602e00320319107a0344da204071210407050b030310000721000702e10042e15158001d2a06008074040d140c0c45e45000d0700c1c0d800c80904142c20050042070740070020400107141c801560781042c3c2c06070020862404070078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94770566 1250 94769316 94769333
    0x90f06140714090a0f08101503030212030a0b06030f15033f07050106031505042105070501050f0115020c030303010e0615040603020406080601031b08071206090c0206090604120c 78
    0x100311090100215000042010340000c14000100080005200101030030182400043e01440050b02633000101c03c9203048824000640d444054100000f4910320103402240b440d0b0403c4403075250001805080c00800c884e84903c5031f40c007590483c002c0c0070803080b81010740502c500040c0da60407120028035144a2070a4031100460034034002c3c54841c2d03250f4205040c254080d12980c4800c1e00c5041000d00e40440300e2030356005081c4900c1d000500e09000c0000c1300e000740d42d000d800021410800009001c844c000800a0049a00440d064520070b00d2550400080c20383c07900300441e0000a550040c0070103240703902c1c0401943c4c1102e45501242000e507882001050f00ba04015001a07070030080010045009500359003c7c106464840c0d07507000c01c66880000540444403030180401d4400c5008103081034080c81366035080e43c4035100d0b1601050001160f40c1181c16208a07421843c9910340b1740c2c0c5060a0550f0405c943c541c895081d10040405c6e0074151249910180c0740541c035400c0040c1c42e070500f4140541c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94771816 1250 94770566 94770569
    0xb0702010f0504120305070f0905010507080f0d06080c0307051e01021e030403120e0d151d01140a020a271d0f0106050c12130306090f06140714090a 65
    0x18001840300b8641840c20700301c80c2808080800101b0b10b050080340780d280c4200d10b40b100e4410300340c03074614605080900642e0360341c03c0441c0861f101c8101700501c265007100c501c054408401d4456001c1500e908003524a070400e452086c82601a80c8103880410031640c601010044e00625120381e80c5400740c00200407800c1900f085c100c940036a240c03020005014600000410403a40070700c04121200100c000100c1381203000148a0740d1014003c0000d001181c9041d441d00d030014090380c000145864504001e02e101426207511000503552480b01c1c8800f03038108521240d02c58841c3c50214649199500302070a0100c0c0240b42175061241740d420700f0104101801b50002820103113840002660f5002d805001400d0102c8a000d44412079800000c0c5541c056811f4074550907002006d054910600300e460031840c0c204001d8040146c0c04a840000860058031448096602840c03401030311100c1410018160741d04c52880d034850440c1d0804001c41d055001e403c0c212403030f80c40c1c2c41d641e0f07403418a10006602d803002c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94773066 1250 94771816 94771841
    0x30e0d050901050904110f13120b0402060a09050a0f030615030201050412060207020303030c0a030c17071b021003020304020321091017010e0910020304080f07080c01020309030a1d0d0b070201 84
    0x121008101c0312100a00610039010b42c1004605827a0140450910790f40f21005060031701c01d60100c0c005142005c054145900030f8641480d40d207a945000810a110b1648100400c03013135008180f0031700c842030041b440c40700031083c6103281c054030719400200248641c2c4690214000c20000c040e0400c5000c1c1c049501042d00141281d4890818030b500301d40c954851150b05010030321b0112501083c90045a85518a001040312030f025503a5800c2c1c242c0380d10144070103851003040315600440041e5118015002c802e00301da1750050301c2e880c0510500d494121001d040000c0301c003200c1c9150002d24000e004881a12500b5904034000286442c41900c41040c48041c42c52030b891500000b2407600c1c040c618062140c001c203421154011003a540600c102c0c030007998090f110881c02c000b07080d0039610740c0009018251141c0d07201c0b482c21282040d2142207030015034413030609402c0020400000c1e5480300211130208070108a0f80011868130f0002489000000030040621454400040200f03000b0b62104012020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94774316 1250 94773066 94773101
    0x14030f04030c14030c01020c0103050a18080a03060506071203020f2104030801090207080301140a0503070306060806010501051204030f051606020c0d0201090c060804020310020a030c030e0d050901050904 89
    0xc980c54400070101090003081c0311458400c40c00d00ca02c2c0b0340041d043c01541e8060f00a00b603188c1d00003004501a1000404d40420709448907600381000304c00c0c28983c5803a80c020301c1140d856512640b0000e0603a0300590080784600800e1000794040b440d50f40c00040c404240341801a0b031b03280030b40300c031104500070340c8010304c00d45c00a0200405101688004248214826a01c5030540d03a2568143c4080303009540c0c000d443c0ca0b00c1403006001000c50002c2d48240000000c1003815210740d9100040d103401c1c03c030f80003101c0c0c0c0c0b40c480c101001203006c06c10240d4050070090030031031309000e10400781d22820f00d4001c1000c1d040000800c40798219a008000729082050103420a52001605082c02c41c081c1d40f100041d28201e2049074803201401d4410f101d02e1910796440b00105144500d0014100c40c40140540240d905026003403503100385a61705e200500180300c140d00c0c046180b20f00c8010180884450030310100303503074106004d08916958408100e0301200c10900b0035544403003c1002190040c4000800b0007284203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94775566 1250 94774316 94774319
    0x90103050c03010c050301350303090a1208010b0307050a091a0a08061c0f05240103020f0307030c09150801020a0314180a06020a0c0209070f030614030a14030f04 71
    0x300031446a501c0c000980003404441a07070320085805100074440c01000c1b0b0502d034070300480b840300340c1c0b26440200500d14078200c81c07075901d41c41e190031035000350b6444925521a04a0fa002c00200c80c210180240301810000d08642c0b414003100c805110041c0713003800300840050b551078103074003410705d503006000071145101a44036605440c3d1500e5201049a00101da010390001d01c580c60b0121041500001e80951604244065500c0045041722864100c0d41801956900d51010303940746516042050184403002c1903514500610150f040d0103640180260404c11003880811000303000300d01112018500041d0320030340301180711540c0c0c0060300102c00550002034001001c0c2c0e4580c10010f01d03e07854040b00300c86c2d503d80c0035190b00c003581c2d050450382d19038007c0000d44011517000e1b406007585281d50b080061402542c0d0740040e04a210881d140004641c0e51402c1540c429414820100603100c041400320000e2400000607580381c035143c0c40244603100660041d400048180141c0f0000511b0b001d0407926103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94776816 1250 94775566 94775573
    0x9061409010f0e010b0a05040203070c17040302011b031e0912062403150b0a05090a0501180903020606060304050a12110c06070b04021e060403031815050a0c030e090103 74
    0x30402289600b0019080c41c24038001d030b9406100e0903118610051050310820314160a000194000a01500a11580101050110f40d40003061000300c01c5280c0d110b540ca909600c0090104440c801e603201315000c0d07500e02c075400690400307003144211b81e0a03902c017101c20742032580c11221031101d81c200c1c58911002c52829400c1101c1070b040000402000e0030540da1000c030007029104880c09030711000d041410304210000601c5001c0c1c0c828940044050022155291124003107821803005490314500d840d0307680010400b80302910184402200003040a003d81c440c140c03402076032607002a100600c01d4a001010500b082804c2000d4401a079000c084c030300785c2c81c5400001901d588448450403469000f1058107813214540001190308299025a500e00b55451b1074080c0000104441041e059000180d1603000d00b65944c40c018100840c400c0e03aa0844600c0d44c02040d40800c040c3d80d111b410030403107070541d0142c41a040015901a0212480c1150142c070b5981011601c100c0003030304c810f800c10300c0c2600210030b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94778066 1250 94776816 94776821
    0x23010b09070f020d080a060f030f02030111041202040203091603123b01030905030315040b040902060a1d0406030c05011709030405040c020f0d08010e090309060d0906140901 76
    0x544800c558001490396010000d0340c02d902c424403101e0040e00b2405081800714020b2100c41e1700034042d61000282c0329204e0031002000c94003a04280c650f00c00c605ea07240c1c00c614003401081d5218481203249810107141c10717000c128442082d03000900c11900407000960480d8204018401d1030030100000c92030701e40d03070f08002c0e504030002c03c2c51a00150ba02000c440b801d00d510100040007240c0c1e210041d031280841e07500c070800010f4144450341010b49071808140420740070005980500603400740144000072030007c0004036501c421000e40107504081441d00507a607100166180003489040035070200500f010b031851782880002c011b0341c0c001c4c98a00b01005000c01c500401d07041d0785080c1c0b281107807003c10b0151884501030480300d10740c503544108014416810103400048031100c0c540115810111003d40150a0000c2010713100001b80c40c0c9401005049142000c0c00c0c0c01c80d010101035450101048085209442280140a1800e848185003c100300d616800140300014940d00720403941030062010b0702 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94779316 1250 94778066 94778081
    0x50303041a0d1517011a1e040905030c010b030a0f0308040f050304121728050708030108010504170a050909040c0305031204030306170a0b1b0f09040c050a050d05042301 74
    0x40354000d2a94a1620140510030701e40031b60f4030107495419640840341000030311540c90080d0344c50b4860000c0180c00e180c440740034400e0290701c110003550300d504011352041e00319101c44000038401e511110b12900400c800c10700b1a640302d500362810a141c1d6032a420414280001031000030414400043c00184580c3c008040f203074400d125003899040800b42281903800e60041007101c103002101000030500b41c4400e581510500d01190078400d09000403619010401c1d0800d0f4403003c082d035180c804100402006101e03055401d05100101810440055001003280c0145100640075032107800201d0184508a4500380003168090f003101da940c1c0380b041c00d824100b401070320b0403400700e41001008030f1064204d2805041e55040200149100100c0b43c035405900d8202030f09610000c003001c500407911224000060140b55602103c4590301c8e4107240501040750714032030801c000c209061284000c040ea000c8111296140b5400b00070440da261803d100000814040000400194030504040180419000b904 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94780566 1250 94779316 94779329
    0x10506040b040207051902031905010e06060303070c0e060a030b041101090e0106020307080702060c0a081e0412030c03030e060a0f050a110703080907081e0c0406050303041a0d15 78
    0x2001d00420380510040c0d01507004010090f1b08004d201e4032122610a14442d1000d000070100c40c0042c0f94a4001010f00e40d00a500362000c0e51240c10b101010842000060b170001c4040d00110b142c807005480f0700c01e00f24014000c40a40a0f002c40228175190303118428040076540106200c0c1141c01d00303140007842c0e5a14590300c070380841c0c100b940c0025450a00361059040790800d0b00a140342807580d60341e108441e401510100e030b02500c02e11070064102c404010142c034492040f5240e035036600ca810440c07042c8210329a1084d1365042d0800003809182c50442260004c06c0d070504200d50594940d02d03003500503100c092001c4299202d620204281103500d40c004540b19000b01108019a850f40c0058201303803484186d02c02040a410011000020b02c54448694000054002c2e5804141c45141080c1000b244001080496540000c280381e10035091200700d18400c0211407c00000e4030b09800700f9100e01880c4500c1081d5040203040e0038a0380e03122000c44030075910450b010011012000c042e0010740d6400c2c06400b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94781816 1250 94780566 94780571
    0xc03040b191a0906030c0a0909030309080c010e060a0902100f030e01050a0501050f010504050a0614040801020c0a031b0b0c1c05040c06090b0f1204030302160c17070e010902030c041701050604 84
    0x9444d0b00b0081003401c940303c1c028060800d8103043c0b00701c01020b007244a00440405556010020210380c41c40b019122180c0c0b241c0020580d08035602c41107142c110003402f110311880c50805a400169030f05010001d064050b400c1004172a2032840040d0000e0900b010706100c0c1d9400c010030450548104e60006068031400c0344d00b075400b410f0460045170280105c9c010980c0040c3c51072000d1264902440c600e88a0110001000c0c0c0381a840e01400c40c2a600685901045907009144150030541c01644450a02504100340c42001c2025100d005104c50041e00d22500b0800010316010301000d00c460400404540080c144103504041c5017669400e0039a104400000301c540c03801081c24244c0d02c003260341e0524100c1010b405c0a1444500c20701280c00035000720207041c0c1c2040748940603032721a818000d15900518842021034074200b0380320000641c0b004c60b1261500030000a0003166201e042d21410746003c2d5100588a80d1003e01c606914031807504011010701d0000c0e850504d070241508030764400e11094800f0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94783066 1250 94781816 94781821
    0x10309150509070b2d09030d020304030204320a0f060321050306010807050d02071707060c111e0705190f050906061209010f0f09030212030c03040b191a09 68
    0x396507250041803110150031203018205e440c06203216504007180054444464038001c0c42c44002450300344540001000b681011804005624040c4200f580703540c0541c5083c1c0583c0d00c0107070012010b16403c1501203202c114107002c103217400c00030780c0b1410364903c4000e07082018680340c0c141100240c0140e20902542c00007100c418040d2846882980d0140806031030309240ca4860030b03400e40d5179800c2119182003842e400d20401003c42c800c12100048000080e0360344d07070b55402504000c81610304040c40c0d9001e2100d40380d4101104600020f6002903c500c4500303a041403400c0c0c0d007043d8240b04080c0c0c0082e6001c00301070301d105881c04c9114802d400321080d078251100600d54030b6003440480f00782104d09590004003880315020a40e003000c0c0317440d44030700c065000040000500590714112554140800304941d41d0340642c1081680410200c941d40640c0c2d881a41140703000741103500b01c0d1000400003401402c40d900420030300d1154010000c862000110240810b4002010500180d4074010516103d140381d07202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94784173 1107 94783066 94783079
    0x30c050106060815013204090614100207050102070302151e271f050c1f14060a0306020c030904020c0303010807170606010c0201030915050907 63
    0xf034900180c00d10204c851440c0405a1041d8140000d0a0300c01c00d00002c65001000d059031201c2114040d50319408003d4907034083d40d40003840040c10a2004200d1802200c440c0b640c0401c1030321401e420341941002282d0b59055441810302680041000b80b002d41400c0c01d01c250311000188500e490440411000340900107400401d69040c42c0204450268030100114240142005a40100c51004501c00540b03c0648904640361140c1c0000500000030300a00c1a60601401c00d015504d060a203600c2100648070288200d50030035240000c0610300c01e40c0108003a0068101030100e0a6140c19503a0b90030095102469096591005010035800c0355168001407802051040244d5180e5241c0303c0164900314544d000005408035002d400000020001081540f160302460500c0c60b124060006030700415403c0d2014041781c07000c0100329130920b080e0700b009000f10a903000b1074240a58604 = true := by decide +kernel

theorem cover : BRFrame.Cov 94604316 94784173 := by
  have h0 := BRFrame.cov_init 94604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94604316 ≤ n) (h2 : n < 94784173) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
