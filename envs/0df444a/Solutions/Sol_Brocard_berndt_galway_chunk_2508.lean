-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:09.367695+00:00
-- url     : https://prove2.me/submissions/c8199ea8-8277-49b5-be3b-5634bbc57e07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450899280 ≤ n < 451079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450900530 1250 450899280 450899287
    0x4090c0e060301121e0308040201030c1e020304080f0c0a030206070203031c060e09010c0f1101060f030506150108040804030b1e0a06170f19080408030c010e070609060e15 75
    0x803611100d01443c02040360864500450300b190901510070400e1066844410032900040c0c00072039000442990050b07420300e000141286a000c0441e8106002c1d0012117040000b0740700400f0070741c0c0c0000948240e52140c0c3c01d81c0c089819032008203a50742807210080e81c0000514004001501d04500603100481c000740a40e071a000c14a040c4622184802c03200c807002c40d42d1840280010b40341d02c0030312680110300c074000300540720346440040c202c1501824900d082007034007203944400303070003e4000000404400c50802000707916803500d00e1325608110f800c040d813003911020700c036070942c03056101d18092500203003802e20b01400c0d5125503c00d1003004011000b081c440741040303901918803400807407050002080011b043c6040c5003113604044059200042258484c1c0094090420049a4032003555442c1c52910225900c030704c0d066505d80250391140c00580030101e5400d64160040d00402c044030880030030381e20f80a07141c180565480181d40100000070714100c14038481420f00c0e2850351490060340f6800c60a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450901780 1250 450900530 450900557
    0xd09050f060c0d180510080a050411040e0f010f0b0109030b091903050a080105030601140616020d1203060b070b0c1b0106151409090f040f08030103060b0f09010b04090c 74
    0x24260b02c03018043c00042841005040c1c10960592240107000202e54008010110a500404000000c0c0400c94080d03a44d0340410204082001c3d94a14150050300521040180171130182d116421161043c8165003000041500980984142603901c50140c441645a601719260b800308404018030b41c0860340309036000c00b0741204c00b070180e00c10100c1c880e07503400f960380d8241c00000b0030f0b80c00107900142c02a80042c0041c001070039503903402000240151080c54641100d85501a141242c0d070310080d40000e48d8030742c04000c1c00404d0900402c214020b4400b4014036a451940c2600e510405801500306203000003c1000d2a0359540109000210700e85011a0b042603003520a0840394258801e00520801c8880c0108c2690813038007440b8840c0c0340e0340d1003d080840f0b40000c43c1070840010100141d00346064000340822000100518216820100498a961b12898244001e01c80c28200303521840e00c3d018982424075007010035506907108000e1540c1040d01c0c005031740c00601a0300d0904c40134090215200c07034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450903030 1250 450901780 450901783
    0xb01091511150109150f05040c0201020f030a0209181302130b12010c090e01030c060509061b070e0604020712082e050f0102030a27030501020310060807020d09050f060c 74
    0x12010980d049080c50ba52400340c0720001c4500c81d210400070440c03080c008001c6040c0b001a02d8048400c16180410110500c0e0400c900903c50b003200241120000f009010013402503a010380300300c09056a2090032301c050782c001c0c00c0401d501160390310341004000c2100c40c0107042079003115900944501002c070341003101d00c0025180140000d004070070b5070f5441ca9401c1e0016881130340140104503002000070b8030350444d140c44644001d940503600900100103140c0790140c90f584121100000c480400c0700c034a01c03442e0b501035250341d100d2045008030640000881c5aa1400380b007282e9581e039100041e00c02a89070518255002c0c1c00c003c2c004440c1c115030440417205441c0300c101c071188441d0325414841e1042d040000f00404000220442030441d4014000948640e41040c0ea04000d062076a40e8011640c0340101410411401e94000500d81c4d4008001d020480400400000a680094440134036990703904608903030f10380401c4203c400140700e0700010002814000405090410050455460300b03070641b000e103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450904280 1250 450903030 450903043
    0x90303030906061306030206041217030a1b14161e030302070b010e0f070e191403100216080304020d0b04030908070504051015300506040b01091511 65
    0x18407aa411503000c0100c40c0c506490700b001c8849504004010791402c54010079440e00650091118500301c06c0104030a105040e503400320b800c51200c0f0026520303d00002950090614101ca0070061640c1c0b081080440d4090034110b82d084981000340740c288201014000201c0d421813a0036186868a810b12000d503500d1980c480e04101e009440151307591b6a076140c0f0708801e0704140d0281d19140a41004e10114201810845820455601e440d030075020044000804c2c40340c0107101c020441c807d50200040c0101d00f42c0355808900c0c811010307a80c2c012860030300d40d010b074070a01c80381e070441810040d012400a1460700203150480e0000c2c152451440960380e4013008580c068070240c020640c91a03003042140b0080044001604058406000b14103040000801030500c5014251040e13045c0d80040203054031843c03050030b40000102e9180640013007951200d90070304c0f01044104643c1d050000003040350605008420b020070040e9600c00115107000000d03408580b8907003135541045180c070012200050300b0450b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450905530 1250 450904280 450904291
    0x1030b0a031506030c0e0402030c06071a1323120c0c0a03050c03070b07030f0f0e03100507030b0d0206040b070c030804060509130504050d0f02070803131502060c0306010309020609030303 82
    0x3c2c40c9081d0300f0242e6191003030b82d205200d03400d840001c010060300c0102d03030f100c0522015a081a1078600ca49081034691006050f9030032890701100400c03a03140d60017008200110b0040b00c601c602082c0c0d02581d190000c428070030a0300c99074440c1c0361002070030908500a010b081045415500c0114007100003403144002d6038000e55541c2e001514800031890180500700042c1081030030300785458450354014204524034000c1b00c0901c000800100d040341c2c018400019805001820340311000b000850050003800142c40080c00645002801149801c103940c140514580007001a030170140b8051040c0095401208110784680b04250000300090700d900c0544060800c42e101e0585405d2628140a511045540c003800400c0c00e00042c01301040b0045000603101714a464001c0b0f03610321040003030b031800d4030940c4003c0c00c1d4800010310b01d090580c92091041070361503841c03080c040d40140c40c00490ba11481601d10302d40c1c4100810100b080303507020394407509981d880038100c1800c1c4410080000d00319003040b1107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450906780 1250 450905530 450905573
    0x50708070309050715020c040f06030506102d0e1008060709031a07021f050402040f050c0a0305070e030307051507020609070e13060509031209030a0c0f0501022506151401030b0a03 79
    0x72b0500030441c05200c0c255010415580504085107003100c504407441d001d5800c103810200b14007400098003901d410000140030f50451240142c00c02590306100c0b081c0c944200080c500400c8041018a4420801001141d4005030607860015501c1d540c00c01010300a050641035100d1203034003d01906210b140da14804e49100c2c000200c51034280180800c0d911300e0728140d400340d450542009140780441054401c01011840c000609035500c00003a01c07100d0500c98420740c18440802e010040060024140d550341540d0a000441615014001d9079103d8055038010060742120105108580d070002e80039034000c0b481c0380d240c00ba20245444110480f5015540900b207500300150b821145080702c0e07440d40d005450403005620300030000c00001d00001000b9001009005032540301720500009405555811000313064286800340c15441505000f01408e0044880c1800e00320108905400d11060800320780b4404028140a10714500440042440c1c40b2001d41c0440100c101001041c0b0b40c103901d040c00d600014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450908030 1250 450906780 450906791
    0x51f15030605010e011e02010603020a260604030921064b0f06081c11030304020a14061315111f052701050708070309050715020c040f 59
    0xa0008050750042d40006051000700316480d419a68071400d019038417850710301c6000700429194403c0b40504486d0b03101962011200e0000301d03100c10300398004001140380310741401300c0c12503000096440f40ca0895011300441c0340740070300304269901444103034992050b007109113405004a54807a000c0f9611020321a0b0700340d8851112011502d000e0000c2041e2000021180381400303100141c9000116200f0b6443c40415150541c803440c0e001c0039005040070f80285410f640062102c050408200040308007400001004103060320b5028102108403401290060922102182014150001240e21064598000c0c404104180c25859091a41400350019802c40105010350250007000300c030806504181941110704400d505510180000344052980c0e2404a603035503c00344c04a094010310944118400c4480352038440011044d48000d00c107440c15214005951a00b02003201122801c1200500aa001c0c110502c000012180a9203070801e4501c1184c0025070a04082400e51b06a18a910540c64850b0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450909280 1250 450908030 450908069
    0x3080103030305460603080a020c0915010c020607050109030c050d140d0b010504051e01030501140607020d0615030b10060f12020708040b0304150e0705060d051f 71
    0x1070003844c0d040b2814141d40c0d2580d4030720761400500e9106444d02103105000040200c00c0710302121040b42d01300c084c90313802000310b5950f908204595600c01d02400005000d03030004141c2625000c603010b0b01580c1001070881c05841c1450040d42c041e4010030f000d83c3c0c00740e800e00c003400001d402409000c03511031096440682c50703012440d20516240d003106640c402d01004038010280100458142e50002d401040302090100c02d610041c1d8403441756401142d041000030802c07840d45809003007001c40501382030f40c0400040ea030300c0020081d5000d4004e04140d200070200010070140c90403010700c40c1c2e1980101d0700080d00c1d0074481043c1c1e40c2c2810951007203c254084000b0040500980c00c407100040c0175905024031403801c5907600070248a4521244900240d010407040300b0b00c010001958064007049407515903a0278a0305001041c41c0c044052001c1c8981041c42c450244031022415a0450700003a003894107025100c4c4401d0301400d8010b0881c00d01034010704c85a40d40d041000c2d0000700030a600c5203440f8111010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450910530 1250 450909280 450909287
    0x2010201140c07021c050a0308010e07140405010f030b0613030605060a0302030c0603130b07050c0f0d0516050a0507091d0d0f1d090a0218040b09280203040308010303 73
    0x21910100301c0c400800c1c0c00c010051800c0e004032904070364119107100e5006004a014443c0104010001d0700d01d100d100800000c00d9080841035060311420441400180d079402400c80c0c040e07880e0b82800381201c805010400c01c2394090411050384560074117012424145c00710218149401030346004221440505040042c4801031103500d82116080d548030100a0841e004650b8485031071084c940910300000c00944081408503040c1c4038103510501c1c840c00c07410005002062a0400c1c01d160340d0900548080520645000070042c0c07180c103264550b28141440c00502c06000991201f0a550a00840c00600d000400c1030241070054082c60a00140c5640e1409a10001d2110241c1c1e4540540c400d44c44083d52607004103240742481568a4070440c8100c0c042c1100e483c007070804060716040a0f5410510070440a50f401a25940602c1a00d407040700f0702c1d02d0200401d0b242500c6013990000704000114000034040044941c00a142d5540c001801e40d1080545080760b1086138250f0000d1500801402010350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450911780 1250 450910530 450910541
    0x60c050d0b0108010308251a0402010e090411010806030c040609140c040e060f0f0301140403030c14071509080d060302090109020712110c030313080c010207081207061805010902010201 81
    0x1083c070700302c04103604507500c6a03454801c0c882e40302856000b8031042403049120703142002140381d02c000c0d5040c180710f1944c070b200c02d001020f0320b040380483c15101060401d41000c0900d10f1043e500302c2554505c101c141c40040d03601d50406403070f5135058080d6941008554450740142c000810b60320780d00040d54400028000e0003400e000e0400c041c5144100410015190340d0000160400000c807030201c0c62018820005281c0c00402c1c410a8040d42010146500b29402c5864248524003e0314144140c0c07032128400c9071280308210b40380018031424801c10020484005009144040310b0030000b4507000d068840d071590741c00c400241e090300f40e140c51050045080c46502203004041c9940d0a5003049265580c48444070140c159030000c0180204616055000800c03920801c04070180580b07a0300d01c0442000310b000861801080102d01c40c3c2c007480d00040d403000034044101c894a00192291801070391400185500881c0280d074071300d40f10271f00310004060300d11244401911860000070b0311201c40c800a07003500d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450913030 1250 450911780 450911801
    0x50405090c030703170904061203020c030705010906110a0515240109061214090a0b1b0f030414010f0e1908030c0d0f0908070b151516060c050d 63
    0x411501528001d500c0000e0050240d82d0b11241d003190b00e2003401c00c0d10455025040005900038140130f0009038600e0300b0b080c9460854001e03800d494804141109066441c0220301c81c150001e524107070204a00d074403d950020250070081c081d40c4950352141c4445140c4030948044804080d501000c0c0401c1421713110103099a011070203520300c8aa0034200001c0c2aa0b046407081c030341445035500940801e0030107980039400a880e00b09490840c1e081c1011003656404062104440d140b0803600800c003c1c90f4680003a00c42e60a8031701c0c00382c0c036000c521005040a03420152048481580c40d18000e41c00c10801e000d040d15800e40034030001100d107880344183d80392042809040c000080100aa60080f40c1100120303039000c409aa01c480e560303100304070588001c000100b81c190b402c07445d0407500d500300b01c500001829610b0150984408540340c40c400f04401091441300da80d440505001003400c481c118802078100e214181000c80048540350703c406003502c002d00c0c1d000b0002400080c000a140805100c1c0c0003818 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450914280 1250 450913030 450913033
    0x507050307090606200c090a061a1204030f050415050a09170a0602180a0315150e070e0f060c01060e011e05040203060301060f0e16110616020c03070f05040509 70
    0x4c0c540500134056400460b101c61140920f8949045504400c1144400e00030000c2d03c80c01c00d0340b80c0b4446100003828075000b950154241d0208a445c04429403055070029103100c18464002d40b2142e40981e15503d00310305403800d00c2414040007515515110203699040003a84030141e452400c0321000301070446a40040c1e180070060400c002d251040040c0c500a22903124100581da40300c0c2c40640d40c2052500d5890540c8882d010303101104208041070303420114030100b0303002e0006004a050344405440d8034081c07082c105001781c2c00100d4840c495039002170311902c040e090901911810f8081641c943c003550f50700b81c1582d143c1408011602d854007a0b1401040f611100b001c410148086000301d4507e140320341d5210b1500800801c0080d6070a41c070801c01010240004040302d40d071201c90381014001111004140c03c100041c07180c1160007101424119020b00000d8042550340800a404c1c0f15804020038085200d840400c008130b40301041400b000e842403100700c00e41c07546860704200a0f64030092040c19079 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450915530 1250 450914280 450914291
    0x303040f1a09150402130c030204080c030c01051e0d0501080c010e0418020904111c110109120210120507020102070605060d0201020d140906070c031211071202030a0f050705030709 79
    0x360702c404200d031000c0907441c4003406540e0302c9500004585040b0701e06c80c9250300746000507003141c03030f5050780c0140100c5003a60203940520211108044d217030f068207272600e800b1803400c1115008200e44000300b0380d114101c91503420709100903d8020f0003114400d820446940e880002104000c7d81c0000403403011010494061049541040301e081f4848030503070b0024014501d0781d010600308030510440e004a5039000d021402200401e00ca03048200441120070b445842d022140610503511501c074403c103450001c206500d00c51015800c1c484030458065280c003c2003903544030542c40070b4040c05090b005034556800940c4800075400c00c1c808650340981801e110707526400c1d01d0300060b60003090f0302002e9642800d010304429201100c2201d0303840b9582806911020002d000e60410004c1550081902d004030303903107110350040c11700c03e130b51154030010000910f6218510401000e14840e1400c11403c0c4050255100c643c03699869004450342c07000112070079040000d09201c141000c00004008292a1209018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450916780 1250 450915530 450915541
    0x4030b0f1b0a0f0e100e12010605010507080c0c0a0320040e0d08060d0807031e1112210907090c0c03120b0612040605190204060912140303040f1a 64
    0x30078410750010b001440111880e40f18214007461684880303e1024002c8440c44a05020040409410038900b130b100312024100742a00c4081445190305455060b1a0309190404a07254818550000f040303540e42c2e8030650628610545500c5a0f0341b0065100d880c0105548401c11030b5010400c0b0219a8140a1340c03500f8940c4900d15800540005840d0b11810015020b49601010451000c41c0c2c200c0070304080c0f0005001e80800d907004a882c0134448a00170341c131082c6800c00c24101e80c0c000409042110940c0001c82d1a0703003507030103800200380170051003000c0446001c4c1c0340030340c070701c5814200c0304070030690003000c4c0400c506461402403009942c0f0628020010441c2a60b000c0c1c05d06201250382821550b55a0705105241c580380111860100403844070b50707651500d49094401340c034040f5a28100b086940311403044003000ca0099074266155916241801ea05210400c04200074054060b034070b001d260b610900484400740010f6000da806010003015003800341c01d01c209904280b0940c5013050481004124 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450918030 1250 450916780 450916831
    0xc0102120301051504030c03210f1e090503100b120c010c060e010b1f020c0f0a0603020319060e04030207120209010b09010c0c06020f0c03012a020a050304030b0f 71
    0x906445084034140c400c0d400c1c00204c101a0b0049400092007c0e68500d004418050030803c44101c451b21051490103840f28900f007124100000f001c030390702154140c0ca512405200318199a4503141d1640341448007280e84200003031078a400144140d49156a4100d007102c182400c0181e000310586030700082c45111042c0000078143c0380c0109010381003503501c1d4003001c94040d0030b401a004160005002c2078400032107609141003520a003035007401511600400941c1c07810024151408241c2c014640402e481c40c04c1c40640180d40000c000b029030f04c0841d50070314216889481944054110032100080358903040c5000b81c0b50030f51075001a001c050b0700258220041e81e03007403d15410758044200480c2c0b40d4040e0001a1001d0003251402815600003190201d01e20381d002400440360b20100044a00100d078071000d0508032150414902d0107e0318098100b0610b403801a0440821131852048900400241e102c69081d6002500101c4036085030100388148101d00442407074020981c103d1624442c0000000c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450919280 1250 450918030 450918037
    0x51005030613050a02090403030515010306051309060b030607051b031c0207030201090b090303241c0318030510111612030603080409090501050c0307170a0912030b030c010212 77
    0x800c8555a030b036103141000414010801041d601410350030031800c0528018000d4001250103008070b02c030b0700c040c82c42c0642c468043c910403a0405000c0303410000f02c008040c0b010f0510000241d4120742c4448210b5116101040817610a04040d55901e481e8011009041510b40c9a08038101b001d41c41803159644000c035214490140000c0800011703a00d0b030071860180d002d40205100502502c05600170054070002c0480211b2045d84541d6840d41203181c4120401c9100ca85e05c1d00032500300d0b80044028014050b0f00409820440c000e00b058a00300b0321955241e01610029001224a6040181d00b4840b6620714041c03800c3e4804031012581c10424084450340211071580c01c0a01511a80d4140500390740c060362003840603580140380300e03030740b1030b290b820500141c070101e0380c03c0300c4035840e0038002080c200030401030703a000d007460f0781d1440c4240c42c1140101481c101c000d4010030203e59148100780020310f807010584202403c40c0c0b0085400480f0408140c10501c10071089815500308014100d001d082401c202c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450920530 1250 450919280 450919291
    0x30604082d0703030c030509030f030a0b010504080a080706271b0b040806040c050103020903060c0306011b1a07030c09050616020306011d010f050a03021c060614040510050306 77
    0x940c0c14203115a12403240080c0c80080a901c24000240d8803040c540c2c10381081c4084081500d0074001500c0c1c1c04001030750b1b4852000825034aa4051000c90140b0b0003070340004c915500c051400703030705180c0c1b02e440050422031400011900c000c00095007a04200c2640548032143c5240d40c9284032102e05219114003210455070b004100a8921200b2041400c0c20284240030300209040f1940311512000115600c02050b81c4c01d8803039065aa100040e5503110780200d891058015003d05101d446400900d040b40c0c2016000c80d06001100d00c10282141500c0e600d00d02c4c1c24041e124001ca5842000c1810461800240c031800c2054201070004403030603040300c0010b0403104150340940d5140c10451034120032120148009505000c1d041c0005810f02c0390001040c60f400803400c0010032640e80320100a00081d6500c40c46400080642c0100054038110784000200261024032036410882030b51801c1c01c82c1c0180d0000d4202d49911002200c103401c0c0340c4a102e601c0360044c2100b52505050100082c0d81d500c00514 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450921780 1250 450920530 450920557
    0x5070c0507061e0f03110a020a0c0b0c070302090714070609030806150316020f032b020c07030209181608010c0503150d08040f14040b0d020a0e0c090901090f060503060408 75
    0xc0564513544203503c034a0001112031506611001480b00003522151415002d44060901c42d401080302d101e07590403610181610002440044c0c519800d10140c0d0b13a0042414081c41141042c1441c02c01c0c0840c0213102041c49514000340c20822485d0140c21900c01512035400b40c0c08035101c1c801078580c6402126001750014206820484040384204d00c1c0008440000c00d250101203065446c2c0c00524904071180b500d4001c40080064000005a08900901c3c0d0710102c02e42c0804010405401c191035031070741088180d0900d40b81258041a1145810031035129030840903c1d44070f0400012000707102d904900c2e0f00d40c1c40c040d85107040c0300e00c91000c034180f04c0c0f00c410b12481411508004001081e41140c2c01414804452454165203000c2080200d10f442c80072030043d42084c0083c046854410302e040d103000d50042a0081580c240302d541842058020160a8071407000c100c011b0b003595800304e0320b5000300b0258501080c0015001c2d44003040c0d80d66580850700941c800070910001400308000d64030181d10264 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450923030 1250 450921780 450921797
    0x30c15080406020c070302060f0307020d08090304030803060d05030c0a020a140904060209010c02100e0a05040e031209190f14010240030b04020907080c0a0e1305070c0507061e 77
    0x20130a052a9a0740d03c000d51004000034266605440500a0f51286081da003d41c1c04241a041054401d08404c03501101c07250001c0009200007020b003000303150050004ac00c0708400c020b807a80c0d51461035012135460f00c416408040c0c5501180350404050000c0c1402c1c05c4090302440c41400400d107842000b0304001c10312900880e480100d640b0440441002076002420361291041456019107000c0d0000d4003240a82440d140100300e41c00c040c020747d948865610025071808100460391422408003504040341c1340201200082903100c440b0398410641c0c01008a9401d06800d882c0410300c1d4940681290004d9006002498101c0c1c2c8078600c2481908028114040c04e0800041a92051031000340e12508805410004410712590302030b041c1c440d502c265261503003516680070540d400d09048650015108080152403040c1788103a41c404600800940411b60f50190800d000c010380d8400c4400c840010781003101d031b0060200800035000140140d08180043c1c00520722818004010b00105405100900303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450924280 1250 450923030 450923047
    0x302031308030f0117150112050c060c010e060a0c0f050703110105070c0210230705030706050c0901021605030303041416030302010c20060703090813030507030c1508040602 76
    0x245000358001c0ca4503035640741c000102c0e00c51040030300613401c0c402050f151000d210300700080e108200707030740c103250424450b840d05000100500d14048200c03041e0150001000441e00d400020f000b03104444030001c070355203884115a61500f240101600343d0740b81041e0381040080d40002102c600715082d40340c11542c80700c1d142016240340e800c60b0001d501e1036180030200401c256102c518094514406c5135034410070189030004942034100c0564540c00b101014656486180c18030005100861041007600e080c603100d41c5504007103c60846108940e1003001492155a43e81400303100101d9041180004c03582c1d041101007503503800005c01c02010720210140b107510008040003054035030f000c03014001150302d480340790003406400c0183c00d0401003000070908441c0b10068098400710108260014070440d40ea103c0118090421480180d911030010000303640051234524500c0701944c011170007010103a2a5143c0301d034100d4940d600c41d0a881198911154001c1d42c0700d400c1940003504101c0260300d40852 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450925530 1250 450924280 450924301
    0x114030303061f1e09230906010807020f0307110306010f0e151302070303060608060406120803060a030218061e01080a0c05090a14030106090603080f07060b060f07170c0d030203 78
    0x20310b1383c01c01480c0030345038050b200645c400c2c1034500b0707541140302108580100d00285801900281c204941c031031080400581e081d4468003d10380c1c0100301c5d20449071001d14000300e150441c0c0c418001610a51744900d14900c0a0404000c01ca0041c4011143c5498551800d40d80710700b4503402030925142001d00c14400315242c1d8130240340c414451078500b000c5642d200540303809401015140b107110081038001002400b28034040c8140c80440317040e4400c8400c280311542d940c0142c0c0d480106110f521100d21b82000c00543c80c0e25468071801e42601d0040446070810004100c100701403100b901c03e821602d00c2c0340d200030b41d80c00804e89410056106000c40d194080718015250340c01110107094000c000d074003000460640c0080c8034105204260000c00202e600d0b920401e0030303203120b40405800801c0401442d2920311400c0010441035000d401c002400c0010840040c0c12540408810501d0850200303062003440503004808580c511007102d10380c901888801410703250f5044030007550502d540840001c0e80300e0038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450926780 1250 450925530 450925547
    0x40306050411090705030a060f06020c090c07120225060f0804020a080316061b0509060f09030d03050703180203060106180801050c0408070f0e04020d05010b030f03030114030303061f 80
    0x50080002c9844d00d00b1200082c2503070000c648842143d41480c400142c00010403030148113449259002e45001403c540a00c8801d80018007014030342e000030000c03200031841103103000f110200c2550140124404496402c503103140242d003580000c5085c0f60040001580054000e11041c666052880490350b4074000654020607961108007903020001e80d01400e444003e00f8440094462141080300c40b040c1c41c9208003901c946010900400c4080001c84d155281c038101500d0014010225680740501c0d50000c01e050007465580034010940394800e002c80c198060040005101b00408104041115500000e0390741c0c4061203008240301c454255403007500c2e03803405540050400d40c4004d000310308200708201480c5d809031142114601030000c0114910f0480c811844c01c0724260101e09507241c907190200b080524240030704460940d078504140006440c1030006032400321a50002c3c60712903240200d03c403416210814258442d401c100100f143c1c55407000c000d214015111100508030084003402030314001ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450928030 1250 450926780 450926813
    0xc1103010603060b010906050c070e06060d09150b0303031005150c070b030414150121120e0420180d1703011a070f0204050702010213030503070c17030403060504 71
    0x1401e111021003480b840d42c016149840c03081c2e070750088143e41d81404407a14041da0b500041281c011001c10008074120b180e4072034102d10b000303226900e41550b089443c411510aa0412502028011800c1200c2c1d1007620402006c0740c0d06801442c0365260013804200480e803030340100d9110301398000040354407001d841c0564803020462000c80d1070140e1940001d50030364000b00c80490b031510070074162000d11100400c0a055100c181209004140d0034455148211003181c0c1c00c0c01c03209020448100c012606c0e4112924401003640c40b603034042c0952405202c16640003a80c09003200040800440e00010340702d0440b40e50707840394000c1001c2e40f055040050804142c2c00d0014010205a05002e400d00e4202001107040f51444500c6d80c6601a0100500352903002c0ca0700040d00e4085840d41c010054145500203d80c8585184001894109140f00f04125030905401c1640c003a03002017524408c0140c8010071130041c02c0c18140c0c0700e051421911056031ba13449580000cc1ca0b954903400030504000c81001d6040106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450929280 1250 450928030 450928033
    0x80c090406062c0901090209150310113109050603010f110a020c0406150810080d0f0306090203060a12051504150507080609012304020f2a0a030c1103 66
    0x10030f9032007850b4004a10046107540e61040e2a00800e48540052007030005495028024a880b41d89006810283c108045c0c0e806030107006010044010290a1050341150900300d0b9591340ca400f484600d24038064075168005055108100c081d122120036501200211101c0c610040f544d5580c1c0e4003c42d0242a0b00280e010456041440007a907a10040003c0c003410385156084032140c488074004c20080c1c035002d1142c0001d0004c030841107005c041c419801c1591200386003c102c1c20042d41e40c20141d1404a014910b500050995180740240903898054030009001440301075045040c1200000c585038214850021402c600712000020000180f01e880c001185405000e042894503040c8000241c081c01c81e0415098600030000b0360f450700404203d402440b015102500e40d070300308040d9503140c892042d00101c890030a90f50402c99550303a400184400d8202c944466151091114041400c1d0103000c2e906a481141c04000c0462201c0080c41240003505444d10118148035418072041d1443c40d1801103070507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450930530 1250 450929280 450929309
    0xb060f040602060106122007050a05070f05100815040e120d051602031e03060a050603012925020d060203090c1e030705040c0215071710080c09040606 66
    0x1da00890110704130b4646848562520b800381d07a505003101c0400d00312201040c0a10450003d200c203d901803c0c0761031241c0300715a400710240e2200751400c40194002c00010010300c2082c402030800d240e141030044d560f400c0981e2542080a01703010b150b10201034850040b550344600c1401d450b001c21242100d600690103040e92031040b8180c81c00500412140c51030b480c0503100c1041116440007049404c44142410b03042815020140350030350780d07800644200d600050800e8003003060b5039000000e50080211148503041034036040c4840840000b03030f424107280c50705d090040f060344a4001007060306042c072507070441d0340c2c03890079100084845440040203030610b480030003000204880000c000100c100c044038080b2000e03003c3d1442d000340c01c2d2040b000c69016044070f0001c211740d060903040b4441c07140d501e00554514001c1c001c207418142008840020018a01e21003a10b48008019545a002219000c000807140d003083c610655403025075110718000c00e9008001000d110096110f24003030030481c20714044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450931780 1250 450930530 450930539
    0x510170f090a170d06050603070f1809020c03070b0105011106040b0405030d050c0702040b15160609020d03170c030f0c16150e100b03060601051e04240201060303080a0b060f04 77
    0x10507030412100c401004e4030b00400415a803401c2c00c15a4850300c0103a032610402c121180049031510a00b43e0f0001240c107400a0214100100d400600503a114540c000d58542007281040342003080103a11040c10701c4188421681d601c00c01243c0306500541244262805840d10724009155106682c00031400701c1c945028410400c1c1b15100403d42240215414040d280716407080108545006009032611501040003030441c100c1e031b00c040320701d075401030600040701501a00031031001ca424070700131000214000c002160501018244030f4000540c0044942145000c14000c15440d0700901820311029002c540a00090514001400782e603900949600c000101c043c05403000d4072445c58905828080c00d09605d90700500c61046008c20000200242a10340712a001560554001103210f00b012190100441c4105d5a41e00100b00403c640b074202190104d003003114030044100380c0000411641030100c1040448d5108841d9070700071903410000a4050303041d02c00942e0f01e1150841d074809080d0003140015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450933030 1250 450931780 450931823
    0x1006030c05030d092105030408071d070203040501020307110d151a09040c0501140d0e060a06080109050a060c050c0a081b030c0615010306050909070510170f090a 71
    0x411a01c003079003181c11140d100c075802d43e81500103004070081111039640d4440041c0c0c0303143d00c607086640a60b05603460980c8030202241046180d80042a0075204000c94121075030300882c40310b90140c9680f0140d42820308200000b52031f80b01d401c3c801b13019200e40c8840c2f1000b9a071081250144182d100300c601e903644e080f0700f484002408100703c900c502c1c09011101200302c1e04240b80c1c010b101c2c80c7c4c82040c5450903424030006440554004080650000047c841010094464460000b025050000409241c5001e44c2010b00b42e9845421544599060011000c005140012070101080d0b210301c0101d0340c0b02100c00c044566009410140c117503403151141080c103000b551720080503241501180e1181070401000704980d00e22480c443c00840e0b038407a0300003e0034100c0c080021280100c1c14034020401d03966442c0002c030898401d81c0c0c0008982c21009003080342d80b5000b4001071041c43c850400d80044414146070b003281c85e000400c07184050f0302030030000d402da40d41880000700417540403c1a00d512112181c005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450934280 1250 450933030 450933053
    0x10090c021612030c02060d1d0a0209060a03020105070b091f05040506060a03150c0c170306030d0305010807050f120105160206010605031510120204062703050705060309100603 77
    0x105141241c00070120b1442040c44800000640685030341104454590078402544e11019030f007900c065581e0a4081c0102e20010440c03030004400c00140420303540c6004222058002030844c511944100c1020001030b60010181d4180c039411610400702655401c1e041814400090030b541000071301c0d5001020b0303980c00b9a000c28003860003441100e01a42d540024441c1245a500010300400450302e4009842030765030300081090a2a8034004c1007a20203903454001000d40d40017007092560000c0200701050500700030055600d20703245401d205551404814907100c4056001e1180200c4540d0410380643d22484200ca9145488100800051800c441101441c6d4004079045d00140224800040c0480c840c0040e240030b030080d00000202d41030101c080042d8160500307040d5090000d94468161070700880e00c003038002460b01352618401ca0b00e042403105041d0103840c12552400503200018804102d0014007801624402c1d540540c3c0ea40f5013080c0d0a150400d80c600e92044107007846008030420603074a004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450935530 1250 450934280 450934303
    0x91209030b061813110901060c330e0313090507080718050915280b131202060d06270c020a1704030c0f05030c18060910090c02 56
    0xe0201e1034440da03003041141c81100c812508080460f5010402c4001c204604c0c540c060b10a40100c0280d001e9507000c22a4408242c1c06013001c83e185200540c00d012041c80344071100904102100086141410000c405114170782109000c2c0b50344408140c80c2c0300040080314004064520f20720040745c0c0d140d1101000d800100c500c84005003440022441080c06a071051880c4100b0000c04865542800144107190600801000c650500c501ca0410b140c1c4031000b03100000300040c8401035100a148071540034100c02544040907000c41000211590034041c241c0300141c451a020380e451440c101d00000b00c0c00e02608842d0b80c00d007460880d001680800150b0280300c4809071000e011043d034003440c501d404a6038035030f00c6800940c01800c0410005108036544c011141500340c15281425201d8031078031004820b5030030010100584d08000c1c40145410010002c1ca000c1c1155441c0368203002c3c80314088060f030301500c0d503409440b03803002051402d03009923008406003800d05010800e0f4140880002e64070b1803505030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450936780 1250 450935530 450935543
    0x91e1e0512070f150c08180f030a02011e0e150717180f120f0703170406020304090506040b04180209010801110f07050f010c0f0f210207030309120903 66
    0x64201c0c051000c140c98085540c030715640c142e082d1510700035800d0582d4810003031003000401a580d1001940c5203015042412400c114660718071094400d01c00860109a807862007580462060300041c0c0c1c2c8200380c40412951441c800044806e58141076561100135890b243d03014000c43c950034050b03403065000d01141c60160705c0b640c540000000300070f5040c0c89050340525074040d07160a842c8150804080c1810400005050368a00d640703e6001503040c40c1c0701c100a641d00d500050810814092042c501003010300210260514092a01074040d603240b0940c1300d4035085944810018030742d03035a5a03001c440c02d002e0140041c0103444803405070036441134485108a1054221500101e46d840c414424414242143d00c03c1a1070080f03490754941c4981c0005400300e0b00341c0714030300300080b0f0070500303000b2941619007548035100d00220048004c0c1c45000c901d40c00808200e1340460010142d090003216405c40407030000c006a482c0140d0808a000d4031403036a0141c42001c0c000c807200c818503801618001100e00410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450938030 1250 450936780 450936799
    0x3271203050601030b06041707091b23220f0303051911030307030906060504020f251a0a020712020319020105010f1e030510140f07091e1e05 62
    0x20044d0f0859280e1450580c00c00018401808a103c0c0c2c0440080d0700c0010104850255540d54504000d0b59444a0a03080440c40021090b81041d00040803144524060104d0710707034a0001c1c0d01c07050b518010b40c0c1b003540c011502c0b0051a411500e9810b0f1850103000000c486643c2983c50303050181ca44d40c009240081c003030304110100c5804034030a811403900c0c005030802861542c1c42c1c13064210f001e0001044151142aa21100011690303241d200404285618005254540e0000004441c3e079078007040541401c0301c0041844030010303401400e03680541001c044240156182c034200d1a0080c062410010407000001e03c584a44036000000b6140c1c0d10302500c03405043d1212400102d00ba1a02889500180c1501c1720052240100e070305001461100e150b400010300c5603403900c07400d1420520000d102e00d0380b41d0f1210803440410883c072070154002d591041c00191410f060000602c059003074864103080303003441c1c5000390b03100551002440040000c0e0420405074083c802c2e1460400c0441e104092140a075007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450939280 1250 450938030 450938041
    0x60510050306010c17090d0b0105040c140f070305090d0c05100203041809110a0b070b01050906010806010e0102010f0c090806460903080405070608160327120305 71
    0x3081102d21072001a519555001084e03503034101d004469541c401c425003001d210a2406c0d44a9074900300425008440151040d4074000174041101c88020011080019198014254202c6442240c07491241102d6481d540c0c5014201113a2501528400a034414160101042400300082d00641613450403201ca00310a031a40f80140c2e92071040e0711410b0000480c15800585d254155070140e02800d005080040c10980188000354282059130003000001c400422180d050080031900d07503014010503a10340e609424044006805403e0062807141008290907890030141d100790440b00e4205003140040c81003084030800a4482081401603860f03500c1403c000904907000740c000c01c0d0148041140c02c901c00c18109400d001c1c43d141d40300b0010715800c144100c140c0c03201494400c072007801d4000c0d3b8131070308a804c3c10b24080341002482c0e170244081113046020301038001c42d8020304c144168141d0600040c1d00140d00c9181400d520400007014030301705086140c909102c030341c0400080410440d9400c00076662034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450940530 1250 450939280 450939287
    0x50c070b0f131b090903020717011a0904110319060509031602011202072415061d120d082d01090c02010e060403020f150f06061606020d060510 63
    0x1c035440c00381411820042008a45500c1e0700440594006649000050b241e660141c05d4604402c000c0b801a801810100030041c0d02480546c0c900f1b00684c001d10501104100010300c03103184505143c415144c9502007410407022a030410142a4040c0980e5040f0517000c96120828415142c181c41c01414080000ca03030081c040112043c003000c0a02401c010090b640044400b03868214004440c103608029000101e514600928600000f15040590101c012079107603085e5401d44800070812800000c007442000c5c1c00c02c0310003141014003e4080034580c59000008c0d890441080000120300410002030b045aa0050000384520b02400c02e00603004411361a4102c19801c09480170854280c1e080181f00d030300181d8001c14100d110600c000302c3c05500860000d414000c0544044000d68045018855071001c00d00041c04820740b061204101450240c001c16410000244080e100d010300040b0980941c5c0e50147c000b8000307412403011512421460040c400418141c0645480380b0720784141404074610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450941780 1250 450940530 450940561
    0x706080103080703050c0f0604051b0103020c0d050d0603020910140a0b07030e01090905090d020f0f0604061d0a110a0f120f0228091404050d05090f04050c070b 70
    0x42c0540e00303030300c2c15015440803101c41d004a040001c040c01841010400e070302c4200690350144d806040603102c400c000c50707520304e242d4446410190500d80148041e204101000c50750016084481c1001342c2e840326400002401005c003038100a51001c100d606000804a1030b2440c00c0c1982e0080c86003d45881c1d5135001c0003152007052041c20800030040011900091040012013500c21060405109039525100d510742587c03012a4184016031081e003004020a80c100005901c041c02c0102402c25010300048489d12628010030180600c0e46a440b40041030403050303a100320b00a046825504004500c0c5805002414942d000600c0340c0d55280c004a2000031500b0b40c0c804560305000c1582e410840d07036451846160740c0b450241e0340300c407201103012a40c035068040b6072100d40c0b000c50381012150905091100f1a12507166210190540c58200000600d0000310600c8402e060700308903444046800011f804000d030b2085840c1c200c1d06181c203001440d20404050103171680b140001c02080c0d60f65482500315900c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450943030 1250 450941780 450941783
    0x801090510020f09060414031006050d170f04080f0c0907050304030c05070306050a14160c02061c0f02042117090609180402030f06070c030e040b0307080304080706080103 75
    0x200101c400c45010000e03a07004010300c108024080341480d40900c0003070740d5500140d010014498880d910780005180a01424013904030b000c01c00c100050a280205000c040c0208000301300541200c12400310b04000d10940d51a01d0824250070707621520b41c0c0d0103a4550f070030b01418a02074418015070b6030315482c041900b1031003a9041c0da501825030790380d40c5086400960000c001e4400b4051418003101007030309401124801c00504901180c9403500007405040454000c1003200154041800300c0c20312540410030760605c5404441858a580301200f5842c12201e40b109000010352070643c070344107080c119801800031140d0741083e80c0c00d14800d003060400404a407060041855044050b80c204581080015101c0c90401600641c10a01c100300801c103810442c0000e0421003050343d0802c0210300d82000240103200c2c0c1c0d04040c00d524203080b84040c1043c80c01510003010b0040921451400e170301c0301d500039065140005c0c2200c1015903a0702034603482e640103024500246c09034540105555001301030780350489 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450944280 1250 450943030 450943033
    0x15060507030f0804060b0306010b03100e0f06060702121507031b0807110307051509060603120304030302030a180614010504090c05040e0c0a1d07032903100213050a08010905 76
    0x65800b140d048079251070061080712403da03100c040c00e101e600d0402a66010348030706c204041d41d81c04c000728000c4d41505203502036190013014401f08100c468408000c01c0d04004166605902e80313990b84002640c51540541d030300024410300c5100103500520010180c01801d040d14100f0005440d0320307402480400d100410004a08500080b4104a206d4400c1c031400503000b0055900785801c40d603507a400c041ca00c1c66a406c0e4280240c05000d19040f05004054102d00210020280d036080d42c001c44030701d400003c01c090305040d030110010b40458081d4004040c100382c40348820840351820319080c030007006195041002a40c6500020426040c41c0c41056070064200180c100039910702000c11000c1c045264194415015244448065480303030003201c0c0140c1a00603540d16041000703500c052071100c0041c203150415042c41e20a80c41301d40701103c01c280800703002040150480c5c4040200c0c0c60083c3c034410038030310b0910000d000010001220103040c00c3d200c0c102d0354903408540e0703065540e0a0b1061480c018006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450945530 1250 450944280 450944297
    0x10c1214040f0c1805010531090804030b0c12160c170f0c15070e090402211b090f07080705030910140405060a05090c040c110102030a1506050703 64
    0x1160b06030344294919442404403098254850200307400d030340484050b1641442e1164010310462505068120040c4908060142d403000350700c5050020809580340c1d944620340d201d0000052040180844014541091518a4a00b40150f4034030b4141c4c01001c501d44036000881c0032844a01d48000c03800703245060340d03885d21400340e1a610b0300c2c5504400c108184990380d10410401d8510b104c4100545103070001c0c0005402e43d0041090010381c0010000c0c807002c10444d40c00b909040c203649241c0c002c1d80040d01960003601141d40e454080e0210706289030308001a01c10203a0300d1404102048800f260611f043e505031505840300200800c84003001e43c0e449010030740d2180050300701413040c0007850b84615040125184040400100001c07200355081041c08080e900c0c0811003444020040701d030b04100041003c02403031411541d040c2d211142c03820464480c5444018017444c2510541c154000c51105100071903903401e2172101d00d402040c141d85010454003001600050844c0244240d40e80207805840e4004c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450946780 1250 450945530 450945533
    0x3071e15060b1903090b07050309150105030a140a02040911030f06131101090b070302150601020a030e0f1801090e060f10030b04080d02070b1503160306050403051902010c121404 78
    0x2028492400d81e408145d0350b981558003240369052414010107094030750f159642440c1251a085c13541a030841a143c034041d0b0010010b540b00007602900b410307009130298044200c0a20782508001c00d89101035405410081e185051100b0304a6124107110120120355602040901d550f488980803940c107111803800c280c0c01c002185813500000030ba104145171001c0a192a88a020200e4205800540040e4031502d440700c20010070f03000c585c1e00003a00340010b00000910f503134010a60310f580503055001711a010052401502c41441c84c0405442c11150f0100540e12111110020207101000800c51301c00c201c0407440800c0c4030712405010f0160b050402c412039055032640e42c1c05402c0640102e405010030040f180444138984042c080d000c1c4501190305440c10215100c00050407500011846504220b0344125016901800901140d610074000b084560301ca09095640d8020306c0c03021008014040440d400740c684c10350003450703c240c02e511001c0020b04206000300444180318030214003228068045030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450948030 1250 450946780 450946807
    0x30c0906030102161203050a1a1908010e100b010302030609010b090f10020f0f0304061211040f08071d010302090609040f05031317060c031803071e15060b 68
    0x90380040040c0015107031a40040800d4501c001c1044141c030791030403500818103680d5043c00f8041c0c03c90440d140604c01c04000e0f25030038640c00d401c1919144608400044d48006107070350300c150802032030100002c11204007001c5001d91903199101d262030042c0e290412200003503004c0e10a0324064400a024a013683c1c0c20008680c640d070388010f40e040d80c4030301c031404000d0742680e985001c4e82e00f000090740034040300c020705015149801e24482541e1015001844180403160b400700e2100c4000004440c00325681c0c86502c1c2c0c14005200380e0700103446c001662003010460210008038102200c81c24102100c1d600404000d2019030f140a0100940c8401c05c000414142c3c6000c0d041c45030011700444454a89a00e1903981514640c051280c0c1c810020b01c0340010030600200c140441d2480700000058401450810340740525840010102c90368020222120320704010100183d0760101e5100904851045002c0342c07060303d405401c0b10407518100244010003503020325000e00d00880351003030076150400d040350320040e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450949280 1250 450948030 450948049
    0x1d0402060f0f0315030f0a0b0a27050303271e10060e220c030f1a0903030105040b10080402060f0d090c05030c030a0b2a0c07150905030c 60
    0x2920891000d000b4034100c2c044402c003d501074401161400d554090100c185400c000c070b0f00c9541c01c01d40c1c10100c003800c0810074005d50b25620400d0303540c0008820190b0305160001254006080811809040200c400c0120001c01540180c0c3c1c60500022144140150070880d0346103001802d0340ca42003201410b0410080c11042c612040c1d0100075280b4151045011000700c800b254801c10140d42d44600348010030910703002c00035200f0f48040d0f0304520340c2c1244e00c500d14803440901c4020842c2c4406810007060002c04400300c85403001c0511081b00c0ca040280b512940c0e40c00038062203218502d0070b4806410b40c038180340700360b0350014542c88000f0303641d603142c00700185078121104d010242c1c4820050112800d880e48156480907201d01031155456041606141c50240508000b07402988458080404215002d03981948a05030030403c04540300d4040c000c954149041c90780c4485e240012600c0b051041c0c010600800340e80030308034400d05038540c40c1421120800c50b0b00c01c054154000000301c1d07603d401d041c0d011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450950530 1250 450949280 450949297
    0x1150c150605040e01091b061e030204030206030903030f060a051311040801061d1b0708090118030f030e031c0c020a0e0c0a0306141e030715020c0a1d040206 69
    0x40c0c4265582c0125094030425048003800365580c400c98010000c02c10070440d0007000201d003410700d5900f0200c0c040d01400c80c42102101400c123030140380344654030980442e4091980540003548a0030515032465907a01b00b940e001080802d20000101c940c00c013000f855044800040c000104004920188001803001c1c403441c0401c10410040418070031000d0042c0b400401c1d690b11080b2003445180000c1d086100d0140202808030307180c41d44441c1c21380b00c0c9010303075801c15040008141ea960303460300140c50711145401034511043c04000000180003010350600780782ca0080c1c90b00358401150004041d1110f1004a440d0b100924141703028030800d114504e088a0944040e00350b264181e191001c01c1c482e80022a26110001340c0000c00e4964603605008040042590034180e09a402800d00000d401074801000e4054806010790841010381d010441000144071461008901a4078410001d4849150322003c0d4040c00d15030780001292840944500038141c0d000c120b12903e0b44903607007084129030004c541e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450951780 1250 450950530 450950573
    0x60112080f030a0e1e01060b0406210f110408100902061b070302130c020f07030c05090411090106020d0f0503090c09091203010f170319030e0106080609060403030501150c 75
    0x810001310142000085960f40c0d40c1c003c60041e4980f01450f0a0035521690008605a07909000402c4084d030000c219401c4900b140a400312050314541580004002000c4100c9a8505004040a1084490703000b801550410410364400d950018240c41c2a41c107031100094000408110b848005048c1240c44000922990300b621485580c0340c000400c068800c46400c50081c0e41c6440c00640e058040118100444240016011113451a11075081136079a42c4242030089072454001010003031109150f0301c4011004003140c480f0750b103800000b03540f014580860b41c00309000300c07200c1e00c03e03d0091003030300d20030501a0000c1c40208904d0701406102000030705490358900c01c06034540c4c0607404210285002e441035081100c0d5031498a4110050141c2c04052824180c004101600c024516240c0701c0845420504000c0f44940e50300041d1401425680e11030b1110f40201414421016801320716140514040e40d4148100d90700c40c510014420003412005002c03a104400e44c10006845202403403403510002c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450953030 1250 450951780 450951791
    0xa0309140109081c020708070f0b0a030906090c030201080a200a1b050105040b130302030a0e0102030d0f0f0f0e0304030303181a0f09010e030405120f0a0c08060112080f030a 76
    0x3902601c0c140105002121405404c07801c02c9603c0c1d8100120402003900400812460f0b142002c03034a1440c5441c00fa640303600300c0000704001040d001e0307004141c0450b4000000c0100600383d080c00142c54441d404200c1c00940e03141c020a420101d68000c0d00d03250000124070344c0000140104180107513110420b44000d004110459400c603000009600380742d00e0041001145074581460716105018004209440e02001c061040300420b5000003070f0362507102c13036040c14414080341c100103034518010070541c11007aa08100407685810714540001d040040c400c0420304c4030720b641040700030545550541e0300505500a22041020a11a4001002c41d5440003140c010442d215240c042000220489983d6003074101c4051110801111408641c4294840c000b005004a610780c1e283d1648110301c14540b01d04d0010b80d14946848091004441035542c032400c450000c0d0342442c00350651405445101d103a400b82c040000f9400000d0250403103240c0c0d103c01142e2a0584a29105a01383c00203800103d480380d450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450954280 1250 450953030 450953039
    0x706032c0a0b10030b0f071224150e0301020c0c0d14060a0203041a04021509120105010f03030212090a090e010b09040b06040f0905031902101e0605030a0309140109 72
    0x2e805903015001d04030888070030504504001000460240c0030856842490042000c1c2c03d83c4280b0380c0c2c034138100501d070100d84280b010030750200c1ca200701454038211140a22000801c03800140220850349640c0e2104541c10f5100d0003058201d002d40707074884a13550050441074190b481d1580c03000000328410f09003043c01e5000040034a1410004480c048181680081404284002c80441c2400401c50002103015071070154013042d07c01c03244040c00809054041041107040e50b0302c00540b0301740100080204015030f52070030b1000d100700035072001350054040c0344d40f15003154400d0070840d10111000340603001e0803454030385954003d14621322040c0c501d5603640840e85047d036840c400c07030b03000360f0040844c08a1414032004010031101d50094081c0080d21b48011030700010001b20644428054400c0840040f491020090b07080c0208540e503480c0d010300d003015880e4000b80d00703e1180e2002505140400000d134843d4141030380c4184c406009800b0034090b20080040080710711240c01010010315100c1100350741e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450955530 1250 450954280 450954293
    0x19150509071206060501081f0b0c0a050102072a0806011211180708090a0b0408131203080a050a1820060d051e0105011e17010b03090706032c0a 63
    0xd45400f00c074400d4071441e00b00025a4802c507040e07040a070220304528680f41d104030322509152144220300c210071011580740c00d048401e01c0020300d4150031900070b41d615501881d10340744a02d40004003011040b2605026600c9120400c010401c1e603842a005068036428002d8221440c1c0c13101d801150b11148103403580c010390300c1c3d142d034024080c585c1e030381d40d010342d41000c2401401d0f489005154408641c046c544840c0824401a15107030090740010b0034641c0c0e20105045102c2c00f401c41d40003141301c50018503002c0201588404460b12903031070002c1c100401e40300c5909143c1901e80c0546a41c003041c2007030300f040c40419400e20441d001a0545d150a000e202414004180c00780c0081551207046030791203003040748980c41034158a031001e001da07040c079080d581040c0010b011800d950501c0f0100c40d82c000a40004a4002e03882d070354051284028041703507980d4550181a55500c1203a002d140b6019200c00090128000c0c000c01c91b44015180c1e02c005141001302a10841c40c000c11485169031043d120100d011500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450956780 1250 450955530 450955559
    0xc050705280204020d020307140c030a03091110020f060c030601090314250503011b0504062307080712020604050d181701020a020d050a080c09030c040c03020c1915050907 75
    0x1d0300c400581ca23441c1844c4054540520b002c2202031130802001008040840801101d000b03c0641c00c0004d1070400d40c0c04c2c00315100b1034004d04130b42c000c420700e00715107032464001034003030355403610300084900c1b035600e80c81d05241c2400190341060202c2d1042005000080d082001108103418441c11144115000903196200106100c4100d520120b410000d2050b82804c4c0a409000f203005031011a6030424101300138100d2155100e410100182c00500c1042040100000b03005070a094680036200d62880c1007003002540801d108550180c0c4410090303800c40d0000c81c0c1180318940200150140e900040800c5d02c19640c8110901a140044180400c04142c2640f8000035590761400060f25485003580c082d2502d100a0349280030b00100740030301b0500c55800161240d21024112004c1d403200c0750349000c80d140246072a2050340c01410241408000f940c142e0150240c664030038122102000340c3e104c072824440070140d0160100304990840c1f480056960013058201400781c0484034602d5503441110800751 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450958030 1250 450956780 450956797
    0x903020f100203161110030e060a2019030501080d02060c0a0504030b0108061e01141915080a0c090e06060304052803030f020901020a0f0204061d0a0c05070528020402 73
    0x203000032581175905201354100004111818100295070303200c1c3c2601d0352034000400700c9948ca51103481d4881003001540c8445000b401c40480661200501040f003250b41c0c2940052b81c0020380340c01c3c0001062000043c048500168a40182a0303544500284000503841906a5018414100310000000e0002c0603018000c0020780090f00003030070200e42110544036021801c2520b107014200501400500125458211f81c0440e03603210032403611201805031820950208a0604069049450450b000042180301e10464201040403240000003540c0c581001c0c00b0b1080880090000610b143c00d0000c000c0d5040340c003d40032104404134403900d0760f0f008a0501d40302404801d104070000101609400b8103185120b455009504003031074100001d649440400015142960401400045d5203541e44814050110744400c06d98074000c00007000b40750002995a901e903a4501560701c13940910800903108030a44c810003030a0640c0a8a103280642081040c002c48102818800c0e4001695184001c4c00c04a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450959280 1250 450958030 450958043
    0x402150d0f0e03090102150a15061806082e0314030d1a0d060903030b0603180601080109020117040c05090a0b241c02040b0a0503160903020f10020316 66
    0x801d6280c0c2521680a0055455403051080c04502d030380100302d5a201d0668491000c00d00da8806940902419150194600d01410030f600860003507071111143c0036a0894400101c0159542c0c0c0086a22200849161040ea010722240c003407005219900c449181c4c480b106038085e907079102c0d110400e41803030410449407554400202001c00d40d0f4140110420440036246c1540100403001c04107551101c200c0f8024035280e0303a42d40c00c1c0205400b07913000d1701a800000c2c11180e05c0b803078071401069011000003403110311803103884000925640140071710400ca40c0c1c103a460700000d0302c600c2c44401140c01d003c0c1081b128030512000100302074445c1c0d01c0c0c140c4602907110021a0b40705609051283d11003841c1c41012140c1000f014402c88001540200c1e00300f8445076145800300e02c3e0030442c000080c001c07500090400c0b80005828084140d01c44080e50144854000e074050003a541d0700b069540016078440250003240f044802405468500c804150307500c914015685003110460300301c40f04081c80399044484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450960530 1250 450959280 450959291
    0x60f16030e0a0519020901170304060507151a121204060f110610090e030a02062d0f07020705031b060f1b0d110a030c110105120f0714090d0b0402150d 66
    0x81d844c106c01824010072100d0041032810480e6412141c80f40700398040d031024000000390403c00c00482907820104004003032400c1000c0e8400600f40e04212003407120a078420580f4100c1c04a802e6004141389440414034881e03d80b405150401c00d844580000d0400b1041c081c022445015044080c0909845011002c0702080c0d2a8100404941202e404000c2810680c0c000d10510300c20503000500950401d810000e6142168160203503c40742540e6103180f074403610500c3c8280800c0400c106850380c05900149c080e14209500c603002d042d55800c00304028480700c10b03041003042e218100300c001002c0141c403130a169803900c10402c41070310183e40c007540c007224150b00500304008540d43c0482018200c8100b0303400307000201d45980300101a0714030000c0103842640b8003003024209a02070401c0f1414504015110007603460401198484c0c90300460314103020601c0584c0340a1179900c030b00200c840310000240a101143c01c15161461400c000500480e003002100e135481c0c1d10701c6000b00103055a4400b00101003039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450961780 1250 450960530 450960533
    0x6031a0703140405030306012102070b06030c091b25080726070602130905090304060801060f091401030609110c07050a03020d0b041104020406090305060f16030e0a0519 74
    0x300c40240c101c00300300c1e25202c418400083c20110841c7e8100c1000d10300402e080440c10b20041c81ca54030041820200e81c030000301c0c00c3c100500c030312040d84600c90403015a1040c400501c04d1007180305045070361050380310344024240319011320741000d09089104041102c01c00c41034100c0812400c0443c0905a5840201240791820008803041001030090350610f0300d007036400d0500d0011388034010820001d1102d6000300b007025004120004600042120410521a0741490107846440750300a0041d540040c0040c4c002007445409a225038002e141180e4481070f00c6894000c1646050166048003410142c50307040c00210444280180c3c03a41010405d62503503100a883c0186e0301d40100c0703a0000340500307103c000c02c00150303444c840001c51068200c400302c03080e59141d15080c0c8000c50110000e60348684049004200e040d403264140d015a846542128095181c0200e08080d1010444204600540c0c046002c02c0c0d60348030360040c0101d0700d0028210f400040072035958604020b240070419041c00081017200c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450963030 1250 450961780 450961787
    0xc020907020c0a0b070809090f16021b040e0114010e10050102061b0a050d021606061e050f0112090501150b04060f0807140c0606010e040c0806100306031a07 69
    0x2504102503000402d42c1201030008910b00c040d043c41140d090213004204c0301e0a01c00204100c1d158a030009100000754a04100036010348002a076050f001d00a500c104585140d000090660801e0003010b0010400c48960f001c00010341003144c8210030a54039030403169900490271a203d8080d00e9000081007003032401040f482600342441d4040c6d81154032190921100d10110749806d07010880c1d0510180e41c80e07100041c191820320940c000502d810340b00142c9000f0610b840c2d0002c0400318413400060001035921a00d6a85010320701002c08070185201000700200d10b403a00100c4000303034040c1014452142d14007031003021904902403d460b5070351690449180c2c05201d06000303000d000001310080c2460304180700202a160105810740078407001d18042a142ca00134440850b101d400c4038006581e403008400d500b904c89105a5000c3e0101c0e2032441008070304d28003409107540c015403d0351140c030340e542c82c0300c10000140e00b8100c1072418540d0b03500c00400800c10260f1000c0c150703c280c1981d64040e003001030005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450964280 1250 450963030 450963049
    0x1a0906040b060301121b06090807090b06030604051b071b0609081e19050a1109060f0103020318070602060403110d080c0903070f0f03020117010608040f050309100c02 73
    0x480c4101d2420107841140d03640c0c2d00070303a07054814000c400d41d1203591628000c07441c085469002400c1c22444640021090340c42094002074410080035121143e981c2c1c0c07101d00940ba0000429580000c0910000c0c40b00d04099000380ea01400070b1f00380521000714810082180c1e4007412096494450380a071310f000d00d1465a000d036004220038a02003004900d400046912100310070000e02c1c40ba40f0045211040c200300b0002440d0490081809144241003450f100d55624030784c0a08036000e03913484148403070a01d4009206031081a008d007007820b680c1c0031f06004400a507c002c001100045410f84100000ca01c00c10284000d001c168004050034103281c140030303100c03917032284900500358040e1000400f943e6000001c0c540000385224595251000c0710006030505096401c0402c50204240c1c0c0010342149002d45103003202c1c001e0b03d03000d038070300c000641042500c1002d00401c404600b1040100380003840d1300280c1c14090340160301fa2420482a80e000038007001c003248000c40014180c19481042d4034140342803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450965530 1250 450964280 450964291
    0xf1f0501200a020a140a05060a08041506050612070f09050f130609020c0607140a0203070209090c13021305040204030209060105160b0a0906050c07020102210403050114150618150d1a09 81
    0x240303030809e003503000010582980200020400201099004c1e42010b0ba03800c07140c080c1c40000c2c0b00a44440e461a0b90304140c4000701c914200041c1501e1480302d03010b000e501a0401e070f88028141003c10354031a001e02c5505c50742c002e40c441c080d642d11f010015601e8003e201403c2c1c00702c0100042c001c0303824000d5004150908103003140b141c0d440100000b117940f40e0008100c0d14419030544103450307669a100842da007015220340c039440e000341003c180561000081c0d402000b80c814001009103036a034840d428402203003e90301000790809440c00100750103600401c043c0000143c18201d2100100180c0e4031910031603420b450304210b007070300c880c0a0000c0100ea40a80c50b4040000880e40303040c900c3c03940000b5558918211483e152041075807140b010608000120340203141c0080007400781c289003018a90301e03000d040b1600c540c11904000c1c980668603290046407100024504100c107440e49640c00c000f00e038070803800f003085030110401c01800c1003c81801051001c040042a103021030343c0320700a000b00300600500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450966780 1250 450965530 450965539
    0x306020c010501050303040e0a1112100801180302061b13090209010807050c0c090a0e030c1b04050702150705070f0302061f120f0c08060f1f0501200a020a140a05 71
    0x2340f08051800f01341c81e03402124454040740c4154100b01002d4607220718a2401504240c4e401082823003602c100f24a800c80c3c405800800011881e00ea503103881420742880240181c00440c081002c0c0040410035024102d1024001890504888002020107880358803100c1d24a07004a8800c0302c640e041000070307038020b044d81400c61030540c440040d144c5500701009000e200e00218404111700101c140c1c0450f90001114049969900c0e641c1512175071401501500c124002e06140000f4050070140613403401040c558005090b80c510062500ca0342c00030040c142c400300308044c081178010400310881410b116000b600602001e05288190300c00f03949407452a444040061002084185154490080b43c5500a4003005031682c50f03290070381034031000390b01045481c0f0490050094041401d8241c0f03000b140c2500c8803200d01e1101090100400d01c0c2c600c1914003040c020000c9510361500c01401c882d5500072070040d111441529800201515601d803c1a003108030955000b5002d41010340080c4058070003101c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450968030 1250 450966780 450966787
    0x10e010b070305130e010f03020909030f1b0f0601060f1d060f0a030204030606090b091302030d0e0415150212070b04030c150f0207030909152d0306020c010501050303 73
    0x450104151081c0d2600500700000000c1804582c20340c506804003512840c01e034086103503034030f00281101e86007070b0009030b200b1030110001c02c003d010b00008403489001401d40703160a02c1c106200441c0d0500829000000d2402440384055140000b40400c80c064a125110301d800303902d03081e20081030616a04011400c07004819102e058566800703040e240206000803034240d4a909088046000e800b85500081181d030500a0204481010707801100c401304040e03611001540d00c10400c40440202c524011350580c20800085a14a21074540b00040c68005040801d560015a0000900c0606030340a02007c100340c03203a0b11009541444890108401c002015040640b651940a0540f401400c001c0038402c1c145101030806c0140c2c660300003035001c800c030200005c04c00704420501a40c003a020480c00500c40b11804580310704140b242405250903064041c0325581065480c2c182958a03400c13810038a8030700a403004001c0e50340705600300998400c0c5009a2640d0b1016000340c00c5d2001a08030900c02d0f001031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450969280 1250 450968030 450968039
    0x9090c08041a0615070b040303110304150525022d06010b070507080a030c1a091923070f0f18020a181706071422170d0206010e01 57
    0x600d000d081500b1600c0c0c1196a40e11400000340003000c1d1074000302c80640c00425628140880f00024900c2140661401d02424280505c40d1242c0d2000703d4009000d41014040c14200c800d60358840d66001140161000380f403401000c81c805680b0a000525005900c001c80780140500211004001206800d002c403d44010218400d07446560500403229050004241031051040421003180105010b1060b600e143d11070307050041c0741400d01e40068400610400e070504522502210311481091564040d010000c0100611504e484030a1400d032070004000258085031415240e041524214400080ca41240b5103608180049038a920081c03042210110800a0a069248406509440d0b110050b66000300f10740136610345c0c60544100c44c080b001c41c400170a00144121252207510322100c1110b0003569060000c481c1031743c04075154160380d2000d11460b0034011642201403004098003841400031a1510100d0341e0040c0311403540381c1c0c00e03482440c8081d0403940601c450390162191750b1000440d036042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450970530 1250 450969280 450969293
    0xa1509050f101404090c12180807120e04060f05040b060301120b1b120a0f0c0203040b09040207050105310201020d08070302120109060f1d010b03042109090c0804 71
    0x144510024000c1c465120300d0b00344421004c84010b420750040410240882000081c000c0c0c1c000110b20921a1078140203220500b020a0082100759004d1f006903d440c0d2141d0b40d0700343d1415909580300500440c94002ca40c15590f038044c500103040ca040000b00c4403441c01041000b51181071a880d4003841041005024a0000d200c641e00c40b5a0441e407442c001c0d440e402d51a1103000c005082210540d000421050505146005d9803801091142400d101c0c02101101140c2100e03118501140940d108000c01c1042da8610030140681001c020001810700c1559101d89084d110129201465030b10804442078904031f8403140f103000c000b141c9010020280c25940003035501c403503000c486000d12400c040012141131180c0c040340e0841745500300d0f10015580d103001079405842035000d030318080d203e451030110b20a8110040c0d4080060301c5060841c4031703460708103042c83c16400900300ba5100c0e01c14002c000e50640e00003030208404c01d0b003a074034070050600d062004401c4417a50700d02c980800070010b041c000070422 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450971780 1250 450970530 450970549
    0x90103200429180a0e100504030f12140609100306020c01021e0f0a030f022205120c0d0f02030c09011202100318020118080f0f010c020f0709020a0e0a1509050f 70
    0x14902000071780112116296450150f005805603a4103003010104010907920044401041c00280c0b03600c0d143c0103d020091082c1d131074103c100291200c2100029582d854110303101c0c0d4210900c4d6801c2c0981d17a440751181d60a82c3c2c0240b40c0380e000b984d00020740072807200c440c1c0ea450b2400c0c10180d0701241070505a40b41411984603903000c143c2016143c0c400c20f011041d040d0304440841440c01c03070841100042204544043e01c0307920890b0b1044292882c030064907900801c00218201006003c09040c40e890384d41e96a099400c2d0000341c0e050f01c280c4000c1141612000581c2c0d018001600d58200303003ca46104020301752031145040302c1003605040458480c0c02502444008040d82400d040301295003c3d0200342581c0b0450748003944a00c1170010761070a0703c0700032603101c0e1101e8040700280845044554241e988504040d81400c01c0da100610400c140344003907000c0c00c1c02000078504101c581050f04006006203510f80c004011001c08250100411071700a00800000d1005840c83c03045500b648000071400e65 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450973030 1250 450971780 450971791
    0xf06050703081302150403060c0f020c01020703290c030414030a0c1e020310020702030f0c010509060706020f030411040b0904020625050a0605040b010e010509010320042918 76
    0x83c4041100001c6554400d80b100401c0c070010520b5480301d03940e09000001d801d8400f0440e0200e0384d610103950030b01d0310109100d0400716060700141901480e695030144140380c14000d0010f000060306482c41d10481c0110f443d4052545540495100d0034542410180c0d40004c18600019610410440703007a15088001c407c101504446601540c08a0211200303681510390b07802940760281c240d1071000204590301030102140250101d42200d50850305050740c07170726208411804913906005095440c6040d0004183c00b41c4981d20150a0011140c00340781250402c0c0c6003102c5250995810784100e05191290120503901120b9a80d810308058010800c14454040c0031806001101d20301c00c903c51400c4000310840303a1203c221000385d40310b030410313200403e0141c0f401c483d40d078404e0000044c40080c0c850b50300c0c103954004089111a918503039645202c100801c0c00c0080030000b01401c02815503a9104a161600f04070480044d8980f00d60740c0d4400380301c009401d0a102d00103c150901c212505541101ea101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450974280 1250 450973030 450973051
    0x8160809120d020c0f011a06180f01020f01180201080915010501180f3809011209021c0c09230a11070501020c0d0804030804020f1512010f0605070308 66
    0x450b07041c080440a4440e281c4160458410459100f124460542c80303034445040b86286400075111034000c215144c810f14000420301d00140c00f6683c5107140045100d42c0f0300205004503000c021059040c1820744820a4144e00d1550400395039406650708058510b0744010002e02412041e000d44d0b98070894182d060082904000e488101001241910a090800b4140040c20031441030396410100800e04c5003c4090351501c80c0040015420400140f1100f49807d100104c19060488040c0112803031441102c0710a041c540302c3c000341c405078413140c0c07550344402e0407445040d400c143d0908112485200070341c41a20006d2410340302c1188407241c81840740640d50386440300d805d181c0350350f040940646185110036510000014003001002415801081440c00240907500788010050081e02d107030008403400f03008a220301c400640103190080107400399140c0144072504a0005192440e03c0b504203e05040c800c5a442c3c005001c03c404130803d0200502c1c0301e180c00c42c0b418030140d4008060250180680950 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450975530 1250 450974280 450974287
    0x60412030b091b310e01061706030316080a030546050702030403030f080609180f030d090209340201020705010c052505030a0f02010b0a060816080912 66
    0xd2410783d100f15510b008441111013080c0c08402c6054080c034003aa45a070042990004002418111401c0028100c0315980c030b803040c2102d402070291246140c000d040a40c503001c00c00824040814080a000140d80503010307458a031110b05601508488025004000401044d00301c207405d41d0404003411842c064149200c10890680611440494803000320400c03540d081804001c02035500002078401c4a0190b034039020140c03140f0382e0079102c510040e1a40e60704000204005074801500c0e06100c00d41c0d070900c4044034041800c40c070142d41150828030f0310700001d544860040d015803400041c220b4002e8510910210110480c008048910112100a46502d24105800400c95000b0740c10f980001e900540207201006644e0001041a405140181c0308060a81d4440c00440c0c80c84900c0b403000b590002c003d514040070001c1c107540c0700c00d407072041e00c0466403192140096a112444001c0003412503844801d0541020390742e241c1d51009510342e800801c0001c904004040900082e070340085680320488954 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450976780 1250 450975530 450975571
    0x4060e0f22020d0209181b0406020604060207020609030132090613021f0810060206040f0602030a1d03070201030e15160c02030105040b090607090602100b0d0203060405060412030b09 80
    0xa405110861030303000a001b5071400d13002e1345c0109018400e030740c0c656829061103001f1011048a004034000c003401a40010001000102640d00414800c0d0000304027505011450700003a0940300380302c02c104140d40c6404655003103243c2c00ca0f410a099100899405000c3c50440003056a600b401418210320711503a0000700195280c81d000c40110460150804181030362600d4042c180001c1602c4d0003414809500300017a50301c2c40480c40038000e5a03c00442c41440d80c0640f5030101941002d4010011241c1d40c130f0381d14000000c49803490301070303c580b403000d9034440005000150071036107104880383d5990032000018500305440c0d40181c1e88201003000e00d101c20108100202d0301130381044002500b40d80382c441030106101116488038400c8145034101d85181c0c1d10884201e4450010b44607200141e4440715005030a0301198021a44021010301030418110311600000c0c6889010347d0180e5442d0481320610044c400c5409240c034901925080c1401180382440104000150080c00e91040003444101d00700e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450978030 1250 450976780 450976807
    0xc0908151e040f1a010305060420030703030201060e09060106080103080c100c05030a200a0305060d020315091009020913150e0f070807141002100204060e0f2202 71
    0x20000340e0095541c16051516203800300d10844030402c142c0d1200d50711000c202d00072100c0042c150503280d100001d0a256110341d078905190000d03001e1914030031407001d420340517103032020044503008600a0340041041c82c41c1540e10980c0d0036001e0a04640c60300080010702040d070300301d5800c9045a40c44200c95903211001e500301030400c4640d54900007420f09010501d818a079000000d140603080380c05081080f0201503100b041c044618008a640c2d5103414410154640c3c06980503075800b03031016101c440e5600683c0d00180c00e18049000c4004445070030001d00840041c1080b001d001c43c1c0e280c0a042000c085a500000c3c0180c2000340b212103840d2138200307840200542030a91000300000d0010030300c0b8105181014985620b0980c03003418040c030801c4000100c44400103450012130794075000003e41c4000700c4003800100c101545180084d40b06103a0a004d00b00031745e10040008011725920740000b00d4101082000115100724444e10404108845a0748000c50018541004510040040e07440801001e0381e07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450979280 1250 450978030 450978061
    0x405030c150f070c0e070807020d030c11120318120904090609020915131104050910030c0602010c0905120d030506010c0c03060603060c02030310030206030c121005040c090815 77
    0x4040800424608101302d6078605a10641d0140100b83d080b42d9034204085465942c11961000103074000700048054500940c403900c0040740074a044080e074000101564a0020f00b0782c00d00a0322100001080b12070ba840354101c04a07107400c180540b0140c41402400c0009004410b0305c0340c8220f948034035201c108900da9014914007030b40a00100018600700da036001071828a000d11502451407003080c159244144d128201d08002500c401c00d0030a03081c0006e2041100004110070846030601502001081d003a00b00c20000b802151300104442084000052004000d035018900403440714185140042005c145054540c1c02e510303000545961702401201c800d4442c07071002d00300403c034080100034801641c1082c0701362400b444041c01849200b5004a031f881c4000c030b0303180031003c18040041c00145000b80c01590003a44401c46030381407907400181d40b07101c640c0680b100300644040400400c00b44c2498010541d0b0380c1000c0c2010082546040901a1507840d40384503501d500c2d59010000780c2d07100c5070400c036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450980530 1250 450979280 450979297
    0x6051e070f170a062102150903031b010f060e25031806020c12070803040f061103090a120302040b120604060e010305060a0f060f05090a0b030d090e0109020405030c15 73
    0x42c040d6820200030070303c0101981d003d24101d1343c1c00440241c085100b002c5900c00225070107400c2c0302c0078442010414440b42c228071901545030204006621503040949040102c607008000000740e00701c03043c01320000326400c55200000010b4628108450404c003d02d142c030601c0c0c0102c107000c2d10003494034400c074014a000c51381c501d864107806180313205211580e405809242c042c032044941ca13031030000c0c040840e03000750707940282030200400000f03002841408c050380442c0d1148901149136045142e0040280d081100e04c03091560040c03446d43c003400078000d001c100035400c03410214038050510219069612468000a101000b501c001c501d980c4c85c2c40c0c2c00b000041c129005000c0c0d440d41c4915003e5101c0d04107803004410b06041c6240324900e1001032152034200d0392000b075024400f61601090141803c00280080800c03a6100ca5a10303294506029403078140944d84e81c1d414215040091041403000d043c0c2009202500c10302c000d00081c1c0b40051500d1b880c40342128080404622080c54160390320900c00d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450981780 1250 450980530 450980567
    0x1602010e031903020106080a02060a140906030c09011707080109180506070203131409131e050c010f170103081c0e030a1b0b06011416080706051e070f 66
    0x705401c200c0b152844101440d100b58000e02c521551101c00d80d541d40c41028010b036000004003c183e15080c061048100f0303c0b260b050b101c9050032411130024590360003c481190005400051484640d070788020324801951645d111811141000a402000480140503041e500c0d591034001244140140201d410440e03440800c660b0949064032009480380c005941080000d01c01c0300c0046644003094601da44089000b03003008559079110706407004400405081964024603055100042005c440402d00007140148000c3c105036030781e0400140201e810082c01800c02c0031550940d82d0380c4c03d04010507030449804c01102500c0d0a10341804061690648c00c1c0c10303d040703240c180303c1040101c010001e005810036944851082c0350345030b10f450b01344032004800100700d6014500040d050358082c1c1c92002d9806080002d0509003030a560401c081040900801e6429547c046071040401916000380c56015074150320032503030b6070401003040403118800b405002c18002012504400c040c0324a140619400b03c444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450983030 1250 450981780 450981793
    0x27090509010f110a08010b0406080a050c070206160b0105010507020604030f0512040e010f0501030903080708040c050d0c032d080d150b070c0602060601210912080f090606061602010e03 81
    0x303840d012603030184c20114007190050b000024000d003110141c070700301c4143d0748861042e60340360342c520320090000030f00045030701d4001c0c42000f0150301c42c200584011114030711145068149414500b20001050340040d0400c14200f142c00016191081990201da9001040400c565035902d080c07030401d1071031300d03501c40001000b18002035031443c3d02c00010304954152551003a020345070030044003a41d55907000680071442c2100030403580c41c86060601d9001d405224080c203030380c0c0c9490010700b0550700300d8000d468081d0740390414418400000d1200d8442c0048031030030703600c1000c2d0b52050950600c1d01000a0246440480c0031030b01d0a1003a000500b0741400c1c001d030300300c1c095201d01c001074040e0030612041d200641e205001040c41400012094040c0e94142c66444160920b10500d82e006103502480440c0151905000c00004603510080300103507400303448940061400d8a0300c7d03103020350010280e0301c03e17921200034081192502c8048801035245081e00f204110018001a81d01c2e1600415040c1c01d881404c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450984280 1250 450983030 450983051
    0x1a090d050a0b0a090209010e060d0501050702011401170a0807031205180606121f0e010e010219030603020f091807140a060801050f062503050403020127090509010f 72
    0x4104100304520070051052183c4944900404403203505400070342242e1170070300611000080e03485072540401300512040400b40260384d00e60a403041aa01c420140c0c2d1294040342ca02240d482000b809001c4481e007009500101000b0141d9820041c0c0000c0c0c08144001522070500d8030403012440442600e18040c0001d04014550710b8513240c0e01c2c0e00b0f40c2004d010305000700d5464503000b4510700d9000c007140d0003080340c0000380080228622400d0418111659039280140d2019000e00805902c07551303190005840e044010184d450f41076400d4502c0d81094640301c1d0610060f23540041c8003400000075a60004a03542d045109043e060041c905207480f0320982d8000207903246007142c41d0100b0321047c0c030910103090f580c0009803106202801f5155001400018914581c10418040c083d5a0f4440c0901030f4a02d81c0c442d600d0031200d02004041e000039a0019041c000c1d541c000c812008a80524181c1115090b40e03040e550014039280e00422071382c10b886070302044900340b0075044800715203401c100400413025035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450985530 1250 450984280 450984283
    0x608010312030e060a0f0b190e010f030507060807200a0606080d0212090f102d0c11010201020913020306040b040204060f050c0a210215101a090d05 65
    0x24802200c541140d200d249040d00e110380641c6010100c1c0c1d100901242c3c0fa4502000003901959010b40c0381b0036982c1458000d0350352a030301041ca1060101070703101d000310709012140805010582013440b03000741e803032010000150001103100480315980382c841c0c0c8540f80d0a0048402d1400089081c540c3d001d4041401c0c240b00e404202004482c2c03003200300f0000e8650313441c00e41d80c5030110f00c080100543c02101e0864100340301400100b1074844018408a18000b220780007410400c0ba01400b50000b07000c103888000044500d00c601025441c821601e9a00305101040003081485103802c01808200e01050f0310000740d000f50146d840740382000b006000d070440601c2c0b480000b5081242c101d440395040800344403943c10140300700c03803e950103030355154009145902e00f5a201c1d4000c02c0103036290b00c034034071140f0007040e030000b1520031080741011181d042c061040d000900e003007601c82140c1824082030040c041c02e5100280102c040310744181c02002019400e40c90044640940302e1340c1038200d030010300040d003041320 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450986780 1250 450985530 450985547
    0x5160302102d0f020906130824150301090b01350c0105130305010c0c05010b0a061e2a140606060d0b03030c010e0304081b03030301090c05040f06 64
    0x5140e8041006180581060b02108030860021514040608016440d500280c0000b00d480f208490b01524140941c004034403a9408051a288040348130003003402405024000f510032203014281009031010425007400301c201c00540450307440040d079100514103403000c2d04501116074200c01101d829680d10900b20050151420b07074481e4400690f60b010034002d14044014140d1801100204181c403406c100549050b40942034401c29480c40f0070303002000030805d00070721006030390560302d078081c0d0030307451502d182991081e40b0014842d050450062010b554050505c1144519a6042c00c245060104003170320040c00d94601d100e0601c1c0700f408840142c881c10711a011583c5c1c4264215a10b40c003904045580759601a1151a41300504009030350704c0d404039811042c80880002c0940f40340018080302d03a406c4804405958040790808501040110028070107543c441d40503650300c071880702c1c60f00300007034903444140204840c031581d40740c0c410841d070b00c11001c3d10082c1c600d403070044013405d072030b0758020b000003c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450988030 1250 450986780 450986803
    0x110d05010b030d110309010c0c0902030c04030204061706060418050609030a0f08070c02060d0b040507031e0e03090d050703081b070b0f09010f0210090b04120f0c1205160302 76
    0x2140f02c081014451240d207541c09002d0412010b1410f10106000445070000d10040581d4074101c00500400e81028502c011800390219010455945145205110503580315600003c08105126022001070401041b06548003a049900003451085501c001104a50200025001d44105003c0100b0044000014205020b40341c0313038003040b4242580100c4045408880e40c100140c030410f00e0400505050001c0e0025840e103d00101da80e2030b010000c103040b01c404445c2c690000c1d40300d04842400c807802c89071844044592400500007140000b1110b40e880c030070034406500404201a055007801414002c44002d10790000500b5035401c0340c0840c0a000320004001150540119080024100056000c9800950211f160607040084032001034650014603070044003980100c20880345400e4075841041c503070034859210039a403420700e8144590300b007403c0503510301402a0341100040494200420b0455030b80c0c030404c070b40c0c11031000c214220b40741e004080b41e1031794140e480c0c0003403020544c002c01c0e03019000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450989280 1250 450988030 450988033
    0x20a0201060806100f06110a140607030621170d090b07020c01031a01030507020c03160906050319082d030f09060606031503121209060c0f09010507110d05010b03 71
    0xa07160034203000540b40a43c800c403200c102c806035080007000d001e130048861802014040c0c90701801d168950a1240700c602d40003427400d0b0400701c100400d0507003601c14400540754000d60310b203603880e0f01c49000f00b40c075005540260400811070481c207a043c840b9010bc4000300581e00b000d01c1b1064842c42c0c0841d400700c0c00d856840250041c101070a0495200c3c0c86002c2107504804038171651558032000544c000c12010b1300c89400c50040712950300241d1400c000703554240c0b200d020343d0782c5039030b1030401400101d58150700964401d421400302d58403080000411110310a070400700041e51114588015004400a420001d90541c03e0481200181c00f41202541c03068103408400302c2281c0e03828280c641c0300c078411a080c03603105030b044c00480d58427180500b625800c1903010b000ca810b2205080004222030700041543d01081b0103103c1000314250782813128540108201c0402410f026203014120064050348421904100010541c0000d010141c3c0802e92400f101400b001c07031600040c02c1c0707030b8040c00b100e0640d58041d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450990530 1250 450989280 450989293
    0x8030a08090a020108060402090415030b011814071407060504081e09030a1b0e0a060911030c0a03092301050106030e15181203070e0a0f0b18010909020a02010608 71
    0x181c0c008207000105680c1650781c0001d03a503d5104010003900041d48071074016680d03141292449030b200c41060040d500500e8071640d25854006614608942d80c00681403482c1040c102004030340c280c080d12500920340303080c4109a0046408454142d00420300c004c0c0905080500f4002484107440082001413800444892200400c0a8451241c841c15001c150540e1100504801103546100c00b00b912000101407001c1044d40c0702c17900e80c814002503810043d19a540d00b0100260000ba01c180b6400c02c2000030820b007035244ca00c1c080c2415004140708070b010b154480456004200c80c25a040700d012043c1e56505400030040002d05009040900032180420b203407240390b0000080c001007081703029036041c2c0c10b01400ea5580141150700140d860000046105d01081d01083d00c40010142d8440e402e680e44246a54910108109041c903041c1c1c407503000710029003014801e502104049485012100c1d0ba886181011380e40101c0d84040194440059188040360b8103800c9641034101c030341110580d20881c4c15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450991780 1250 450990530 450990541
    0xa0e03180a090c230405041a040b1f1d060a0302070302060619032d140d0c0c09050711012d0501080604030c050102090310240f060e0d02060408030a08 66
    0x888081d081d901c07011400b01d00c80311a1302c0001080001c2c04181d072540880c1031968074000708003500e00201e0740300e09000003c1078420075401c0502c510424540102e48290715020b00d14003072142c0c00c002000c40d9082007030300d184000d4885100c002520b00d42038007410b0310380d40d1a159807008000f5001a1f104a0040c015840815810700c2c0140401c01030301101d60410800c181f03103540340b01d0021242c4550f46c080d10052990000f004414003480c0003028040d00403a50318080003078401b400d100d602402607051022151444020541400018054644440b000152500d8200f825101d002186406a92644c00d09003004e0409412024105200c201c501d0160549032001d080c41c826500240515180c96004400085c042803141c20603080c0940035000040c502040c01012078101001c40f4084200c04c1d403544081c51250180d0380c01d101500451445802c511820141140c0b031002d0584500d00402250202c16100c0342e554800181103140c0c002c018582d0703a075488104517102d4200f45406004544140001030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450993030 1250 450991780 450991799
    0xf0305030601261f031709030618060a18021f020d0c021305070c06090f0b0109020702010c11031006030606080105130b0703050c1603170a1505090a0e03180a 69
    0x140e0b00c100700f003000e039126070321410310707200c1c203c00100303422040030b5086000008100c28101c41d04141c580748400d03e640e4102001410704c1d201000c0d00d1701d03411105d00b030a4850644404104550440c640300004244101d2a901600b410a111007000c0d512040c00703241d82610401070100c82c0c8601d0320310380070340b13404511880043d984201d9200001e50440f15612450482d10101c0d40443d03400b0b92642080b580c1c000c1142c840e1401c4032000c81046034181c1d00410701c101070000c542041e900405511b40150b14161050740002c0408550030300c0107010741c010074804012640c3c1401030010b010281c203400c004484ea241021009003d503403043c90541d5207003401040610004c1c41d25078a2141c2c0100c154000d54030b401808900412004090341013020b001e018204c2d80c2001c50400d003c11501a80d2801210800900d01030314021b0060300d090251841d14a0f038010003405070700d44008507032084070302d0103503a5540c4441c41d024284002038240e8500002681000c10107035482490310070041903c03448200c54550301044c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450994280 1250 450993030 450993077
    0x207081b0d05010615020a05010506040203010b0712030f09050106090c08012702070804030302150705210c0c0304081f0c050409020903072115050408070f03020102070f0305030601 79
    0x3251610320940100105040c400c1e03211440764441c0c000007400f10f075601e01d02004941490f001d02c0060304120f03111340600009014007038002000300c904501d554508901c15000b441062401020b15a0b09001a01064000d0707020085483c1c141900784415041890094001d000328011140903c1c1b6200b5201d18840c86408424182d402c01c00600088c0503840c840740c800000d031a81c10600d019020080d2a0000d4072200140001307501c03940041c50700d802070080c0c2d90583c0c1401041c02d400c0003414095212540c880f082e070f1580401000c01c40140540310038a501c8800d01c01c403e4101070318800083c00082020001030f0076642070f520004c00b00c6a1a407500e032a0410f403440060b010001400500062000070340d00c0e4000d21450b10000d0407a040c075a5140c008107030600028221140c18001010054280100c08424254180319458200058982a03a84044502078020098040c0c1102c04040007098001d604580002d03800607695140d0220b5446c004100390b10480c2c5090026400f0300c81001020b602034800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450995530 1250 450994280 450994303
    0x2151810110714070f060302040e06120c010c0c0317190c080306091f0305061602151605070b13021e0a051002120d050103020f0a080303040219032001020708 69
    0x7180c41d00380181c950358400a4900800c0090b801211030011350b43c0301210920006002076140940c40d0703460b081c888180c1e0703840201014000d41c1c0310344180714011404a0403c10303100003420501c2d503841c020704000519120030340000340101c3c0c40b030304241e450036840b4004e00b01458822000e0009441110b00072551001101d46c0181100400c1c8003080e060300d415201c0070b610200c2080e10440300001c094119502c03185a2b8001d80e12500b05800b44001d01a05000c56500080c80d4002043d080c40165130803e440d107001843d1060f2190900180301900e07105204991049401000e060070703a051511036111428440030049216044425000c88806846200c21011240003803030800c84501c1c010501c0101d12804450300118007407402c0402284c08410007915010059400000e2150306620603c0140c101d204140c6204800304a0100203294001084a9010341d0581d2007891952225060103000f001c19000202000b0a001143c00010204008004600341c240d003125a050b555810f11a00c44107000ca0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450996780 1250 450995530 450995561
    0x60601090e1311100906090611060a0c05040510030213240c0201050c0d03090b180304060302070618060c080a060506092106090a0302011104050a1502151810 69
    0x840c1c1d0740402141c2d0080d9402030802d0703041038060b0000608405003507568940402d4520106102051748044d01710042c02030703401d0030700d4001e030480f40d60341ea100d80007095529000d4844080344e500511503003da8008280184c03007008000d5506002a010703400041c8010701e41a00d03039000003540f05240150414410305010217600503001400c00300d4005030914000da040c4001007040c40c0c16410100622070b0851200d64000450200d98035007489c03006800340600c46400009038040541000100448044030007a09006950b03c20500d4070f1000b4200c201c0703003503018400c008041002e000013904050282080b9649170407440d075801440c2e80c208c91050190540201040c8512013043c1001059010b90f800200402c8401803002c04800345081c01c01c4552a2003a040b003258041010340901890b0031403642c9a02050416052402080710469940700d903a09031034000086c01d600b60b000f402a904c3d03041081030501381074035009500c603c401910102001c224421682c0c00d0b04070340b250703105030240c030003d014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450998030 1250 450996780 450996809
    0x305070b060102070b0d0c020114090d0f1403071d010c05030f0f0405150901110f0c09071709030310050108010812090303131202270109020f040512070806060109 71
    0x31180c031019040281060705510850354041000030102c0c0c0601008482c03568041908110a2002030a5500c005151080008200b0511103296000701d00c19517207030344a1a14040c403c0000d10700b01d854880e44481d1558040000060001c100d41c04144032400c82c901d09487d0500c15203800044480348054240500590400e000264a100550005200d001c4031202c4450400380c0b0b8000080c1d01262000500b0010700c0300242c1b01c211560016503190742c501005020f0020003940d5030002e0303103c805038026188948145070025038114001c1c0e0500110180291051499281c403482c0340c0d640340d1003920312044034050303154001150342c884c01c1c681e8162080c29003d0841c4031b130110b02401c0d580e00a1030b6003640c9030106202141c01ca01019002c1d40062000d0300e810701c20b184480c0188103201520342400c8007800340398003040d9001280c507651181110304110300107039582c03040782c02c1c520f0500554010311740c440c6c2c4d00c504894a190000070940151021002541d1050b00d6107401965002540d11030245025060b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450999280 1250 450998030 450998033
    0x9010608070804320d03051e070804061b0e0f10120203070c0b07050409050f042003010609150305100c270308120f0702340803070b090607030207030507 67
    0x40b482d0301803612102424055501135200038400c80c0f02000d42c041269440200102005541070040c1c541024070220041d03120094400c0f02c400740400207086005102c61a0b02003004c00c42640d000d080348540c04a00048085034103140100440c00c18001c0d50701c2400e038624042c1492174994440e000c2d0416039242c4003035007006a103545019402c018180010301c40c01c14071250100b800481c00510581c10f40e5619982c8500f00140c0a0888134081e09117403148400b0010040000d65071140400030307070034072803142e900c130048100020302400940c2c1200685c00d0a0042d01c95485e0b2801800c00180ca209200741c9024a0006021008880740c0e004c0301d1001502c00811500304d0030304000364415140000d02030400c460b4603522411015403000c034103481b2007941001041070707901203100042c0c3c22005500c0a4020501d000e141c40c003815228250407001200201e0035510010801d008000081c0000400c0c0c035251022420034445190048a81070000e000d100001405503200b4070880b09140d0b49a2101400c18115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451000530 1250 450999280 450999293
    0xf05040909050321010801151202210111091309050703020105071b060c0210080702030a0e180405010b011b0804061d041a0102010b0402030c0d0b150307080609010608070804 76
    0x10001c00303a6242c00104001e03082c40904035064140c0c21500c40e400c21840d4900b841c01400c590380e0719400107a80010f400c0500c03240c0d0809200c02c0c2490f4049074080400105a40401301d149800c51450400f986007200c80d030441d009540181c51094404c84030202c844842d00314003400c1e41c14481c2d001b01707140c07c4108144010340c0580040c015880c042d0300f107124601c0d0b90780c0100b034007102203402410101c1c0c0400d59200c00c40c90417468541402003145007000d01814a8000a9964007500301e003202404071101d800030381519590142010340342b0884060b030050510f414001e00901d002000745000a051241c108422079095880b00c4c5216441110546414900101140d22240190a40c3d0344000b82c1144039905945c0c50150b1800340c00c00004042a43c8041000682155807040040c4c1c0101e00600c10424845880c00548400d03c02d05c90020400c50326100010300740d8444c080288121240100c2071206441d031014005200d0fa1043e40c0c0110f0b07598a071042a61160821034102e00000c00380360020740002c4a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451001780 1250 451000530 451000541
    0x702030d14190e030f0705030d020406031a010f02061602120715060e090309060703091203020c0316080303060f0105120103114b0a08100501060318080906040506030c0a0f0f050409 79
    0x87c1f0266070a0600500c6820300341e0384a5403010700000c1d100d0101e846c1c220300c908005000001c0900b00102c030082c1c0c03100040e4542c500140a50260303215070004010242c028401140000f0404010517540d071903618100241d4031031201400c0041c4d240410209a4411801495016401c0200210700b0701d40c0304010000554031540c801c4042001928001441e10035130152143d000d8030a4028000c9158a80140351a012280c1c1d400f120588100d103040100d0000402140c0d00701c542514002607500100c3c00680c0c0b54031034800400494a2808000420300a986071020b501e4002100c9078a10207683c07411000f54584800043c000101014000704640070390768900124070f40c030030700816107482c3d611400030b107841540d540141c4035500001c40c403100c03641c01e5210321409081c17103040c204119400154101c240c00c2c26240001e10f04540010100c42a070b546105840042c030f0020016a943d24111401c0103150304071200321000f01f0303c6024144109401202c0039103c4200c290f031030605052030311162001416 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451003030 1250 451001780 451001783
    0x7090504060b221401050f12031308070303020f061909050129040b090705031b13152316060b0d03180f03020a0e0702030d14190e030f07 60
    0x29980d906041d5183c4888001d070450800180301c2c00e0f0b4030006000c1800540c0e03254098103e03000800c0c40140043d40d104249500345500035178514a0001640819500d54403c026640d12103240c44880040d41c0840040c19001750380c460b0b400d032b039113007590100003da80b50401d0b52004c0c1c01c884c070032080b8000d591450380502c8006001d58000f050b203030b8055114040d03481c030300c82c550a0b5402400846450794107250080d282074100664100c04c151600303000091450002401002c801030a0300c14850f400d65882041e01c1f1070912681ca1142d07119aa0700380e00307001c20000c1c0078080115201c80000b41000380d40a001d5410200b080403d9803500080300c200c203100701035a25044403004d60b5140c20046580798040781c040210f03c26225140c4a5141000d110307851002a8082104002c08440a000503100c800c43c46085400c241a100050703105c040091307040d405140c01d011180c80c0341980002300b441244156502070030f540c50301000b440900c00340301c0054030503090071440c035079001300881401006410018801603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451004280 1250 451003030 451003043
    0xf03020d0906020301051c020a09240803030a0c0503060a140307080613020306060307140f040e0f010911040b06040b07020d0b10050f0d02210309030703150f0e07090504 74
    0x540460141000c03610070400541d4510ba0200040c80b450401401104515040300b0641502c00c589900084241e0518010114165210019408580d409040078140000700d5180b8416868032842101d07a40c0d0000c50f0850401070501110f082a43d0140e0308890003900007a201646982c20603540344c0c03140302d60306812038140c0b082a5000400c1e02c400d0184078003c04560f48545c815400c240101403500001414092094200440421540814580344845410155442c1e4400c041100008000b442c841800d0010b03402840b4200c2d09078003041d40040c4c4014403030990a80c60041180521007151140064107030840001c0009106402c0484050303c8441c2c4000c09011002142d59100200380b003090341d90108158401e042480140b80414002803030480c2a51031510409140d000144400f043c000d103000241c1d00248424010034007407040390500742003d02203c0c2010f41c0c1c0d00d006003c240700c519603040c159181c290078900b0308826002e01d04080090034010502c043c105000c4400901c1e0151080713408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451005530 1250 451004280 451004287
    0x60604080106080105010807090506010203071113090b090105010e07020d030e07080d1211030601050f07050c04020a0527030a120e1009050102100605210c0d0b04021215070f0302 78
    0x22800d014070320280003d032001007029450000c0c51464a080b9401140801d070070f000801c0000e0b40d00005513009140c01401032150240c076580400c070f10041c481b44040110b810810130f88c06001e06414080d0040c0542c0c40204038903a40e644042d00b2174141a5800780050704240001c40c02c07180300740c01100030300c1c0620b0301313803004155a042900c5c6440c0800c00200081100c9100c290f0304103803280308444034000c806540514619084000902c541300749402d644240304003082e1310b02448020081d80100700400740c41156543c1d140302e8050700c0d40d0850340650070001e01c1c0c0306000c0020303507145804041841000c0c00500b12400303142e4454004c268040400c100f088200c926404855540806851000403940c494007a1142410002810455070450885040c1d0a000302000305468646c0345070304841459441040050719904014140b03511503900e198000c1c0740c0110f010500c20004403060046208585003000c520f0804000c0c0d845507070085240c201180c18030005100d10340261400c4144d03500500e0300514 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451006780 1250 451005530 451005539
    0x7120812010e0609010b0c0a17130b03010807060e090402060a020a0c090c03110a0903110307090908090306010e04050a020f0d0506040312050601031a0d1a010b12070c021008060604 79
    0xc520000340d001c0141c0c60b41103828088a1304004000c3d9015207a581c82092400c1c008003e0559910f0304240c009010026002002d031682021005850711080590b6000d403209680307112a54190b0028060076000340520140091140d0041000703c1c0740003405003500c03003203950f035400300720b42a00602200c10a602803038000b10001060380d60504003030480308600254141c243c2d0801022503002845405c040c50341000308010a582000180b02101e41c40412840d0004032500420b090402d5070313028143d00744c146403413401004000700181c1032004090f802c031146aa82d0724803801c0c103884199400f501e42e030031403000c03a005410700a0340c1c500150b00161811004003113a5854500d0410100d4050b0002600301a04901e070f0b00d05406000d8101c40b007442e051184000340c02c0d00c01c1145d5409001e492003401c03400c80b002c0c20001205014425600350342e0340000c01d903070b460365080201d41c041e0300c0802d180c1d00c90900084086001701a550039071600500325038119049035109480704240a4000c2c5d038015000c2c080010b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451008030 1250 451006780 451006807
    0x60c031407140f0a0507060801080a061a0a09061703040b031501090315090302061506041707051206070806040207200f0603130b0a0c05120c09030712020112050405071208 75
    0xc1a809210009220313016181c20a10304246694220108001c03d980040180480020f4002c1349260840400100c2c00d40800e0b071302510502c80f01100d070704803685140004c1d01e072200c0e81c0000211108442c0081402e2812101b60b134691156008441c8400301c14404241c20314002e030701d0340c042c0c008103040c45c10b840c0c0d80ba526000c4030600c0e10030580344090744034034440702010750500c5140d810841d81010700040d9045103001456500a41c0200c1281c07950f8042e004074800410005280100805000d040000080890158603543c0032140800400d1030180031070150304103807080729800f540100442e402440c074489040d400c10382c0200b0b65a4828100d0340d14007900e6840310300650082489201c00300f000c403d00c0c0350a0390b820100400500a035480c26110081c15508003040f103419100e1a2240095070717907034002d0754845001d00d030b003c160144a07103075001c07643d480c1d000400c0301464002d803205540c00884000380001e90348105ca0003070054100c4841001458031035003ca550041c40703400b8049c205002a0f0100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451009280 1250 451008030 451008043
    0x15090b0a05011401030908090f01170108030a090807061b02010e19050a060305100306050702030d05010608061216030b06010c050f0102090108093c011410060c03140714 74
    0x4030105680d07a0041001202d0a1014801c11400382403e005a9145031107021507801991003050180e41802c42c003540580c820949802803072a4071420344e03c0303542c40d91742040c0c0d01d800403140031012507000140402c02090002d01c100c1218519507861041c1d60f14400c01c0031503c0c042c400300300d05100c1000c11b044101da0b0ba000d1500080c1d0305030a2038190071880c0c0310070814074000c1d50348590306240c40d0a0a0000d000240302158065039080000410980c4602e08200d1961103810009400c55103048000b04920b40d0100c103807402034400b2510140f03454840c00f90300381c03903681560f620f4117034a07210001003001600c084101307540100141042022050151206802c00e01003804070751f4076175070010f2402039039a0499a901c1e0410500002030100000f1928032102c00361000303880392000114420122844000000c0b625519410000280305101c150f03410b40071542015114840804030741000850380350310840c102e4028075007664940300350f00b83d030005032662503011181c181d800c0a2a004507220a10b8200540c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451010530 1250 451009280 451009291
    0xd0b011103030a0c090b160209010501032f070f060207110108011d071809020c160f06080c19030b01020c1f08060d0f1208100b0a050c0f0d0f030e06060d15090b 70
    0x400085c1a47d52040200c5068141c000c40d05140c074000040e01c811000c0c0c1808000c040d00c1c0760065040c8100c40400e0311039806506002004410b140c036801003003040f15009000864410318110304904071030720041d13801d008240a81c0c190744100e03845003a090404d85541c1a0080001d05281d018044d091f00710102d281050740190000c03e0700021040c0100c04100215050309100100103268030b41071120841480c803032031103414200710074040030a00341030480c01150206880c0c900c0c45407544480e410043d01400408414501500440c0c220311481d081c0200c0c03086c940b00c00c0041a41e58030318804e0702582d403100302400190700201000307403100018070000c6020560307038060541c12900c4034000400801c01200201909030000c2081010014000858283c40700003a180c105203481d900d0203003100385803030282c130500130182c4203d400c43c01c1290381100346e41c1041e079a0741ea400d1042c111b03180000c1d551100161101900550748104610219960a10b0b01240743c98203080840c0080c060344402140c0c9505849 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451011780 1250 451010530 451010557
    0x711060c03040f08010204080309090a0b090f071106060f0415030215031006030e06010302011407023102070c030b070507141c03090b010302041d120d0b011103030a0c090b 75
    0x2418400c3c4030302d881e44a001810440300940c503003400d1001c103070740713a00581e03101d54054156100031070b00244464006401c20300380600544d140c2c0c50201e060042c4064282c0e0b251000c00d2071110701360090000800c420b4469440640221595250b900a00c030041001c010011108007040f100407006940b80e190110700095a4814151a402c0008569441c4120b41d0302c264141440c00b050864294004a04c0760304490302400d00054070b2081c0603d03881140700d590310095100b40071824000001d5503140100380c9031b00d440c040840b1004aa1440c181c01c0f482040409021980c01d00c8080001078061003207280d201145143c85420004e03180c1da842c90101000d14141d120f03410400340c1407000c4101441e4241144541e19060102a00c0c0b501c4440d0700354010f0201071701a64a9010400c441c01180d081e69440b200300b00200c509a04510b03424851035000600004a000c0c1800c50001203984585400300100700390340c0180d0700d1903c03040880001040c0c2c0d80b10250610819000004480c083c600242c48080020360 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451013030 1250 451011780 451011787
    0x60c07020102011b0207090b130c030e0c0f0a03080d1113060215070815150a0804021905030d03020702040b120c01020d0201110403030e041b1806030c140711060c03 72
    0x100283c2502e415004108404c04031000400310603500181d142e04480c90706400003034542d02000072600e40d00e14403c5d2129444e04100011907000c0d8154840384e9259042810303284030a44030001c008000a03000745031940200303540300500110b00010010a29070701e40c801c4c0062a000c1074510084650410409621344480403003003040b8480e01800006414294a03144502c980303081400a452090098107248030b06079401c50b18002030710b80c0f07041d1502d10301e41c0801458071030100003c002c1400504072001c030300549156110090b8245051403520a07603100902a04900c00806002c5000350803400c001c0c1c4e80039403120070702c0080b03031182200d41000584000c0a0080c10b10894000782c0390081140340a01107a240c4660307210810f002c00d0585054a07410704d04141c0c1013000c0c000203405401803645601d6070603007040f8041c3c4115002903a59000d030406d4444845295900c0800360101c0b8030300d035100000b00340341e9035119652003030303140007004081c0c41020840c089145170408149580c0080324000c03519440003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451014280 1250 451013030 451013033
    0x120c080f060c30100807090b01090315090c030c03020301050708041e0602120a0903090e040c06050706020d0e01241805101a12060d0c0e1008060c07 65
    0x280a240003604400004040c58246450051690701c030712480500c58200010b10108404000d44001941c0001e00024041c6814650034221144546110b0300d5010b00c2106000544102c65004018a51405845040740903280d9228a0900655100710303010040d07071512480c00041340044036274040c50182043c8a688c41c15441810308581000d0162340078080100c00f0040080c05640d010040356501d4005920315080030b00c3d08001a024050361400402104410480381c007100740c1c8031030306042c007954030002490b954814245596230251006858180d0000041c00710324042e1004203841d034410f550040c074151042006804803102054019202e9454003900c6041c06002458001010811203c60203450314120340308000c40d16070251442441c1d26100014207400c0c025500c00004e001410200c125044900f4000030383d5409103031007141010041c2c000c505241084019103185544c040300082c0c070142040684044158010444080c200b62108003040003882801000c6c016a01e04039881e4854005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451015530 1250 451014280 451014283
    0x25050703050102072009010311010507050312061005070c06030504140105071206050303090108131b0305030702040501090606020a03140c120d06060203070b0a09020a031703090709050105100e0307120c08 89
    0x50b175207410791155402d0a944200d5a0f0135207103a044030350103105650340104500040e00e0038001c121000d80103000201d080450300112030300c4184241c4044410030001c031701a403000c0d1054041c400025115414011007482094040d40c0036540081c0100f00716a01d42e2510b862140c20745104a40050000b1009108000040c0c45401030302c1c060300084000c1c41c2401004000203000a400030244000c1070500181c02c8188000b050f0061100b1101e44100b0044580360300b0541c0d80c941c0034410403400746141c0310001400380141d2141300143c0e051a8081c0c080540c040d14115110128507090010328201001105240c590810005103445c107a84c0000340c448507008110b404462040d800300e82590030400500000840084125074040d540440000c0d10300240d002080c51041d00380c100074a1400c640010306440c3e1440c501540c405c112035412905100c0d03c0e0140081621006e01c10107400c00d586c0300b04007242601664421000280140868007000e907211492a061400c8480c02e5070480405a014880c0010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451016780 1250 451015530 451015553
    0x51006060207080c06030606040f030317070f17041a090c0102100606090513020c03030406020c3007080903070f0503150402010e0d03020307060e0d11122505070305010207 75
    0x41a001402d1401e280c03005540e11048481c080341d1081c000000090010b50300c1009840c00b45c0782c020717030202c202c45e12441c002d40340e01c400c405440b901e00342c882c0c006242240324400007281c0c41c80c15030326003914001118108019603409042203a081030508410180c80410705070503841600ca1a006001c03030f00d50003002900f82540b5484007020241071001c2400f003940c010950f001102e1043e00c8252020448801c40c50003401914419001d50100000307000a0101039009400d00303821910589821641060440d503081c9c4a90a000c2140480703101d4090030105034002610a10740515074103490300030007000081c00c110264020600c0031803015030500c0a418200007008040640f1301e41600c40d81030076000030b4042501814840e209502a44079001007501c02d001765450340744d01c124284000528a0b144a464050b02c00c940000039100d1005444d4036030000402d0041ea0806c890818580a0b0b01400000744668241d00e2603401da42d4a268000013890400502008500540c0010f844522501e0101401c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451018030 1250 451016780 451016789
    0xe0d0206130f110d0f031e1103040512071e1a031e0c0408070e090715080105040c050c01140a0c050a1407050f0609030c010605060c0d0f031508280b0f070e0607051006 73
    0x241c207923011505000c000200e0307041d608202c4240b42c1100300090258a8542160841c00060b0480b00441a2907080300c1c0c803080a50300d1641c806800035075030080c0880940411900c4100c840072940c0b2105100442c04140794010041d607408501d404d80391000d45140c02d15690116002c40780c8001041082c280522106002c0d00070304103000704008040e83e00a14003030043c050944216562000d0f003034054003400c22101640c61100082c00080ca0341c210554500038202e41d4094210b052461086070325101d00f045400500094440f0200603208081140d0380384c101407000c880d648288895602d400d4800c216043c814120100103503500d106000c00d41e070a6413445d92040f0300a0405014440a040c1c0102c1c40000724085840d200800392040d0000f280940b0700e00c2c42480360802c0e100e5011408c040086a520400000c000160351045004040d103040340e19103010107400840e4090200c1c06003518100c02c00c0c0c00052600c0c220307409070104000a00107a10080c0300702e4807a4461030184609802c540613020090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451019280 1250 451018030 451018037
    0xf0303230a140d06030b13050d023f12041505040c0b030a151203021501050d0209070903050105150103200f16060e0d0206130f110d0f031e 61
    0x1210010740948407000500e54110798800100b8110310045507030b4400b00c010342d0400326050580c208422055411410302d001942c05001c2c001c04280c92500004005003152040c001e01c0b01542c130110364031080414084c40e004000240f1070402c0200c0c440b884050040181c42c120a5846410146003080700290080c41c003000c40b506240812011841c000100d070101e810741c59a43e40e41790b545c0c614250050914609104016202d45c0c000308920060000c8102401e10a80807100d940f02005008801d8103070901c580c3c0da0201403d00d0f10700040c200359070241d800a096080406984c1c4c0c580da504d41c05d45004540c5110681c10342200540d1542c1d040c003407003130814940f0500300015220100399008a03c5021128030405100151241d0031480740d03d28500c17078641000003001a40070b080c00080d02c0740c140d442e00d013005126020108138603500d001c000c220f54942c08a402d141d80c440b259980c130498842815240c1d4002101403040001c80c4502810b0091103100741c1e1100034500c091900f001c1d40503021388400080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451020530 1250 451019280 451019287
    0x801080a0206041202031617011416200a0605160509010e04022101030c0e01150f12020f0c0a030909141308131413020906030601030c090f030323 64
    0x150b280c40c002c58055071011036080d0b22125060011a00d841a0f110307000e618039103079440026560000d0035038007070014500002032114056001941c1d0300190285c0724900d40c3c03e00d080c44a06668001c0301c1444620408010100305031a00c1401c81d27003401d030031940944049482d8400c000c5041d40d60040026460364a00700716013001d40c6000000d154101d140c401e40e000700c0c1d0008028001c5440c82c4100c0d0340c510302080100070700d9a12440c02c181e5600c0b883c4114002c0700c801c1c60000c100c5815007604603860902699a4440b9680c68484c12914005d044002c0b554003a070801070020707048a5000104602100f980040420400500c0c008080d2082640407804a6290000881c0c1d07007008c100c01c40d504014400e01e1b22101031486c0c03c011032540b240350506844541c034602c0008401c40e441000d050307142000c40f110350403202d02410503421b030320900e448564040c104000140d002d43c000d40c000c010102c400c0c600703c01070030f840d0312004440384007513042940401e00010000700ca48032503030b030103082841525003094103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451021780 1250 451020530 451020533
    0x20f07081b060a1b060609020c03070b131a040c0e0a091a1306020304020a2607060503061809120a11010b060412080a0e0d030801061b03210902060d0204060801080a 72
    0x2c00d084030b45070f075445200c4000e440017884620f41240d00601180c0c101156500d00b90000540d0301d9000d10000c1310110710000000d80c44514107400c081405400440e913410003010407110490600c3e004008903160740880c5070200f882210300c0101c911981c04114000f41f0000981081c2c1403240c9000a2100f01358004010405c4015152480006940d800030b40941c481e01c07284005100304400f90401c14803416100c02c4214812611480f080c054640401514030194940008486c0383c0b00c1241c03515040102d2010030b1f114906142c4200d40c3c014244001d0701d8503100d1114005805611000b030350000541909040d9814000c01e1203140385200007103540b01d00e001d14185400c400580050300180104001261700c0351064040c520340744d000307c4000d141c103070756a00610300070344030240038050314000900207005507040010440205010680545a44914114150803003050981d1061508152900d44000c0b00c01620340b100602030941e00c540c0c2c05a1542e06103100107140c0c000c164043c891541c09280b41c4c0c0e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451023030 1250 451021780 451021787
    0xc21060b0901030b15031f0602120a05070f0c0806070e09091908120a091101020a1505070c02090411040c0207030305030c251a090109020a15020f07081b060a 69
    0x100141d40c03c2c2400306030840b00100017048092038651203042d641d000020051480240240780d0048140c51844004864444c10204d0303036a10005000c2c0844d0301c080042800b03c6010390058100d90788545481e0400701710a1707a440307851860580c410213290307000c2802c0c84100f903000900303c0d400400c150f482d02c600745854405581d0b1850000c80c44402d40304900f80e0134041c44552811074841410140c00b920050408042550041007152401d40301c1c016000030701986036101140e012546600860544400136260810740010034025000704207000e2075114034801600e4040101c2d102d140903010a011600c03210086c0b1003558040c1c6803036011500145401e200290304201580e8018464503501034840d00464052480600300c6401c0603960814282d07076001b004281814100300c1007282000003c207880c1c10074881c2c03d85000e80402540615070300e50900c80042048a4000d01280c1031040b6042c1303500c450b01c0a41050f86c182c00c002c1c0c00d030f000307a0407408181c0e541014403402000700f610000c1c50a02e8009009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451024280 1250 451023030 451023037
    0xb0a171e0f0705040e0c09010810050a0b060904050c0d0c0306030506070807090b220305010e010b041e1802090f04120507030e06090d080c03130519061206090c21060b 73
    0x164440e503900c011a117101e04042003880140880580703050020758503200010b03070b1102c1000900c02000d0030100011380390302c0a03007d100c0a000014100314142003c40e01000081c1400425502c10143d051010388003000b0240034800c1208050380300082c80d1421f60600c01e0410b00014034103800c0c0110001403060700390703014591104496500da030071502c0d5040101d01a182c45002a160011070301c105801005115066000032895100113001b00000c0018505220903141502201c1c4104c61a980300b031020360b10b868021700000c1121840c94030542c0c0065000030074000081d0703816105650010100010002d8001070b00d1820051070828600b080c50aa80081101c0c042054613030003040e010031405601d0303e030b281d0086441d6904c0500d46840300c000398605503494001911501c1034ac0c0200700700040c5803c189003213621800b58000c0c0000014140f11042d40c080d60701f03e00f07030100741d6510703900042c1c000a64030804032031418541d00c600100a03110006001d003100420f10703841ea2480e00000300185640803045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451025530 1250 451024280 451024289
    0x304150f0309081b010e07080c010c0f060203040c030209011a04030204090f051f1a060706110c070602010501140f0d140f01020301090203060111070303120b0a171e0f07 74
    0x981a40520031030120080c00c50202c1c0140a0030300464101c0314034152450b42610070589400810540d10401c5205680300d416201781d5229400010014500e9403150b0b83d2184004d000f0240d0b9035950342c0591710300c0d0407130b40701302c0d000d4411403241203092003146402d208050040c03c4c0760310600c44a860340026494984181d00c030084c420b5907102e4941d001c10030340301a0b00400319002402e54613010800c0862080100700d804c0388000031460680b16010000e0031410f25030804030041e0040781402d645a94100060a90000c02d2140039401c2c805010060000c1006034044c0c50309500104d16540342103c03c481004644842510800700004c07080b519803901442c1b41d1010b904050b8101c0024002102d82e400d184010388001c0f03140d4000400440c024041d60000c42c05100c00307030703103500c0600b01003030341c0320b44642c05800014000b40150881340003100d07481c1c00002c1000801400d078100d59540d0385040d80520040520190035802030400c135443c0c1d04003074059142032128603020b05042d5904480458031464030313028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451026780 1250 451025530 451025537
    0x120a18030c09020d1d01060504060f0e0103120509060c0309010f26062106060a050901030c0b071a040308100803030702122110080d021203070c03020a0203070b07060b03030415 77
    0xe241c0a000708580020b00e100d2044c1c840410b145e514100d145001e00042c3c000c0d81d020780e0409400081c603400c0d00c920f010488034401107880391070342141d03100aa0620140000400c020b410f106444280c4c0c2c07a1402441510804001075644540f101c0c00580f0748000420344401b40070841c120480c082c150f808a40c0d5502c4040c81410380e030b0355100c2c00090409030344118025600000c0e00c0345018091400204070780116400c4621454440e5202c0c05c20840150900000f0305200070701804118403420b2602070451240b04018050040780c42815001400608980690005581c401405240d004442003200501021406149075141c001310283d600c2c0c90007401ca07600d4610000742d00c058050140070041400781c0d244101449402c02e04021f4402400c80d024188050090002c044005400000e00d00d50942d54401051b056585951041d038500e010a4010740c10341c041c0d0f02c903483c0143e8051016501400c0c0c120411903c40d280340c140f100440b920103c80902035801040140310090b00d0f000030030b01002c00d524 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451028030 1250 451026780 451026787
    0x302030415110403061812200307061d0d1e030e120c16060c08032a0a020c0406050306130f0803040809011d090a0f0e120a18030c0902 59
    0xc0c061220400401c44500c0c8103140440100442c000c0710000d0044a01540d41444401d0b040100c6d509a034103e82e0000300407c0f00924a003000c01c0c0900c3c2d000b5404a80d24010045c6030000c9181c01b815640035440440d021030741c4012888102608400724441019020000e00d01d404100782c01500000c0e50210305100305c0381c1c00750f4103240c80d4030941003540502424000d890074a181c40b075040616810803420005d0b030f405036034034618511890020b810102c40a660b14000400301d65190030480da40003402c1c00d0f031451101c1d840711b10b807030303182c00140c100100d454448180e50b604440c40007800c00c0841103c00344503e003040d2013048203940020f038540c0c02c101304001100782c2e901d251401c14426421210001c0c2401400302c01c00050152810241c45081800c2e01c034000350018a01e620540c0006d0b0f260143d5020081c5404103912004c0c5900030700050001400008100340301a04440c6402107044801107843c2d40091400540359020403003044104500c0e006852540c116501c031112010240143c008940e40071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451029280 1250 451028030 451028033
    0x4061421010905150103171c0c0c05010c090e010815060f06161209052b0507050409081308031c020c03041d040501050c03091b03120301060f03050705160303020304 72
    0xe40c824140340303a005045605101c0002015000c4d08400d01c000e031007031000343e810381c41400d40760411101903020751748450078000010f84d0803200070700c5039039003010401502a01d0070002500906c14119a507000f0f44401c2c15007440c3c40780c14004580160019245074000500c035422003414a0041c5400032411600c9601044030000440c585014803020844140c1130103c0c600203010b40c40c4401c5224040c0c030341d0352010058864003440300c0c000110110102420800e480a488440004a9502c001d842201070b00d150356aa00000303810380d07035001c4003903a0880000078041d1250941300200402044413201540c04d00d901c810601c4103070110702005120194002680796040c510a000301d6002e41035801c0100d106c10705110854a28100444080741c00790b1820011030660405001074034851b5072080300412011416800350100050701c807040a4142c821600c620010f03000b010061030181c2004d070b44682008058660043c15580c004d00700700e0a1000400c4018850b440018034421010b8050602580d03d8949 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451030530 1250 451029280 451029283
    0x30c01110705090c221e0b0901030b0406030c0602150f070801031b091d0d08091b041401080c0315090601050d031209080d0c020718111b03070204061421 67
    0x415030717902034144200c81161181079241c452501641c588400b4070f8200c04c00d2a4141c032060f00f090080f00c04420051081c038103158404d4024003011000a88040741c615500d5440c08840705180c0c11940140e001350380614207074000c401010f0360002c03851804e095141850080988000c0041c04044e29184541ca014000800070f00111801000403440400104400b030508010a5090318400441d0b0f01910f05881c0320720344a000517030301801a00001e04842c004820480f1028411004920b4005031030b101447c2c805810315540b24000c4c000c8601030004000c05d0020107041200700b480e80f00c102d1200e101407003000080010811305454043d220b03022581e2443c102940c0f40c414075401d4001d5035041201c00c42c10091404094408010108403e0100c41c0f07445505031f03219070050154107828031a21018500102c0f10b81c01a942d40704100542c00c1c50006100c094540c100c0c1e1551900d00968000664141181001e20901300200140040d094240001c80001400e16050b521091f002613408404043c44010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451031780 1250 451030530 451030537
    0x1b0d0c090e2a06250b0106090902070c1e05031903090b160305090f031b190501230c03130302030607110312090f07180b040b24040314010b030c01110705090c 69
    0x800b0b00c3c2c100e109144c43d00d08414034540c01d00034140040e040071000030b02d940d894026a840a54484408000241000808100050800d40c0140784040104000806440500941c0c4955112600001200c145414060300000003a800705640110411802c043c44050141400c5510b1789450440e584615080c0029242c1075428040307a454003c00c4000600103103542d03081c0a02d0941a80c0038a0a2441810301c5d0800c0701191140c03e01145400301060340c4003181d1503186041d203a50f524042d080c14104142c1500d141c00142c1c01e82c0744002001018025440d0411907640d00a0051030075010240c01104032a40360f0044010081c40595000c1c007150500c00207001542d0140d1541085038211a501d580b025154080d40745002c80d0035142480000c01da0401d801881c0007084043c184443c410302001c411065a00c0d0081d00d5507503500184804030002d43c1c0f10010690369529540049071001c0604105424001200b0885050200c43c00e1680803c5070046010b400f1038004454040d910390300c60003c50110712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451033030 1250 451031780 451031827
    0xa0f0302131409070302030127111207090509061507050106080d052104080a0f02070b03040321050421030e061003051b01021b0d0c090e2a06 62
    0x18100d034000c110350780b41d40c55015107103030200d03500e803070300d8540c0d0b50140d007288001e000e96010301300787d2819101041c21146540b800003091400c0007070850100d03040c054581d002162410700140300d000030b1100c010b51003046100a81411240c02c9040d0403c07000044e40020f41c0c0150041c1c0281c04074410051040a6004500521401040e9040c21445040081440c1c1c40200c01909890748104112502410241c20381d20a41d407024400386400c203080800c1d00c0100c0e42c12122401c43c460340e913001c1801c20f0b100b40590700a030f20a031030f80d00d22081594908041121701c54200c00403546001c00b040045050b465408142502e070300032492010300c0f0b1390f004a01414619250b080c40d072007180180700111148070102c0b13040380e02580c2036407080ca6242c80590031030740704814100d00581c806802e000345803080c4199004080c030300820b505490381d01d95170f074010a000d9640c04155120350710030310411003880601070080c0150b4642541080300020300740e41148005290000e5006080104130444400350705442c2c6d823440c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451034280 1250 451033030 451033057
    0x904050c18011a34050706021f0b0120070503060414150705031f150206091204060207030b06030a021503190515101428050405060a0f0302 61
    0x15085038542400214003071050464100003d2441d9610903d54010386191002c80c0c84265040d4200303c1d8264985682100240354a04510f180c10000400030802d0500a0015070041c06542c8942d0005c103401003d42c10b00d80c5081c3c0c0c24404521007907030384450441d0010072203402c1c8100e90b0300b920221914150450b0130103900340c800c503030030302c018009981d02c0c400c1002d1070142111026150b480c42249440019607003200410410f10214945022292040090b0445002c0320f0700d00c0340d568803003a00c00800c12107105001d80c102d0000d0105910f81804450042072030b400b5034a00e005c0c03a240000350b80e5452844003800785055070000c145030756000d0110b00786181d002030141c4941803005007201003036401038942e0142c48600a41001c44441103000742445003e0424803001c01c40b406006210342d660605003140c0030000d120440e0343c07100720994007905a80ca4050102141d200c52140b00710704441c01d564001062010500040003d9601c07030701101d0150249240281c07281c0f1202400b0380203400b640d007220110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451035530 1250 451034280 451034299
    0xc090521160e1501050708030106120b0409060c02060a1a130204050406031b14300303070c06050c040f060f0302090d060b100c080301050609010e090a0501051305150904050c 76
    0x1410710b00e0300c070340940300f01818521480f10240c01980c0307500ca000e00c001c0241071700348010084075010baa080700190b0030040c0c01044070609003000504407100e04008413604c694440480084903030401c1440d6000e41c0d8601c0400801501900c00d60680c18060307100c0c0c0c82401404862910b840007501940d0003030602500600c0700a89a1070312050b40b41d04400f4904500f50103070b0001070100c2d005904040301c400007820500c2d1720000007426049500b42c4065030007040707016065180310000d040004600c074291603681c0d003040303801c42d142c6401a210054045404020144414007806e4a88920b80c401c48465007060f001402030b05001ba4040c0c0500001c3d6a4070041d0403a9040a0140071780202ca0305607011031301e842c03c03510300840540c1c0d81d0041410181c5924024801441281801e00007007000c00d40506146244c5418680001d86403142111980d40007601d550040090703040200da424040741c4507100500a0b0329004902007903a50b803501d0710511651000010501740181446200001030018004501c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451036780 1250 451035530 451035539
    0x3050604050907050d0c3302010213050402070614041518080d090c0e0406060609090c020c19051c03020705150322020301020703030606020d0c020303031504110c100c09052116 77
    0x1207000008400581f01307100301501500c2a1040c42202c4045e11f80d03150540150341041e041c4402034002c03803012100e09030b80e8018a2038030320504507083d1246200f12504c0c220400f007450f20000ba512a16994000840e10903015070024440c40e00b03840071410ba040c000207400d1401d003004208041260301180014426106200900c4007640103441510880d44481e1040c55a811101e01140d00713a020031700040c1c01c03146880700c2620700700c0041601d03039140403010f00c80e2a4403200020203240f0080c0410804501402d084010150140500c1c00101021122450500b501c02002505840000d01c03000c0b0446448446600c45800020311303040c0c030394010b0700031500c03086589000b8000b002c080c0905409440750741c10409055100300501c2d00c020350b0140c050750542d03c4143c060b202061420040035403150300c9052050310f11010a000c0c00309500c1100080481511007000744007100c810000c0f0314100070350001c00703000c40d0300c80c44400780640c825803a048500c100715194060a02248a2107643c010f60344520016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451038030 1250 451036780 451036829
    0x7050636011a1c0b09010b100e040b0102010908030103140a120804051b01020307080d02041d011d130f030c06050a0b01180608061210140703050604050907050d0c 71
    0x441c4402585401100e6442ca00c040100f48440c3c030014000020340700320f049000582071644150003541000011520040c03810000d0b120001c00301e45000041d41c0000582110702c0e00d809020742e07004c0280001c0141503c5503d9041d0703103101c1404044c0a00f43d88d580d4007003242c3e80802841d00b9050700142c5001d0702e580e04000040a001068605072000e11403441c400008034480165890303a03c0c0d050300298505451651880020303004092081942035081c00005002c001d107038201c4410403a02c031002c80041d81800c1140c2d400c1050174032010802692601040441c0d6410030440a08640004180381a00001c2c034084440b800d070220000d0046040400380120038000c0e41041c52000002d80380c0064100490020107103c140c58031420002441a2010a41ca401d05401500010882c5c0d0140c59500c1e401c000d00100340c1e00e400c0c2d44041102c03010001c201c02564144103c03a044182203a0510060500d1507c2030f6a0b031800b8060785d4400d44550a4000170050400070220040002403480c0368100c05500c03100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451039280 1250 451038030 451038041
    0x601110c04020d0902090f24040e100c120504030e01080606071506051302030402030709110415020304090506010c020a030b06040e1509010b09070804110105041d040312020705063601 80
    0x17203000e100c11001040ca400300c607021080c810515846440402c0003418085180100b811603550f41051b5a00c488040c6101d050004202a02032031501056541400500409902c940408400014035200c28000040c4c1d1004420410810903e003c1111381c5814001079141c1c80fa40d04000c0083c501880d810300c0c84040342d00104e04a480c00c40324100c0c40c4c0b03010b50382e8005922080328005e5142c1c0002206004a8941e5801101c1c03138440641c0e058101703a02c070030020111031035180c01c00015030701c08a810408a11907008240e0300c1102032900a018680580c00308074041c81e1381c00f004107940142e000007801c54503070790f0143e640c030703100c00c8201d4a440c0b91080484440010690fa1a000ca508000741350801d802c0c407500440c09528680c2e0f41400641e05c903154649141843c0200c41d040020411000071031038810340040c441506200340d241c2c1a4100703481c026143d000301510b0b408903d401442210007007100071500943c0486000d0900c3c1e4501c100103034001610f4200229400d90703103660320810b0b00415055024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451040530 1250 451039280 451039283
    0x1602010c020309151b030a050904150302062d0f190516060c032910090807120f05030f04030618121808011e05010b120601110c04020d09 60
    0x8212114510404984074800c10904642160744210455010201c242c01803817000700c0c0e285001d03400480c80b80000e04681c44070894500158000c20481d290703140c02d02c50b100b14043c10101550038145103501280842c060040d10741e4039040d070b55141d10750107030b1812030081c3c0b0902e0510100303546150300d020b04502a0003418800c644049442200001c040c01002200e1312801001524403107035a807692a5000703000e4502c40071080544481031340c2c1c00c0024004000b080302c005005070264036024641030244480862510358100001c000c0200540c640c0801d0348010b4a003100030f2011112481c0c1480d24000800300001000d5120000384440b404400300090001d82e481403405010b0450590010700c0104905400030305a201c01d020700039a024080d02c511400600e070040740c00c000c0c030358804034182160000d09201c0c445c0b07481903142c4440c00f00d040c070070349000d00030813100c0b581810088805907030420002411681404002015954007050802005031388110040055541c2c00c650300c035510203841b01210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451041780 1250 451040530 451040533
    0x706020f010b03030703090e13020d0b090606010806010e0d050a0206040803030910020a05040b0d1b081509040b0402210105090a15180204110405120c272403061602 72
    0x1202807689008400c94400c150195038410040e828000c1423644c45170060481010250200c0d9028010307150180355480380c1d80070310f6135200a454846403c3c0c0c00c0100080020313040241060400c4440e030303045501040100320548200b10344209a183c2075240c042a1480a03500c51408900000e8842e0004000e601c10f114803c2903c01500e041e0b0012800d81c0901903a860120b00144014415161030001030118040040000700c0d400b00905201c100c0401c040c521400011840c404000c54030003200e48507208a58192610401840c054596810403400078100a100b5201141d56605083c02d10440e00000c4c01d90500811041c01e040d0b52050741e82d151000103e540700104802c001207111070344181c10080c00c00c004441305140712942004010200c0e1090301820000500000c0343e16294a4950100c41c0382c280d005151000c440001c0041c03ea030718081c0689400300000459a440601464450304000f0070289148030b81c0d0407080049010125200031a0988108400c2081001925111155602030b030740 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451043030 1250 451041780 451041791
    0x1415090705030c19090b0f060a02070603150503210c0f060402011b1101030e1c0801050405092a0f090c0a03050c25150903090906080a170c010b030706020f01 69
    0x80904c40108001c2c0c1d514048404848000c00100384d19801c8030081c03000c001c2441402d0300441d40050001c1c0c05c003003104001a03014400a001c1d0303607003522400b0000c49250741c034070285a10381000a966404e140e403040407000255000100d01e60702c1c000c03da1b0060002d40050304c5000328001c0071180c1da56400c840690010341440a55080d43c880c41072000d02003a0810104024a03105200560262884960070b4909215100c112103001c021000030b8581841c15544540c0b2552401c801c0009035180034100000b1500030340c034500070101107c00307201d0384250080030203022400000c5c0015046e03060a059540c0020742202004010b801080052109040d00e86003003000d40c0702c90804024500605001050040c00c101c001c1c803400031200008450f03103100d10145403044408154400644030051000c50118407841c1081c08000c0c0319004020241404900030a1802044d488614107140c0c4501101e40840740000c60802c002d2003900174a00350800134044885140c0d952074020355072840f8440c02c608651070003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451044280 1250 451043030 451043053
    0x41215090b071b120e0a230a140a0e1503031615050403212901090b071703061903050615180403030e1f020a090501020105070c141509070503 62
    0x10480603c41c2c201460b5103003c0d180100035039000c83c01413900c80d4002111400040c407402d00010f80034095840404a24008007480248005520250422001c410190000e074506458585111013100c0c02c011401c80d0030307200c40c2c0c0c804107106041745216805010007c0d0014071038084000c0304640d140310700400c840c3e8008a00c1560308656054070005c002640600416030064951000d035174100c24400000035003044440c442c43d404003c0a0030004031041020742c0c80560b5038002182d8002015400700380c902d8004079603038205203111314502d00d4002b40c0c004404a4041c0d1583e696043c00301d080400188a059103a0030602e50301c00c1e0480700060000c002040380d5010303003000241002d0303001d0b20b01c4003c10306072aa5941a000b404050703400304100d205440f0082100541501301c66150524600016502c24010800134103107095508840d0640e8100400d000810360300010588504e82c101c650303410910801c1ca903841c18510300008907030105240100b444000100480d0003004c940080f170444d0b030710702e052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451045530 1250 451044280 451044317
    0x70632060d11210a0201020706020d050301050904140a0309052b08090d0c0308041a0405031f0213060905090610080f040314070f05010c03050903041215090b07 70
    0xc8034903581244810510400003a044407029060080c000c100c1e400402c20382c00e600090481c42c8242c0e402590040b840d1074290b5805100d40d038040c3c900c0d8805090724404004001d4981c4c40184901801074070752800140074084c4079282d02c104140c188090794025006800c008044402e58060303a03101e0414000920041301042c101128286003504074072510405070307104c2a1303071a007000c280543c0001036a507002c00081c861a41c40e402851181c210740b0784071820030240003420658040d0310542400c0412003449542d0300010310800803550341091603040b00c0d22303050210107405510a914180e0f01c030001c0100b202a00b08401009481060341c0f28401c550b90719042200c42d4154084550200e034440010a0300c003060322040c103600070301a0912a0b01900c2660006a05c1d41c00305405503581e1001c030904008001d000e01460f03032211114a400d02c0542020b10b0740540785e1169116488070b05031036110039020850082030380d1181d141044070800c100d5685082443c6036082c01c0707545000042181c10f901000545 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451046780 1250 451045530 451045631
    0xc0302031008240a110309030331110a080d03020403030210111c0209060a0c1104050c0307051b03031005030d0801060c080318010509100b0a0e070f050706 68
    0x20b41c8208652000f00c02c0c160302c40c0d15140604865040303512480e02890a40020000714080c0a2480045640303142c1208080f038402032a8514004842d82a2500750002000c951207400c01c0b50030424490585002c5400160488c4050703000d2511030081d21155031a0795056800740040364026020f450450101800450481b900c0201100b04413005119800884c00c8a03984003c1c0880452030040c0b6002c11803000840507040b44084c000000c03000f20b80141008661920f10f10028802d55040c811420802c1c0140c0d11800001c0040007040004641a04030000540c01051403460503015a59030341003485081400507640c2c0203490282c070602407840e01862080744000c3c100c07461691041c203903101c03681c1c900c0007a40c40903098a000351241041d0051040307082c40703454064460710000301521246149260261142c01d0061031045080c014200f05180d024842698442c01a1610f00400b00340240151618010f940002d44514940124490b84144c000240710290384071000309003c000c060108039840c0036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451048030 1250 451046780 451046803
    0x1006030308160c15230f011706040201021e0118080a0915120c05091309050c0f0619230403031706030a0f151505131514030c040c0302031008 62
    0x19550151301c0d02c84281d004a04803103215404482d444850840f20007078100a82d0000c01408002004101003600c0c220501c01540c0e1080243c103051a20b81c00203900c44944980503410b07503180e40c0020b400200c0a520142102d0124040c6102c5400325051100e8950071501c1e288010402545d40032812509400207890208c000340d98440c05114074540c0c09000e030104940c0074050110902088019a43e0600d2200241b0800000090703a601c6c0c5081c100d1818291000d01401a0140c070042c500b41d4680d0707422152407900e604c20104040c81d14110454071114201172051041c4008040d030280000c081005008480c040d90fa8030300076000740a00116000b00030356150340d240e17024000003c0028412208070b02c0050249081e42150200c1c08922000d07140d8148071610700c940103003000c6c0041c0c80e00f600548061b00c00c40404000b005c0d80d12030f2042401406024056040f0600c900c400a20750701080b080c9849840508140241c400c0010040d02a40003660003d800c2600a800800e200000180051114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451049280 1250 451048030 451048043
    0x6030d090e040f030c15020a0e0619140f0406051803011a1018081e010603022b1e03031a0306010b090607060911090a0501080616021006030308160c 65
    0x1912550f0310004909450541142400304100d032103c04500918541045548032a40250b0703101c009240040c01d10340d42203000351144d113050000f66103035542c0f105400842c0030705040594201680d01503209640c011820000c660120020f0042100c55212000c1c00201080203210f51202c0c21a504060036250400e040480c00361481410103114600034413202911841c909044d1080ca49102c0344010801458004400590008540035240c251041d444101034940383e000700070443c11540003c0355003030344c07c0d00c003400403540038180d0340011034100c0680806a80060b03000c0b04c10541480031080e00c4055842a004649404000b03801c04c801c4085502c01032400902034202a1b0800c01d25130a145c10180000c3d4100c1c000748181000207605101d011301c0c2d14000c6410000201d090010400219070051403003003014203110041000100014066800021000c1407580d014001d6004a00e0b010b05648035204003030a00750000103040d0821411405114198402904c071802d54100355005625202d004044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451050530 1250 451049280 451049309
    0x1c0203040b1603090b01060917060903090d02060d0213030b0f25020a081303050c100203040e13020d060c110309030303180f030301031b0f2301050c0706030506030d09 73
    0x504614502c01e5640420700700040d001031107444841130a5401d80204010500e84401400f1056607c03250340c503e40e03d010020a041e1901c42e000310b881340903408080380140a506100c034119034030030b030540320040395152003152030741e203501c242c0312542910388025900f210744c000c04036003000c2c000c0905034030030704c0d404941c903000b02003101101c0f680318848030303a800450042c20b07400703030003c0c9406004144548020f0b9108c0146411400d009050811116410707120706031104440d000c142c1c0110070b0301c00b21000c03a0740c0c1c2902603840050300d200c680c03840b81c00250300140d002200300c20807041c2d62003549051465610380384000c520000365950f0f0310803030b1354840c0e050780103100141e4000800700348040390745680000c0c0c0d0800391503100001c6c503641081e08100c0d000d858207800c0b4589840307107002c41c0c0f0041090301c42e010340760382ca8500700180003003410019146566003028001d07041c0e4010700072111540d40880486540070394038080180140070070740c2c40d58803030700505000e8200c007441107001740c0c280c40811940c01c0a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451051780 1250 451050530 451050541
    0xc1203320f0405070906080604050118030f080702010f050129040f0b1c2a02030a0503150d0203031b0c0d0c0e0414030a0f0f030905100f0e030309031c0203040b 70
    0x62501c0c000304100c40901c101078002c05e03c0366043c06900c005092200081c103903402c1502d4403c1c2503032004403000c120542060450b10100360301c41401c0000340e00c03500b0483d00039122003504a02403c2205650076545082000001e07141403002d40c01c44d070040129080b8200c4030a0080854400d1049100d41d8903404401002800079420b440028030303010383c68003100714007480d8503041c5906642c0010914160304540020b410513034000942c0310002402184040c40ca0164080c3c400340540c0405000700e000055070280d0712465807541200108016002803c480c1c0b528444034004210000b0b415048455010301c00c4800c01c107003070400000104503801502e82e01d0450501c1210460040f0040c816507040e41c1084d10040184000d00c001e0907030100070b07600c800749841040c6024100c0c200d1039441108261400a04801103880828102c80442c5000710204036542042404000b070070f2202c201d003055000002c20700c4001440040100100d015000d00c0702d16103243c40310f10300308030b020458000d49029160400160b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451053030 1250 451051780 451051801
    0x8150601050901120609090c03120206040201080a0b011b121103070c0504020c160902120601110a17070c0906050306100e040206070218180c03030a020c060306010c120332 75
    0x8100104c00320000d15180e640c2000c0342660070130441601c00024050060003401042c400c1c060112845000504650526900003005400000e00380441540d43d192209080e80c0b085c0041203811008120444161041d4100444031400070300182020030702c800c1c1411040500031041d01d0410303800c0505103071000c0c03a220501000c2d5210742080103403401005c040a0030344590405100140c8001000143ca407807034002c40d9101c219010f085c082c14042c8003075501c0003010001030b0039055940d0001c2d10155507240342d514051640a251002092000b03205000700300c1441c10340c880d80480340214201ca483c0e8640382c510740b41004032409003d441819a000090140c1032080003080d00728409820304651005005040e0380001042c0e40c841140f02c1043d003100b440d03500410980490070030840140d490304145100107555040034034a103501407030001c40056416070145040510b8550040c0400010590000000700100b101420020092a05100c014121302a10010311002e0380c81d105200c807113898481800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451054280 1250 451053030 451053047
    0x80106050102150417040306020403020a060314041b1503150f030f030807090b0c0a1704050d030305040809040504140d020304060512060d080d0915231905070908150601050901 77
    0x380d41002408038031700e09102c201002000103500641c030040c2c8982c1144104844246968045000c02d0305100c0d4440321141c0c510740c02038100343d004180714003010803501c010301c10300250750107011854a40c54000e007045405802030485050188000041079460320b014400000c1e06003c00b40c1a09400c0b07082c000000c0c0101119500210319040c078400c400e56900d0071843c15032120700c3c403110603080414100308010304007047e84640a100142107050031b041001049a050f852640a010103031250040b406010340041102c1139000090000d00807072526003004001a1480c0744504107a129115842203610310200c10f41d0309640065407510710304010398000500c40d100182a2035400503500c081d900001da68500140005c41242402040d41c040307a09010801c414040120049a0301380311580e51500d10801703248071074581c2c02e000d1010750784401ca90554114031420400c10064078200621a0300c54201603400125201311007103130504052841541810441600d9840c042001403061003129230180d1a038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451055530 1250 451054280 451054283
    0x608030f0307090f03120815130c03021317100e0c0909030d051006031104030804050d150e06181b0907170a050a0e061902070f02040c08060108010801060501021504 72
    0x3c5800c484d102ca089400c80c0b040c0d07a204907001c8001500d549110f64200e01c4d070a50040c01410301007020300215010404600f052000d80040990310003040c21440c0c01399054a15401c0603400c249582ca0325140031011343e6070341d098999410701c03544090840841e010b002c3d80201c0c3c9044409418140420350078403044440140010015000030300160050446138412248620824040722040074500340c00a400c0303a0043c080250915800c00c8144003044203581214111601590400000310807400d00800c6c0c40101800b1030241070501408041d42c200001d40640900c0700d203a80e6000708020038010075900ca40f20f15445c03010180d1008803800e036241c900c03520b651180301400c0003204289600c4268145440807548032803401e60394002e00c01509403078818030403031051510042001c2d040c02d40031180c800c0b1a01c494851003039000548001080b126080f00380c5201c1d4050300a004800c0c0c1c60001a1440b40e0485080b4000740d00e102c00010034400c1409158120748060700a00303190784007038404c24080302e0f00510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451056780 1250 451055530 451055537
    0xc0905040807020d0303050a1a181b0a0c05060f1608060105090a06020714150d0908090406090f0e061909021f0206181515030106090203010f090608010608030f0307 72
    0xe0039003d61a4181d030000030343d02c80c1d80e0002c1d05140130311aaa08890005850311030720510000041001d0b15014524800d501610510340c20503a20100650009851000501c019820120700010503e0b001302f8010303000c6114106a0b040c0fa41c40c1001e900000f502140c40403c84071a00d132036940224029921150410010f250440c81c0003e0000030500540242d80440d00591002c0c1c410044282a108040300448080f60f02e4540c41003c203016030280e0040c00b284402c015034070080241008494002c4070400d2001800034880f15654a69050040224603030329108213040200100708120003150940c0f0482c078804817480840d03441c5104500916001034200d070230039404900c410020a841c1d10a400c040f0f0340b039008184a29005140c41302040c0c004034181100d9200c030a80340102080c5205e4682d000182d44a50007440000c5d0000138050500c1c3d5000c840c4180c03000001141c1c080d111b14180003981c41c021014003405580300040c500722071152042c020290003d0001e02d400380140c000039a00040340c0d18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451058030 1250 451056780 451056787
    0x60e10060c03021e0c041d030a180905010e071107060801060c080f030109091406010302030c010c061b1211040807061b0b1302130b030a080d1401031109060d0c09050408 74
    0x40c06482e544914105500540e0b11680790a41741d450180500c00980e0440244040040d940078071a0b03559006003000310061106840150601d0900f40d40748200408440c2c00c24040c0d540d488420728201601910f9100002d195003100c1800c030f800c009080d0040380c80d40c0e9540201603190020484038070004400440e0011820811515840f03015800385020b003040c0003000070040c0335440c041000945072415002103410120040002da680800c003440d4a060a00b440d4562900c140b40c0403004000714024040008080c00220f0a59a402104401183c417001001c02801e200e104001901e0b02441c454069141c0c4821070a000180c8a904070550381043e40e51000d1b42c4503980c1d91000502082240c08001d0802c802488409514044100b00040b0703103500c000b0040204100082502c4a0040c400a4407041c80002c1078010003910780c2c401e0800c511400740100042d6180d00d40784044c45280340100e40b20b0021030b40441c1c21468042500c104142c0d1020803d6101b5240100500181c440100155055007060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451059280 1250 451058030 451058053
    0x1503100e01020306011b11012003030406060303390503070803010305100501150203031303020c22060905010e0412020c041d0d030b181b040806040501060e10060c0302 73
    0x900448900400e0a8009a201c1c40e0101c00102414141d03080310089500d84d1b41084040b42280d500c102c804082840d20801140100a4100502200341070000d03592000104100500440d0740c0506c0949100e5990b0100c40c052840c94100641c41c2842178085d80050428450940da2200e01151140c0384602c0079a428260341740c0f03a43c1241d03002640142e905800c4140c01c840b220741075200d114094604086e00100d84101c510000b5170b240001480d54001102d010032140c1418000c10800d4404000100540856140001d2455184000c0c44c2c40c0341e1400e003000c0e40400c000300103001d254141d9940d09103075800c0f66110703201c01743c80351101405441540154482100141c0b924000c000c04980ba102e058400c04040c84011880c01400c02c3c99601050315258400700c15507600c110038804042e10b0b40031031301035480710800c0840e000040c040c2c081d201c04002800040c41440460268820341c0590000c04c20a0f0703a0b02c6a0704009a8101e51591201e280ca0406118580c040d80c2c1e401c0020303000341304079110200b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451060530 1250 451059280 451059313
    0x1806050d1b2c180a0b1015120c090302060d02270d1b09060902092e030b060d020c0609150c0d020d0b0d05070f0b0f03150d050a030e120607081503 64
    0x845051768040c6030502006400029150036000401ea44002109202c074000d800504400e520290740ca4400e0305c1d601d00590342d502c80d45d0b0541c081c0d50000c02941c2c0d1100820400030003544041026004911805070308003003581c025075078a0952002504040301050f403903403440402c2107142c20700c220303607680031101042c1c0410a12401001c0c1400c801c0044e44c90448604106071400b0440c400c00482569002034801500415041d149401050801081c0f404d200350000c1c0c407074000d8410340280702c0d10110348007252400c0004c00901800c2014140c40036801c034602d2042c6d200c01c0031900920740c22020013640921102560080032054000f81002030000c3e0344800064070710610110036217056001d4042400105225448000140314100c6440d141099000c0100700341c0c0401000c0100c1141181603561107900c2d00200790405a9208080d030b82030209a00d8003410000381d5402c42c1c0c2c0201c100002d030241c4200002420b5001e0409a103a010166445901d0018050b46040c1c1e01c5030980102005843d000030b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451061780 1250 451060530 451060543
    0x5270105191d041a06131d0f1602120702010504030609110103150509010302061305030d0302180a0803070213061d040b100f1806050d1b2c18 62
    0x400d6072004080702184404015041d20300010b10310680c40d04a10b41e90031000030203903001c0c010003510b00d45d0700c0d0040003c000d075612000c0e0f4405031000140c241d5441840c00040c440310b20171650902e810f0b41d02e4031280d641c41c81d0400c60240e1980964002140d0344420b40240001d00482441450454a00340d1031350388110564502120444142e80329138013410080d0380600880d01480340750100c0b14095403030800081c070310b91011b10000c0d021f5100001e10380035218101200e00040c00f8040c080710140c5501c041e0080095201150498602e00181d000d0070030340c0303040000c0a0860700003000a508000da186c08026002642480441c65a43d035040002130100090610051954907404400c03140e1a040c00c004403090402005c0038400c82a4120a1040507a03405410b0152840d00d00580c0c080c03141c2e03007408802003240d42c109540c408a1042104200103002441d015540e031054403041101d030342c070112880d0900603101c00c43c00c946488894500704034105001164030010126204840e03d036a00a260b04111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451063030 1250 451061780 451061827
    0x1a04170d020f0c031e0102070b0c03070f03020403020f1c050712050f0703020a060c030203130b0d0b0915040e030d05090106060206181f0b03010e0102180105270105 72
    0x400110240c001590140100c0c240c81281d41c01410704008810002615084079028100441540b10407070755a0308825810f880d5204da01c0f50418604d400d00d20740e03e0a60f0740045030034000281509100c942d8043c842d000b65011694068011401c1640100411012001c1461200f906c0307080c4500000104808104801c01000e0000a03407810f4000c90403d2030034040d80325441c0302a980815002c200507181e01c0507c1013150070914040000320040e16040741148604485c04400c04072840001c0341200c82800145204031511008100c411041014001c0720001194100a07070341004081041c1404e05800c00500c14055000740d80ca4403850032801d40896100f5198801942c0d0359000038001c1c03075010402c1c181c001d2104413210b0755011512440f5503494207880007135a90f84009582c40f4044198580020b00c2c001c100400a00c50301600100b00c6000350002c40c02159100384412450381c1c41d500a4040307904489102000a1031903510102103079070b100c01c0a210504004040000703040010b000702d0fa016082c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451064280 1250 451063030 451063033
    0x1290d0f0c05010311040f03121806181e05210304141c0f02130b0603130b18120a020c12010203060f0603150f130204060201240602071a0417 62
    0x50b41001d0005080316060251030050079800c02c8280107002c5103600d8602101d5219555202603e0226002c685d403c4404c1c8800f0900b848030700300400c10b6030708020401140501600d518905c550b44101590302040140c4940402c550142014006801c00e00d011612002c890002c3e903004020005038245141e01507400b00c01103c0500d6030500c000d140c0f1a401172450308010310341c260030380c8803a101c101c18005e100d04001d1084540314502c60f0820640c0e001035040b400c00a03c0c55403245081905841011402e5104481550541d800180d1115581c1d129110340d045000040103c02134560f10034015500003618581940701c0c0d481c0c1c0c115903507900b810501c0d403034550000140e00c070708200c014801a060070701c6000344100303804d00c2007100403008804c601107010021170320000c000e0b1b071500100301100402c010001081c0d00000b03012070820740541042001c444242000070416003000d0041224511601510300140c1040304100082808841c0f4104881c0314440400c0c41c0568030648034120201d0344c1d4488000703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451065530 1250 451064280 451064303
    0x303081f0b0d0e01060f1d040c05060301030602090103060905070225090e1b09040b0c03070309080c07050108090c060417010209040c2721030c050a030e1201290d0f 72
    0x68142170041030020703e40d48208040d09418521001861518003221030a801070b1100050f06100d55401010000c1c0300140546680f56123909150010354070265005001c03a00f8510000303942c0c1c0880c86110f110708542d40c05801d603c1c21810802c03044214004a00c103100c2481540801c10410500c10f42128412490060440b64868922034a111840c5e80da00e900c1340c40c4003801c11003c1010b10400540c03141104c0da0340f80d52640e42540c142c00508812501400e400c80204032216070400015140055a00c00d80b0350068950300d0b0700c1010340d04d41c070141143d1340205040c03008009008030711204c01e40ca0344089002505100d0701c00d006c00e04641400501c0c3c00050242c4400304003c01030340407910000211955102d0890781080508448d8174580c0b501d0701c3c014202010f02406051003030f0742159400e0b5000c02556038100141c01e0080c14030310214501803003011000300300305200d0014030405058840b4804102001c2e0380205a0f206603820a090050300050390302c414000180206903540829845010300707204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451066780 1250 451065530 451065551
    0x2180f01090e0319020d11010e06060607050a0c030303022116030b0a03080a0810051f0509010201060905101d10140d0206030f010f060e060403061107020310051e010303081f0b0d 78
    0x58030604041d42c0c1d41072749404007181c1704200c04103801380d1100c1c0540e485d644c0c40e00c280c50068601802c2c0500070341007048104c0d01004055050700141240011030350111002c541c2082c0c00d140c1000709449a40c0380b50407140201102c01d000750005004014014664000700e5520340352040e41e0b91101d500400015040b80401c0340d81690050228007600c4c0a690a5152104510741201500c41000710175041c06008148500240c3c401d40090000d000c001c401032105d8140340803048803001c2c140c0502601e46200300c1c1c0300401c0d1800c20490522480c1d0f8400c1d5407003801d00d84040e920104060781c11091304102d03502c40700800360f151040294000d5000d210585c910b5817410300c40c032111452035084a0704014001c040d0f0360300703691790009580c06c0d40c0d00180d000031461050403402040e8800d1b000c0083d054050600c1c000304442041d84544e2007006015840744020100c0c10801c84100401d020003004982d91601082c0741d01d45e0a81c4641d0b0742e404445900440b10303140c0908002e1900451000d00035140c40707410085 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451068030 1250 451066780 451066787
    0x19120602120f0609180a03300209040501141302070203070302061204060b0303091305060613060f0e2202030402030c040e010b01020f0601260a0204060603060302180f01090e0319020d 80
    0x140d10400316800049400200c5d00c0098a5200c0d000001d400c1100d510a113421110440400d2040c02154810484000c2d0f91520440f020b5001110000d11031380c82c08000080c1004c80303403640c0c1e2842100070404a458280001518003d401003101030740c02d4401c40102200580f41c1c507000b084000080140d000180c502807400c00e00f034800c44000540139410900c040750301603c54542c1441120b0001001045030340d00c00c03003c03030500d0180440b40414802a150001012604103c106041c150340782c0d2020310000f0070301c0038056024915150604c2c0e002000170044009480e40d8060f6400510050545800c0c40b008030009099440070242100c061350354421150b6030303607010083c0090380240c0c000a00340701c0d890305440c10750091985180905000b000420428a41c0c014007511a0480e40200100662a104c00c0000c0040c446400220f0055881c007031000c900042c10100e2510850480f5031405a40c1e08080f0a9005044010a1070426120621085410038623450094000c2e00c10b0740c0c020501c8811a03d07008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451069280 1250 451068030 451068049
    0xb040809130e0316030e18100e01030305090f01051b0708070504142809030815010c0b0c0a0504091404020f010908060c0f0409020309060a0b19120602120f06 69
    0x180701440c6802500303662180e002c410b4480e010000714003071012080a0070700340c0b2401c128907140c540c012685180241d140060010341402076554900060400d81c0740c5d0350103401d201081c000900440d00a108038106407510350300507400d810317040c502181070080c08400b40a00c01203020044900360006913041c4082c250400840c4000c0c4011a018441101c0c510000d102070140a044204032818120208004400303c2510f12980c00c0c10660400010149040081a03000182d8039000704048242e00051b003507104481d524001c1da0406800c000988403851004203035400301d41e09000303005061000048c40602841000400d010f41203459070386161602c1041080d0050034903045c180254410107008800c00001d529910010380104540d0f80c00c0c08005011190103140d10440c00b0f5800081080031696010a196005800d040e8003402411444010001c0785400701c4c058403407208210800b005044900030f881d20301d0902a01c401460407030701d0302240402c420704462068000300110f0921549040124a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451070530 1250 451069280 451069309
    0xc0302031b0d06050403020f0f07031a04120f1b0305032205120f09040606020a12030c2a0b010f03140d09150e3303071b0303090b040809 60
    0x24a048400c540019820101c54040503120584c0e0301e00140415000300550402c0391803d80c215604051280821a9513240c1070104441c054042c90619400780303c0c400610307001e140d04c42030078140e0112680044400780103001c0d11004002162110340e0072004a02c240e400c4d26070180c1c1c1d419039646007030076181443e0070040000084100344041b00e440450004036108800f552415000e5603600650450184a4004c00c80b415600c9031620030001481a00082d5817402d80d0300ca1400e14035a0900b5803001d1742210340340c100c0c40300450142c0c0ca1360b030368081c0b01b01c1c1001c1c01240c00450004444000b616140c51452098015038900c8042c10010700074003941e55561003102c0c07080d0004140c51101030400401c414540c0c840d4080c2000075001050a541c00f0300070501520501030300505d004030807400300c004804140449022050303600e0b540c400c0003c5040045034405c5030242c69004801e800d00c800b00c4010000740c001030b01015514140c05001412400c2041c0c056806081480c2d25004d9000400101d541003d08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451071780 1250 451070530 451070563
    0x5060a090603110a090e072a0203010b040e0c3003090108091218041b0206070e0102190b0405031e0417010b0109061d040501150306050a06081614070c030203 69
    0x2030b954000c0c5d40311500c00140c80e0044c80e814000d450781c071070503030312429240300314166808080c0e650050030007920107440980740210000c1c008681003d061000f00c031005942003d00d60024141c019003410a03084030740c186609003400d5070004c05520303092096602d510303e20f095150000105800b0030b41e0f008201a800030300e03000142a24010001c2045414425010310103000400105048c2c4155680d80c032136850b4a100c0000050107003490403000351161380444064001c56400c6201c0c404075480040c0400054126003d2040d02d134000e602d80110a0b94001d10403034040c80304001c0d20900c0c004003504901c840c1e000310b80702c039213403070500e900c40c4070811503071281c0034080c5c0c90000311304203a0380d2146100c000c542440c01c1c48a031250060b8008200f40580f0800310b90081d090400001c0c501d41c0c00b6240080c1e6510a030340411501307859104000b140b0a03d4030840c8001a14040812121310300301c5080c540c0f000c0340c0c0c00e0441140c1030310f03081845a034100d801c054521103500c96007002503007400d00004850501d45030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451073030 1250 451071780 451071787
    0x1506030a0f060e0c04091d0d02150a06030507030f0f02100305100b1804200f0711030307020102030d11071406060915010c0609080906041212080c0702040f0605060a09060311 76
    0x1410181d07280a42e200d400100e41d01c41401d28020118843c2c200010b007c0d18013501c8241902c554003030b5403140c406580211405d10b520020f506034800740305030780a90b503011015002c001c2c5143c44204c0200504c02c030a4500e0220036584000503520565000504081a1404074092502a01d1414214510343c40703100c20b4001000800c880041910440d2804a022200015000d5040c10b6a0f041c912581d54a00041900000c0540b001c110b148043c080d043c3c802e81c0c1011003c40300c44281a20f0b0f00911500034003603881448504043e0741e080e00300c52118619480100e080121a4032401c0510081d0010030080c0e8012800f80045800c00185142e401411104102c403203800940000b0042c1041503c00341c407440d0385040c250100a0002c0803110408e00c0201459120b98952001c240d401c000000c00b00d4154000e01c20076003980780519140c0788102028040c0600b04200c80d000d00014180d02c20107080e10726075078a4041840d50345e1002810041c07020f540d40c441268103002000e01140c603004414a502642072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451074280 1250 451073030 451073041
    0x10501021b09040f080a0e0a080328030f0606030506041503030917030c060f16020a020d02040905100c0201020a2a060e070e0c0702010e1014031506030a0f060e 70
    0x80a01c0402402665400e40a41d600d007006420f206850700001d00704500010107014a035402010503007a2201184c0074940c0a03900c40300300e80e4a10510030403006c4205804924203101200184070075203400c071802c000c01d5001c0404e05120444800d07802200100e03036100140105030038140b24802460b209035120845041c151b0700e014106901303a104000c0100322603450f14216210603c00c0e6403415150784c0c120345850404840070102900b04449240c6d10503085903004582030b00c0090300a07119600649180800005034083c40090310164005030790500c00d5200181c0092800d1281102d070103075583c001600c1e0704040c58000c049916001c4030300058030f201e5038003e16800e9107014040109a00c00400500c2c1d07003045101c0e5003805815840b1209140a200c20440040108401060264401d99402c91031070100000c000351240079031a010001000000400360040c2002c00030b40d0420413808402c0c01c800712650020307026500440e610816692944066015140301d409034030080c003040d52022175540303440c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451075530 1250 451074280 451074313
    0x16090204061b11100e0a0e1b03070f0f030204030b07030501051306030c0e090109050a050c040c032706020c030d0f06050402030c0a1b083c09060c030d1e0501050102 72
    0xf01d0500d42e100340924101c0d415914040c00740c140c1007820140030040e005986141060004c0c00071580600240030300c40e480c007074001a000460b84518204d0b26001940c4403940d40488228202c00c07084814141e0800003c0045484060040d2041e6155900840c0540c10f0001744400c00110005e00304c8680e080400c18400651689108002c1d00c07100010071300c1607a10240c609014000702c41001d0403900a0000c844c0c14450041400444000706485c10300c80f031041550b0840403600342c40035005440310300f1004662100342589504e40a54081d03034001d410000e598065609681c880400030304496602c40d10282c45a400b4094640100400c0b42d04504600c5e107001c00e10030038821002d01e80308210611556544d4030b003440002980d5950002481d545400445a02860f407981e0054a24400070f503111201200e071209120a9031040100000c5600b400460014407200d508807440c10b20036804180114000b100203803003811b0b00420013000c20300b41c0141040703080c0103c41d810303003145045412001c020004500d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451076780 1250 451075530 451075553
    0x18030c030a080906040b0a12050c03070c0b130507090c110a0201080403050c0a05010501090b0f090108030d0914010f0204060f08060a0506030c09040c1806050903061816090204061b 79
    0x401a200a940e05080c1000404d248155005210003020104801c01c00da50302003055140c1c8041e00e5020484c64807030b035640c52440c0c013003200c90f0000108040d094400240d0410504c640041c000314100c0c040d030368203960f1a42000c007981c00905d1200d42d10300c50125069886001c801c06a41458050201c05070207030002014002300410241c2400400100b15144403410071880b0003003a0840020000c1c3d584881c0b9000c05030841443c81031254405d840b07002d0726440c09481c054102d90348803005615000c00218000040c01c00d5078016182c0003c0311341c41c40e60005003800380c030350324040100b40180c2c0c803401c00f14041d203000310b80300001080004540401c01e15403200d4400d20f0503600100c403220340300d0ba60703004d90780840d21030105400c0e001814142001c6085410041c2c00e00850481805000a9900c80400711007074060744034582d505170711040c042100d59000d191383e030642e0480c100c00e035011014082050400000e40d45e1048194a1380040e0411903e540886400f104840700445181c2541d5281c488560404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451078030 1250 451076780 451076783
    0x402071101051b06010303020a1a1e07020a0203070807050328111315090c020d081f1724010501120b030106050d0507080106060507021e1503090318030c030a 69
    0x80003c0c81a0a6029100b485004040c003501150441e684a2400035160180e50b0011580302c5514481030200144103010305101301001e81e4050404828502c65040c0b02c0e8000d4075510540c06014118801750310f0500450014000810003804460b161006241c54110a000c259607940a409120070000c070a00d0300031910180c110031440307040940e8400050000c8418680800300520301550200040801111203080302c2c4a1142008086082507080c1d86440210140200188465001a4966410340e94403c0601c08010743c4081d04c40d100d50a14142400114803924941c1c0301071490804032550300065202102c02d541180150351420b80045c0c86000501001d00d9040d440d45200c100719142503200c01e0042000034203108510f6054102641c072044a4050050720f5420320300c01003800d40c0500c085920302c0794058852414180070001741d1458a0200c2042c561005064500705800388007540a540a4a00303c4051595074079004d2607000b2002443d0456070094120020300e485030368001c2003025020707 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451079136 1106 451078030 451078037
    0x150105010f05090103151412010b030a03110a080c0a1511030a09170d2009220618020a0e010206190b06040302101110050f041212090b150402071101 65
    0x74ad000c04455905580034001d044002072096820001a010703100c203940c41006503688107080c43c0c2c410b070785240303280c1c0c404441481800f002022100d4480c111007420046940042d0700a2307031600004280e42e0b803017a600c4504105105020140300481030024070000d85e660100700451004050b0701e0600760311086070038121070b10300304004111800000c0040c0316188580c543c1c000c60701d03e000e2040c00032003865110b030000640b0081d1502e4a014000c1500c1015803928600c01c0000c5c2076a0311000031604541c840ca0900405d0b800072602040c90404c40760300400d100310071001180c0e40b03214940c030007504941e25810038803100d035104000043d58801481a40c0d80381c281c00d20320500391202a981d19404030a804082030014070561501c4038805400c0c01c01c0d103c44080004414111800082c0035100d01e906c079000c01c1803600a940072141c40e5135048408500708011504c804101d9001d0707a001c40d051 = true := by decide +kernel

theorem cover : BRFrame.Cov 450899280 451079136 := by
  have h0 := BRFrame.cov_init 450899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450899280 ≤ n) (h2 : n < 451079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
