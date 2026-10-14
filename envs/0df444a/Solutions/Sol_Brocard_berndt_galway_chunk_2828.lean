-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2828
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:08.912447+00:00
-- url     : https://prove2.me/submissions/13a1350c-85d8-49f6-b3cb-c25c64f7668c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508453237 ≤ n < 508633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508454487 1250 508453237 508453247
    0x8030103120333170c0616060f02040e160905010e03010f110909090d050406030b030313170f010501031205130f121e050c0609031504060506240a08040201110d030e0607 74
    0x84070013034941c0001c1da4030003041c504100a80f040c003d2039a09580d401c8144e540d040c003111807682c0050103a50b40442d050000a040241c100e610018036800041064440741018040845e82d2240504200c0c05501203401e0f510290001c2e0300c032560000d018004c3c0d507912030a000c940d42088111a000c0d0092500180c0c0680e000180d00a4914046d05c2d40d91800381842001c40281203c061019050b110422601d0944030700912250010100184140100000764000358140b10300c0044102c0303540e06200052020501d02012040c0c091280d040880c3d0342e82d0100503040c0001c03000e9104080c1144d0a500005100c001500b0074603001d44030760007400b9810241e5041101c08401c05101401c958080314904415080010044c00d2041000301100c1d620800400c0349a0038140880d000c55600740c980040c0304050510440404025140708103044a4402d01c6064503407501401c489441002403000c01b080030759000c1c012892104289905803011102010303c040d000d016903401010452058200080c0110b09c0b40e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508455737 1250 508454487 508454519
    0x1050a0e191110110607030b041506080f100807170715200102040f061707020d0c17190f2a03050d0209180a0506090408030103120333 59
    0x82c01900400c0d1011080c004000c140150300303410300009004c80c081d002000c100e801c5c030613080c40d6030101e101c0d02014117010656202000104240c0c407000d006001081c0c012100581c041e4188101c1c00090752010038440c105c1c1000e60000726580204540415417241000e03428428503085011a40829036030085554016900010000020500b00f07000718401e5800d070f4400010384840c8000b50401d91240000c1e820b0602c19030002c000b0038805002e42c0b41100e004075071141c5c041914009000003600780c0001034140c0c940000001c0076040e04910148140c6000310a454814001131080e03044c80f104140003800c8550f011100d400071038141d404411040020103287d01c42103842040c411145900d0341c1d0151296045143c0310001c2c039401b800107002c00d89482c2110201321403807014170342c018144000070303c00300c500103455280100b401c101000b01040300c90040302e0441754012507582008141210407402001c4070311380f84940c02001e210200a03114400d10b00d15250f150b8485490170250307100c5060507842e001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508456987 1250 508455737 508455743
    0x1081509060402210c220e0615060a0909021204050f010c02030d15030b0f18070503030a0c0813080105011503020313120c060f02040906150e130b0301050a0e19 70
    0x10712440010900780110310403083c000510200d81405101e0b400181c044240d941c044c00080006e08046040705000e0b004455940300140d02800c20340c1000c0c0644443d1806408160f4001d0346e000911014441c40703185a6401003480302811900c60101e4007040da801582074500752410b1241107465815507006106d26805803803182c000710700c0d100b803900c4104040e2003103014982d80c3c4411180008049082c1b640520710521680c0300881c11441c04001026103061142c1041816034081201840729841c0002190201c1e04c260a10000034409440c0000b0b582c413710385201d01c0d50b2207613440002d41150540206040e5044540c003a407070300804141c12012030200b01c030b44950041c11580d8400c04a940c01450100700c5045203042843d0b40707451307220b4905079104410801c000d01e07800541000f0a030154842d400150110380c0c000c0080b00629580104501e01111305603128114042000c80f564500e80e128103400340d03000e030081c85580f8281d44010000c002d9a1041101805070306a07030f1030030b20b85d40b001102c03050354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508458237 1250 508456987 508456999
    0x2060d1a01120216030e0f0a03050307051515210f0a11010201020a0801030212011805100605010f0c03180f03030201050618010b070f030c02311506080c0f0301081509060402 76
    0x4405d460854090008500c0b55400810078000c40c203c2e51900c0f2001c0380618040c40086984c0c451524150b45012109900c0f1748208a50509001400a10740002030080e0400c540c60205e0031980030305059012114102e5200520581c1582c0260034004114030f24618000d18095030b0504c0200010ba00340d11441c0c112100042c140801030006182c2041400d03206d0610900004074030004103180d1171b450340003c5040d64035501601c161118000c41c0d0180b840074207428078011040c2e0340000f101070302c45000310000506000c070721003d00011403200a0703044014150307000d2001d0402d82e40d0802a0003000d0944800c0d002e0302d03401d0805542c9001c84c407100c42c100e4110f048180c0c5072a030f0a0f219290712032070301c16013101044110b410100160342c030303204c0c608800d138000c04950b01c40c03003400d44042803940c190356007005c8004d0509071030313008444484103085c0865510b0b06244101e9078440c0e965031054845e104810740b11700c0c40070002180c6120f001032000381d000905c0011003c01d8584c184e50707554400341202d000358061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508459487 1250 508458237 508458277
    0x1606210b130e10020f040305160b0a030209030a05061806090c060a0f050f040f140904030813080415081009020c07060c1406072c030c01050702060d1a011202 69
    0x50079600400030b1052820990380c54070b098035540001e84c0d01050900005840c040340a005000003801850000c0d200c585895241c18035100c8034038040d004800702d030018158007084141c040d4805108501149034041c007030352090b01c0c0142901c030a14180101e079801070300ca00b80005141c3c02001610060511000b00400e081101d5050100c1d508113040f10004100300b418007215102c0e1007a040a0b20107014003a2280500500381100b000180c00c030201d80364803441a000c24080482e030801031454210350380c110b80c070800280e2801c100120f840740b68003030b070001d81055900c1da01950780258168003412014244a4840d0381e10340c400c0d07059015030700c04e403007486e0021002081194042e02401c61900d01c03501280031500c030664104c2c1d00300f050444000001c00c0007500b85a506080744060b9610104103030001d144140340e0440440c0e91401000c50850501500103840410b65488805a40d40000c01e030300b0500c41c41b402c003089d280780901c4126100f408181c21148224140303e41e07000b0361303103110b1082c01f48010310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 508460737 1250 508459487 508459519
    0x3090c03080a02030412030f11012a020a0212010c020c0603040803011401030609090f0302010606050c0613030c1e02010801170312070905030111130b040e01090e1606210b 75
    0xd0b48541180ca0a52004200c00505544070190040200c0e01035107902c8941d0a5406029010000203680d642c3c15900d03048401c02000800203440c02010071700c51401c048000f050354203070710344a45074202960041608200104070081500155100150746e405d84481d041d41d01c0500c0091701040d200141806c0c002d10041c480c10034401c4588000003014503010440e03e03a20b4200c10212240d0007021385030210142034102c00e254090040000410040c82c00510b050400104030703480f171902400e0343d004001d864517a0030174180b1681c01c104046800207600c1c07d00721501c070290182610030500c124042052100001002c0100000002100381d00364051860001900c0c3c000701c0f4418024040307024001124004241500e0074410600c00f0402c4145403682d4a42458650804041d103611414410310100310501031404c0241540741101d00c21030010919840d120340c0c150804001d0802c0140e0000c19000000703c00703600c11111034185000c1c1c41c0624541d0320845c803600a454511140641003c2100c0e00d440034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 508461987 1250 508460737 508460753
    0x424080c15090d020916020c09070c0303110d06080a060b030313091805101e0204061b06060b0d0501060e0f0307060e0d08030906090d030b03060406020702060c0d020609010b0103090c03 81
    0x160102c001d003a8601100244c3c000340d000c1c84156030b28080c003141114041c2d0901e40410640c4005402150103040b5803600c0b0100601c54000804001c08042e00c80361654107404000e01615a60307503a0034424045542c8400381155a0b0007680c0090301c00b117050540840d45810080103c0c0c44040c1010b005201250810a02101070820000d00781c02544200c800342d40131074000d1025140b864905070b408548900400c00c21200b80b0003842491401078410007040086a4000101140340c0e041030f4030000b4a81d210381403610007010307a54060185075000249200401c8010b50001e8140ca50035141c3c861820380a20900a40c0e020414034a901070340071040a11419024050786950000001e041d1040701c0ca550713941c02d0581d00b0507a15110a07a00440134044803080c1440880c1c036008082c9010001c1d00641c2c1c00280c0d0790100504054004c603800140304042d0b4960b002107070076a00f0345004441c1d08000c5400300039a03514044031491419481d206c500e41d0f0390740c030034010240c2060b00302e0b005825280c1140c0f10702007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 508463237 1250 508461987 508461997
    0x5090109033908071a0d0c270e0708040b221509030905060309030d020d14100e060f090f090304030c0b19080903160201020c0424080c15 60
    0x1222100d04041412200018210b0031508003440b03907111181d0303d003408007854120f254021560b903981c40d50000552015080940c2c600f0076114002042c0241c0c00300d8151200029114040020203000c1c1c2114140d030f25980f611800c03a24950040a1a595500d604888079201039400070003440114011a0003500c40c083c804080d0001c0500c051031a4440b03684041c02401c0104542e03100588900d120424990040c01076001400152006440c52a042403050b0f241c0c481c00340842980e50740400c000c0050003a0342c2c40404070300c083d1081c0300c2e618100300b1202c4035900b02900c1907000000c4210001b0703d540c00c14484200c84124090540142600e40e0f050f144200c000c018065200b61106110000105654001440050028901141e40c5a0031314000c00c40c0d00510080d20020300002000b440488100002190f50f080034082c043d10000e07042e840100c1c2410800c0603103551042c00c014000c44062000702942e226403400c000b20314481eaa44070300741c1d9203501200c210036a00190011000001c0f003403003c0105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 508464487 1250 508463237 508463273
    0x60305190908091c15090b0a1104050a0303121b020a261c0f05010e040803070c0602040b040504060f060509010c0804030210050703020f1507030e0c040204030602190509010903 77
    0x2a0402c05014082a8044c1880c0b0811411800c40c2020109011031005800d00f00410701d2010f00c542003840d15685400e8401030001d140b256511010171808800c2d030415640075041c004c0440003000c1d56820010007a041e4500b051400e10310b00b0480e85506031416445007100000c540190541100c19203500307480054003c200f0368000380a00d1b05082c43e00c3c04000621503103400c81e1198002c40901c20b801011102098451242c1c1440c103030060103c0c40d010703410356034400e40c81710b0139540d0380d1303180d62049500040503480104000d00204000c0b4518030020054403e5500580307081252039900c0c041c155100c02180300c1c0e440411410061f0b00c54651240314030301075003401a0350b00d40c40c01e980c03603007c0f8000b200c00b06101c2002071004603102013015410f001e0320315040d1400009009175041245002d4881c00040c1c2003005042d81c410101080002c280240142060010030464866075242030440c0a944030008150040042202e05140640114107651150300c040c0d651160050840e650031710040091a840c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 508465737 1250 508464487 508464503
    0x1c0c0b09010909090f030207060905030c040b0402070b090706020f011a0f01020f0a050d092c09070f0f1a0a05071704030f06060806060102030405090f06150307180603051909 76
    0x3096554142c0101900c140c4105c9100207490464100242410703039a0700641e082100083c6c0c200460364000400607d000c4088500207000d44275000007034028810741c0c900030b08554a260801070380c00000320380e00080300c40c140c0950384047c4541c11020b003250551000e908612500044100d968100070030807000d80b11040c0122007485c5607603a5494a80406034404881c51f902401d9421000f69000400500900c00500f40c40c0714410300415052040f40c030741699005001600340019182c0d02c08200203002000340c1d290171600725450750200d40c5417100c40d001d241c41c0380c1003017007110140d141d0030b00444103003840382d5840b58141b8149981d07101d00740341d40c80200180e10100f40008408a6070403541c000c5840e208200c0001d0042c98880c0c0203003001002010f00f415900103100810154903003c51490340002c400503050b6584c0d0b6082d00081040380f003142040c0d910300d0301204210300cdc103420454500c03503c41405203054602d0359441c4101d056460031542c00b10040107554036104514510b4008a085510510075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 508466987 1250 508465737 508465739
    0x2514280203032d040320060f030403230a0903110604031e050a06140603010c090b0d15030b01060512010503010606050a081021023d050c0a0b061c0c0b090109 69
    0x1504000d07400035001030b243c0a06c40e03229620700101c086801800b880095480608108410401e030b1203a010040000c0c0274003000c0b489020000b90300d407a00080c0c0c0c0e050001d4607502c03500308820080c031452103400102e600c02d545201282c2185008802d44040300d612030190010506088005001c510507d80102e40920440082c2c3e0001210f60141c451260604c7c0c2405450303150210406017903580122014007031010130f0806001000020088482140d909900032a80400b1030f074030102a0701c0554030141c8003401500001c294190300c040108800307501481c2c0b07101647d80381c82c20103003200c0980c441c01d00410f80c1000039040450141c600c083e4403c107605442d11381c25540790417a5607041035100d050760090303071014150021454408100c0350300d1140c0d529030303200c0300317422000380e00c1840c2c0110320042907a1001d044041c040c80c0b00708115580c0c8a140d40584a5a2281c0d24010a102c1400d40d41d50b8410340ba040c9408004100011102451075001084101090720f440c2804036258006103a6078100a8040300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 508468237 1250 508466987 508467067
    0x1b0b0913021908190c0e060a350a06050a090e03071406070f0306050a060e0a1a1305040b0d0809010e060f030106180308251428020303 59
    0x11000b00080c2c040d12403096502c0e00700c0c0f42d8049400d85010b001056841c0c1000c100029500038001e85014405845c0980d582001081c02d40b0300c1e40c41001d01c0502c82649a448000400140000984141ea200030402c49500c541c907000c0c040e5413050080c0c0d0317080055018108201e1100c0c1e08170401b40191401620301e05025a140c2c0c200b1404021803001c040c3c0d1105090108003580020100f00d1402c051608204060500380003800503c030b944036600400200f103000517820756591000c080101201c401c450041d43c2c41365090503854005204415080d4100c40c2c0016050800c1c1c002c0c2d5080b900010300c0c0e07083c96001980c07026816001440020f04100d02103180510310386500006110032942e86410b1500e96241000049c01c3c040c14800f140c820350012803013000040e200e1009c0d14420100820a251804040e444d02c4101c04115035020b069484840d400210700d401c00304180e8015490034010400c40b1030f40c0403c821080c0c1c10400001d400d44d00403c03480c803018100300c0700b5511000c80403004540c585030000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 508469487 1250 508468237 508468267
    0x6010c08070f0b07020d0504051e0102010e100b150301030201021009060213032301110403080d020910030b0108010803040f0b0c0c030d08011526090a020406121b0b091302 75
    0x2c203d0f20f60324410180040759404000500c1c2e445840d20302646007a0601c000701e0208640344034251181070350a444c250181c2e0003900025103031a0b10302c04076400000340a00c210050702040c0c00c8280103c0d0040e8445410f80c0604e000c070fa05a0b40c041c1c009200e200c5000c52900028000c4140130340d0582c3d400d2060340f41c40f12054010310b004500a45060305141e0501d01e0031510342200740031400e62a890002e110001005440c140d030100ea420503282c40d15002d11400c400007a10540c3ca0340c0b40e1001e070580c28483d01c942c241d0b0002c4101a002c1c2c1e5524501c0e030300c44010b150380b0b10850064004000030008100103030300c5000000e24443d032140b02610540c0c030149020925040c0c0e03100202010031031250050041a814010390500c0702602d14000c0040044910740c0032480c06000308085051614400080c030f10802007000340e490507405402001040d03070f918914408544811001c450908050b00c5003035942402800c50000d80c0c1c034100b965031a00c4507110801c909062040b2a0b00c40300e5409000c02000b41107a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 508470737 1250 508469487 508469513
    0x301210c150c02010e09040b0c0c030915030f0f0f060f0103060b1204051005130f0302010902121f0209030705060313080301091a060c210c030310150f0806010c0807 72
    0x1516800320b000080c0c400548038062000d9035500803294581080701040007041101c0e0040d6402008941c4c40c0307032001d00682180306561540742c02c003007440c21038000d0442c1c3c54001d6104100d00c00c1a07560540b1240b018040d00d2100f62646e0348141e030700e180400c2651074120596a1070300c5050400040155495000301e4150b001104441001c0190303500300010b204051001c0035401424140400c254032344150a41341c0c0811050700a000c406200d610502098000d500115003e90010110f0500c803280460107692100e400041c1e0318440c61409454441e090b0078002d8a829180081c042c126880c101000d10055800080503402071282540c1c511010451800096002c1c2200c100c02003000e030210303404031030260104152107016071002c204100c08503502058042501c074900c00140405007408203405650f0190209042150000000f4445045035901c80030302184c491425841214000d02030a07292000403130000380100c1c00c4800028103542c8524160786ca1b06114680300c50422609485200c902490 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 508471987 1250 508470737 508470779
    0x100f0e040618050604080d0227130b0604050603090715020a02031b130b030120040f08070b0a0806030111070f060501050910050f15070506070f03020301210c 69
    0x8120203220901215004208141e0740c090340c00702100400f941d4a544d1818004c001a080d40000718160032111a1501210301000c0400c004020801c500c03d0198209030503c02224483c1c2c541c0c1c01a21208245400791200301c0709c1c0100034600300751400d01806025070006184207034074021280040744201c0e00d8202e110003600c20340e00400c0e44183c10302c10300d0700d0102e000e03001610385048581e000450b0361360710356202000a1201004122180201c02003400b50608200d9000d080c0c0004101118040311800500204c85400d00c2d094400c0345d80d0042942c8800d81c0c0e01a00304901401c0102d003440754000d1f02a66000000075000080b151355070390b404203483e0400041115510b1009654005218081c020b0031301510342280c0891490808844c0e240d50071a103845043d0207a0100b58039a2400c1c0e0b1601c40c08410046006032840d91404031b460100d03102c203001c5070038802085810087c4582e651203882030b281a42e1004503600c1c4041c60704031051845c4001000c04480500c4c0c044404204500d441c0611001600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 508473237 1250 508471987 508472009
    0x10905150108011a0609011206091a03010b090c09092a18030610060f0c0b0c091c0210032403050d030e031303030e270f0f04030206010608100f 63
    0x10502c540746080d41c40c0c00c0d0540200501c0341038462100d60710101203a4a24000f420620010460006030744080c01056010f03460741403800e1081c0d403180102c40324119031041d086000300040070358002000300461040e03816450892051013010300c542468000710360450840d98000c2d84000370503c40550102032202d01206101c004100d10b41c01500c002c9010802d550110007505891416203c6903070301d0826403242c14208a41c582e09003848500415142d842ea58120310001458a07100082c0c542ca5032240d01d036035004001008110b11840300c2d2245189e68598010320b44040d00301030b06d0302180545100d0000c40c0ca900006040d1203001200310342d00034019403042000d000300c021003e10140c1110890111100d10307030010884c0104c2d0340c3c01f600038001500d41c107040c0900803030390000105034000c1284c1c64101a41d824111009820a80c529400d846010040300000b1181c0d144103a40151360030503200100964400300041c0007035800b8000455104403c41200d0708080da58030201d0195801e13561103040c02031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 508474487 1250 508473237 508473239
    0x918080d0b1215070f030b060309160506030c12040206091903060501080d0c06020a090f12060b0109080606010c080c0102210105060f03070302070804030c081608060603070608090109051501 83
    0x1c02e081c6000790140112030090040050346881006600d8001400081000a014120303481d05001ea4450840d80318090401c64580c98154512581c0e18803a00060210b441f000c40b0015061034204100e0388540340190500d414200709440451281b440540100d80c848401c0c01071050a0b100e020b2402900302407602c0c0b141d00186107040400c2155010781110b40c4c80d070880c1c9180c82045400c014000c6056511050040c0d03103204c4800c0803224848503411810031074071154400903021250070031741e8240341e001f0101006140303205001035500c0c501c01c1c89240134a4002c0000a9010360155801000d22070042d89200d1a19003d4401d407422070784403855071a03080f00008000502003541d01c07189400342405903003d501c2c04200c00c00c0b030610307400010000c1e0100750f00010100c0400c00d01070203840085920610342080c0716228121940c49410500314114481e0603c2d00000b08641c000a0450042c84060060003440c1d00380351044a40a8004001580c2503483e0042d20f070000c3c10400c11403d03003166030903200040d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 508475737 1250 508474487 508474489
    0x4060b040c030e280b01030f0c0501030c0903110102120d14130506040f110604060302091c0b061c050a030207050907111c021e0f010b0312040918080d0b 67
    0x39030003401018105464a0000c2c3c030b280d800081d00c4090080551500071448003040d902c078081c10a00c1d60000c0c403101111000000b000741b1403001384107440c0715a504130740541e1607100440c211032039001c82d0350010b400c00c581003000c2241c1c078464506400040c8151307203480110042c41030b543e5012114010509139289980000070b81c4121115801440540c80c42d0100e101d283c440956031100944007508c0500d1a40185d010401080081b0810807130240c41c0719100c55a40001500039040100b8203400383c8140715008140020300c41e810414141d210800701d00c2521450140a0391204400032100300c41d80320764000006c540d0401c090b4030582d110354010201c49051105002c00440003810074007d0229603400d442441d000440d0901e035803404002000340c5c4007041c04d07040b80345c1031405141e0b124843ca0074400d43c1d00a140480c0050174000c2e114000d0110858903003d1681d0740007075180600c840c031424041840503012940004800c1d8280c10041101608561070b40038071a0300050341080d20316500c0082d8201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 508476987 1250 508475737 508475741
    0x1e0903090628050d1103061e0d050a03030b040605010e011d03010b06070609020406170d0c08090607030840020411040603050121120806120a0b0105120708100b061204060b04 76
    0x1144925029403405c0d41000004640001c042c1041140c540b00d108c0c40c08100b60b2200c02e076405c1d80340c0d04401107034071414144c240a8014803004425901841c103145001c90194003403e00042c01c010180e589000380610280c0440608014514141e4075540b02d030b40e21507240d92600701038501e030b50007200000345440240c41000102d546c2c0c1da214100e90344954500c01448240414032100380b151310700300050722482606d00700020f80b1840035140e900c1071000c00d14a0034198455415031042c4604c03040b84488021003580410741c1c01030116a90310b2480105042d02e0390105000070042100e00c00390012805c4421804003d415811513046240025a40c100400541d01c0d01803076441c1380e80b0050b00e004030f42202500c071210080b1081040a041c4540b01c40425469100e14100051800c0041d0503103540c600145020b580f401c2080c403d42d031103141c15900c40303034200c0404030b44c0c1070850351003000411041000201c020080d01000088661015040c0302e0300d4000611a650103120b507208504c0003036074421175420001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 508478237 1250 508476987 508477001
    0xc020f0607030201051e0c0708070c0302040f090c1a0405121c0206090d09060804030806010e040509014506060306020f0403260a03200f031e0903090628050d 69
    0x1b02001064144004022483d04451019030131203045542d40071641049600c420b080d42c402900a0328205c07042e21003205540c03001803110b200f810350704900742e030314400f210030503103020b0740b080e00301c0003c210410551905070320070200f801e104020340d00d09900c8440d26103094401e50441c180036030009003c020a1036130a200080340b50900e400c02c80c6140742010402020f078440108001c0c1403140a00100da0707980c0c0982025141e6a400803c14072440c0f07401140607000e0544481c001e6422050720607200c05055030b41110301140c007980c1000001030b00e20701c5030030032400400141c25a420340c0c0d54440440842c00d140005c1c400030620406540d80c807440e62404171240b05540d804410351503041103031540d010780504103c0d203003500149804188401e220704003c0302a0f441450301da8910314002141c122500da07050145224410814040400b540c548083c2016880304580b01c0a4a0304200210801ca103001c001410412072101300c00e4050520180000f030710380304c5400100c0b000c07610101d0a080310030007500503e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 508479487 1250 508478237 508478281
    0x603020d05060714030f010e06120a061a060403080703080c131212020f0d080c0d0509070303180e0402040c0e0907020c09070918020a020c06120604060603090807030c020f060703020105 81
    0x94174500e0440d5517900c0400040c0210941074081e07801145041da501c880e100c8001d44d000c420348007901524035021f4014000c02c800400342c12140a6440d0091502c1c80607101241c0c1c000e82d00c2442c1c0320040d64219140d5030000e10800d003118083c02188250441003502e20081d11a0b4200662111f10750700b042c100a04d18030741c00e5811580541000b11a034040030510b070100030460f003003882d081d4031190710000541c001d1600c03121321b183c649020010340742e00003d041400c49009172540340e0b40c030940c049440100e1402d4020030154880ca600460010700b0641d011402480d0240b62460305403034041c0000741c1c10403013641c0c00310040c0d100b080b80d80640d1500b00710080c1c01034010300f4010180c130700d00288804020300040820410541c0402c081316071600a116500071400c00a00310340d130340c240300010040247c1007a100b01d4012482e025021800c107001e44a0300c034446d03810440c0d19062030420380d012609009003541c00c84e0001c641100d0a0b03001d80381d00016082c800d02c030b40c0006c982c5141012404111020441c0ca41c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 508480737 1250 508479487 508479527
    0x617060601022e0b0109120303020913020a02210702060a020a02010305060301180201110f030f0705010b3708070602010c1b0209010608041b0902040305010b0a0b0318010603020d050607 81
    0x50041102072203c2c1d0031481a0350389001c1040c04400b001a140308185034048004030755201001c0003003540c1a4001d04041e4002c56411185100722519030049024840d202d80150303003c420a01072200c05040740b101000c012070300c0e40d072524403c0d5010884541200341180301580c4804074080456806004d100e90203041a8020881c1c00304042405041d03442e07108019040c44000c60381f6602159040c03160703082814180d4200e03035a440d10307035a14210640c041d5105031019486c0c06803046092500710480380032000780303840300b0105c50400c07600c04d031114000c1d00146c50f02c15400980000c042a0078040040202860780000584820a0101805107030000f0081a15542c1c10340180d001603850301e040905450041c0707000710741c40d0780781d240c40a007007080455080d000344600d0400041c8603a950f0002c0068902c00e80081c441d000c000001e012005400d40608180d81c0824000141c19500c00f40008a8556100c2c002144a55803900820f201c1c41d61000140c500d60007580c10004c44030380203229038650090160070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 508481987 1250 508480737 508480783
    0x1005190e060a0e040906020a0c1505010311040c0e0a06031d0c060d020c0f01090506060a060203090102121c021c0b090f0408090126180d050405040906061706060102 72
    0x64090300c02d081010041c0000602c218469840d9507001080303582e403000c01150f40c0d003840000509401c40920040b0b0b50400701e40341244030742101d070007058100c2ea40440c10100d000c0307110040101524005035500c08202001c2c6030142540e40740300f801c000510300790710009045100182070070308140c1c01d00c86100103a48104104030340b5894601c11212105002200107840c1d1259010050625200034004480d56003030903015000c0c040d010038058002c58084404820b1030703035034000070ba80724020003c40d43d015812024402d482c903414200108215400520034600400188210b4400c0f80c2000c0160300c0303950312910400d00b607a09a4484d0301075a9000300c5000c20580b8020a441d581039500a00040ca014000306818425034010240307142c81800440c54000b01c042041e18a00407694110703040c218aa01036011044030f5039020641d40602d40d0584d03900c0d840c00c2d080c1010304c0b0150484a03000c503800d507039a510000b000700d02c20180e51403880b01c00000e00014142440028038008540060014043c02f03280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 508483237 1250 508481987 508481989
    0x709061b08270a03080405010e33190302090f01020105060a0306180c030605330108191515090e1909080f0c01050f0915151005190e 58
    0x305484140420b42d690550018030b515004500400001649400c0b0300c00c05030100030081c0d0100608103482007070340d404e41000c10100402c50310206031b010078801845440d1250059441c09100c000320030b5410345241c3c0c6400d0b108202400c0d0030905075a0000048c1d400308541d001c07860012203240103010248020300c07581c280030002524505061100808031035039334001c04d106940c0002c41e01102c03a08a03003000030a56032400d24401600089600032b90070320318a02c5c0844012094480110704403844038801c1e0030050090010365103401c000c0d00000341181c1c60701051135801e900d40100032080410130044018a46040c03440d05504100030124002c1c0000200140a50498508240e0740500010300701c400d502c440461207402014521301c0640382a130001a01200140560020003090300048003c004594030f540c4924040c0c030041d21280304540110a4240414014003181a040a44a0840050704584d00001207d140c81a00008081003022601034070000c1c400080202e0700e6181c2c141b03250301c0382c4080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 508484487 1250 508483237 508483253
    0x1b020307170c03160e0415050a090b2401030e1603030e03070b120a0902010c051510080f0307030e0a0b0d1b0302070302151905010e04120c120c080906030709061b 71
    0xb000d508445143c03c00002e01f480207489030350a80007101c500c00c10a50901d60314100240c800700400340d84d902c0f41c00000c03651074140c0c4075403074100d10405031407a08910200001103003d00102c3d01c00c03507210710a0f07441c0500f00208101a81004510035216044100f02007403c0c141008100da00a40d21840c051100c1c01c034904071142920b50015501c00c0004014a60f4070060b13070392105400e0003a00700c0c410b80136144580107040b10b066003d072081c2c00c685142542d480a1403a900d544921101c10a13810610401c00081d0142940c0e029420004186618403a15041030800c25001150070440c03040e01c5421a070882081003609069001c0e003032505501c3e041daa81c9029603038012208410195280310400034918002e9450320a0107c0c0442d02c041c015542c0d28580c0c0c1c2640f1006490035076009901540b0340309030b5809a90b03d80f400035880f0310150502c07280130300160750000d4202420340f001c0c0c03006c12a00700a50360342d900039882205c960719520301d51820003400528541381c0d00101025000c081e042000890524 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 508485737 1250 508484487 508484489
    0x1030b010b1b030a080919051504020f090703020319140609070e03160513150b03040807060903120c2609010f11030a0f1b1b020307170c0316 62
    0x10706119510001d440454003901118580310010b400042840e0002ca071380020312030b008440341811140403000715003114034074511100300142580d015910103248070f610141900e5000d40028006400204002c0108405031401c80d00000029400010045d007291310b81c0d44840c1d0310b084d80408010380000c003c4101e01610014048a1091780700f4800a51414490b44480407049400360070b60351141c1c820451154440c550740a00e901c1044400b244e1480f80590384900c40402034034011030b01040785802c002c0161944090410ba88020003000080007240060241c840264420766540701c01d2040341c411402104c0c161030000c0200411542004458415600c1840d10340116603035000c6141c458182981c01084001c0e01c0075003140c204032500b0224500c08004d5445180040824022035041c01900030441c1c0c0b09011881a06488501031100c0a00c5003422038000d004140202441440c0e540000f442d080443d070100c800b2901d0b44004403804e11041c4a00340854a00b50010410681a8540c0080800711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 508486987 1250 508485737 508485749
    0x150e040209150415030c0b28030b030706080105040f062301180b0c15040510050402031510060306081501030215190314181c03020d0515040b0901030b01 67
    0x1040208199102c40c0b01c1c00700319407900038000c02200d4502a81001c600d81c50b44001d86130011081c1c0005404022101140d00005020f5206c0c51108140d6240d144151014500c00c41019510000c03085141c40801c101009410b943c0c84e08161585402d00704026502c084030b284003460b04018080009502041102c50140d526114808a45540c080100c0d4501d9150541b000030f80030a41001622030240c074014900c0782c000c581a070340a002d942e0100b440d100c3e4250307001030483d03100f40002010717044c4507440260030500c0202526a000c90302200b443ca500c00589525537a0030042600f000310b145c140c41610020410b01c40a490140688a01d00781000710510002e030042c25111400a11030542c00b0840c0c2c0103140340c031112600507a0081004009052000c40c1070b902c187c190010079035000c821201e0b2003011701030400620101c640ea41c640b401d10500c4850b541c0034103409000c4095803a0141c09501c1c800c00600c003c40c0f610420950810054882407842a406400711400500100d0a007a40c81d03415921 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 508488237 1250 508486987 508486999
    0x70606090e071406090925020a0f1502040801020a02010c0206130c030209060307080a050312100e19060503070305010b031209100c080d02040312080a06060219080f040b0409150e0402 80
    0xc0300c0f0104560b4407441c5510780d0b2118451007013054550341480c41341149000c250000341c1d040d040100980c2c0d68210800c1c05403401a8508518000607080c080350915071a51940260a01c0d41d56040107099070022148240540d44035050682120341c104400c540c05860200c601c01c2002240e126042081c8050001034041c404500024803240c604001990040002c10300300e80115002d810950340303e410004640035211180b2012031080106e209146003650025229001d840d19130110f030242e400c6000c041481c07080e0b12080c0001e210b9809105a6004500038000071802400070410503092101c264008140041c06020001c50768a440f503441d02d9216a605050071588110709010f12230b405075200e15007202340000340200811002d000701090411807a01d442d09140c656100364001d8960038024800180e000310009840840b00c6803040300f0407070151201e54a04015140d42100d0b17540700c1d81001d01c200b080040c007084010700d54420410325511000302e80c81c1490502c2d07403020f114940500082e00c560 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 508489487 1250 508488237 508488269
    0x210601050706090f020901120c050a0b0306040209040e03030702010e0715020d0c15050c0706050a09020102030d0b010903060c0f09080a02030c0622030b0912030603060403270902070606090e07 84
    0x1c118000140c1c4410b40080c48111907681d108d015140c0440c0b583c200301c0301c15444880c005030f1800c04189420641e0301748401d030b03811507a840080c000250004810580c1c0651140b043e20800003040c00210300901e50384d40003146103607041001c03915064080d809240d504480d40c0703610b0b060700c0d4080f480c808441220718210388400c102c0d0410404444020500c01c0b0000d14000600141c000e82900604100d441000148a0b03a03072581190b10442d01c1148000c0d025800400521000d11071a9220f14503001050516080a984039100c80c0c04a480c0d60000f01c0c040b505108680090580003640f405c000c10174440203054403812980441d484440a96409008920100d108140410f800d8241030011198cd40110041ea41d01d00b06000768900c260f4031103609004002d554081d80c1c00f000d017240e00c0b40e64050002c04854540e030740c085a480e81c03120b400b1032883c4542c001316000d01000c400e001004000115002d81c42e086030381001412560158480040315280516008640a0206045040721140c0014000003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 508490737 1250 508489487 508489493
    0x303040b0304300e0609090411060715020d1b1d0a050d030806101439010902030c0402030106020d110106090c0207030b0a0e0709050601020a0c030821060105070609 72
    0x70401e0403140c0c074007a1074000fa00480c850711511101d49100540d6840b244070080400503c101441020f00741a040640240003402084960b6142d00c06507402412007490400d103501c405d10b0042007209218030b0f8540011b280c219580550042020042d0030440e060b4500a4240000e0516250900d003400c80b10390a180c2e502003540d031000f440c40107000c0541074504194107880c00a28842c0120b440f02c0c0321324030f0048284a10741c4914500e5174011450f2060910b0481541c1c0c143c8000c4190095040f00030056100c5060404d00e007030f918602840c40c81e000421100417503c10181400c50351400c0c41d004501c14801080020303400104294080210f00f05007940c1c1004041060141510340c102c1e468260900411409255000602e0012603010703041241d22900c3e200120350941d120390080014aa10548e000c0c485681c00e42d0219400c100140116518000c19503102c2e0769442d005e81c02656118004500e4800d0900121404010000c062640c3c2c191890501c0028149006105010303005d80d980b1001c810070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 508491987 1250 508490737 508490753
    0x30703080a11030901050708090d0c0632150d11040507090e0c0a2c0603100e070c0b1005031207170c070501110a05070501140702090a050618060303040b0304 69
    0x741d030340c0c030100c1c950f903e20f0b20340c500074040d00c0240c40560000704071400103945014041021242130315555900c2c2940301181d1140d0000d08106100c10b074400a103043c20101400110340050003202da0a4880c1e400e0b0703d03055103000049a0f1000900b401803600802c524001a6020100203540c070007103030000b8a5031205103040322419096081483c11800041c01c0c40459440c1e1006414003504035a103003150001c00c401080711044858001403280f00c00d8407103c1c082c900e090009107501a400394034100503035070398111202c1d907108103880071004245018040000d000b04050401d500001242c3c03110b420620b00400310780d440c0c2d545400c040359000003140238800c100390302c0034400c2c04c8900e074007015484c0c5032681905a10b590300d0b481080d011910b5090030805030440070039120621a0440013030301d4410710f07250055890403a181100e00600310700700710080c0140c0c0e803d00294010103c451001070146800d0040c0100d2010448038050044800420461582e5000003200d042e1461645100c0e200d0700d441c585910 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 508493237 1250 508491987 508492001
    0xf12040e062b0305181207060305070210060b04030b0f0405060f15040204170d0206010303020d0c111e0f18010306090f0b1302040623010f09211103030a02030703080a 73
    0x882c0708003001c0e1070824507074044040c2c081801408440030b81503110742c0400c4024051190748004503040b500040086a000303500140d030103c140e0040d100b200c420320030728004941598100744000710000c2018010b2002c440003080e03000300840c03404410344c100b030380312642d88050082842d842c0d003001c1800560b202c8214082c81c44001c10241c415900d4a4480c2d20070704c000c40b60014002c0342d62046106940c0e0040c070014600d030403a80c0540140079843e07950701d0101c0c2e0007080f4420954145012003e186511307200c0321340f9807060b80841040020a80340700f004118042c0f5140c458280b08419090481c001800304c1c0c00d415044075400b01001071003080c240b514440a43c048480940300000050030400d19080442400081c1c9100300d40800280b9110340c3e81514020b06070011003075024200160101c0d95000d11514207480d0780c0783c1404803031969100b60107040d060100240034a150b5184003070000700001c6c01c6e400e00d004130707084011f0b504001d45580001e42e01d02882a025003080f0380c641c046121188a680448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 508494487 1250 508493237 508493299
    0x90d0201140d0504050c0103091a070212190e030d2109050601031a060a060f0807030e030c0d02160605030601051303050a210c020a1e05060301080f12040e06 69
    0x754890700c0c2c548920000f802c080303505031160700074000361885640c442d206000c50141d01100b14107580d80006801303844a40c2c0240018207500c00d86001100300020ba00c0039111041910075112140903081030b00404441140da001401303940441c0240c00c1c625003001102c0307408a03841d401c810301500c4070988a000ba003040722002e86030703000d00e80002c000c1c4241c254070f11400060030031080c40d00f038682c1020b120014a00d41f05000008150030704010142e44900209500b1101520b004111100c0b0701c48480c1c296800408000200d03400410107c3c00355406000308030003c0c6040041d94070360391030054042c040b440000c2c286070403c20000380782c01008811610810165411400b00d6510703a0544ca001c0c407148541c40354103c501244689900006881101070307076a520f6015001c411034510b0a124180b040c80380c40f08103640c10601d41c0001c01c140d03d880c00914020088803000703040e0000703008052400c04c4603140d05000d050104100c14090300200ea100190030030300a899440e201107811150340d926a04111003a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 508495737 1250 508494487 508494527
    0x90c02121b16030804031b0b1207050c0609301e0403051522020307140f0301180b0705120610030e0a03090f0f050913062415080408090d0201 62
    0x10062101c201d0180c01500d12515000700742c09a1400c000c80302d004548948c40c030703050b000c0101d00e00034010302100c40e800c14000c3c10094109030340700c08202d0078400112041443d07503220540c51040101c1020110301f424950f025003801c0090b90460400092041c6124100c2c1401a54403a41c281d01030780d0100c2d0021500041a1081d5050b420a0368404035400da036100e0b40d00500044e01c8059011050344850815401001401c1c480d01c0d2034501a0b4494200030042e5018140e8003400545442c20b008080c0f18442400d4890440c0b0624a0041051800648510104441840381e40c00401c40038075043d80000c000c6851000c242c0b21154110050f1080f6540503410f400340090740010160490900c4041d181d01014180b07440740c48010049090f15540f0410b0f0b03000a00f4404542880d00740d5600c840136a00840c0e0108504c00070300080078580084522080b0402d404500811503d0300310018242288441e18020305541000d8075134410b240102090548614a0b025005046a004180c10354408201e1104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 508496987 1250 508495737 508495739
    0x3010c051218122d04060c060f020408100b032b1b0c0b03060f0f0a0303050c0a0203120a1b02371805010504020a0503011206020c16090c02121b16 64
    0x4031240000708503140320218654a41355030a440c44080658050303a04550350b21484141d26190f10001d440300d48080380f010741d400c01006c40c560000380300c0001c24585a141c0400c0c08580d00d02810300e02280c400869401100c0c0301411550780314451a4481c03400003d1030a01c44c0340e4003a03400740c0c841019088005000900301c1d10002009d540d401b0180d032086a040f15504e0841c5000b800f81320513031a80300c00d4160310101e80304003880000d019601420701e5014410446204000c1c66001c20328000041d118040b8030b078000f047c107061090f4007142c8020001c03c60224403000341c2c050b034045038082c00382841c0b100400d13201400714860902c107000f040615086400c0c2403040c0e140e03603603903e14042c10100c10b01c041c100e081030004105810280211a001c012a56800b0f1840e0300c2d00e00760b00b252170801603040303c0954003000740d514002c5080180701101c0d031200c0b041c0c440d07991602030074a08480e80440c030b14040d9001141c01c024041e59940684a07003030b1107140034061040e1107040385418034422415148010321403001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 508498237 1250 508496987 508497007
    0x30717070e10020a110607030e0306100f1502100506030309100f02161503090305120a0203181c11070b04030b011508090c100e0409060b03010c05121812 67
    0x740440c0c2640a651101645100700b2049072240a41d200251899403e116055560b040120082c18914082e25100008a20120010b4180541511024500d40f104e01080c03080c10041070400000b0701c5044080010f19a610501039111951541c1001440380e4074400500e441d1018400c4551b030040041103400c4940e15084083c010198800c400710041c4070782c681c0c20401c04580d854040c00d0340c2e544062401841c8400c90214064001805d04904005051006510318074079500a140075900708074000d0f0b203034074241e402e1030484d0f00034504158455100e144060100d440b00c40c240c07004400c2d48c0c0740071800c0069448807149406e400d680b01d8040c1840008001007400512040c16041c1e9080401c07640074101048070460b40c110083c0c1d14000030303800c80000002035141594801000051908250300490107030b8000030119911503006403041901c40c0385540d92441c0030f1088403555001342c140b4500f032440130085414000401800c0700c00c5540c640900072500039041044172043c0040101c1160303a02c013080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 508499487 1250 508498237 508498247
    0xa0218120109060e1513050109170703021603080d05042f04140403051c15091508010c0507060f02070b130302010501050d021e010c0206040602030702030c04110f03071707 75
    0x2d10a8981903d05a41c81034889000725012005000c4040111100d403a00304a9107018403c50304200e4a943da0f402011000402d0b160744031400b410340c0b82030700382c1310150360070f02074241003c0d078038042d4281e03400a0085c00000c100605440040440601c0084c055a907480c0030f905d40240c07108000381f51100c52081d01c0744000c4034071441100003410341e8240001031031103007142400e24043d80c2c000d0108005204401442a100d00e5142030b400c0d50000c0401d5266a9081038048198150000084c460b00c80700e6408959a031454000300800480c0020000d0b0920f09900404174062030344010280c40c1c1340d0040050800c11501590f103201e8108a1604a078140121a4140b07d08139500c120b016500700800014985058414400741d940c01400449078111040c00000790a460074078514140450b420429006d07803115005003002d000280c00031035848006004262030194000401b80c402c0341080c00081d40203d860040d91000c0380d1424405842e9211414143c0b50340f03480400c980514003885041210850b448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 508500737 1250 508499487 508499501
    0xd11071a0307272402070608040501091205041e0e010911040f09021201081906020c160b0309010b040203060f1507060e1c0e010c03180b0705010209270a02181201 71
    0x1800d08201c4425001e611038118013a241c2030341c00541c100e0a1b04110341030141e40c0c3c1c00d41c0039100d4000001c00703010340c1c7c3e9040c1c690444503800b100014008034090200380c59400a02100701d0341e0f186440040303460704035021481001402600c4a094903220803940411910090754094041c07190308410b00ca8070f503041c000c001d400000003880340b2201a070000400840104054034608101070098034080d4442c5c0f5004081e602c0315550102c144900340f041c4c4c005010f02811400502252100e081d52810045540780c01e591404440720b03c0340d441041844480d6582d0380303414802c00400e0b202d42140285a07a60f090140c002c0c080094a500d00740030a110524501003400410320007910345240c0321000144c41260b44500107044903010404014a041c042401620b01c00e1050354101e64003400141c41d4403121034150000c0c5001c5800340c0d0049130720074113458003014200c141240032080e00245a117101c001d03840004040c001c0e0082a071f0010b000f1882020401c0b0302c1d035448002410290314000f600110500034a65 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 508501987 1250 508500737 508500749
    0xd061a07050c060307021b0f03030c061501020d02030405090a020c0a080a09060e33120402150306030601091e092f0a170f010c020d11071a030727 64
    0x40156400d160b10f4400b003035034041c01c940c1d4000d0007220682583c00549541ca0564030790b0112180d402a0126501000180425032070b441c0a000942810380341240d00c4000380c0b203400d06640003049007100440d400000d69003102c104442010484d02e4100e80e100082c819403d01e000a80a840c0f0101c2c2400800001082040441c0d0344400b00d89542d00c400302c40f2038402c0062640d01542200300b24401c10345880602e10044062003442071606060609020554400d000340466084070204200c00d44c03401030903440c074608000414501d541707450030020761100d00500030210001c0d0345a80e8801c4c03100712440c062040e041a04401c2160114070704000f081008000d007006100006c211200410381034180d16441501c01c091315280045081c481421556443c0080520040c400c002c0a104c501d0000d00806900c0780154001d4401c404004600034070021003005c0100ea190b00c42d020030003001d44065005200200701002407034607500c4151080303896061000da00100200d0100d64a80c003030b00344600c1c0c0c0c812540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 508503237 1250 508501987 508501993
    0x70f1b0e180303011a0d0e01020a030b030c0907050901080a0b09070507120306030201120e0c0a0b0912010207080703030b130f0606030c0207210c150201050f0c0c0d050d061a0705 78
    0x2120800d5903030b0300c0c4400d0294494148801c000079a802543c100901071106400101041080c0b040c52240c0c02c9170000041e2100290315a854110141001c0c040121086030680e215421407038034aa010304a4070841401c6410040c10000152350903503c0d600903802040700030700d03c007580d080084006101e074100100645001803c4400300904500a00c0f98004036039060711581180110041a1401001c400300588030314000d0400203c52a5075a0605c04080c1421030042e603102c001880c04d10200b8510000c3e202c0701c6a00c10440c3c000460138800030f071882c5940c5850302050146125010a00715860382403c0c9400c18200340254200c46c446400450030742d000740e85c0030403c0030703020482280da94002c0e104400105d5103564100c02c817070030b03005520100705001e80041e4101c40d60b80c804a20155480700300400040c2d65031401d109249604c40c03c4903800502d06013042d402c0800c1001500d44444c51080140144032000425030790b005016007005c1c0007404981c1d0b241601d08090140310190341d005c8241110540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 508504487 1250 508503237 508503271
    0xa0507021003090f0b0907081c0809030a05040302040b060904020c0d0e1008010b090105040f0e07021902061c0f020c0f0c04060317090f100f03050903040506070f1b0e 73
    0x54424410b98a480e9000380c0003000101c03d64444c0d503890321300a000c6d0302c441c0c0518500810781c13100401c0001700d0507801d070b00c0070000f0290301c090090440070040c2035465940c004110200b842d1303a22105030340a0b80d0f01182c0018035550300b400010014440c18906580017400481d812040610215954454052646030620b6407a141c5081145400142c491100429404401031080884403000b0740842c07141814400d1400d500e5046840840c0340540c40419014035000400c01440e80c1884042a1030f00201d000c458811800d0340003c600c0c1c0955002c4080c0402c007004103d8400002c0c0e000712204010300c1c1011980e1300f0b41c200b00c294903842a11050506031064144200035400c00384220001c5a401894011203004145c0407200036034040504154000c03055141207900d40d954450366441e050f810b45409ca03030030f003910f480070b0300b82c1e58010030860703060300140310401135600d5900841e180307640e00a07111000340d0181d00d41068a81c64a11068042d900c500901190519084407082e0007003c40805090006e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 508505737 1250 508504487 508504519
    0x10030e150906151f2604060e06130303020315120d0e0a05060a080403020a02130b041a06040519080d121506120f0f061d0903070f0209061f0203040f0819020111030705030a050702 78
    0x156101f5072b9507e4281c09080d95941c04a80300b62b0185030000324810402c81890300072000104520b820192201380c1ea0499107803801107542000e6051310456040e80c1d490034071880c10001400758042e002448041c400940005400c00d803007400400421079008000b40d02c80880e000302000180502d81d0b6490003245400048048001da8030841d442040009054a1415042c4030510441d0341030a10800c0c42c4480e151400308807054144080e04458089a84003089407900d80d40b23803400d523440d081c5580c0c05445151b40c280310403a40190840404d03c00c45030042030381d051a40e03090005103405014a40d003e4604034000c542c000c600d0802202d1b20210112151003600d654074201d4030f074400c442d0001d1114106000384801418442d0255501c800d0080104401000c041d2403007510074003807507003080180c00000d0280004400030340c040002d8508800248140c0250303420060903640109170181c1400040b441700005a003081045810203503209050701c1c0c0301c02c4400b901030102d17000048220b2042d440401f6920039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 508506987 1250 508505737 508505743
    0x140c1209010f05040509130512030c070308010b070302100c05070c0f03050c1806040c050c01021803101a1504030c030f03120507050910030e150906151f2604060e 71
    0x1a281e004206c400e50391140a0118803444001c03504440e10300442441107410f0791100003561044850420507641c030b01c920300e0024012201600020740d5440d00b404040c000ca0b6002507080540c0811000004040007034880075503941c024440b008102c614400300200e4030070203005e0303054100ea10407011200c000d5224801c00c00e00d006071041d0001c02145c4000010080d181c079400c004020205428079902e4245151025404d81e4400e1051003030f840c20907200f070740d011b050401c0301a5900e281200d0070031005040c401030510498203044094403d0304010f18a201d06441c0c4001c5030000c55004c207044804659174501100c007454000001d9000c2080c54800340424507850060f103100e1061941c030a0301d0300c1c1c031950411205e481b45020440805541e060581c5603030030200031419203030a601c0304042040c5480701445180400c010039000c0700e180e52514200e2240c45594884441002c42c1800281d030286000003200c200c0300d084004d0180900481202d40d003e4040c1a8180c040c43c002c00041c0210040c0d80e0070350750307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 508508237 1250 508506987 508506989
    0x30403170a0c03030915090807020f041e15050307030308160906080c2a010902040b041b050d020d0606030518060402010e01030b060706090308060907080403050307140c1209010f0504 80
    0x101090b03000408500081c0301c0c5d4420400d951003417044a241c80c0480b22020100c41d6517040894000c000040c1010a40c60309000042481c8402c650900440e400001c0107076908181c9884991181d03100e01d00808245900d0800f10040d04020b001c44190f10380e60b04004001e000280c0310002ca100309502000c04180c40307080e103501560710710b44a1142c117403556246403900b0703800304600c00708a02e00682405101c200101c2c15465480700c100001c54090513600400044924003044548030300d140100e030f6501c50035141100c20303081d101e03410b20070380f1842000c0c00080603110384c04904068500d82000810101d4155002c1401000403011848040014500c2d20381d880e030b41a14080c0c04907446040145280d842038105007d2400c0c0036000328100307801030f0740b14002e403605014120081400001080a5420206040c03540f06034a8540341c1c92506254401611902c4090701003403c20041d50b551000048000046a4001201204640b1220740018006110360085000c0b68001480210032031807552254050350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 508509487 1250 508508237 508508257
    0xf200307030e0303070212010506030c010306050a0303050c0a050105040c14100801260609060604050610080a020721231e090109081506090106050c0a0b1f060203040317 74
    0x40c580200e40e1400c1d6000e0002d281400d03032500c03080192000603100c01140c0c0c246014404008105400d00408040c10050b0040119040600e011010000e40c1d0b28940c1b02021250542411552502e4207208182003954030407010b411036003090188420051407128490444008034520000070030002c081080f40392030002880d001a142034010311000525a11550000510300d054244403c05442c00c90306149044075000c082e80c006204009541c2014000e0070b0340700c14110743c15044c80102c1c00020300f01003005081021038a90104c0c2c00410040000702c3e81c0079180d00300000c0d035108004a18020300da803a8030204840820012102c09041c031120305c08cd201e0042c1480242020f81c44c5c07051070608980c01840d4600c4c10440151000603003040c050242c25a00300c0405402080c40c5005414000045410f03030140c4100f103000c00c0700000040c80807450040b10b40e03000190407402d0f01c60107501d0715034072801d20500d10300c411454000181c280c0c00000400840c3d128240e10300c4444150004400a40200b45c822 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 508510737 1250 508509487 508509493
    0xa1a010e0c0f09100e030a0c08160305030403031b02120606030f0f0a0b130b0f040512030106080c13050907120b040c020a02090702190609020103141b07060605060a0f20 74
    0xf0101d2412406843d6140340b10b10f0881c50039074500f40020302d450960346059582801c2d01c10240501c85c0d0500c5a0181c00761342c150b12041c803a21315550305649100e07a03c00502002044241d50300b54060680407a88e0254000b00030820780358804114a07141e08013aa0001d2003440ba0b0004080800310200d0501603038015040a880e804629450f41240000001d02039008050081d8046000410901e81c1a0260f01a01881304017440c01c0c0c0b9140340781c8080800301070a914401c0c40108a210381c44005503a1048002c550309440f9986280d5003071000c03504d074109951050b4030728104450b645d405800c0070100c14201e2030074840304200704180720031240c24408100c0103801054042c005800d040c0412904110b50f0b10442e8040c0903e80f42c400000388921004a5190345c07035820349000c6d50f074180100c2c4015403404012a071a401e00c6017001000010740c1c10b01ca80c0e07001c3c001c6250b50034080a54031200c0204005020790b6507480903144001d11040c262152040403034008424060300c1040c080211401140388401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 508511987 1250 508510737 508510747
    0x6030606081f050f0d020603090a0c081b01050903010e15070e0409080406080405031312150227031203250f0503040b061f0c0c0510020c040e0a1a010e0c0f 68
    0x140220090804ea90a81048044404c40c0040c0c503100c0c0210711401c0000007800701451300786020440b640850380036804590202c1000901c0351510003074070080c94801d00300943e581c105a00860701404000f9030060f104d0041405031481d00200c0c8a515101e01180e66511403403001d0360303041204075202140c01400741d09c004d00040c8800ca004880d610381160040b01283d00308800103060600044541d048562201e444c924441c0421030388ad48080002120b0140660800c0ca620b000c83c0100b040c5052100c0460540d0740042c0350544003805031102030070103014095500e18142288e000082c2d0f43e6602d2500704079000140030021807040b8070200c490111940e80b545180c45503100c2c01c0c2d940c400644901d44c00201e80b02c8040103081d408556002e0101c15032110200944a4203150314841c469911107402003008800085a85901141c1448081d90490700000e80481d2900c40c2490300740c0081000740b0b4108100086241d007590030345e2141c101e40b5180c01d850410b50707903145418100d01824442e0024038105000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 508513237 1250 508511987 508511989
    0x18190c12230f03030a09170307091d01080604020f01030608011104050f0a0806010e100b04150f02060108070608100e070c060b0f090a091403030c07021504121b0f06030606081f05 78
    0x4810141400768680c3c00e003100d01f29450b100d46500031703650300c070200d5018182004100721805800070360903146031800c0b54540c0752002850711000018002842489245c42c0c1030b4003680640d00901c050900311008200302401e08501c4800c65001d80100d03881200c03451040307180c48c6040c0564200f42c48045e0060283da074070340104502c0c91a03028022110003a450f41010400c09136900c083c000800c2903040380300240c8042140548168003160b043c0c03045400000061128142c00100b0004403a61450090320b5583c0f4000c0120f0030040750707000010030a01c20000c0c025070645c071106211f00130340569003c201c10205c20701000105140890300c3c5811518410010311900c3c0c007548420105801046140140054910001c0c15948212612641d50b03001069110239070400340625141c00c0000c141d42494141043c2440140404110b40105040455211a4414080c0008190091440f89041440d10b6203030340d03028000c1c0c030090140d600080c1aa5002030210404081864100c81000c3c440084481c10300e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 508514487 1250 508513237 508513241
    0x2104050909010204030503160614010e0c0c01140106090608070228020d05060415060e0c07111f08010315020711040513080f0301080618190c12230f03030a 68
    0x1d10012480d507003071000201154050008001c403200407002001300d08a640761100440359900d002c0c03a4a011034800501070b14440228a5400c0460750070602e0300c509500c00e40c035024000d40c1004113501c08185000081c03040d0041e003030320155041a12401c0c0366030b4440c04120f035180703a035080181c04c500c01c4413081c01101c41d051890a80c510b00140030001c0998007901e03014070f03140003681e040706c15001d5544500b10003541441150094046650103001d6414055030400041c014510040c000600501240c0e405a031070024130880d0006906040510b016180c1001c1c002234800d102c01d56403506460140303031412200d8409c4030603083e40b111504991007544001d120041c4001042c400e0041c060b003002801054450300601844510003110750395960410b0380c4c4505141d07014242c95030810f440c0c0d044a00c090004541d09174200c155401e89840c44216003460380e0f094100d540002c000391441b59000b401c3c840004800808680c1c0c024a60900540b00d1001a079202d000d1000d011080c1c00c244041580d032442c80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 508515737 1250 508514487 508514491
    0x1c0f0803060612090d020d0c02010207050906270603060a1b030507020f0a110f01140409020304020a0504090807061b020a03080c2b0b010c020a090e12041721040509 72
    0x240050307040010200f900b90f02c0040c10b8031810750551000004004440d8100120500c0c0c0703a00d46418500e000c1c8560010f56594031034080e80f481461448006650b81c0c81c0e0111400c000441c19000c0303440400303107110b1907810300b809980007800707401003c00246c11181382c0d000340801e1011500c0203043d44118854220021b20020340603000318014000060007a5a0800000f0f516034008d89a00c85840110b0040014a802c03070345802c0e06000280c502a10601080b81c1030300d007203846804015940799034501c001100d1201a400c9281c0c807a190030700340010300c0200e00181012512400d41006014500800703042c40b03000d0140c900b00164418880c000000b44a210380179001001c10110f141001c40320602079018101114151260141000c80c00030f00eaa51800348801310b1100b8280240c6042d015008501024010301603410010741740c0c50030349040c2c4010002c1c0b1204d16425941240c4079521000755103100000d50720380d00c54520409696844025000c4280401d04d100103801500e40342c9013206201c901100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 508516987 1250 508515737 508515739
    0x330e22020102010f0509070609140d12021227030601081b0102010905060414060a06031a0c1b0f070e0f0106180b0a030c0f030e0d05090a05031005061c0f080306 70
    0x21103610130020482c0d0b0089a016480301c0024001c2c05040c050024400074260b03000d8840d07214282c400480c0d82d03d0702881e505a40d6001401c600703115400e110141d05c1c2400c0400e40070850100000c070008103030410500740c0548500301410101d00140a41059914403081c01110100e03000400040b80d9800001001400c1c41010300003c00c10f051642c40301402c01108071000c1d140461115003070600f40b50207010725a400350303130800c081000c50f080d600d54080a10004140d03841c00540d1300003103507610080c0300a031006480088c210b079409460080c61903484a00c0d00c6120582e0380700c2c0060208001c607201d00b455208840084150815a181035021581d8078611199403862080c010030214031103e54100170648643c09450204140b903403800020300c91112507580004040c904003481406650210341240111420b20300315440718660800522080410380c05140d040c8a18000541c840c12540c00441c4149401c60b100741c0010200041c420440011b0940140360140c0c11080380001074030707540559000702c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 508518237 1250 508516987 508516991
    0x9060e180a110d020a08100b04030f0c081006090f020a12020307110303090105250c0311010b0307060309060c05031320060406020a021504080c04020706330e2202010201 74
    0x48009140341141c0e010380c07a010405500005c0001c3d0207904140c035a030f0462142d038000c0540500c0c01110000074040d60000a1180c04203003805d50034002d14641103c050903041d400d60320710710100a00e000003004240b10f1148000d0404400020b000614420b030b07888035000780c6070700074110f000745181c0003398001401d86040c068000a040c1c030200c030400c082c41c030423030385040005100c0c141408060766001c8440b41140d1180d0518812400580d400300c0c0300e1001680c1420300c1a400200b800c01c2a014240b81d02c0d203142c0602c1205d03c00104d039a8140c000140481c001e100c10403d4510b514001c60741480101c52145000c1040c128034400105080c104c102105200c40c03080d03004030100c10000d00b23203511561054005a000030702d280301758904440015490481030f00442d182520f8100300c107845440c9107800500c141c0c2e01240000500486402c0a0303c601d000c062400f400c2540381d180ca054400741d0391000c4100741c000700404146d92803408625030046010500200100c1d407079110481b10544200c5040341155 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 508519487 1250 508518237 508518251
    0x14130f02041203050d061a090d020f060c15010f0302100c061410061b21020307151401150512150307060302090111031e030c120c090109060e180a 64
    0x2424054040b00c62480b075928070303990340c104040c4e10382039680c5900112004540403c22442d8160b034941103800c122002c0d00e44107402d01750350000807003204100281d190011400100341543d45004180d4210511540700c0d6a501031340c0300d4803484000c000717030300009400c85010ba110072078080c003071000c41c0306892007910045100d442c0300501c0840c3c1101500d140160046507a001c2c04100c0d008888450b000c500711038011901350301c41d2202241d00703034100400020400003824004d403e038800d00071208096044115602c8015180801c80000c01c3c0c03200e00c28100383d0344a0001f040300c4889004541c465503143c0c0d545800d200c011078918140c940080c04005212509240344161038505000300740040807251070041e1a84a05000034048988000c07194086410800c4000008003d91011040018442c042582c481e40c416110714018842c1d004840e0311544034000300130400003044000c2c4030141d001c0e603a8241316613403a401611500c0070052047c5d842000500e80740350540203007000b80d0703005588100204010b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 508520737 1250 508519487 508519499
    0xa0306080a1e330e010506090613060308070b0a0b0603010807060e010509040c0215060a0807031101031d010b030d0c050303070c081e0714030309030a0c0501021b150114130f0204 78
    0x12042450b404100c030703c0f002441c088084918428820110052070080c405481c02c40002905004024084c51148071444100040400d0039030040c4080d680c000d081c0d999035412170401d0201e151040b0b40950209080081a0b2441e08201060381c0c102e8060b2070007041880d0606c0b10564075044075035031260400c04103010500f595a40c03401240c980028a8002c1e02411041c6141e4010750080101214055228001d00f0040404e00151080c1165041403086e02101400740040700a040019080070824a0a0000c01180d2006500850501c01c0850849030f000303062031015a1026054880036040342c2060000410003406050720524042c803980a03140b42402c12a140400740d105014140c84019001c508081081100584122010400300003103055242c110915940d0f8407625201c60204101c1d818880e040020075015100041244035008400c1c05507503001541e140c0741500741164140c640e0700006503a44c070001c1c205442c8c120260000000300b8810142401504410396031400d421f6080100180c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 508521987 1250 508520737 508520783
    0x80a080604180b040c05010306052112030405150708040c150c0b070504090501140a03120909050115020d0806011d0d0b07020d0f050a0507020f040207170a0306080a1e 73
    0x2626103e502510400c1c1407038148400700c51043c2e00414145072905005000b242d8407591070340591602c110807244031801561b440c030308240c1c45030741503260101c0100601c4104000421400d509004c1c0303845400640d6951a400c4603020f4055902510b40c82c1800814004400034501c503101c000081c1c01d003078a410b4820b40e03032103207d144120f1320781c400940045404d10802c4514000c4500400d0000d00001003075400900250840580d40700003804480b014503191445800350380068000c00410302c0404c207540e9291058404030100c05034480042c090078401c415201e0080407100e020b0f03030045c2d503210307045003154582c4070254041010080d4084000c10000000480c041110b91240e280355001d85905182c544026146603d505460f00c14042d00380514400c00d40d0000c00c0d10001c503011141140c0d83c05020303020030002d200e03104c80504110040e200200f86020320400a24141c031841c2c0d81001069564440d25480307801e20003004050700c40c58100203c20100d0301e000400440d02440c1c0c10344103292114543c2c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 508523237 1250 508521987 508522031
    0xc0203060406060f08030f0301170f12070c061814032a01110601142b0c1a0f03010302060919060c0302010f0501151110060314010c020a080a080604 65
    0xa02c5903101d080a000d08038041c0d080c07a0091880740c0095050480c0f06015102600050042c4100070702c0c3d20442040c049020042da20901080744e00760f0300110280b0308105542c0c1e11001050f584050451000160a8455030408000030003083c005400319081480c030424841c2d00810003030b41445061a07030000c54024610790b03032507012001c10020a40c1e110400141a0020000e19031820b03030844e0004004c07460031580c06036003103c0d040303643c42c10302081074050104035a00b8403d0500c4c40c540e03219441c020414003061405c10f031070b05550320000c5031900c003264151511400c41c2d0043c041905000410046c00e1100160005d15001007000d002032445803071001900010b5171144000a803642911020302d502031089500051811800b03010540c101302200010307903400da08840401903020011048600c05000304007694812000c2480500e580c2d0070215000440000f54030000d510f046507400010b40009280b4140d1a840070500742000420501a12085001001280c101d521072924190301d8180440080f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 508524487 1250 508523237 508523243
    0x15010c0611040f0f0302030d0302030c0d230c0901020c0a05010c0305091203030412120c0c030507170c0706030e1902010c0804030230010605281208070302060c0909160c02030604 78
    0x1031354a01c1c500405107403500c061040000c1c18230400500c4909043d4004503442080c1c0503102080e01d0140b181c03c415401c0c505110402181c1340340701130221410010005083c44d4109900320f890902902c010080030340f84030320610b40418260200700700080c0c01407014000d50390340108a048224104144181140d000325811070345280f4840d0a001410b41103203c074007a0b540304420420002c0210700029001400c0c01d90003605002012480d60208070003000b000d441b03102c801140540310805415459904c401360700469010a080210310040c40c0b000040d00074105e1050040c00502141540040d151b0030a4000c0a440e003100c2000048003603218000f03152200071412000301c1101c503040b4201683c2c500c601d217070301140364100807003080203980303001c1039840400c101c14031090051612074001840e000c0e154426881840b0030781d00c1c0d105001541015091460007502650300310342d60718030b83d24114401c2203c0f660707001c207400002c074400f0816854002000281c0d410420303184422074001071305d444c034211422 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 508525737 1250 508524487 508524509
    0x20406060c05060a0207110d051f2c0c061c0203010e151c060203100330050406090b09040f380108190b18090615010c0611040f 56
    0x20301c081010420010340d01c8681182c0440c20400a941c40e680101541090144103910ba0354130703a4103010341072069000341c05081c02c0f409403181c8000c020030090291502481c26600080c102d660110f046034002e01e400501c80005010300707a14480402031550068a41b91080980c0351541d80501405440214060001c0340c1d003030200c0f072a08030380c9040d20b8031090700a107000e64031011080c1d084c8048800449d044552101d000b43e1030340d450340046111300e50280e01c041c141000440e266100808202c0001020041e000100380141c00011000d03181c40c400c520411000841e0b46038208035000544000d042c00b400000c00105d0140080245081503d081c4d05241d45002c2141c18062213000c0041d1700d103801c0310140c2526003010407140c1d0019003010380080c400910004048800032101c1d000d94820842ca41c002410780c1e02c2620f40c1806d94503013460440f00080540f180b0400308200320015143d2800b0781d04141c3d20b4000040c016038a1b400a00316411000081450620000c40d03000540740c04c11020700000d140c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 508526987 1250 508525737 508525757
    0xf07020d17130f1410080402150d051503011404080706090c0905060a05030105090304051203040509010e2212050a021c18050a120f03020a0206070309030605060a0f1a0702040606 78
    0x403c18100403140e105107800b01c498203002c0550307150078a01d03659404a60030800c026940354004240c60204205460035905400909040410b1581e8840da000d000c43d03000000c1d00c158050103150803110a8518040000e10303d01c00600081c1c40b503001410f51911a0703901081c002030039514056000e101e50042c404450f01c03542000300380c1c200000c1890081004400034001e41c2000381c00d00e42c40b07110301c1c0502c40c041c2401c004413802c1e8404c1041110001d010240001c145e039a5503100b50034440c0025903500081c42d2804040040c0140a1042401d9154000404030200c40e6004403d44050307000d034950340c080d8010907103c21912400210000c0704030071952910003041c0d40d01d00840d10b608803180c214503c11000d05400348140031801042001d01580616040440304183c1410703454030b00944402075210380c00140010405600900344002c40c2c3c0b00321403d2241e61108010403680b04c07034500a0311740700b800240c41001160f809000c541d449503610b41099282071201d4010505407916038011a010440c10b00d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 508528237 1250 508526987 508526999
    0xa180807031e0b0a050f1f090902011b0b06180603030a030513050105071101060f080d0c03121503060507030b1f0309051212010803030408070209060f1e09010603020f07020d1713 78
    0x1a4994080408484806c00521031001e02c821f0401d20301070003810554800000b011a4000c0c2170b00c00110880d502560320409540c50848040a01181c280740600c80c1084418200032901d0901409020b004000c0c6040c81f040c00801c90003000700900340c4130f030a840703c401d01e00490028440e0501512150b600c41c01c038003185200381070944400b6402200d00c4076558100304840840469040c5502c43e03949440c40654005040417070b0f6200010028090072031030004c0e4442c10035241c1241c1c2c412070380b0956003401103689400d8154116103140c541c2d150801d251100c00c004182c51650125005a4107003000142c01103940c8074240b0b030030802c0301e010b0701100c0001107030750305550b1000043c0e00510300440114918074203590355039207502a40703100034010f810040200b410f035900c1d0603041160500240c00ea01181e240d403040c4100742c01d012001d0074040c154042c0042000e9110340221a080d11100308001d2030821942d00340080e1082c5c1c0b6805940f01d036040c1e03004003a03404041c0c00900419000e0034403060f407203007054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 508529487 1250 508528237 508528261
    0x8011401092705100303080105060723011a510904050112020a0e070201020d0507020a11030105070e0d020409050d05040801061514090a15050a180807031e0b0a05 71
    0x744c4405101e504240c0f003040003c1d440849030b81511030503a0b201d620f50b4201e00c2d1143c0d10f121034050804400c001100360340744902056014403101c1d81c41150200520400c0c0c8240400f03e48910004441c8e494090350201104450100301c9903031030510700100201522520081072018003d980d541c5024a000130550140e240c10f00805004d0700403010303281c0c074035002e5600281d04880701d440b48000ca4081100040d603014003c2d4161000005031a509000c0e030318024100070344542d4190b030105e076841c0301518100c0b681d003814443e4910880098848035a000c00e4402000030100c10f00c5422a800f1f6210140c00c80058001e111b00e40701c0814a8951607200d0341055000c0b0b0075500d1a800c920703003201800c00c1103880e03564481c08414503100c940001e0342c0d0b00c800c910301103a00c190941c0c000c00400c079504048104025400001411490b245640d0721400d020b41810883c5100780b24442c0750741503440140103201152281c02e80b809601500741901940320843d94545605107400c076050b8004660311010031101c4a409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 508530737 1250 508529487 508529491
    0x207060e04050f04020d050309190303120509030d09020a03050d08010302180606190c0b0c030109110301142209060219021c030c0e04060e0a11070308011401092705 72
    0x72103082c082c074500492a040485401000648100c0700303940d00e84144401407044422021010300f5034252512560000301800070f032840110005640c0d01420000200e0038491240502005c3c00030754580014003a110307001d4940304200f1780e070010039000d0000000d51b0800c4880d40381c0f801c80d02d0322646503145d40108030aa50b0b4900f500c1c04503401c0383d07041016650781c50046507100300d02d07420280d42e00030071031310111140f030b0410000070199620b0741c06111a00450744080c5048840101c0e05000701c55202508100c103000a01c540c44c501c2225403000340040c90418008400200000d031503a241c2400c0e40ad0140545108007400d41e0034940c002400621000103006202c20300c6100d000a2000d01410b101180d003580d1584018810590307a14461824a4480e10701c81c405008006e009000ca03540302c0c1d008102c159001d80303445c0852440c0c0201da0384800c1c4400e0944a5098060b1202c0103140e207401032000028150426031030401450020214001404500c40482440804801c0441c031038107a032250215840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 508531987 1250 508530737 508530739
    0x1806060203180915040c0305040c08120d0f0b0a170d030207020112110417030c010608062406250308010605031b09030307060501081b0103020a0921120207060e 70
    0x412038014200781a00c8007040554041e95420f2603075407404280c050480b8035500c00d07a03000b8200782400c2500c0c0e0349038102030b0144c2d0152140b4142c880d550a03c3c1d42d0343c0c004107248450100401d0010388008141580711740301c1512900e03400300d03c0c10603050016145907002d800200f011441d94040f254001e0080051030b0038030b130650900718901100c0e0340000e4413070784030129010740050720b5404400c0c0581e4a03101b9500240403c00a14a03140c003130903241c1e501c81c0c1103200c196641d9860050000344907800014000d001c1e0800c2a03080310fa4000e44820200c01c91540c0e01010340010b0100002c64041003020709012100c00e00d00d400d601040801d00e0010011081a03224004021040c07092141c614000f948008041d041b592400d95607802400209065004180b0090560f034035103400020000c10108098014400307100c0028021801d030350040d8200e01036150010300065412000340440f28115228021500c080066085490090380e00c51040745048071420340148c01c501000c001440e00b0090342051288 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 508533237 1250 508531987 508531993
    0x603030206042f060703030e010f020d05060405070e01081e0112060c0804030504120f08070506010f1502060402100c05011b12090f0305071403030106031424101818060602 75
    0x80303455810310f0706010038072005205080024a42c0c0815000794407a418081e9002c7c02800070b01c810101b0440250403074001213055034101000202c0382e00c3e15204440c810080d40c0c450320001c001c0500110b0342c0c2c120003402c509032452000e04080301805000c0144d40284505011401e040c8240e00e8000103899426104a0034840c0f040d0902000a0300082a11b080c0c074190601c24130150380504246c04d110801d40b1020b40140c1d80002c1d1002441408601241a50740507800344204035590300038000303406441100c0d1001604480080340040c03038025801c0c030710707620140742a003424805600c820342190300c0f41040c1c58141e002c00d000c075100c080e000424038011038820101005030240c103865400c400c0f20031003c01030812400044800410002111000580350390108403a00e940e11420007600500010b03410305050782042c400a1205415403010050070100d00102c00c00e07145076102404510074803189201c040c081070445c0c14400d48103081c0c02c0c80062040075400c010918401c40754000303d13125030b0456001c40d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 508534487 1250 508533237 508533293
    0xf04060612050a030807140c0c01020105060915090403050d020c010b01031506051e0403081305090c0c03090909010b041404170c0d050c1203010e0a0605061303020405040204020d060303020604 84
    0x5200462045062501810845c00c0d6035501d134030883c0d80701c165007005e46094030081103104024000040740d035100042a0000c02c61a19100c04200b0807900c11962000f40b581e80d50010409814141081c940043c442c1c1400d41c108449148603105070b8000f00c456440580d0f662234861002d69150181d2284c050410903001d4030141030840041051182c800c003000340300314499494001060150441d0011a04803080315180c0c8030709940164000d51038400c10b44a101c4002c0843d508040620442d010209040c00440c50003c060b414000b00380e00c0105040d0040d56501d80c000c5880d1078501505c090b2680591089409203400c0c0f821441d41d400801c0b0303003000c050050190703900180001821034110359140c100a5194240d5100152414400c051614000d550100001600350940074506004d121511004d000d80d6407600300740b103080d01070000103103048081c643d802c202500301580001d41160001d070025241000c0d50f1010400d880c000e0348102d005a208804000c203010802600b0038280c900403036480200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 508535737 1250 508534487 508534493
    0x140705030702032505070e0a06060e010e0d06060302090c070510090803010e280b031b0a09020f0d1a0907020307020315070216090b0406080705030607180b030f04060612 74
    0x240550180d0300440360140c1d4650151300d8440c50741c101000d520408a485040e101e5000d0000c004042ea5018050f9090140109440b401001c1e45a000441079480002001d00c00b02004000042090150703240d0740d81306408005078407030714445841400343c1248255105803624003140381450645901c2041071400ca0320000060401085a0454084c68800300d201c0d140c0700e12034403094581603072411740600e58800120042d0310f1070304811003c800407000d0703800c0880c41e0607000040900179501075034020800902400401402c0d800b0b810b807071049070b44560520010403c01001c4a41c0311408011400380c5115866103031070104445607020381c062000e1130030032031035602003581d458103805ca0f0402050403800190100d4402c000000c54151034030a00345680341d5500401c001800450b402501450501202185001001400c0002c40d40f001c2c008088582c0e550b90203c8840c009400161041c0751455000503003120b071000514040e561440003446075060510f410011110f81b07a1015504502c02c207407403004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 508536987 1250 508535737 508535743
    0x6071e080114060901120903020a0201082212030f0f050a11070f0b070c060c090810020717030615070506060415030210030b0a091d070911030a0b01050d0609140705030702 75
    0x11002a0f80c882e4550f042100181c44c055480c504407a0564074001a003024182d0000c1c4d0094600d001780c0f5481c82c81c0c0c5405140204e110600d940144a102c0000c010b90001101902c981000100510300050000324650140059440500100c0c3c0440c0d2030700180a4641007034411000508050717805286840342503610110300d5000c40c0e501400e0b55218100103101c841c041c01030341c0040c5500c0034040110940c00c0708017405003a0720b03004806861091070a0105141c50030720032030b94455049440d0402d0f120004415004651000302201c2c1c0041410100d407604900c030030040e1403042c0c829806400c031450003005000848180a9001e40081c007210380420150301c3c0c80c0016400304030280f4009c02d002d8000b40126040401d2584140d01207840c0c0141540d848004298501000071800700781d501c8281c2d1150081d0544500c81c50102800e1410404642d04940aa20800c40700d0010706003d0b04007030300b82c1242c0c81140c05652000e2030190729110901420b640c150343e01c079032050b520f041c070f103055003400003001b13503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 508538237 1250 508536987 508537019
    0x609050102100c020703020a09091727030f010207080c0607020102071104020a1110060e0a0b031c0c05030301060903111009050f03030c03190f090b0703030504060e06071e0801 77
    0xb440d5540e6000b107418502c01c0c03020a01943d000707889181d400760380310404c400509010b802171381c580c14680e40904020300000105c802c2c2401d240b0003c2689500000d040b2030058040140c240c0c184180d406502c0404800e0000c0c241c0c0502072906c6503165918440c1d05400c0201c02442c01c001c5900c100650780020700024101404c2c094195001030300c50601210988101030135903400e101c0e900c5064581c48400080e44c2119080e00c0300340c000a011501c40409210654454201c900c0d030503000781c1070300d41c2201d00346a8841010401441d0100006030f0701e1702e405003103600c2a04603100013501801e041c4144203e015020410003402c0d2904c40100907070110080405616008541c421a03088400c001c20f5501007080e65081105281901d54800c80d04502003078044045009101040c0a08072564a00303000b41d03d01c0007110502c642d00d901e0000180c0c0c5c11001004024000ca40c0c60380d80e0591400c2400081055a00c200a13a844580c034020305200511080d0b080d06c2e14820801613480d0052007029080c0405407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 508539487 1250 508538237 508538263
    0xa0b100609080c10031e0603060e0d0e0906010e1c0303142406090a0302090114010e0307030f0f0f320c01050d090804030b041a100503030a08100f09150609050102 71
    0x1407002c000c045014507083c441008008290708000001c410300003542d1069036080180000c44bd40d043c05810305440070391450348502e40c0540744400007048c95000d40c10a90703058400400c2030342d0036181000903a06168aa5005400103a81d0340f01010f504610240c065070000c80c958222001c20314192011500e81071441c64040c059031003c9001070041d2540e512140245500034031481c119a15664484465492140800d0008901c84409042d034203001c0744480a481e002221071488109940760f00302c40d4803a80008603007090808150320086401c00381514980030322200000a41d4101c0c6115512124198400c20450b411503c89180301c0d80c0c004040355041d550400012511711424103081800e030050368006004240d07164100300411071a1103040f1440d24180341e9200050711503030704c0041c072080980200c982542c01000103899180c012034059501c0100c200000300079039101d07065002c003200e00303512604403240c581c801c110050344a40c0d5501c001e000c1d240b814568071886c01300000d50340c1017400c00704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508540737 1250 508539487 508539491
    0x60a0c12050403170f07020c061611060c07060203030f1303171b07111504050a120203070b0f0403060e0106060c240e151e1f0f0b0406032f0a020a0b100609080c1003 72
    0x5a02c240d21900e060f94200303010302c03041e078000c0d43d55800086d403252d0003244c10003520408a40051b1584c2e8005c00c40301805901580e41d0215404c03031009180103101f0290001c01440c80c0103200000315000c02d001040d030544a0305909103040206001e01003841411103507142c140e003040c4400c0c4081e4440b280910101d80082d03445151601442c00400d0424901d87c210402d1600700240520000656600901c100ca00c540802c1082c2c8445901c8142228840d00540700050b000f80a600041410140440150340001c0580c08031140c42440d01d200301d440d02101e039186900301c8c40b00f02003030442c03a034006a4031444003440d902c4114004c03400307003035040401054683c20420b846440200800f001c003112003d000b5590f81d45d11010380310905004150014410440020f0508444500c9104d900d142840f501946106000850b804d0416410032a04003a03000d41c1144100c41205020551003003516000c1c807a454500c2c502981402d0000380420803d404c4100d0ba40d00140c100b00b959100c0754010000207003a4030300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508541987 1250 508540737 508540763
    0xc080f15010c020307090b0a060203030124020c03070801270b04021c060c02030403120219021c08040f090b10080426031602060a0c12050403170f07020c0616 69
    0x5890901c0c2c884030107900740c402d0702c6001c03071840d110b80e105100c00756044600780501541d80404990b01e1209001d018002c9081c030080342c008000b0501799100e080c500380142c80b1403500b410003092030442c80d41d0140103160b454090701c5203440d40060611445040c041310840070159551a41360038500054802030252402c1210020410000e000d61415160702010034080644511710003552a08580001d80300c122150240010140c00090085480d00c02d5481106040b035651702000800f1010004800001c000d03040c404002030342c11001007010b4401e80080300302450400701c038003044420303055030310f030007911440f800c140c109070481c003a41c0c1e000340d1200400310148040c031108010048444140c000824004c014032101401510560310320800340c1d0f0803a074260381c0d201218000c1c0c81c142400080403c580181c1d840210400340c000b02d90050007400d1080380700030300407070070491700008483c0c3c02030410140040c80303051a414072494262800444140b0f040c4151000c54030549940944010514142118 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508543237 1250 508541987 508541989
    0x10905150f030709120804030b0f09061f09020c07031a0906040609060b15030612060709050d1a040f0c1d06060a0e040e0106060216030812090c04150302040c080f15 72
    0x62100c0181c0f456113040c6807031725041e1408030590342140c00100c0b001e5018500060038452003403145442214800000c040944500d00d581e03045484401054002410f10f010100d51007075a03000030400101c0b102d0040000c0e500d942000b4610306c0f00c05204280003a000c4c0c007031000400c800260315800681101e00001c02c0380c0c65140110090a00000302070304003900001c500f0b07004403c3d1000c0c0d403040105940128810304c6030003400b621901c00f10b5200c0081807a000c001c0c80b0a05048041505107807080510704440303144041e0985400000f00e908030380b9102550710a408200240d41c0d09801800d040703401c40510b403038000c549080e0481c0202958016023002c118800d52502c104903426540ca80278204112107901202042d0103810280174803c0588140c0000e1352000200e140303400c00726074002e80d00a0a1a440b28136900c2082d2000d41000410300c0b80300c100c19141e41c0c851150b021000c5010300c0340d0a4041c91807040c00192480e14801206000b045070800040903440580a50700840d200c03500040401040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508544487 1250 508543237 508543247
    0x90d080702010f06090203061c32070807031a01120303020c010209150301330507020a180f14040320030403060e0c040e0d0e0103090c1d06010905150f0307 68
    0x30300d41c0c01d106042c004c002810f9112a4000d42c0100e10590f12120801002d910b03a00900a00c0e0304010b100c0401d90005030054072603860004103c07011a0386500074480480d50807441e08c907441d004460705400a810810401074100c1c4a81ca0046500c80c41c0741c1c071503160014001c042034410101400b030507000250040403107c01e6040b59030041c0300801403803820700b1320005554950002d004044820040300003080c0d0140d0000005401030303c003030b00448203c142c0c0c204100c0d40b41d0415201207030400c89040003c1005030040d44a0304683c1c40c001c00008000040d212540117854050780003407440303140a0244404aa844900e0405020b031460500c0300b0b842c642242c05186124941c0003402061602c6115003010707070003054403c0078410480f13061042549429005407107050410b40c075400f258008091045a5000b90000da4015000d8482010f20940e14043c0740b0006800140c4850b4013103115081242c01d40e00000500054a070540340300c481c00d8600082901b0900c43c440510080c18000700005041d18418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508545737 1250 508544487 508544501
    0x10503010b09040c15140a0e10050913021806030a0903090f061e050415030608012d05040c18050405250308090418080a08220602030703150f0e0f090d08070201 70
    0x10180ea0381d03541f4041c03031f0040550425444c0c1ca07201d401a400300c0080ca61048056406200c0010110604100e120101c04001d60003800c482c416541400c01c804690754030403000e14410000c801c00442c0e04d10640c80e006024904540000069904858007448a25440180090098605100c0701e01005281c0015903890042c0c2c1e1201d030010040d45001641c1c0d80d0b140e0000c40848104c0340003440849041507a014024800e8000744901e01d0780c01c2400c068030852504410f030801e00a01c501c0c0801c50300c51458049050603203640103e101c1d1244103100403c9001c002128003143e021800d00c90380c00000368810200d91280c407019201c540c2c04075600200340d0361584102c3e6002c0c80d845114420f20002c0ca409043e5401c500180b8010825030310001c2d1605000702d0140c000000804031015101441e0b9803414025000607000a0805a441401c03a18500c201090b00c80544400300606540764030300120400600c100400c0d207a4503d803070380300344020078000240041030f020841c1090480c44d07598030341c02c0f03004040c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508546987 1250 508545737 508545767
    0x1090213090e0304230919110706020702190303021f0b133603052a03031603090b0402101205010303030b010f0c03140a05160506010503010b09040c15 66
    0x1416a620b105403034004024811602c1d03100452081d05c000201075905c010040c120180c0008140300000c456007101c0d80b41c1c640d2444031804c0003400c911941c040b240300b6002440708494156000a00384250f140c080072403c1e040c0f07400040080c0c001d043d0743e00203460340ea484024040181000360785181003881c50300b01c0c01002e9005002c2910880c140f0702550081c140864032205c450480c44e8220b140c1e047d0050461a40640900c0d0100a040080e502100d156100324078401c40700d108103916044000001c101013100044d5403009541f2030418070300540c0c2524914000100381403030504500c0000d9120001d030759201d601241c20451600c44400159160b2240c404988035040c0383c0130002c010150180d009402501c0e00382e0310003800070615401903aa40c0c41d118009004541440c80210003000318000602c0724242c0c43c0390031810642d801c201c0424140f48001e0444082e04094014000d07400c0c240b0501104180c02c0b107248800c1c0c03c00c0c3e200c082d0305110307a00407a401003854620851a50b8091031408500d001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508548237 1250 508546987 508546991
    0x2100e0717150108060c030403050711190302010e03010b0a090c030e0607020610060801060804060506040b06070515060604240201021902011b050a0905010503090a0f0c0608060303120109021309 85
    0x8090440c41c2d240d1a8082105000030409000803a41c010000791081c40340041c0c0c0301d694034685994605a0b0140c0214504850b0b0000b03080428040e61120907043c80010843c24183c5086411440003500f00035040d01598000da01d4500383c050f40340d0b285c400101c1210f00044002541e01a40d0740c00724040c100c028104009845480c06005515500207105882201c00703480800000d0f484c0d04088505000038810000001d00c00408180440d8240c1e00082e04001c3c0100001050108100450700c150485401601d56400400000a50880106900743d01003030445001c2d1401f800c0a000c04020050080c4084c1ca400210f040500098000d44c111000c0451604100d5010089108001c0c0a0895203680a51038060404210040ea014a00390361001240d501c90b02d10030b0341810011609904000c0090704c1c203101c1c450b019408030380c00c1c4021020340d134045c010900e420340c2440340c09409100c4c007809072802a4820024000140500100181951520030016030303508544074032450221215000400e07480c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508549487 1250 508548237 508548269
    0x1e1b0d170a2d050d0513050607050a140a02030703050c0106030b0a1e1a0f031e150106090e130206280e0d0f020108040507080601090c110102030702100e07 68
    0x1034001140b0303500e4995200503120201030981140d11108000c20880c0d010a8041c001c46540050f0b0380c0089500901220010300c1c410f09070340328035103001d40c180d071a0004240b00103441c1410701c0c0e02c112001c00c40f6800d035055070b00e03181038910001d58a100c6c1420140070082d022590401d00701080d00142c00450b04408032421038100314542500078600290385071100720303620300c858499089074020b90080301c000f10302c25180c4c1c101c00000d216445070b200c01295854080c400201c95012007a821901c10640c0f400c006100c1c030800c103520099101c1c8103800071003e22460800400c400038a14a149a00c0021380c10300358800371007840440c540303001e004424100e00c024110700b04568040302072080780040c1d840d80c1d0b19044031245410700100711900c441c060040740d00c0f0b0b694003016502604907240c1083c03150044a03100c0d035862101c1d600385002a080360400e99100d4804c124542d030302500300c0e500c540101000f145181040703800a95510b00030407074100078940703a071001840404184054070050040b1005840c40c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508550737 1250 508549487 508549507
    0xe0d180e0f161124060f010918060315050103030206011a0a051303050d0e190810020903120403060905211e0c0102130905010801111b0106171e1b0d17 66
    0x980130440c0340c202e40c2c40c090400210286002850245529010b07107901c280d039400c0251800035500d0345010055a03984841c000000100b180494054001e03101600140c11f5041d440c009081201c1a0321143c0104420030f5008001c5010800320789981e034035030030000d0383c07040d0301941c4043c24049540040d04501803807000703034800e80c1c114103d2294404206d6202000402041c040648100213020751516644505602110a002c950080942c2a0010f040711680c003110104004194402d4000303c8425460707040c10410032100304034440700c0c41c2007903008020380f41e0b00100000c2507025034800828600c955002c403001c441e00c0c20f011a05c2100c1920002d541e2440050001402611144212141c2500e080300003c1c1c240010f11440c3c5132180c40b9110700b46003241e41d1440c120700501386510800d20b5561903000003400700010b50f01c42200c2c04100d014103511000c0c01e1503031840c101601100350081d00524118140340c64141b000c0004410300b21112021103089090031a6a0402000c0d4055410f100041140394 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508551987 1250 508550737 508550773
    0x1703070302070302010b0301180303020d1413140604200d0221070807080c0907030209040614120a030e01050c15011e09020406120905010e0d180e0f1611 67
    0x4524000c4d00240714a114560500d400c84410480c0820110881c080b0540024803a130000e080d040d110b43c00125811120007011070b803400781640c1c403000b0310052340c40e00400c200302000809003481200c4041c0c242d0b0b26140c2c8602e007a60803444000140d00b407102d10082c1e03050351081e4401008640150404580d1090711056042d10301440844a40c14812204000380d80c000c00909981941c1200f0040d0400401c0d10041c060070040150002090603024007003e40140c40724030901d0010458194030308090769904042c0005c42c81161400320b8650030000c0306074003103074016003d00a244401e28000365a4418101c3c0c490a0420f40384a920301c600302c1c80c00000d280d03000d00410050b0300e541d8222100c003050703030b90040700100e104500c030355404520445201044075010f90f00102d1654040c000114015601c0410107003070071000d40310301d004204010300407800760030b0480b10788026000c44000792040d0305100c94090b1021030b00509000c1106075051000d04064410500d00c15281c06040441c0c91141500c071a00503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508553237 1250 508551987 508551997
    0xf0b0711010f0c09082a1201090b0402010917070614130f050102190312020d020c01150905090106030f02060705070302030619140c0703200a0c0e060303040806131703070302 76
    0x400130300703d1100031074010000f1468890306c810900d40c100781301e5012400311075a40e0302e0401c4140d000111201c001201c0d41d00303000754003600707101e00c542a0b0176240c180300242c0610ad560300101d02e0303808488000480200000b6075503003500c0d01e6003010041002244220615849034211509003508010800603001c4140e40400b03058440c01d8094429803040002807100120b0000300c05400079080e4000b249815010782e00170203481c0f01c2580c000d854060301805071402d5a00340401c0f4410b420810f281000054014400c040e00910610000e10125296454007000d02c66031890191046d0b81c001a20300411408000404c000d40d4081d0660b400b610300f0390644600c0180325200c0902e940d08000385841c000d0300c1e100310303076100f44020f582440c146041510110358031100300c40c1c0009016660505112588000c0180c1200540700b00f00604045082c00c4c900004400064030301402039000f0300083c400d001021a209a005544600f082d4041905050041003956040020b0110a00000c00e010301594190000d00e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508554487 1250 508553237 508553261
    0x10306050106020102190c0203030d06060215090d0210050604060302041409160617130503040816050d02030307030813150e0c090c031603021902160b070f0b0711010f 73
    0x1140c1e03030b100420381c01d030710070f02e9100c0d04685040c00c090320a0303d000b03c2041503002c1c0041c044a0504d0070b002050720407201c2c150070420241e130288101c3c604441000c0e00281d4440801030140502c1d406d0716002950340d82103c6007001d0240d0b20f078000511151140e03827140d0f0003503070020802d02c00740d8000f0041c4030b0304103415075130848123020b00b0900400c0c1c0e5000c201100c08076070071a660058416060444c010004002912403076030001c0d000038840c0812410000340c40038062074805041c0b888584400c008901140754031040c0a105da91100714056900842510401c80c0c241c240086076a5628221070116400004010407172103221090300030b840354940c09400900c0e544011078000d001c00408000c88000200d0b15280014410800500303081c0c0c845003004c0440b40141409420401e0b541c580b030180107025600c2c00010381c481c000404642d0a00049030000340680703540c80e0b14007a410340312072191010b07121010f0510003c3d1808201140d109541085126040c4002001501c0c1006100c40207004919548 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508555737 1250 508554487 508554491
    0xc0c1502070c0902070506010302011b0203010e07080d1e05090118031b0506070b0414010e070e040201020610080c0d020f04181403090d060903020f0706210504080714030f0f03010306 80
    0x45143c0300d0070f1013101c0302c00e03802000030101a031039940119402d4030703206000032401c0d4100300e0441c01a1024000da16030481910064079a4034240301005103407103113940c1c0030070410294030103030148200f69200820880960380f61840c1e0720316445005948030054490124042c2400c420000180b07e1820300541481001c0300081c1202c43d5207004000150051481c058544808040441e00240c4100b00500c4541405000400e8502c0242e00090900702c02d540140300001034001000115039040c09020381c404440d2a0075100c040c00c140940d61f07201001ca0080d80141e0404114606550f1110107030300044e80000c0c014840404103000241d0041002401114454010a400d2440600200668030410000340c1889159103460325070001030003503040c0540c1580034a000ca00103071082440848042c100701d4079001c040701000403680b132141800501d260303080c900c0d000510001505407421203400700d4004550042c00d00400606030f04520900b140c01341e105c5000201d59812002040103107048900490741 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508556987 1250 508555737 508555739
    0x3050d0206010906141e150f030619060c0b040606030819020c0102010501060f03051506040e04120f05070305030411031f0e030702060405060f0d0c08040b1506030a0c0c1502070c 78
    0x45c001010391100710141d80410521510001103001106184030900c3c010654212581d00d13174065500ca0b40a0180010407800000270000e02d42419044240d40c4031842c5d440026113460403000801e819444800200314131030030740c00f0400380407490300708030301542d00705070900d54500d5142c9408000c202c90200b401c0260294511038901e541c010b00c183d43c102c42154543c1d1212050b840400c50041000610040c09000c69101008147e100c8001410140410002d00041403c1500340b20391104c0014045408102000712001f0380ca40e84401a00c2c8065494244981c580e10340381b40c00526415024916a00341c4100314002d00751400c0341d60040300300c000c09682002452141c814003500e900c980032002e508008200b0080040f0b040000041036610740564540b4101b03031101c4014420303181b00c2d4401d003000541e030400f032209010740c051400b6006007200362104458034503c004103880d4000200002171880d51031a030521010302842c03540d85202d41c4030b80d01019050710901075400a411516083d9010025010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508558237 1250 508556987 508556999
    0x10080606030d0f0c0303020d020d140a020c0705090414162310110a060c120e03180108060d080d090516060504051909021303290a0b010903050d0206010906 68
    0x9602c500c081d15503582c100c2c4010104006940001518404500305a0301304004c4150001c5413011f001c0080084c0008680c1c01d10b2011128100030014000c0c1442a00c10003c074004d10600207400d03002c441d01501c840c0c4496665007025102e044807020f19421900428000381000840481314030259024604000d403c02200c0802c50740c81d070341030761034245c1060300c0182040d00179000300805100410b400084881c1425a65920b200b642c41c004520340c04a0010f03402c502540c042402078460000c03a00b0002c0d4280101c11480400f06074a40c845141882070580100b100354850300124031480b40c11241e481d9454074a4001c02c0000c101502058501e0f0041d40820741900e5032070040c0b441250700640d24507003030504242c10400310410134420a0030303030030000f5000030700d801650014003481d6120b130440d40d458502c3c5080aa03901d05101120700c110a0003028100320040305890000e81000c8030f03442c001a0000010010703548203a00b0742020300684180302a054200c2d6002984038160b0b42441010300c084c0359215 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508559487 1250 508558237 508558243
    0x903040503070e27010207200f04091509030e0f01080601050706111204150b091003060e0a170417071a0c01060b1617040305070510020a0203061008060603 68
    0x101800c1d5260b04825020420350a0b070700c6400e500304045080f001c40844d202044001130348083c001403100c503500440e8940038040a032100b03118031000000720154220441d00029030342c000d0040c1151040c3e648406400a001050040e0405402002c1080144800c242406080140240201e42c46500c4c014540a15940b1802d10316004540c103850f081e00303002182d5681009060120810510f115040c008903100f860044a29070040d40a580e5513540c0e481980285020354070b48420490065043c542030080804040010808503500203000044000040c1d2036507080003c4150f014055144043d54507000c0800d000080c07085400340d8001090040ca4a81100d485801c184104002c40d1000c1c18940381c910304c9000280ba254120030000540203440b27070090f00d06a000b0806800020101561000070400d05c0e01000f5601608103404600f814515030f6025610040c0d80501400380111859000030f01d4000c000501c0c0c00d90307000382a51164681f100000e072041440c1e00c90000700d03104100129070203003008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508560737 1250 508559487 508559489
    0x4030215070c05060a0e1512071d0d060b0a090209030601080a0512091c060f0b0303040302033c0c0114030402010e090c0403020301050c130f0e070f03060306150806090304 75
    0x740c1071142c040d01c1c040800086800c101c42d90700601030070340f1085d81c841d42c134500d0a4101c008803448041d01d4552130304a00080440c000c1030b00c0305120541d40040c0b240101444005a0724508452900001805282c004d010f41074031440950420354201011464010035006446100b805800711141aa61072104941e29440d0341c501402d240c1181c48642c0524040300000c0c41468800b5001c0112400e48408500160240c0c10094071065940d0403009001d400310b0240011034282203000714141401c540001c3d0710b0f51100d0100282d40d007103c03100314500e06503209050503410707030142902d800d00556100f20f075140c0503903c4080d0300080e03006102034180c0c24002e0949000d6601070791245450103c100512a00000c0074081340041c9405000c000010390382401500c0c4030700b00030b41c01ca81c2c0301e88041f0100c010440b110307040310b900405104014084038090301c0c840c5038000c54030311f42039114a14404098008080d140c2010746083c0c1030449103031038500824140c40403680701d079048400c9a0b54003004140c03a8022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508561987 1250 508560737 508560743
    0x2070b130503300717030f0603072c1008030415120903050921010f0f0e0604080f0313060c02012c030a080a0e0d0c0b13030503010509090708030c030403021507 70
    0x544120503c0b00c9800c0d409048880c2c801c02c61103a0a80d403000240c02950400c48078a260f21038a0010082d45007014020a0000c0c1440c41031220300b2030703091042d4144146907401d10120002c50f6400110010780724124600104542d000ba40d0b5581d0300c44040040c2036954441e00d0012800c0c0b02e9901006607110f220350a001501503550760304151a00080003010805080501303c80a8011072000d021b100031300c5020300110920b0b80018807000400090802d070342c105030030003031550810401c02000c14042012202c18000b4504225a2030341ca078050112034804440380a400f95107040c960306a41070301503012541d160520b24a03405a540a600001c00d81d80025401041c690410300c908848640101c079050b030418815040800c1900d0000c5650345804500910880062904911403040c041d1003e805504510400c81c01c14202c80c25032005401e0b0320040c40307618080c0740c0e00000034244010a00080001e01602000d59541d0009494442d9480d0003034081648035813050303040e801c8410002c400301c0c4e40203070f4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508563237 1250 508561987 508562053
    0x60403020d0201140a0513090c0e1306030503070303060e0609060321220302011707050307080c1c051b071101051e04090911030c010e1002070b130503 66
    0x2055909219042040490403410300210307629000241d0038000280c1490071480e66859110300003080c0c44040400c440d44505e05841c40d141000340502d80c41a51617414102c02d03680f41440c045441c45400051940b03a0014241c0d000100e40c80082503890b070030107002c0f611100c02c00d900f43e4680354100000341d001903d0711031703169001070b0031150401605002000301c951441c41580c140706540310100c00e0740f2100d040c00804580040070030b00456070422460b006010140d02507070342c00d21713101801410610010b00b000080c01800310004038220422800c84814000401a442c01e26040040b180090300f41902c2c00a80e00d115012040c1420110f5000c1d41c8030182c100810071102e000c5000107554a502800141d414a0f602034910201481002c00030401060480710020701034107142004c0000c2035048011034869084401c000c041c51780e10006044a00e1401ca034017002601542500742d1509032181e00800040002181d1035590f16510032110003162404d40c1925240d01caa010b5005001c41d0f90303080209040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508564487 1250 508563237 508563239
    0xf050d0e0405100e090705040513060501060503131b150305010801051e01170106050612040204110c06061003020c150603071508071412010305060615091003150509250801050604 78
    0x61014138440e0007006480c25580015101c40100e01030b51070454a14600b100c002c92524204045031107400e004140500d4070034214282062100351300c0349202c0026009002000000d00b8031018859004010450902d600c0880d582007400500640001d120341c0b4030a51034100010340c801c2140c201808000c03240081130f10941c0c200402e80890130120000c6006541d41c440011a01d81caa2800501031807000d0b03071443c40d6074645841003105071000036001b058208414840802c3e903880001e01c198011500b21001c031080620920114001d0040d203c0c1144148681102003031942d504c0340380300d40604070a030300303480c941c0e9103801c180210030544204040003d0500c400140710389110b01d804129002a00103480d1411007070801603c1c040f00c080c0c2003600c180c3c00500070b110700c0345007944100800c462124021420220141c00144084a9424150052644810f0854020200d0440f020054a40103043c42c94600b800c0792050031142004072a030b003000c2c400412540201d8021460741c3d0403568002d200034941 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508565737 1250 508564487 508564499
    0x40b070204020c070b0a090806070c121b0b0a020a1704020a12030509150901110f0d0c0f02100801030b310203011b1e09080304090b0d0f050d0e040510 66
    0x2035000781c07044103c0303018015022031014190b000504911b80d0903602c01a640e814480031a0070100c010b042101404408030302070000492440d40c01448040d00d04040c903419243d00e00c80000c0d200c1c000001003a00001004103d1801070a9018145c51041641c0f81300c40ea0614205c011041c1d41c05075806075006803140400c10038107140e14420700006109203001400e00590001244052415401c0210f4245010800c00c0481d41d0240980f500c00305c14000511841c100e0f013489585031780307900c02d4150412800340d80e050b0134810070500d05030380581c4c00b4024580d104e00804008001500030701048444002c0c281c00f044e0310305408400003503040c0700c04a0f4400c4031000b80d02c80a0128a1003102241c041d520b41000402c0702c010300940d144210b2298a03001c2ca00b043c000c541c00d0fa8040418000e00506c5003501c414403000100000760f8040c0d82d03854500141000c445400076103020380c1000b0050110282804e0700d010448041400c414180e19030300c501010303144c460100702c00c0c1c80c1d048440c00215100c0b01e00400071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508566987 1250 508565737 508565741
    0x7150504030f0f030b061b190804030b0c0715110c0f0d090b03010e0126060406060303080106110615030c030d020a030305010512031204030905210f1207030c1707030e0f06040b070204 80
    0x305030410040b00e0540b030708c2c1200b040048011400c2540d4040001c9401c00503c440e030303507030158001e1030085241e140440710750354191066068842c820311160780304010f000c080755a03004c50f9484803c603021103031070100b819522956941e2448125000071122000051090502e0003a02e050303a100354024442a800c040e8401c810042801240d03040f10f0703070300002c001000c1041c031145008901915010616038103504018100032f0741a0700202c1001034601c0e007108000c00125049070081c580c520740400c41100c1e000020301c3c00000c0d01d2100e5040c0995031000c18095000250304000c188207803420302803a0390310030401ca00300b001080358844c0e41d0400c0040000e0b60f00c1000340c29a01a21030b04007801101d44450104401d00807111418004807800210601702c0300041140c2007551200c1c000900d80c040c004c06004080d4000c900b001170900050380c8084040010041d21203407004180f482d65503c0d0909400d00610030408401820b024420071809a0884c2c1004400c440946401400440c6001078503030034400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508568237 1250 508566987 508567027
    0xd0e1c0c140301111e070f1202070510020a0f08090909030c0c0d02010c06051e15010219050c01080403030905060c07061803050301050609060d06121b0e0c07150504030f0f030b06 78
    0x1c00005e0070091100012003032118480d030310380a000a8000c00103d080044d1612055811041c4103001482c1c403e020380f40c0c0015009000b0b1f0303000e030722059484040d15003081e8034052034583c9903005410308200712079074400001500200035000c1c03c40e81220b0f06501403200303404141da8080c1c0040d900154103004540a0b412003a000f0360300d11100c0884501060000105480603201510081c01190744004c4a40c0d04000b903d82124880c40740908152981c0e45280d9100110040603050010317042c000742c00d01d402030303020064480c3c00c0000d0341c05038076000601d9003644d48458000c441e40742c9004150142c18817890305540e500d56040e01c4092440c0d080400700b0081e904050104c42e4042010080c901505807a0701903c0c004050689450080311b4140c542003407449c8619500080c021500d00003040602c0c0900d50301034101c0500e050503540c45242c3d0420210f240100700e00600541e00b844207010815601c00da8080c2c90401e0340d41c0303140d000d01510303004a00b608c19114480798001010700203801c3e141c03c00000d0311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508569487 1250 508568237 508568287
    0x50d17040b06010c1205130608091905120307020106061106100905090c0d05010207031413030816061401060f091410052b0c03050105030d0e1c0c14030111 68
    0x70001c2150307981040046821103800001000400c3c0800e0b4580b01a01c42e20240074a8203010027a494040102640c400204510102008017800c0c1d84090210902c95486040715000b040341c0d6900d008440a40a801a84038000c00550460000540d108001c600326004e01c52190001d0b455034944220f0801800780030301800202e00420006c542c890b80d4580c0503c42c142e115074005038030790105050161148100b41d071540da010008000c1407051015410781602500e0340440c00c203031208000344001c0c158040f5a0340040071145031090074641c84200f403040030304a41403540c40c4110300000c00811a41011a4070600035010040c10700400f080c0380c02c1942503480300c61440e20a081070402c1244500849a210310a0207107006140884882c56090281012194490509024551400010a0707580c03844214500402640c001440e040345d9170844034406c11101542400c41594107400c00010007001849100c00710040b010030ba11142c24180958070075441c01b030300000c0c2800034204160f050382003509130714 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508570737 1250 508569487 508569497
    0x1021005090316051b0d0209040f0305070c08060411040e0c0f0607230106080c1008091507051c0504170310050604060c0210032009010201020702030316050d17040b0601 74
    0xd01484119039140d40c0d9001d07000905d0b82c4803a0403810929a02c000052034050701e0b100e9036440c05610b8444900d600030f5405084031550110b00e0408550394082c1040040c0a00c0040c2c0c03001404100000300c01303020318000d00d8824407007a001410003080b46d20044251480d0341218460440514200e000440c0b548005416203281560643c1c7e410118800350242d0b80c0c66103010850311040910034401e0b00081e00002c40102818001c28000640c080018036140041007007910002e100070100f4019000306166404202c9007a0421400107002d0340c01460000e250400c0c3c0b130b034002020390028043d041c040d98114081102541d103005c2c01c00e000d68802481ca00c016600044002110b807a0040204000c01a541e661080c103142c9104002280c04c4042200d402c26042500344441c400001e8400d41c0100303058901140c1d1213110000503806030161f9400a541400085850000d62600400b290b9800b40716a013520030342c284441d402e980700400c018803c09800d09120008002651007204250460014180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508571987 1250 508570737 508570747
    0x10b06030901060e010602010c173327010302060304020102150910050109021e0d0e060408030603060708010b0313110303070302160503030405030307060f2406020714010210050903 79
    0x114a269109032140ca01d281e540705420400000c0700c204140c0500824402400b00404400d001003010b0109400740000c40001c0c000310b010b01d00c18592040100361011560901c03e100d00381b144040ca90380055842c040c98024122106101c101d0400310002820080c0942c1d442e4210380a201840c0c100400403415807080c80300c0b031540c00700914a000d1085402100a00010004481d82c105035141a849070440c180140900118061000c0d01d030b000c41c400004100352a500700e0000203001d841481c88422580c000c400c10301061007440c0000394440c0009408030385c2d00e41c1319510100c41240c801d01c500d0304c5103281400440d000d1032001c00000c00d12802103034400011124400060b0860780a603004401507404001d14100040b45030b11100018682100034606080c50030340442d48034425000003d00b40c0f50b0310403203682900c2c0030b03601412003003030360081d031034181ca40b003401400200c4000d0003008050b1141d0100040d906400024108000a040c0d001d0841c50002c000520b0140001821301c2c0b80501007404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508573237 1250 508571987 508571989
    0xa0902060d05010303020d050a021e07090212010807140d150f020c0604060516121113080d020c0402040609050405040213020a05070201030506060301060c1e0c0605030105190e0604020c010b 83
    0xc007811208002403400200c0e0f5140d4a806442e0004043c94803040c03290038800103801c150046080c400c1000640f141c03800b41d0981082103030802d4080c1e0400ca82c2d5901c0491403a9142c3c0c0c2a90307106060381c03080021207902d15242d03078070800e006024000b0306510580040e02c03480083c0301c24011142494050001140074098005500c0903600103144080040d8005004c1000b07200403030160640003003814132a18000080700100502036041e004144c100142c490141c5200906c03624105c0340300903082c0b00d01064032615850301946070044401e40d000140f0400c1410019844c00344212000c4609684941041a14110500c40501402001a81e010343c44a042d892000241d000514610310a566601c1e901c4034030348005000c0340d2016002c079000d18020700051001a80180d003a0200641007181d60099204c3c1d00b00442c3d0750713020100d00800c6600c2c5580b0001d2115000405507050760000c40d038600500c4100541100070700c10790b01c103400c0882b01070340c003040071410107038010f006900c100400491042c443c44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508574487 1250 508573237 508573249
    0xf0f1b0c030a030c20030d09030e0306070c0309080c011b06090204060315110426160b03041e02010c12030b120d030509030f09100504050909010e0705270a0902 70
    0x601c2c1e1801181c1c58080402c403495001076140b035400c18100c0004480c8010036080750b603034010b901650601c507503200d50440030b06000340100031140400408403000b81c41c0c1f0b40d0004005a9032090214041040c0076000f05268401140c0038110303420682d01e07600d40d014184022034460402400c00d48103031750354081010141e00d07603000d1400514010024541e0f220f4a01d0266001c0340c03e19400c0395103c0e14284400d01c0129241150b50156296800d1800c601c000109c4900741000c0c0b5503006602010800900040e8942150f0055032003240100e112540c284806d1200944a08107184001c0c00030f14024100b0303000030f00404100d8170f410064580040c0c0300c894400800d0100c030100078000e646034445c4800e8848158540a140d900ca0001000385003002420145e6081d10700a110516204452000240801d80e1086007910001d040003442c444142c24182c00c03841c001c08100701855201e0164120121b03c90070107004c0c4031441e04120781441c140d130902c3d14190000040142a54070000c0e114015400560740d42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508575737 1250 508574487 508574497
    0xf0a031b120e0112141503070b070b060109050a03050309221109030d020c0a0b18100c02031b0109031b26010609050103081204050a02030d170f0f1b0c03 67
    0xa40315101c040900800240001058504d01610b050030302092400080700381032625013102e051800c00c40c11840000009003841e034503070013100200c0300100d44201884120220513004020a8940c81d80240d15441445071402c4540005030040d402084040181d080843c4401480c24807840280700400c092400942601c1c0070140301c00c6240804034501000785018017541000d45018002842030000250105000c4c0b03200384a1803c040a0205807842e03001100e5004580e0508002c000c41e244c80e20200000e00641942e110a80c00781c411030950000d20100c2219030350001e10143c40f00310000f4038542d92034403488005003030078040d000d00500000d000d401580561448003106030031300392541003000c0c0d0a4216206580110f44a074181401040480c444c1d104944404c034158410304030555440c20080d1820015a000940522813107003106200c540c403148100c41d000740180515150744031004511920801520700001e603080800200b0b140811200c403062403c120180124203141000a0960450f041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508576987 1250 508575737 508575773
    0x60503060c0a0e04142a040602071205030403410615030f160608070f1409180a020c07060e1f0c1b05011b15020f090d140607020f0a031b 60
    0x802081401d103401c2441e02c072680c111901c101641801d250180082d036801082c450942f500301d40c400c02400303003c070130b00484014680004807550460650006400d0030400b022042ca407507103000a031005001500d440c404401e41d043c5005284079120903148041c0d4081140e00c0c10303030611400e0201e007060a000c1c402c81207040341040c058074455160400261583e02d005011400300300c81d041c0229800c80d041000d11007964400600c4907211a41e0401080c030200000400c90428281c1500b00010709034141c0042c00406c000ba026110669070fa004107440320b0140f0041141c0c0180407510032186110240c00c007051300d40b01850105008662a01d82c0280031040d451850102c01d00d094040c011941c203c003000042c0030084445207020055901c4d4051170010846000d5400303500082d003000c4400d842c005a84800b0b0004081c2645182503141010136821074032010101401031500080340300c0c0c008941640e00b030030f030000542108110f41e0390840f00b81100341c0310460050070025080c0b0120341840c100094001c4d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508578237 1250 508576987 508577011
    0x150108010504050c01020f0604390503160b030c07030201060509090c030606010e03100507030f0e1b090603070b070602211e010b12100806040f06060503060c0a0e0414 73
    0x1c0c40d04001d4101152140c4c083d05550140c1d10307152100344001001540700c1d80144000800703030303000d080c081421034003400782803076001107034080c80741702078a40d110001201d00460485d00c0f0018080840c905044140c0308111a100081c0006400d0180190041100521a100014403244c0f51030004802c620140c0703540d9880d50201143c0700f85400c0400c41c2c5900001d007403c01d0010f03c0400e00000c1c0c0d548206c1c174420105030351660046000903001e5000201004940e0304103000619266003ca035544554114040042403103584681c0281081c191060041d00042e000d42644e504110001c40c45900040d02103d0480c0e0802c40d402c42030251804082c0040142264280d01c0c0c101461358448100f050310f00d11509207580f100411079400795004840002c0f28126001c4282d03079402c006590303c1c2415601180c3c0074050721342040100000f031100c0c0000d07079108010400c0f00c0c42c4c03280d0505540308022180d2030303005542048019100c60081c2105100391308028170204621211450b550910301013520700b005808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508579487 1250 508578237 508578241
    0x60a05150f120307420921030906050c030103030f1803060f1a010f080a1805030d0b10020a02060405010c140d05090418020d03050307090308042702120106050c1501080105 75
    0x3201c09036580102c5e0784d4960561103c0c4010b82c10355150010078021244680d0355a03403120104403001d1000e80011694030682c1e10384508036178001d00903003aa03110072100d003443c08001860424464040d00c2c140da4159039980e5641134000c00990710319246050f22010601d00c9030340000003400030f0091030328544003404086404120320390410407580711161390070b041c480031098008072140d0000c1045c0d03014906650226000e81451014a41991305440141c814000055404031703840e041e4100800390710040d54003034090045181c0880c0c0718031040c08004e40c0403408000c01c0006621407215018094002c010501004248803240c602c1c28029040d0700340400c0000c5445406403401d407080a0000000b0f840a042000351036000440c141007142c001414080040046850741c2d11403010813000c2c40c0d101c8001c558a40c0c03200760020743c41c01000020300c2c0f500b8038000303100c610400d14000e69601c00805d254003012642004001c1d5400d400c01800100c551154401c600303180303242c4010a5000742141400000c1d24 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508580737 1250 508579487 508579523
    0x30906030c0309020f0f061e0406180807060e011413030b0606070b01030f1106130f05041b14190801031a060109060507080921060a05150f120307 64
    0x16500c22001641803502c3c1402480140e2140c0200c4459114101c58001d40c1644460000d4900c0c0200184042c20151140c02014003260440090042e107110740c80d105c0074610041004030701c0900d5401102c03001c0c2c002420411a160140302c202c1010001410096400c0c81c4104250300c140e0444100c2a001e945807080070014407141c502110342002c0c09a400924122564030754040480c0103100040546204003204803d0240100c4034002003140208070f45d903100c0c00d03091044201c0c503a60185140e0640031500000f200e207440e02c698000024494100f10030141c1075007045e04c01c00b12000110a1902007040115140356009035003048003001501c99101c6541181000f02d902c0510f484c0c1c20301d000064a040c03080b02e80c1c02200d040300300c0301c4918003a0b988075064a8100060b00801c0c2010b80c02c040021541ca0208124071a03d4003400940c1c01103548a60303503903180300152481540c514403440b00d110030380340381c0d401c0403004070039a00320203007400012840080205103140e10080b030a0b40c0f210b00c180104500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508581987 1250 508580737 508580741
    0x3061814010609230a050901080609150402010905100905060a030f0e0d050405150c190b070815010c0204090b0c03190b030d1d03011407090e1005270403090603 70
    0x14003080c3c5084101603007015060f40600032064041090305a4160305041c89a484880c00d001420015003011401e50f500d21040e695444240c62075041c4c4d011b95880348011144d040006841507405070b54440c41140781006000640c205456134034100044031030003080548410b0000e0a8550fa5a03030000380ca00883c1110500b260410a080450340e0060b4070296102548602998190399084807404009114841031100c1c13446075400060311801440390703880307400740b000380c1280000d402907543d07002a0303441c8a400c8078158411a1030240100960748030340b40552283d4200185a03102500004980120391a041c2c88040e080b28001c2c121040002042026244101c1d00341c5030021350a003c1c4012128800060307140c20500d150f08042048212800d92400500002500b01c014003900030084e201d1003080402c078880007150200c0100c0c038503000018a20140c0502148501c01610403910101c1c2003104004a4841e5050f401c2501514020a0f400000a507014940258481e440700e2000030320f07205002e42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508583237 1250 508581987 508581989
    0xe0109050306010e0a0509030d1119171503030702120a02031c091206020904090b07030b100c0b0a060f08030c060703110306190b0a030203011e15030902010306181401 73
    0x10080d00a507004001d02071a032144d0769040040c0c0603010600e0396403104050715501071031000c00e80c1641059181442860800002d05910441e001c60112500700c0c2c03034081e10701440700c0f081842d42c3c010600001c2c6101340300c1c420a645425005050303900e0300340300b6000903d04808000d407507944c0c9d800c010001c2d011440c00f04071920480007100d1500440099114010f88060902e00c00c043c0540d00d010315410800002e541100d500e001d000f04104038024140c10041c03884202240c041000c203107801c1d0404018580351000800c01e0f451941c81090003102903890001c414800b40c86511056112640400d02c54a03041e030300d20103000e104d00155203802101c1c60b5185017000142424081c503182000380c1c03e1200c0580100c9500460a80307001000310240e40041000d00c0081c0c1c4171480c0e43c1070100381030000a40c5900203504950b40c0340c05851540f01400d0703091404507414400e0340010501200c8001c0d0a6000fa0004100c0ca40141000210781d07075141004841180902200c5110581e280c40e11080d20810341c140e28 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508584487 1250 508583237 508583239
    0x3061707080f0d020604030c210f0305090c03100b0a05030607270f140a0e0106030b01140f09090a02070203060a09020102010e0105040c06120b1c030207060221090d0203010c0e010905 80
    0xf07803107010b9580194880d5400303007003c1c3c200401003e4001c2400a0100143d8007850740c661202d001100141d402440034001d000c280d8000303810301c0c0214400041c002080d41103c030006000e031808510540486009101004001d40c215000c01000141a41c041c440103100d0710303e940720088140c810780e030b500c0541944c0a00a2882c046440000c8c020300030000040070a41d0f1022004490006040c00091400d0320164040091864030b1400800d005905401107c030715002030301c8000c22030400ca00d404103280078000100341c0c048401d00009029103000146103400c1100c03080010300e032802d00d0b00402d040c10811074034500e071640c840104e081156424400c4483c0e400c2144020440307400c1a0342e03980d41c00001d600c81c0004100c194060b5901ca141d2950080312000d400500b1841c04100c01c00d05414004162082500980284400042d00c0350020441c54041c120002c1b224120110000380800c030740d013091410580041c08070400b20b005071130034810f403028070300700d82c40c0c050250541000042007000141c100b9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508585737 1250 508584487 508584493
    0x40b1614040e0118020301031a06120a0c1d0903120402010909020c0d0e030f250504090c06090e010608071d270a06140d05190b01090c0c050a1203061707080f 69
    0x40010424140754204070008012640070545c50f800c0014a08010081c0000303000c0c0a40280401000290217070700083b201080c1403d240d202c1030483c90622540d007210300b0038068008000c004600030795410b881d82e1052050600903130141e116813030401280c01850003004507030b002d00004414590010040303002a0000c030b00a022204001000300e46441d101888900350051011402282e07010103603070704014110243c400c01804c0410308050501224501c203c40200340f6020b000b040340304180006034161817050311030350700c40d40300c2c4178044902e50108500c1d0070120fa0941d0108e00c4c565100040a42090a000740da044520382c1d0030581c40600c03101801030103c65103040b90800010000d10b50688260340d00302c4403180603c1107401c2407420155001b42c5a4940034507888200c0030030880041d25810b0301c2c04240100010b20202c0e00507140f1403440c40c00a0615444030001304001900c03460743c1c492440103031402107103003a51140c1d0030b08503035400780816a072a000004d05112003034041014001e0b4107154002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508586987 1250 508585737 508585739
    0xd0801140a081f0e0a05010f0f05010608070c061506080402012c042703020d110a1e1b080309030c03071d0a090803070e1008040b1614040e0118020301 66
    0x120b5a49040401904801c40242e00c03035110448410340c05001100b186001740d4440b100c041c98507a00074607900309080300715481c01140e524164411310906040e11107031703280e1014a86904034192803c011741d40084648580361280404d2000d0818080c400911241d160b8000604086c0b0024144800150308602da90010107004688032910744181d8014403c02d48000030180d17400e21182c005078000586540120107003403140802c16500094000c0641d03029555120381e400c090b2000342d00e034080c00c400a0480c00300000c14030419000c44100b17440152045c420581d4018420204c030441031071603400316a154001046100c03d03800e050240c01c49508084026000d0b1b14117000302c0000d040400441706005070440b10025110300c95070fa002804254001780f241e03440c2e00d40900010403400c00500c0e0030f4003c042020303025a01e80d008580d080d025560000c54002a640c4040e296100001d2040c5070000f08603035256400000301700000104082c246401c581310480d0705045900c80b80804014035505181e02c1080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508588237 1250 508586987 508586999
    0x9050f0f0714070302030706051f0b0703080604111b030306010306060314070c08070f1b090506090f0a18060504060509030a09050d06022505010b0d151d0d0801140a 72
    0x2201118090350b0110039480d980c203414100d1131402402c03001848030b4600414004078108005a10b145510350100002c445601d604015495000f540303030040c00302d08100041021850a81c000c031036841d400009250a0107480c18166895041110103400e05420000510085513890300460010307000c1410140550600410a03010070b4034000d00740d40c100f04401c01004100b0101c4402c0f80c0b07045070401204030100c4c04e6030420100d44051034000d400e50308086080081c6c02a514020030b4800c01c03000f04000d503140d541010141c400c074402000320a006a85000e403402d062850412a18040c3c05588009481d1400b8a0034008444025040d0f007104d0744144119968107500c200c0388000e48a043c0d500c15005041c2d0714180c0086d000d000c41d010b60b1000c081d1400b0800c4808202c24030101d80c000c00c000c2c00038065078001e1202c4402011170107000c00090000d194003051050308100000c40d50081d80321404003e950080307041c9050032030484002516540100002c0b20800138811032440d003152050600c0e89005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508589487 1250 508588237 508588247
    0x1080603300c07060504081527031b01020c15010e1f09090f05070f1206051e0403020d03150506120a0b040c02070602060a051b03040f060609050f0f07 66
    0x14904040d00e19000d030354a40d881c08025101ca1107500c00441e2069034485402814980080c09511540c0c81a441010404c4040e007004034007844020198040c10020058a001050303109501c01491f8071081010100e41c045007141000b000d084c0900060b1902e49c0c0304801c81c10010b8000c1c0f030300390085030440180440070340c1c080095002204407001d10f0b4614442804400d04107001c2d44400034040c80c100700e1109021411072941c1c00c6920903001e50351096180c07094008088624020801040c41840301c010001d80c899200c5e640003083c1400090b680142c84c0c450000c1c03444201c40480c0140c1080115052154140c0140404180e42c002c144c0821030030080400d0f6140180d6107103040c09203100020440c1042c1584c010300010030040c10030300440d041d1100181d41d509440c400c050062281c03800203034009500c0d202e200e0050400500d43c910081e00c071100744945c1e0308040c0003034504031510141d0b030340000c2c29845150000d00e5a044040f440d40b410a29a50701a0002840c0c40c50b0090f2140400c50103941c81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508590737 1250 508589487 508589533
    0x3070506030703020714121c0e0a0b04120206150402070f080f220e040f0f020a06050301170604080a030213090e1b0105030708040201111f0b1005040303020d05030a0e060a06030201080603 82
    0x11209840500c060440382006002c80300349c207032454007500c1d01030010b12195003212880707940140c072030000017070701da18040780c3d500d03000c80f100034066580e005950301500e00303900240302c2c403801901c51400440040c0c60300915507124026464001030000b0b9882c41c680c6501c4840c0a03000001d460b035260341da140500300b12082100410003440d101a04040c0410000c1b400c1201c16100c2d00600188400d6454403001303010340d8428081c2000c01ca803141c848040000c000640c0901c00c59001c80e0440c140388510342c094001c4e4202c05400e43e00d0f1110080080b170307501d41d00d01c15134580e4002c0f90014125074210300b90142c000d507030015144d4100801001008101d98100c10000d41155081c44c04d201d40703190312201941406014800b04403a107040c10f004068548550b04140425001200c0c003e22041c8511403e541903c194070000f80517801001c82194428050f801565110746851404a0480301c0309880c142000c400301d03a03034030f0051f0780c8240500c103550f8013441c0c5690204042e8001d10a201310450311800080711 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508591987 1250 508590737 508590757
    0x1504030503151302070f030305091207021908032b0204030308040213020903030c06090d020a05100e0102132723061206091c050f0301060c020307050603070302071412 73
    0x1e0050720082d889820901910071080d190854907405d051510446401446405400090801011a806890115100210904921039103242c99010790030711505420301414140c004501010000754002d060000700b40c00903502110310039944100c41007070111690140007414540c41032000f40006500718000039081501107401030f4442c0c4000c181c420181c41001442500340c0004203000802c0a000901940104030700e400780c460600340b08004076596203514901070841d03407102500000c080700c50307440300310b0380c1f1811000035160060080303000e0b000e08299480300010380741800c280340c981080c40b6500d0092101c545404d0117000303c18450f840081d0b15007240500a8007000f030202e095a42c2e0201032043c5811450250380c0c0d14900b11a02580316085641500750b68603120b0300c0b8030340c068840c0b070031544901e10034828a0305607400d182084521044a88040382c051203401d401207102d545590280d4031940d2542c0e009030703490405180c0109920300500f00185958044140c031400c0180510960ba40840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508593237 1250 508591987 508592011
    0x100911090a061b05190203070503010b091305010e0d05040e06041506051c0603080301051f050337020903070b1206040b18131a10060f1701171504030503 67
    0x507000035021482c01800d50f0003005441090405c1d0b1000801050700351405000302c007a0340380d1a07a14401d05098604d0203000d01c5c0c1c00180b44000401407400750000c2c0001c98003850000940f481c0321400702d807420008881503c00715201007130420044401c5c10007150302c42010f0341d09000f0070700c5107034400351b42c0c0525001c3d03034042c46030200710120301c00307201d144058400c01090401c0c800ad41d500e044c000120713071003801464016019480c54444019004100c2400e1114580d141072841e0388441c1c4640f000460440300d460004000b01d07505403001c1201c41c040d000031112030700042c0d840e90240e08040c60464142d001d850310384400d124041002c842e01d05d84d103522030010350300403881400c90000611018000070050700302150f4401480311004112420f42c0100d0700c03d8500125002c81178150415002c4102c808800c7c0d164041818011148680740c408918400ea09140d10b82c0c440301040055000c038240c1140f48038050301e403188a0a6842003000c13000d4180c048501548030700f00307a1130050080c40018004071241b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508594487 1250 508593237 508593257
    0xb0a09060b1f080c09090a241a030414030c0d09060f08180109020a090c020c04020304210e2106070f021b190306050f0c160201030e01060e100911090a06 67
    0x107038000c0211900c1040040c0680381c1ba02c0c0c2100d1030002080c200c90105002000c141080811403107a8182c44180c031109109164003c16002d4103e2659000801c2200c220500e815625900c0710200043c054600d003401c007400a0060050004010420700ea000c41c2c10041010300c080c803446d8224020942081030303559003980f034645e0108224050319203404025001240c80100240c158410343c4207814004035030b4299038850890804000036404140c038080c0484204400d880411101940c000b031103001c170741c144007800e0390036080020041010500d55018000d540c90714800f02d40820b0084590140a600740007921700501040255141d0b130680410606c0c800781412015240c0e120351034030841c800500ca511090715224500703003003e00340c1501d0f001e01c0c03105030a0100e114044204183e41c9604214110325a01070402c1d00114007906211400600c255641c0c0000310b102d20301c5a0f8694814000009003031000c2e460000c800d411510400c00c40030881006100c18082603444500c50400c4074402d25041c0680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508595737 1250 508594487 508594501
    0x3010b060f1305030706020607110a030e0405070903080f18040e19050c1f0806030a02010e01030f09140102370809010f1505100311071403070b0a09060b1f08 69
    0x80442c030f410242c1c0c90f100d40400080c13100e0b03001480768414034140c0d032608100c020640c886a500c007608200240414650000c9400c1da007042c0c1c0c8507660001c0306240c5848406e80c3c0303448583c0e00d0380c045518641e014400143d944001d500360114258040c0040d0b030104a01c1c0c4400801c1368031089032441c07800b40104004240801c3c00410045142442001064400c0801900080302e00c1d2801c0380001e88041040000001d02c6482c0104861441c290103031116555095240300440003001510f21000901c1d0382d82d0f208002086040c2800180030b1409000180e981d00801c5060300c0e003203005081d0249000f2400440b24403030317940480100d01422a07050105007522120080c071b0251080e0f100e0628411303e0021180d084031420004101241d505480d40e5084802006044041e54000b1082d2001c801081001c04009245485105040319403082904c1c200a0b940d41c1301d0b6209502a68009101078840c020304051000c507200e000300128040394040500613500808038001c1000050180038000f800c0f00250300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508596987 1250 508595737 508595767
    0x150405041a0a06050411132601150f0509011206020307030b1e1903030206060d05030f030a051902040608041101090815040c0e0705070f031205150f03010b060f 70
    0x1d824a071030100d5501c1e00c1c000100c0d8000b045681310f20381c85541030072240090404000300b22001031002902a580440c00c00003450309a0b4810803583d81a00104141c034a040c110030b2081d0348030b2014281c07068602c42d203082c110b10b9903c510354101c2ca10074040180108070603440c403040c0d5180d1541c0068056241d40d41e80409500a01c00306c0c26494004240d02850189102c11440c81c41e203c0004a442d51007800c3d0301070000c003030030256000c024056404040414008e01d000c0c40c0380c0030420b1041c0308503807400e552401e09d164640c00540784842034035241c6052007842c81c0b4290a0341c50401640c1d80442c280303840d0881c002c0403400d01074009811802921590031440e4846c03410b12014191140071070300075100f48002e00304002e00443c1c083d9480141c1d40b0000c1001494110b08074014200d036a5942e007000c1c01d0f41c440c2e845810820b4411014012181d6001800003000e01555100d40f80f4804a29202425a0b06100c00302c0e55000c84144039904d0f0040e15140d9695440644403007014002d24941c03550215000c0c142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508598237 1250 508596987 508597013
    0xd080603072c0f1006030b0d03271811160b07140406020f0105090d0c03050d02070b0106030501061107051c050f0a050109120801060909020705150c0a031415040504 72
    0x200242482e42000100752079000c0d014090b010032440903042e036603225411401c40d0a10142240d2003c00e009500010a2045400e001c03002c4552408050668482200246006480d400088e601e150800b100a08843c1881086e0380c4503098201d80c1d00c3c0000140403503201982002d801010002c8d40f07400b040c0d685104100b03684550583d010486c0d07407261621006940d41703031104104c070000e60a04002800d0f44401044d00c044501d943d40325648000207964007036850750002d2502c1100c05500b84025008100000ca8840c02000d10f42c50000c2c1175410000c0c020208ac01c0602e242c5c00650240c10100300684824091011408681d030301c03068007403038618200d420003960303841d0750116100700c420580c1408019884400380601c101580c0a03403040c05601a99291001d12400d00442c2c10400d04101d8182280c008182e9030f44610280e404d290035021001107002002e440440b038039040807624402e40f81e014403444001a079104040401031a04d44402400741000007885401580c83c1c00204e0100254000150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508599487 1250 508598237 508598309
    0xf12010e150f0730090605010810110406080705130e0402130c1d060c0a230f030f16060c0c0b010902090303090d05010b220f020708030403030e070510020a050d08060307 74
    0x2c0200919401c145001d00b5080c022200217002b040c2d5a40c0e5078250034410008680e000c0085941050f15054050340c004000910481c1032020412000940107002010354018140340004200b150900303006012446204070403050704289856055261242c1006460401e00380900e03009900c00c403140003045582c042c5200000c1076118580180081002c01c840c6400700442c1c1c81070060180c43c51125061341d6140c032544446658008004800424600320028550309015862199400c1400d5446000b12000b101c2203034002407190b0340c403004224590a800f4010a00000250704007406180003d8503807240b107006a03c032303401d0a001c243c20000c00b90406024941f004040003607010560021500080115000191091402c005040f44001520035512200d0700702c0c6460f03041d07695580c2e0580c01040d0910a294040c030581c03000045d950740f0752000402060482c1d0207403114041034945246440160112042886040010440c441e04c0c009004011100d07448a01d501d003100002040c40001c4440c5000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508600737 1250 508599487 508599491
    0x90c082e03050c03102d151d060604050f061c050124180905060307030203060a0f06151b14061509070c0803060f12010e150f0730 57
    0x818420003007a481810b0500380c0c01d84054035660402e0702c04441410b549a044042c101806c014070020803d00842402696500020042c02c0d00701e1440c21054294885144003410440b600424118050010303004003042c0d804508113424400014160b80d440f0b0b41c00e0b802140d010505000400e4103014154103090604005c1000c1e58581044031110552050251580340840d03807080d4515201d10b034040e00121281c8040c410f62800c0406100145c1001b0704082c0c0c0c548602d0201001580d0148150f034001c100b0b15000182c807803184c10342c0b030095807902d51056070000300010030606000c2e006107030405003550358011486408000d01e03121031809001503e03011948034800c1000018103020040321640c000c1150702c4032940d92429000c40d501140200d00905081c401d001142180c14140955008044000d020650300b8103014140390031182080346030701d2a0303800349441c0f8821400e400e0201e134204800407401c1c40c0d685040d0201170403d440c10b01048402c520b20000481084040c6020568a49068031007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508601987 1250 508600737 508600739
    0xf0c02010b040b132307270e010b0a031401060207140904050703060c0c0b270105060307090b0a053a03020a080a0c0f061508030901090b0a020705060c16090c082e 71
    0x1005000140060f1850041c030b039800070010150340b403c3c019070202c1d4000001c1c0304198ac02e2030b1100781c0030703040b8407032040506499051111007540308a404034060201ca9004040381c0389400c80090002024280542c080d031110410705c03020400102e80c075030950750002c1e0b000c1001c1c2e00c440c0080328050702d0604042c3c48911450140003c2c0d1203119081e01038030203014041020346c142041880d007210340a0740d6041e49948410800c100b031200c2a0080c01008200030a000300d000e50783e0010800e00100305084030f400c00031241c0a41c0c46807540d0403c400050480074112401d00440d41c0c1d010790b0314402c2d0034029012a8012414482c1527114a08404c4e0701680002c402c00300d200103282000250002800c50040340741881400b094240000050b10340321081690340c91400da251007401c4880d1f90103202c5070070450041000100c0c103034035414000c2412840c08001040650300c82c40000c0300c110469001464034070b08080c0924440d03940b040d0800d4004503c91494502108a608044159501d040c407885c18070400c858 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508603237 1250 508601987 508602001
    0x2d0f0f1602030a050a0b0a140402090c041d100b030106080c0c0a140a03030f0506010507030309110402070f030e06120123030f010204080c12060f10090f0c02010b040b1323 75
    0x1407617007441403042500c0303a4a0b03160b190130078007901c0308018400903280c820360004002d841c0c6200d9803500121450a60340c03400380c4030004d00076042c0c1c49003040c00944c0070354010700180f0021001c0c0e0a006220000c6c032107085504003440208100d001600e0180f81d2040410003990300b01d0300f400210f24240e8040f52030303005d82c0002450141c880711003901c00c0d0040707490100c007451603003001d008141c07041005030340310303440c1440d0340d5404c1d0020401001c1c165011068421008090f0719544010865180164050b030f00e005a141760041c2581401d0b03042c0c41c0160014041c0c0a061001d4900036415240c1c503111003011411100c10b01400c00c403502c0030203545440b034030403d1440d03404103500401c1030310700742c2007980ca5540004052081520441807421072613481175000445100c04240c4440d04060381e01e0b80b50000c2651100c2032130603a00348c4240316044a680c0c560b442c1c01660248140b020340740c0c0655090101e0515440040c0380c620202551705001500e0305c21001200c3d0568802100100e0488160b890a0405003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508604487 1250 508603237 508603243
    0x10b0d02090316090509060906162606030d09082a0d0605090f03090d0210020f03030c041409040213020a030603060509032a0309010e13022d0f0f1602030a05 69
    0x4030404c40120b16002c041562444081107143c40f60b2401c1008003040c8d242c0e040c0001e601c040b00040901006454001e0340c3c04041c00719004003a8582c0408134a64508009082600340401d4100321000d024503041d08000240003c40d207030010100d900b00e2081500200e103004c480709000103491a9000d906c00c18820100440d03640709a000351090000c0340d10b01c0300320200043c3e480c400d4810150f40b100c01c2c3d805a400600d4030510b0083c6103c4984159440b0800108255245070406d85040e00b1241c4041002d015642e0001d0420480382c00490350302c10a800d00340c02040035456040210904941c0004d44061014000d4111000455000000700b0032460691130441e200c1e080a80c0c04402c2400700348501008040c404003005c0f0010200c000303540342120300c02c01580d01505042c20150010110f00120400a0721840581002c448034094281c0100e5107881042d014600f00d82000b142e500140001e4541401d03004c140c44844241c051010341d42c0c40034071082e08200d041e0303100095142c4114107085042107004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508605737 1250 508604487 508604489
    0x71413050a0501080c0f06120a021207030b090f010605160c050a030c030b060904020112020310030210030f0b030303090a1b09150806060105030f06010c0201110706090501022103010b0d02090316 85
    0x2c142c6401717084020410404900040d50380780c1c4400300f88126106070701803410098006180312030043c50140034148000b40f1510848003c00070035601c900c011b00c61b09281a9042c0d0040d00180ca510310f03981040c901a009008201003030300744503254116170040204107a000d00c040c04c002814049101d03600c0c503202066400501007150303880c00308000300b04103007400807030180181ea050310348041040c90340070030030002d400081c040311180171807510000150312804140c8030407500e1540d0210303d801652014006803020b41c0a041e003c0d0b40304004100c0b2945022411170f2101c0d44c1701203c083d0a000b183c2c5070324448403250704801e240130303c0c02011441e0301000102c0403040302c141500341c5203076507102401034034a400215502c4600d2046000003809540c03280440c00e400e207105052108803544503d24052070a03003540c10400c080b801f4010280310540e010810b20351680600e20380c0041407400b15034410810300061192522002c0c0204400340300901c903406540e623152000d4116000c0d075413103840c005002d02103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508606987 1250 508605737 508605749
    0x20a060501140315100303050d060e01140f0d0503030a18080301061e1103041203020a0c0b09030c0f030d0807090b030c0d050106020a050628140411030a0302071413050a0501 76
    0x904108000e00300482c0900d600c05c1c0404d4007903a500502c1d50b141038402d940302194130040c0d00c0c0c0d24100803079090740004138075000c2c0c0b15162140000100f140140500d004101d000c1e58895040f11180c1c0c40003800c000216a8001c610348000703c0d1400d4032f84010086202c00c0440204004000300022030396503400542003202c08456031210308003180007a02174038051512540c141807500100800c2c080c5000c184e0141c040d2602c82c0c4116020f008007038503010740c198116040801d000341c001800000c0e500e0b08000304240080219040780000702d42d8070009951300982001c510602c007810000074441c0b80502f640e0030080c00002c3c0540c1d620301d4030900c4040c1d0b990004400001aa10b00b030000324100344005102100b19501000401068650b010355850038200c5161aa0078881c0100ad0f02d81845140c1c05605c211100b800301c0074a40342002c2c07400902c40c501c159a01c5009601015904000c20350002c1d455040b108651140c00c0188400300200b980e120900300c100d12654204400d02c60040c80f42e038031585c105c1d05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508608237 1250 508606987 508606993
    0x9061204020f0a0e04170d1a0a1a040504090201090e0708160e0102210d140f1e0106050309031323100914120a081c02030c0301120201020a0605011403 66
    0x5200c204028500038030340180242000132000090008481c0400400c005562500603801c224002000e2003e0380d5901803544884e89100b10352000d10705101e880c01001e01030018602c0d040c0304603140c01c2001c030301440c0324007449580c4440f8284190390041461002801c50651141e000346003250010740003c0090391000e0648444150001882c0c2c450f54a01d20040f2059010303000021941c403050724901000d06050340c0041c400c122911032040b40d482010b80100c101908442240390030407401c0203480d0000c002700351056210301c0e02d0454526101105065401c00d060540d26034450002c018510300560f1441d00c0540d00241020884030114800c02d101c04600400c00e04568400c081031220141281b4541d4020078443c8106006000d100c000340210404007410024002c040c481c4401e1502c03400c0002620394120000d02181c00f0340308050791206400315502c0a501e10305084503141540d00c8144241800402d01c2498281103a01c00c0c44000021600320a003802156101c203101005180540c0e040351080c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508609487 1250 508608237 508608259
    0x60518160e0d060509120c07030302060903041a0a02012405031027022701050a15050906030618010e01170f0c2101020f2128020906120402 61
    0x81c45001c96001441020700000080390030b40e507440015100103000c54401e4003494000c0324403401c0100c06040e1608118005011083c81c1d820041c1c03c04e0320203002c1814a40040005000b001a00064082108a01d401c180c3d545c0003601b000700c2c010400c0e000e0300300024000d20086c1c4c1c000501100b440c0c0960340d0803025034000d00c00340c42e50001102d0b118142d003510080354039900036105401501011135580090b09078106941c201c4224003c0d5554242d03550083d0680c98014000b03410301c041448050447c1c024148101d40c1c400c035010784a400b52006041c802e0b039000000400c07a880d20b06101480c0040c0d084002c4031561580c8240100703820074051030304030343d00c0082d500000d0680002c80b5100d201d0f00b440909400030160741030100e0314041010449a1000708211404080801d1008206c4255200300040e211441d0b0220400d4041d1402c44c0c002008038400c05010f0032904040c001c0003410240a4489800c0c5074044d10100a4040c0b81d8a10b83d20140208106401003140c4403034502c104e108660340100b007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508610737 1250 508609487 508609531
    0x6010306140609071d010e0324010b0a17130f0302100b060403080409090611031311010c12230a0804140a050a0b0712091506060201050610030b04060518 67
    0x40c0c00f04a030081c000844091500255030010020154610010b16005c040d500f05600400d1409640341b51041d0002003100d40e50307085030004841c2d80c0c00f50002210745403814600300c0d00200701e00319910f0303500210300e58000032034200e003050006000c10035401f100304c004130407050030065122900101c010001d0b506000c0d145600f45484421581529480640c407418035040060b141c008020340c00080b51940d5481d42029884642903020314440d00080800303804403400c514100881c22101e002d2903041c00704540302c18001a5590380420002d55191405800c0701c07445102c0300c01c0308032101c20100750f0001d00007485c18600d0390100e0480d201d24051400d4028040d10114204d649400014010300b0a8010315100e02c0041c0b260b608164002da901c1c6000c25854620f03082c40e40c00c544002c3c0d0101c41408074480c40d200200c0d6240901001032242e40020812031038600d0102c0c0c0c50100c284481020107540700000d03d11075440750f000d00b0140002504901c801126000400c0c000d50054461440a01d100e8181140d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508611987 1250 508610737 508610749
    0x907050904060212092806020d1b11060f010311150a030e160b070803070e130204030201020c01030b010f0c050109120f18030c0e0c0c0a06021c060f1e08060103061406 73
    0x303100c6d00ea031645d4108400d0400004255032400e8030884069800b001301c0c0d070b406c98280c01800001c00f40f003241280c2c0e91000c500060081401c581c0040202d40181d03040098800c0b10380b6a0301d04590308807100203140e000c10800103a03042c161f40914842c000b00428800c4103241d040e409090000488e408071200d400708003a42e008103644a1085540c1c0d420104510070004442c64081d40d0806128105580b6864440002400d164100324080e012507038080340070029582c1c1048140c501c08000c1c01c0800003561800d0008085450f00d80b90381007808040d5070450200802513120040d050f070407a0340311030451090000101000d40043c0f01c0400640710910b10500107454058620480350704c0001d041f5400e1424541c58600388009040078070348041400102040c590038083e0b0640a40b04da4030041c0d64010a151756011f4075035180c0c100301283e140c0001408440451848081552000d9400000c030f4000c442202d2a007100e00e0b0440c28090144e80000030402000b50051074440f000d01180d80016a0383c4014015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508613237 1250 508611987 508612003
    0x90c080402030a06020f070501140a2405010f0c060e070e011d010504150b070f26030103110f0d030f021e0a02100e10080a050606030402060a030203090705090406021209 74
    0x5410381114000310001001c542c02000803115981c1550704220123a00d03600d00b1a01d0a81c152a40d188024040049100c000d202d030030f65581c0829400b002500400800c0b81c0c41c801140100c0b418460001c105460301801444054041c2da48079505011058101614988540b05442503101d07005a480c00418560151081003084446200c03118100d6840c0030204806450791101844d00c00c100141d020a40740c5c011401040d21b40e001d40a148441d0405140c002c0741080030031700207030003800d040030380c0b0303220003001c0d0b00b100c2c11aa002000240c1203a01e500001d0201c2c1c104940055000391a0650041015040348120600801680036181c00e60400c2a4640c20090741084c01c0d00103810640f00000140342c9400c0b104900c40d01854405941290140429407132602c040012000c00c81c80010400c0c80d02e018000c0c1c90b808170090f58594110304045e070200ea29805070550302d409041c5c003c8000342d0405010414000203003001421048a820203040c10b4009500c44109285500705a8002440b59000040c07107034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508614487 1250 508613237 508613239
    0x204030b070c030f18030218090705040e0c0f0f030331050120010f061e0f030503031b0c03040e040510150b0a02010f0e0c130c080408030a0e100204090c080402 70
    0x1001c0f07540403d82145c5841e5510f401c10681d00c0390010200268699071044001f800340004070384080d0505051080c07902c03040f6880180f1503170401d01c10120813940030501d0070701484161855246000ea4100165070204000061a0188008600321165080101c000214045e401024610050310131000180041150043d180841c0d52001c9400c0b41341620070303c10b002c3c0100100000343c0380c404080001c040e240c003039002880c1108074000c0110181c55805070f01c4003e000400c88182c2d9149940c1da0240c82c0e0000411100406030000e4515084040b5201145c08041214064a40e00c54598030314040c035240a40302901c41d4840c18000b9400148203206000c0010303041104009454948070015000e0781c170943d0900115500c0300042c0c00686007034055100d4149059000d4820b00a5000a000c0d0704100c0d61010301c002c0307042680100c034460f00302484d150007a4112105664075078840c0310110203002c03204e0042140b48114580400d40d41e40c07580c00f920a0703828000060011064102c8101d0700080203403806 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508615737 1250 508614487 508614497
    0x5090114090d0f03480b0a0c020a08030109050f1303091802041d0703140c182706030c01020c010813050109080403061a0607110906010201150305010204030b070c03 72
    0x4900401e1001801000d0799200b450840300c442c01e8044414011041520840b1038200c240301d0325444180080180c0717000c0c1c1d8a010314281c50041e1741d10380445200025000d28422903554580040c100c0c0309009072004941c0000400e03949507558843e01d4010702003183c1d00b80c00e560311000410104200b44800920280e015500c60b8821801d20f4515070424200e541c80c1c0661607420000003c81d00c00d503403034280c0c0c20341c5050995a800d10300860003a0954810072101c800550707400d41081109030200d8284d9482e01220b55820314850f124001082030501040343c40d40d42088080c49040c5e40911f00241c03170340b15840503429140d40d51041001643d440620020180c00318415038002000001e514035001c1205018000104680c0c2454a5000c02d40e84960025203925880b40c0c89040c103a030041c88420b180d140142c5041d8a00409901e800c00100c85620b8070310300c42e150380408112301e68800d41003a840c2c0e00c45509500c0865659181050003035015200032564103600380f00243c2d282d4005c603282c081c4030b80c16440e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508616987 1250 508615737 508615759
    0x30f0b01051207030e010f061802030402100c020301140f0405010b01180e0405100915050f060f061b07060f020705030607080f0702150708071707140a020c040c0509011409 75
    0x260b01c141c0080035441003540e50040b0b0312056100340120020f401520380002245400d04c1100402440840c0c04003d81034010418400182c441041c1c4529088052414a014040910009025220130061004000707800030602c400007001c02d100b607014a200d10300811a43d001c1c80010345860a5201140302e800d010f40c50304018204030170f200c85074810f200d271081e502c13503104040311402110010807003524511a00303180344803d420a0300c0b4458014145662180e001e28001e800920703401c214000c001c0c00340300046240036200e001c1f07a0301c0419410020041e100003a454800045c000040b058100006104000300000c440c207020840c5401603900daa1040480c2c0d8450030194101400581100110b1088501900903c038103100d8042c014503080e51804d020f41000107004108c0703446440c40e2215034041d43c0500400742d420a143d40307500607007840f10300c1e159100c446040e41030140c042d20150300241462441c00a15912100408843c8400d880325151724280f0000259103005201c809034021041540c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508618237 1250 508616987 508617007
    0x11109010f020304030b13021201110d02070219031410060803031f08030429031302011d1206091c02070306020702060412050703290a1104050901080c01030f0b0105 72
    0xc24581c1ea50200d0040b02d14191750b81da66001d02032404c440c210001503424101b1003c41c9030001c08a000141070700300038015142c85030200081d80c0300702810300103c00d40c0005c240701151201e0800350101c00c510f2011040081c2c1c2e90900707800320b4403008810300050040041182c5000f0303040c07003441d05945a08000b03500b1950307200c1001244c6191008840c01d81081510005042081040148003510304142000702c22084182490f490450010422018030018800c022150100c01140c0d0071403502480d0005e00036400c81030600003044240030190300003966068054000c076002841c0350091007140c040300e03010071b40011090929034000742c41c200140c004c03000410219480785c0141005c2c0340010017482c43c0c2035403005035060390000c002044130240c21841d0100280017100e1191405244500a00c20884030507501401045200405500d0701030364581840b40301c0ca0001003503501614000c1c0c403150b0256140c00019940d049035940c5240000c0c03d28441081c07811480c00340e8242000180c4405060040f614 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508619487 1250 508618237 508618247
    0xd030f051f03080f071e0c050105040605092806273f1a010f21080d020c0f010501080a0b01090b121c0315030b0103260d14060301110901 60
    0x8595940c40d590306200d01401b140d40141d09a05c040914429140400c15604e84440002d220754081818041d040c80200402a006000c80b40400e8007219103801a089051648030024418000710b003101080d180040341090300b0101154501c0ca802202070f010600801c02020000841c0c06040c000003805540c1051030304170404400f0b10341525259414003042007581c0c1541048114800341c0d000407100041706a054803c001d00c90250550098007003d690900300c3c025080c3c0c0d0100045060202c1d250405010702c0310280503600c091361082d80940d585d01505860035130b14580f14034580c0c1c1651920000003000500041c441e240c3c20fa120301c09106aa1070440c0140c004c00c4007054083c0c010007007060100c0317420700902c40124050100d12000454440c4030301d0042c1240d11a01e4120320071203c1c07a03400d00105121204050450307034802d6031a03004004180c4001c0503141c401100030165075001c00c0440740b00005030400d02e640101d524428620b591014105803d0740c9080c800f12040d0b00007040b60030300380d52041c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508620737 1250 508619487 508619497
    0x1106190507030915081806070e1003060906090605180f0703230c04180203060303041502240103060e030315011808030d0605031e030307030510080d030f051f0308 71
    0x904041d6031056940760040801390340341d040d240c0040d50f6001085481021100e0071252821404002c216034544160007825a80307644c04224030035400e20030800c2074103101c1e070854006002c01e508207004441d0b650020f40098a064000e0314400c2d00840c8101c2050030b41c81e813206224070ba454800c03084507151080180c0080080d1307142802c8506844540d02c40b40804845450f005449003215959034900d4401c248003c504085140f032442c2d4010000c0c4103540d9030000a60741514031035829501c10a075459420fa140c504590b030302d5004000e4180106141009426403141241d0013024180a490750300001c090312032000f101c51441f55450352000d200301e54800d03110b031000b144141a11a00d05626010078921319084420006e4015803600e0080c03001c2d040a010310391201e8007a1104042ca03145c400b01d40e549034040207203914101691030000580818044607203100038404c80c0d054509015407518001e020304101c440c3c4c50600ca051002040d1074920080c60044030040008159a11505554482d80c5982c4a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508621987 1250 508620737 508620743
    0x70e0405040c0b0307200d050702121507051801080106050d0f0227100509030304090b0103110a05030901110c0c060304020409080c06090d020607080609040303271106190507 76
    0x2a0304000301d1480c042400030b6016a0054888600c02c01b03196101c114204810140a6010380101d00b58100d0300390094162074059904403100d5600e0007400e04100e1a080446003e1900000c8502c10700c8159034000703009220700411084041e0000e44410300660329800b00384104000904100548000d1224542c08521403403002000945030460305a007102002c03081d50003013888090010344102607407415a10000c50844c0c40c0c1451803d00078001c00003a10303401244542e006041e01c81d480c0742c5c0540c1c0300e54030054980082c1c3d2052030700d40c200301c10001c055030000c56001c0b0707081d840e200d90302e03061160301002d440f100d8104034000c00300c040ea2070b0140170498001a00c206d03049a03d9060100003e00404040c0001c00d1080c1d006050602d8940c4140e4505028030f00c0020035500120b080c008031305c1d401002903600080c19100c611981c0c03a246421001055143e5608040d200c0c03108000a41001d00004034030042d01951302c10b1464001c05040100c1c500c110070080002ca030305800001d45c001d002d10068500d13030340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508623237 1250 508621987 508622003
    0x60509090a09140718060801050408030601081302060a053606092d1c02010e0d080d050405061b130e07051c020304060e1c080c1308070303030b09070e040504 69
    0x850303011918074114aa0b04102040170907040049694403c3e4801c0700d0050107000000c3c003041c00d05450704015440f001c1c00707042c100000a0700068070941154920006c445c1d0261400d6a6920b00340001080c0d90410707071242198a58120341c10200158020b501140002d5250858a0f111034150410420758005054103411440d410b5900c0048205100d489042d03800282203017102c403604004014444c03c450100c031044035441209440581da015564020008040e85d40800000c48c034189440030b80501140c03d03a845044c0b0301040704000780882d0441c0500340a0030314110001c55441d001c81e01d4060001d125901c0e04000c0303c1044110302c80711440e6042032040c01c00c03510305420480c0c0c3d031005181c94040d0604c0342c1d07000400c0c0003c0010341d21170f00304c02058103409403a01003919041c07004424140c00b101d00400c00d134440464845404070003103690358a07011541c0c001069844c0103e03900d1790010303c819000710345408080105820000c401030301c6003a0550317a2001d0400c03000304000c0140030240c0181c40750342d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508624487 1250 508623237 508623263
    0xc080a1505040204090605100503040308011e05100e0f0f0102150705041703040302150405031903180603090b09011e09030e1509040e0f030f07060b030a1209060509090a09 75
    0x2e00d40b4030080c4050300e170551010401c40d0401007403003c1080d101f814542040006c20070440480d6000301e8640c1510140d1100010306614030311034150400154021541c0801100350802816400c0902164003003410348484070000b0010b010081d090f00003041c20341c0035811203030805950002c0d1080c460340c1f04806041c2a42002d45880c0416084110f02c074000245a10000701801986000f10580b5070587c540410185882d041c0408030b612850b40e050300304075500d0f40300c400f41d0400d405108101803011801011100d03181d43c611000f07000d00340500041d10301d030102502181c108a81030060071924041885850540c0030001e0b0114000d000e901d409400308480060748140b41d41c0c8101e25201030340040840a03403195803c2c000c1104031b441450003142c0a9210000444001b5004000d80e0001a2005009502c0700c229061040140000300103107079240c02100f202900f04207503901c00c0c203041c1d0420f9445503034032901d4000541d002e10600780900d500004907000146181d45640150941c2c0d8840e07041c0200d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508625737 1250 508624487 508624489
    0xf0106063905031b010515040e0c300c0303071e06050708010806060a080c130603020d05060103200a030209250905100309120c051c080f09010c080a1505 67
    0xa07988040382290960000511154400c0006032400800016070000300007a081c8100c000780351100c0e01104038000c903150701880300144030600070801d0440b0b014000381c000030402d040040a85043d00301805c00b4003807200d0ba00507012400504800c00c024094001c51800000362504000240540c0050310124886030214001802c0b0b4004d842c01507070146c680021315410b0041842c1001d00041c4801c0c0210030034201005000f4002030030b804244410b60f501c2607240e121416500c0a8842500040e401c01c108240b03100030481e0018040d81240d002c4c8210310321000b102e500e401103099200103002c0e4030106042c810b001502d01810482e030045000c191804203444100c8000c1c8039400d940c4004030201e104240100200c0c1050300804103403c0191808102204055a403000348402d00c3c0000702c200500d07082d07000100f0808000c000390754012803030b009940c4032084000a0901c082292282640411500400c0c00c81405003d05548003010f502c9484407036540e40140d100800c1d501510320600d4503080340019503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508626987 1250 508625737 508625837
    0x11815060f0b1218010c021507110607030b030a020a03050f0106050108160e27010f05101202030c090a0810112d09150301080601080d0819110a050306030f010606 71
    0x1001054010b2300280c0d091023100c40c540000284401c041c0110703640d103440159808522903a10800307500b030004921517070f200420303d042c101c40781c002c0d0081c07000c0e0070200a1103000580c88080c4038000000313001c0f160b110401100c5000040c2caa280402e11030040d0b500340c09020b003441142c0344502038100e85035010420045558900c100440b55034000742480117000300b0032880000f201401081d101403901d00c00d6040001c2446d65100207102c210703030303021010528900790881103c11507800100424207480d2244803d036111140049644181131070042250021601c1c50141e070003c60004004100c01c100b91410484051800080840300540400c01c2d04504e40c2c480c0040942c409104240a4496040402e00740ca001c83c1078014025682c44204100203071a4000521944042c000e4012806800d606a581c0c020780480b500d1650424000304800a1050740306010758481c10301241224810540c240d40d440c01c071040c0b80510400035510b606d020281d409044c280c581c042d02403c103085080340d82c0780e14070b002e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508628237 1250 508626987 508627001
    0x6031005160905010809031204140303070513243903081302090c0f1e0910030504020307050105091206010e2703030711011815060f0b121801 62
    0x2480e5582903410691a82c04206140a0074080c24180700900700221042d40d00e0151001701800780d02d030302c40003504101e955080a010b14264030212a00d90070060800f0b00381d07400016800000c4014000c00044030303900c00381390101800804899008104240e48119107011041d20141080020f5400f1041c6c15042d88080c0c403410b4880c0c0034528401d00e21807070020500c400c0900808022151150801c01580e00d0702d001c190091081d0005985e100b5011540c5101801001041e4201e60f03e82e89180c0c14802d0780000408e40c13041c1c21504055000001001070302120780070381c1d010f034040c1d21403203080c025540038600810358050001d0100740c0360512031503120b01c0c080c0241c20201b69613841c0d9040c40050f00c10903401d42500419200d200c4142406100041e0341c0e0b00000341000c0c02c01104c18041d1204007400c3d4041d00d017045100031481c0c1c0c05c40841c1000c043c012004000305425030300d0581c00160b8190221111001c4e1496091228540507a40c00804400701000e81034050044c048801404d08200c24070800ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508629487 1250 508628237 508628251
    0x90e0f040c1823070e01050c1b19080604031e0f050c0c0a0909170a0507060209121b100e0a03080705010e070e0402040b0a03023a060e06070c021806031005 68
    0x2c1128589240c00808450320007071780c0d60500006000d0031800384004516015a0002e1464480300220313041c00141e54840104851902024000380c089016a804100380380301d2170103a100e021005d001003811040c954001514480041c8208110300b1145209070010151800c074401103d1780001220000f44508503607130b02c0110f00564942182e4100320b5401d01600c14407500600890505c9074885000d0100d00c14080c00a00e42d84d800104501c1d2039507121107018502000c2c8084840c907102c0128000c2c0c0301d0078040c0d4800c0c0300d0700c020324100110921030900c144411a010f080f86030400d2869846c0c0c3c1860704050780841d039070354a076008a034240701c0400c8500d00030b281800e501503050070940184001c95560075100341c02002c40c000107001503140c04e41d2100e800200020362001b03210f03244c4c415202214072401196081002e0f02e1421062050682200701900203c00503a0f10310303225000280c9041000b0540207411105030703100c600176081c150001c20b03409540035007a603800810240c020022204121405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508630737 1250 508629487 508629551
    0x40b190f02130501090513230a1d030306011403040825030e040b210708010513030206061212030703020904022709040c0521010507090e0f040c18 64
    0x25103099665410b80001c0200303082031041907042a021541000c52414020402a281d825000d9290f92411000c0f0040c6400020030800303041400410000d0606200802980441d07642d40c00d00c03100010045a000d83e10585600c00c007900466a41002500b000700700b5210780b1001e0012609000f52030302810140e800d900d007450002c01ca50314006e030020028000040c025071405203464102c0d20b5494000e00c2e24109125220f07607081c03013284e00c1c61604d01150820850b40d4242018008075510070240d200c1064865020b9404686d1100203201105030b2200614200782d1189100c6d900c00000200110341140c0546005440d01fa41c1d00d001c601640c0c4020202428030b810403080c0c0d0820412205807190020b07040710000e02c10700b400c4c0c40720030420119014007032107030080d00580e008202903090401c40c28034000c4000c2c0701c00c0c90280c0000d064210144607641100075400005029403090952041c400c560064980e101a41841c1a140b040414914803085050b40c034591804101e10290300454004004041c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508631987 1250 508630737 508630747
    0x605010210020a0923030a0516120506041e05060708010501120e1c020a050a210c030215041e06050a060f030c1205070302060412050c09040803040b190f02 68
    0x9280484506802030744602c10b10034615510303030154084044810780003440a43e007a2894a441e80c242c105480c507a818815a060b1104000d004500c150110303480e18000d0105568801880740f03a03030003076540207015401c0a800140090040521840019600d00000104d01036560701c00d4500720050300d4140c0032811a000400c60b960348101d4102c013054801e40148980100c9081659507055a0b99641007130305111403140707244503c2040103513a1290010222000e074940b030b0400390400358022040c0c882204030617007402c480900402008044552543c010403110901400a006e6828040c00c100d91041c1440c0303140000c0c0c00391000308643c00b405410009414105102010211142a0b0203d0110b4182d0303003080005c00da9103160a400c07960b82c001c54002c91056481c205040500fa03801c025409400450085808004101c0c0c84e40424460812a005d00808a0812a0003602114005e041e82d10800026000450340c0507881d070800003920200c01c080411503110301c141c608008505600075804a2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508633093 1106 508631987 508631989
    0x40b0601021002040f080c09010b030c2805181f05030405031213060b0d08040311030a060e010e07120209010b0a18030311012a0f0e060301090605 64
    0x4001c41d0b03203d0301c1784109920390540c0c2c05881c801d84103400040c0920b041c080f035032505030360207001c9807400d51341c5024400009078441c00b144140c0c061366000949000410030540086c00c03005032610b03034561118040304102844456030452150402500c101948c15050044d07403101085842c283e035880d542c90810602e144622107400400141060030091900c02501350706107003d03c144000d010b0ba18900040240341d802200c000341083c00104020000a00c1011060b44100f8006d41a283c400b4071940303620003201c88032a5000402e03519101c04e00b080d4142801100b002c3c01c10000c10384480e80c0c1e9078021038403034101409110310700030b0300250310340c001d501a43d00604601c404031030401c100764880c54010201003020081524540c2010308111400d4200b0181401c3d004081503880c0803d04000c0041ba40c0030f035804c90480600c10b5030244801349440c0c210007117018001c2c0403000300c0c509103400 = true := by decide +kernel

theorem cover : BRFrame.Cov 508453237 508633093 := by
  have h0 := BRFrame.cov_init 508453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508453237 ≤ n) (h2 : n < 508633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
