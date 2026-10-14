-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:31.424517+00:00
-- url     : https://prove2.me/submissions/90295c95-6ee3-4503-85e3-988cb45898ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 434532374 ≤ n < 434712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 434533624 1250 434532374 434532379
    0xa0c0e060a08031c0e0f03070f031b030903110109030204021c1107020904290906010602060106050903150402130c0503040b0708012403110a05031618051507121206060905 75
    0x240b50b1a0f501d1065170040b455054002080741c2c101100918400d00b10b07006008103e5807400c1c80d15038001810760007007480a0902240c034000c154007000c0d6070040c5c003030780d00c03484000d0506c0390768003085213140e0003117001c00700a68003c0d01c2955246044500c04000c1c1505000c40e1140c06d1408480d4100b007010281915509503003d07055010703e45858541c52000a0072108039010001904000100710210144013401450600c006008a5045c640003a04000050308554200070050042000b540d40c000f0300121100381d0003108003843c0d12140081204d8441c00c0044070750150500c5100c03032019601000035407145000d0127401c14075888001085074000800e124124032681d2038894500c0c21030760b00d0003071076003c0034034100010801c44038109032500303400905541b804a1000300400c0020032203203c580500c402140b4060807490100102d035845c42c2120302485014004141102c44002703c2c0c081150015170300000c49400c0500810b0b802009401d00c0b96080010b1818600300040c1c00b4041c22500c02910b000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 434534874 1250 434533624 434533657
    0x207081204031509050a0305041d100b0912010e0307170c0601060822030908060f040305030114062107110a1e050c1909140105060706020c0a0c0e060a0803 68
    0x4580b0f03034a107608400d400ea445640d5035103103000006003040003031200c5140310351911615203190140c008101c21a0311250f40d941c03a001010454415101881d030300c1540e101d000056164030340440400d80c1301c2111200a45a5840e0076445008064000094003d40d84541d61400040522482c000e2660251101c03070b070001d51050300140001b501a445583c0c2c04082c400940c0300e0030640d0b0b41c0c03200950f451010142d001c00c080c0001440711001c24000c01d41d100c1c2468408400d00d090503a4000c206202c1449940c030700700c0280082e4800c3c1d90300c013021501c0283e00740883c0b0307005101c1d03841e281265034015104403021403e030440c88954014045111200381e80c002c0e804003010050111103400c2144039810480f2140903010780450039030f035001081142e0b030841040048049003001382c00000c542c8807102c3c20361000b501340010080c80d90741d02d080b140c41d207500220143e25001c1e111045441c01070b4100b40184541041c85011581d04034900e070881c410501190507500c2c05681320b031000d860344550000814540d50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 434536124 1250 434534874 434534879
    0x207050303090108090a080301030c0e060609030c0f03030408060114040522081e03070309060c020a0c1a0c030c0a02040b040b0607060506061b01140601030501080d0f17160207081204 80
    0xc4c0b00e825840f403181c001307581034034015503103940315540243c10841e072103000d02d07409224000084072810341c00340003518090310701000707100060b42d6048400c4005200742808461100f140d1024425a40145458011200c56503100d4500d096602000e01039603000b14078090002c0d5000c83d5133040313580c8189442c0f88804003000243ca42a1455104030059840e010006640904002c60311000318403c4c0480e039000212072040c1d151400a40310350444040841d40704c01c42d4800403071503855074001118181d0b0808074043c2c0c0703055803100301c0c0d000701c1c2ea4190700380c08040f400e01c482c031001064000e0704a208940170050300002104000c11522050419a04804203000501c0001e4056100f160400c030020300d2141002c0034040c8071407240d610000210910b944841311203060041041129400400c00d01341848251b0422111550b50f6820148100412a00d914444400c900440607a50749502000a400c4117140180a9241181050003000014810880d00241c0240d000c5070b602402e90032080100e14092 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 434537374 1250 434536124 434536127
    0x512030708071b0c030303090209071e030b040905030c0a03020d02011b0f020106031e210f120b0301060312020f06010b090f1201020d0e060c03040b130320031902070503030901 77
    0x140208941416503c1011804020400e074019500040d882560042000d00c06441402440100a413014050155000c1e248131528500d02c0902003c084602d000102c042400000802900707501e0703070141c920300000030000c0c600718010038140303100c40c002d40071288605107604040f1b00b00d800e2903403400603113078420403d4592180b00ba49691004401072002041c1291a03440d10126440840d1b0600d0060115240007c104885442034400d0071001c54007a0b0008561000050020001407070400204039003c1071850700700300c00303902c8003d201401078003c0004544929040007001901c07881a8050302c41d010039080c02c6200051240e042c0d4202241035824280400709002440c07995050113a40034801914035040c061091010b45406503100c080403503072519050300e860521002500b860074103002002080041b80c080400190880c0b41164030501260341c5080440e055040f00d81508100345102c0070303c0100140c00006011960180740f034100c170101c0700382d00599603000c0b04e12550740c06800c180305400140d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 434538624 1250 434537374 434537387
    0xd020d05030403110a0506151314150d0501020708040914150609060d0e0c28050105180907080601020c03010902300304030302030a08010902030c1801021e0109051203070807 76
    0x1000303001180c5c03a49206694850600d03508079541e51001c949480c0000f800c1c9010308802d03110100501040207041c181007420801d07003030001c200700214404400420b4a43e101d01c0030700780055030000c0086480d0892860482483d034032070f125468010f41480190746003150b940302014000c6041c0d000d0f088004c0018070a006194000b00341c21a8805010b006041c414401801400c400d940e00303c000d8075144103494100540c128484003015840c0a001b090f014544101803842c400b170b00c3c07090900071388483e041101140012183c0e2001034000c00c062040c4900349821030f0807a4001c107026000d86050140d21001c1c10700325504004085d500c05509420100d0510441d030308506210a812000c0c0c020f00044103109166502580c81240164400140010103560040025000d82548070084d0320f542005032101c00c0c01d00170305a030452190340c0c05001d040d250703000304a101c0c2c0c11103030100942e41100c204001c0354001d100a010541d03d6024146840c001a00c103082180c0c8141045d40711203c031502c41c0d91046903007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434539874 1250 434538624 434538647
    0xa0b03190813080606210d0311040f0806040605060618151201030c0e01080102041211010c291021060905060f011401020a0519050a021c02030d020d05030403 69
    0x60300701001420051215060a107019151000c0203241034200704013400641d660707524400f442e50346100c0d03c0420780f02c3c010807120101c0701c0311718001c581c801d0946501d41a45c45140d0020f07419100e00c00000520600c0802c220703104600440f030810603176071144c00340501c038456a51013040d00422010164128030b000310b43c9480c0740481caa00c2c1810704042c03817401c2101840c281c00940d1280703480c2c0020006601000291409465032800a50406250130070522180c60f05180c003c100e0843c0c01080c103446d0344a41044042950040222079a4030659105800d40c02404100f00d0914282a80010440c2d0040d00d24401119000700005044907544450403902d8818070b241200c02d181c0710011200070070010017005014660f1414030412652501c0c0c2040a890461845181550402c01055012070404074111450320110450011120054030784503040148420000750b015003240042d8420340880c120105410788258211081c0700d000c1e8109036030b1200c1200012000400402c0083d0000e882103909005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434541124 1250 434539874 434539883
    0x2d06070c030209090703020918060f040501021c0e01060906232202270108060112020408030c10061d16050706091110050f03040b090a021206040201080a0b0319 70
    0x650945981c000f450701e480c1501c440307146a01485052003940741c83d0701c000c0c1d0484082422600c0030f54005c0c400e5a203400c0002c00003011840c0300d40004040c03042c207404440e21018003481c111201500d001c03549008021940192446610340800400c09128901c078210a48491406a403e40352203c245d04020014105129821002e00e450500d10325025016030b8085180c11840542c031213460600301c1d4a81003601d046c82401c007036003011803c030300d0741c00610300e40d000902071030859114860304001c40080d1090780d005020a00c000182d00710098400b0400c44803103418480207201d41940c404110221611060000c2031000000c00803806001e00d859a4151042041c00d22034109140350700c8540c1110003040c019078441851482000643c58010261003942100342822400d000d2480031400c410301005100900c9110344c0000705440c2d180030442c081400e580204214000c0e003000c1080b0b615140107590803804200001d000c560840540c1c0119100c418000d4000c02c1d100d40320007424050b01d0b0401d002541e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434542374 1250 434541124 434541143
    0x50601150507080a0e0f090c1606061502070807170d0302130b070f05060108010509151008060106050a031118010302090411041d060603060109230a03060b2d0607 71
    0x2000030f903c01d019081d01225070701c1c0d41030001460300510010b0241144c8952007803c000c820094544e01441c01e40d01103c418445d00740e0352409510f040402885943c0103c401032a442d05241c0c20180e0000d540025107400a040c0c07200749584240380c10b030316014a6a10b103015000000002822032180e400f400001c41d214890994440d501c02c0e80301c00130380c40f5280a44541d14030311040024880100121401843c01100170081450056071017907d808144c0048507000c07a2440104202140105c1d5000c007403c03c0e002501c80a5944d2500608551711007020100401d08050701c02210342c1c406800d840c114002004d401e4144c042003c01100213501c4002403a80c00346e0f448002000c1d155000c8043c1018001c4ca4444165405851490110000004008902c1180200308010180e40e100104504030340107140740040040840c280c3d014504400300c2981d402400b600000414402d00380c003d1180841c2c01d541070f9003000f44442da4100301d0783c0312050011007007407884400d2044e818032400030268280103c0307858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434543624 1250 434542374 434542387
    0x120b0d080c0a06061814040803280f090c081b060c031612020114040f1103070b0706060e150901031b05030709021908010806040f02011209030908070603090506011505 73
    0x3d204440c0b01d0340000071a080f01d0905100c100c00c9921400201481064003080d292030035544103038042c80001d03c10f8804607169220240d62036455910340d9040070380b401c41030000703207030268042004003414402500c199411480004242d40007041b0000d0318988000c0c11141d0407162814804290700c20140410039100400054589107004004144402d210b01c50b07506180015910090940d540b071034189401c205c1a406000000d140da00d00140d619902501c0c0d600c0036074a000000e811b05500382d10118103c00001108402c00880790300002c2941c135210303035000e92a01c50640303980968042c07020350741d00403480c41c1c0180b010540700d461241c501d07411181c1c00c600c0c440d220b101103810a103a070b511014420f50041209020750888503a140a0180c0602e449659503240c013801340c1d60350764040d102510f440c0840d0750020659110350303808150803040320b200380181c07149454000d00e0341f05c442c494520075000c4c4984c0403505d40c0c86070181d13200d400e800c40000d105030390900c13454020300140701200406018040044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434544874 1250 434543624 434543633
    0x18010903120e04050a29060405090a050f070f2717010213060e01050d0c1403090a0c06080c0409110c0a080c06130f03030c090504020f0901120b0d080c0a 67
    0x7030052200c855a542e1480e120040510003650b02c0a042d00710004d003090b07498001c40300d03200380d080d04590400d4502c542506810b40880d407603200d590007071a00300c0c00f110100a00b00d80d030342d003060303004002500401c0c2072030f900e202040343c0c0c0220102c20f200004a01a00108450368080c00c0320401c0c49882d60644062a9640302c4482205560400385d090b5075004640500300703560600088000f04203034280000316660000c0002d0445c425410300b10086552951030340c082034032410703141c0c40303103140589482d60747c0c00c0c849040f50340d841400104580c03010a241c00031412904c240251405043c080150700d0130a03007004040b0000e440c50b02c0480f07441480034042c0c0c45a0103420000c03080307150701030f81f8101d076154581e844207820311a0060607500c2080f60703032101000081d010054039400e240c01d45800984545110340403240c0c200c1c00c1d408103a1282c0007040c031070350f5035041ea00148040320003600c81114955001c200c01c002d0380e00340c0c141c3c982c0c440019000003000c10201801040a48014026105060280c0d0366 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434546124 1250 434544874 434544893
    0x14010608010e0f07050f03060601080703020c030d021b070e0112081204030c021206060307140321040602070e060f0f060c0105070309030f02061b1b1507032018010903 73
    0x4006600c1c1e0064001000003801130001201a0a058a00000b40c1d04440042540c81c030000d032645040241180004403d984240c2c1a104041004002d6079035448e52a483c2402942040720500018a00032441401420307000034180c3c2200d11111b6103c9642c3e10f0500d0382d51001c1c01800d01501c1103001040800300d5190300382040b40c8901c0c481d0b2191307220141140107000b8602210310644285601102c2800780c6503800240190403141000d068003440000744011900784800200c2022500781c0544101d21000d100c0805130040c0c039480d600f102c0c078056030703000d01e51810b0005643c0d40342c100482008841282c00c042e854a1451074014021500d003144610819003120022680c03140081c0d507401d09802090360007804a0180c0001d84014211418280814040d4903862410050200c500183c1d0107441000b9003420503842080100ba1140c0c0044034200c2c0e0000d5100701c0384000013901d0a41e51120000408c40030041031220b40260358144031061001e0300080640502d9581440002c21001001803030705075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434547374 1250 434546124 434546141
    0x1b03081c020c060403110304081e151e070921330506040603020a08010e0c18060409030e0301141902040803070303020915071109060405011202060d061a070c080c0d1401060801 77
    0x5203007070b0488103250012030908a19280c40000610bc400038000006a00607a416240358040c0301d043c1c550700c0711202920101c44540c01440640032141585021503006c6660002e500e015000280c00001e107038950b0390181900303403001d002d030581004506801506545c44164842e0018100140080d181d800007000111268446d0307846039182c4440c05c003010402e0001c07454808003a103112048034040d0b03044114664000708014080d03a80c0e645054103241c4118500c61035440060002c0111100755025440a900100d440d078000070fa20304910200500303140700312822514050007840c10680950b408030701179404070307070840e51040c5604155140081094014804503104003400010550454140001d000000304521b100302d01c3e0400401c42203a04204000189a04841043e079560100107841d0007864560840e8004031084031a1000b0184480018240390703000d10001041959600708483e40c170071044c9040c9070030903e0700e2000e8000800c400a002d40c7da041c0d5000100749281c0758601d0500b11070221 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434548624 1250 434547374 434547403
    0x405010e1e0c0f1e2b03030e060106050a0f23090f0a0503030405061608070605011a0705030a08070320040609080705090c071b03081c020c06040311030408 68
    0x110404601c0e208001c4208566020740b4507940000c02c240c00900001c3c1c0210243c200741590050503d080d5880c0c2034290b01815640e41d0782441521031516400c090600c2c56030031000701c0c1c500031180f194400d0000d0014100e0316240d85aa00d024000001181c441030883c094800b80b08091100b146102e511141040304c6810101406848010180400000d507516601842c011004001d051010f42c80100031039082d100203450540da80c0516503480c82580e80d085001610484002c9064010444c280d00954100c440e14528003110f84403481907505607105014008241e54420416084000c0c0039903015580b0102d50b0070005003031503000e614800007440b0f03c021501d4046001900784102e9801851030800b0f41032280090121a0600707011854400005d88001030b05074001c5041c00c1002030004c8501400d401000030740c800303942c0c1ea00c1e1034041138022940441c606401c41d02c0c08044816180300fa181455071542c010b01c420b45854506449586112210038003600041101103040c5030200007403404540f21 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434549874 1250 434548624 434548663
    0xa050d081603150312120f050114060c0304140a090903020705090c0901080c0708070807030903290f0403121802030c030115091e05040807030908070f0e0405010e 71
    0x84040d421400e0703109201810700d0f14031460020380081c0f4107401902c0d80100a0007900e8610542034806003100300320301c0100c50802c0010300020310190405030484100007400281d45030400f04000c0f10340220b4181500c03d130f0040c80204401c624030300c1c2080d411070025140364002034580090805a40c80c108059002d41e01080081002e03041551199a0002c030782040c960030310720a013000178220440901441007400700412a074042c000c42c01304988269500c180e40c656101c01519004d02594820303c815280d20407000000403c034800c0c0303050000c040050180b08102d80e9145440d2481d55407010300182d0030400d031105050311115451150a4049017a545942042c00e8148101481d004040614074002c0c1d04101011410410f03049415059074443c0790007199404450900e48800703410f01444405081c00c01c4144400d1140c082c0c000c0055500995802c0107140d12000001d41d10000c510881b1100044894108241d0940100254015100f06c00119080d000007111078542513144206409800b04c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434551124 1250 434549874 434549881
    0xd0204021b1b0112050a020f0403050607031a06071415070c0c05040212060d0f0503030a0603020f09040c15020a0c0b0301050a141c0201030e0a060f06121203020703020a050d08 77
    0x1010820390b010030701c014551580464410000814661021100158154071038021034918035440e01518a02a00050180c0d01d031036981c10000d80e00d65081d201c80000c00e03d0000040d4002c100b080e84c89090300307400f038255403510f40181c5c0c600c0e400b4459109164011b0051a000c40440c403201d0401600400269699582c050214180130b46215a03e0340312031301c11481040003421103031180c200c0c1e40e445801250710202003015410302a010452000d00245940400000c00200000781d60041d000d89000f902c501541c40059401d0100c00442600c019000d460709000400104178132598180b00003c4510540f42513401c06da40d400444180364100941c54a404001030049007880c0340c41314000c002007000c00c00b4003901500481c808a0b0415030904d12001003008000659000707411100171006002d04036140010f8500b02580180a0b0103a40114a070601c075000800c01034662514003a945c11050343c84002103180c1c000d40c002c3d440250110300354024034440901140c01800000200d0282c2c1c1c03034505c0c1618 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434552374 1250 434551124 434551177
    0x9080d140f040303270309090b0f01090510091d04030311040f0b0a091d0a1d03030c0309070506040603020c0d0c030c0b180304090204050f030c060d0b0d020402 70
    0x2902040c019010039020800c01c1030072284149003981080c1c0600b40001d0300c03485c0071141c101800811400d220044030300f19004040681c42545001241c00035041008480d9400e001c006040c51103005060005811080500451800c2540c4682118003400e1038048260b071010b105100c6038404a2140d04410f28004200606800d030082c0941c251000080c28506400d00b0400c0e04460b04030b01680b8071014012481d04405401a5407810160070021800d400c0e510601e5400132031802d0441c0e60603195801c0007258503040989810095070106a14080c0d82944c0c1c03000c9540d20240c0004000700f140388207180000034161500c2d8014000303001c1c6a5000340c0c0d1501100303115468449a2202e038020040702c0701c06800402d500000c442075040e8007501e0030982e5103505011200364040c1d072072500c1c00f50000150004000b00c4540c0248102c82c003d44180c224504450205500c403000842003d03003046003084403510a080e03075848000000c1004010540007400d580119040b6041110502e00c0404100314030074000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434553624 1250 434552374 434552381
    0x2210403111507030309030201020909090f0d030203090304090f0b060708210105130e010902031f06090c080711030412150b03010b0f010513050d1a0106080103120e031009080d 77
    0x6407080c2c2d05501c002003924076800a502ca410030140c20555034900c400209031007901110030f0240000e080100a060210006481d0801060b4010b0a48105024118014040d0007030340d05c241081c10245081601e0309a9110261407010f5031050b0890351100310307000c555140f40140c135025010b07282103500da40c500360708450f04085400c102c0c1c0c28060358400401107035980c428065144080c01202181941d43d102403a40900540e03c0c00035494042c1440400340c4090380440100020b0b840c900c00d00650b6640d003200401caa1012200f1000a420100041c0070036020b00302400145d035141c0b003100e1500c1d81c0c60503811503803811030a04079500e61030000744940c1038903035005007000c05200318002c014206041c8006000b0707000310b070341803811322002003080440e0b005450704500007440c010b8508140080315190625142c04550103034401c502242c0c00100d0424402c01d107103816030354452200721810581070000e6841005868515030715205401e07000e60940351600814032000e2041515545031081d0310042c5058 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434554874 1250 434553624 434553653
    0xe0106020c0307060309030e030708100f054501020307090e13030e0307090905030304060e060f040f11030a03021e2407030e03180301150e07030b0102210403 69
    0x456001c00380110550341c0c080750880c01c03580c0c542400103150095103004c0c2c41142e0750a07122513060041c208002030007080400c45010300d0108005c2003000483d075580342001c803041a61900c4807040c940c00d50f400100002c01400c1414100c80709003002c00b00402a0307a404070400d00220444a0350080207102c2da03950408202e03c054116500507842c1850400c00120103044110b01c0542009214816030802e44c03402c2c004038010f441c0c0e100e4240103202490400070360740d41c07044c0c1d000c0f41d0480c50440171480c1c480c00829080d0058004400000b460740301c5403550b2108100744d040c1038035070030f5000140d1f05c1103580400010074018400e4002d4284103207040ca0b00b8103010591054641c2c070350041d01d4285c0d0500b0f04100c000c241e4591410149009883d008400c900820f0381c40445841440005440b0103032084d802900044a1012002030004c14031002e54030041c88110710482d04484081c00c0400c00550007500300ea0350111303040c81207904242e04d2507081c90ba148003c40f144070340c00000013014002d01c041d06505009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434556124 1250 434554874 434554877
    0xc030906051c0906060f0608010e060906150a030b0a120c0f0605071709060703050d0b0102031204030509120d05070b0610020c130f05040c0e06030c090a0b1201090b010e0106 76
    0x3050381c50540e003402c1c60085641c00340b9440da40c1c494a410010660705c10400740c8078016403004000c1d00e0724070185c03040d0000e006280315124102c00145441c50a01140d522828000c1c044036103070480300d03a040d101d640080090b0814551102049441500d030840900c0091000803c0509030440d40d040090b00c014031038010700d002600380300c0d041c040260000102d4030159070100f11b418070300d2041d240704d207020701602c1d80f069070044000400c00b081c990b0010140044084610342080140719007401603a81c0d20429402d1038279441d5500011700401d00071005081d003000701400055208505140c61800c0c0f01c0d200c905c810110303001144003414044c00c1200c6940c0400d0076600c912940100c0200a903484001040c0c03103224001c1030100300070f100c4040e0003142405561031824031007410320307242070421408070b03004400481b115800011842d01d40040c00c545102d0000c1c05022031134440c079945030040c0c540c00c00910f800040c039a081d0007085000f440340c03071074440c001c0c50125810750424186181c06081030f8090380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434557374 1250 434556124 434556127
    0x180b010b092130180f010e010e010516060f1e0204080d1101020904060801021b12090d030912080717070b010308090a052701050105040e150d050a060614041103040f060e0d0c03090605 80
    0x1e003598011083d009d18220900308584c80b104805503903221a1440c1000400381401d0000c2c440c2c01079050b0300300e0040c0c1007003204825141c0418603690b004038011885014166408002079200c038900a400c08030700c56000e130340003510300520400420141d548560102d8510b81d07001610724011100e400b84050019040c1c000350046001016840302107000d5001010311551301c107864481054001e281c260002c2800d18000380c01104281814840d0350400c401c240c03a480510a5009038000c101c0d002ca40003d5880b060644540e4215140e00c0300d60341082c0d20240c0c12000004001c02da6070b4401c07205c1c0c04a411120900102250480c0b118842e410741031b80694140031052000744800d0f004005210791100030301c40300600c80c00189001078204154001d014289000d00a450005e010140d008017003914484541010b440020605000c21940c40702184048148103001185c005944151541c010710700406010860002851400d820000d4400c3e1150200304140c0d0048201500101651b00800b0b140c10b002d1b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434558624 1250 434557374 434557397
    0x911041a01050304080313140303070f03141303052505010b0409031202090103112107020309010207060c11090c1803030f030a180b010b092130180f01 66
    0x782c00c40c000a400141100c1c0003100203807100c2d0200d40030317180041d0044402c240d1b0b1041102c0780c0b5200e5209884500010b8154102403d0440c0280181d83d020328000e89840d80ba55180d074900400c00700302d41411401c01c07504201c003007c21905045054030710500c004400c00700c2d048500e4620308645802440d140158188138603000441c1d00410803501c101010003015a840c034400340105c00038107115501d61050340011402d03065050fa20601d11448444003900b4100c25200c80b08242d0703a900642a029005a003d540306100d070780d1050384000c560710310503240c5d001944010340014860a10494100602960200320086404401c00d08080d0f0410240c0c00fa5250001108550419100040020354202c1e200c07507401ca218a58480005004c540041051040d0f5854640e904031300e52200c5000d51203481507a48407001000313000014001f000303144008061600322803442040c04216038503000e8031110001c10980100b00b1540040801030316402035201d04e8883c5000300f0083c07a880c400c2890400c059820786 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434559874 1250 434558624 434558627
    0x203060105240d0e2a01030903020313060e01080f04260c0619111c0c020a20010305130c0501200f0f2109130605040911041a01 56
    0x1181540c00507109002c0d080d015040160400d058100c080902c0e0700000341030342c2410a140d02203c411034401040d2458100081650f000412400025440412583c42c421003190b004e640401e0015100b401568182060180880c25003865588494007103405020752011640c1e00c20219603000c2e0207182c149500c0d05003a101c45160822003007001280340d200400b103d00380c6003035005407125040740c00211583c03454900b01c0ca90148400b2050a841070341002101601d141c804401c1d40c47c040c44989800d40b41f103d1040401018000e401e1515095001e810301c1c0401103030100d01c2c110050304400c00b404841d120910001403c8070030080c00b070390b5444884c5c5006000240d02c0101a01210007d10f0604400174240489a1036054055409002480b9480b013030590841b01091707a4180c011344400381c8031803010b21144202c21864100500094a0041012809620741019401588625080009550745d22200482c049501d81c00007507a4420710f4484a1701d007464140251032580040300795850003905801c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434561124 1250 434559874 434559883
    0xb1507030f09140d2f030709091a1f2903010311040906020d0f050f01050f0306010303110709020a030e160f12060207050706090e060a1508042103060504180203 70
    0x8110703102e800c0410080d001e11444030001c0080c01e242c4000a140241d404c64425804400d2170a210b0290149100c00500355a0038420030300d03d15001120300300c52081c43d62241d0b80c103990040280e6044185404071020341000311454001520a00302100e80d81d04d0009007003002d4000b110b13051007035a1004c000500004040e143c2910102c00260b4020032003a6641c904000a4000c01340e500c0d9484d842d0000c0c210051038075811840c001d01010714205c400c0d03600c81c0d00f4080303a2002540c80c103805070320020041000902c5006e43c041000800d105031551980c03185803c0c41030380d01503510341c2c2c00240c5071100080814803c1c0400c3c0305207082c19450100b03851905000c101107030700500c20725107000341c074010382c405003d180e804840c980b070750003003c0d00c140680303415019141000c0d5004808a0b42108800100d4500703000e800401603400c0350011007442030000c1c40c116040c500060084030004003542c11004408024080e00402c40c41e1510301065560800d410f020885400c400c90740041032a82c103450026840106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434562374 1250 434561124 434561159
    0x3405060f060a05270c09040b0406061e020703061d06060111071a04050a0303030501081204030803010b0307110a0302010608120301030b06010c0212030a0f120b0916030b1507030f09 79
    0x104c0c8103040d80b00c1e10720007804090703028042043c1d44d40c00004000060600c4802410f00c8207045408101c400c0c456001d0004a84082c0200d4003c18803642080e0450880e61805080c0100c552046031080d0f174490b541c07081605c103074450b4200c0e0844101446003507000244102ca40c000400c1c680480c180824400301b65136210b081c46a0311401840120701000401c405045a028040c098440110030342d40c7c0c0384c004c00609092146807581c0c014204c0d844402c10180702101c003100c0e000802c1c1810742e403d280d000001d6500180007403050100340404044106018030140c585d8030300903000010380620700952141805040d010006d000c13002080140300094100100580024081c6418003551038148042424aa02108290107504c0085a00d20f440c1c0ea01c412584071a1880f0766520840c0c840f1100f0305002d851400680031b92052003280069017030106200f081c030680c0110f20700421880c8403003010030001460700c0500024508002881018182c0148000803a601d0030300c1c054110603e000322001007003c108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434563624 1250 434562374 434562379
    0x11130501030c0c08030703090b090d02070b030c07020108060f0d420b0f190816060c0609061e24050a0e0c190f0908010e0304050103023405060f060a05 66
    0x7102141146c0e120781d10203c03040e0f5104400c080c4ca401c000c044156518803d8081c1030044c89a160301040e090300b18070540b0300854000d100c031803c2c00b0140e801980c0040d401403066402540c0c5c0d060445143d55440c02950f2000d0040404420541c0d840312042140300c150036112301710720420105110607405401080c200c140c1d49510014281c3e0026000039890a080507070146d01c40e0000c505c040c804498000f8603411140440c046401c03800e1010881c20040d802d6101d160041100d0303500400210700386030454903010348202c0c030006207416907001c4401070b65108151001d416544011440b441d110302c0b42d0004410100903240e0540f149810001010109036004584501c6145000308079510742c91019a502c106460400c6029005a900020140c8a550090b035000a42e020000039011f001032080515254169000d180303001d00700001900658001c2e4848982c600901200002c1c22107281503040741001e04849103580320505040261400002800a1917a11254420721a035a51111412012918103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434564874 1250 434563624 434563627
    0x90602070f14180403021608060103030f0f02010623031209061b0c0d060902091e011202011403010e0403110c0306060103050c07020d123009020307030611130501030c0c08 75
    0xb540c01044100403121840385403080382d402030004264011134004001204600380c030f0400c5070340e204203036901c030400c0c40041c0102e1200400700510307034814000020061001c2c000400c41304d68030f000400d2240492031440e110b07481c3d05199808135190612223010051040f8201e642441144400117038144981241c0d0403132240c43c42588103906000344204044e21000804d40c502140035800c18801a05018408034410481000000c1102d803600080110b441c1081c0a11a4282c0c00c0c28040400d0070180a41603041c0810100c10044c0007541c0760081d4007070600b10b118070089042c149809451084800c1e0000c080d070704154010401514001a2075034031407424a00411540c58411801c12107115041010703402c581c0f10680c0106000010000d034000380c00d951f544c003028501c000c0c41205000d000c618070340201c0b5000001d60814858582003200310034002070030394030b400350750b96a10000ca851a404810702e511022483c11b55402100c401c090003083d082c2800d01a03060500001010381c02d0200004222980 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434566124 1250 434564874 434564909
    0x3051c05040308090f0d1b05010e0915011d0904110108011d0c0a091d07020c040e25080f070f1413090c09020d0203182b031e0903090602070f 62
    0x1502185500b103247c0294044d049290240c50300c039000605401281e020039801140b041c0d03181441011a4810900c442c1020340d41c40d1407000440f500f400003501107001c00c0da589404001551a111014080c0384101070a03050f0351541c100250100c54164400c030b5851209403c16200c0201c00840d5951111606060302c3d914540085e042c0c0350781160b0341122051040c80e03054460210703400041580034030601d4085a0709248400d00300425660341c403e4034515500030180d900507004d10810076141a00c464004540207588a1052624007d100b0201400c21f40c800e500c10458008042802000361004c0c903500f40450180c400032524883d00345001020f21070381c8000d21420322803031310400400341011003001c1d0b503500100c01c0c40c0e2003e9041a601007900c1c180c0070350140c4000b940040c40d40d840408100c0300c110f8001018414180c00401c200c1c0c10303818140c0f5160000401a190368500c02c030801e4064001820300d05600740140641103d410000565000c54410302035600b03504111411900d950841003100c44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434567374 1250 434566124 434566129
    0xc0e090604110a03060c26010b120a0e03032706040803070e0f03030a090e0603030a09060c050f12041518090b030c03010903030605190e070309051603051c05040308090f 74
    0x11211342c40580711602d008603601250742d000c0e031a0f2540001d099034100c42601024003021030300c40d00f031141c030152200070810300e0b01d240040d445090348600b00e283c00150441c81c48102500f1684100d07000180e002400c001044409440440340c42e42d5034540004101c0c9140c190b6504016100203042c1f1418094052009505035442e80035691f41510041d083c2c0f61902d02c0070340040c1100b03640d0701501210480120006000f824008152001140e00b0b551b0440399900e00340c41035420301d01c00720307080c0c8190040c2020100000e40070003120800d0000001e01075640c41c500320809400d044000203560401c040c402c60121a0348480702107005641780006d00113004950b100000340341965818155425508207081b0600389501a80f00004482d010b445640741c20541605001000803035024034801e40d802c000118202611945c80403210a202e00f0885a102101a5040e405601164002c13500b640c0710000e107007140800c0080b154145545400e00c20309080c1036582d64500b034010151098003403000100308902a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434568624 1250 434567374 434567389
    0x9020f0d1103010903030c11150a0216060203070c060b180609370b090103050a03050d06081f06050414190615050406180506120a020f0a0206040c0e09060411 69
    0x41d00103000300001e040616015000d0180b030092280428100d100e00e406015001c5604642001c41031559081556800300000080d008180342c02c14a00040007000d0004110380300542c00340c503040c0c940c00b859006070303c0e080003652a51790303d090048695041c61654640b104002d01c2d02b10204550000441e51501c101369641c610011100401503d045443c1c50424402c000160030805904000d0241c2d658180512103422820f12005101c1d42c0300340e00304000b10344164050f10b5545c442c0351011810f1690746151901d0540c155810800d81d418980c4118401d004500c92040100421755050103440d1041314a8858520018070041c0306c00742007070f02c10705000d459500000240410880e409851a034a410042007900b01e8003c100c0402c60b42109040008044074804044650042045103802d410040200d01d00c40c02403d150001a0240300032905501400b01801c0c0e1440180d00405642c82e150074071080110982d8410072a40b0304880c140000a0303004941241d019030014a01c11a00c0501c0d00400c140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434569874 1250 434568624 434568653
    0x51e011409040f05060f180c030403090e010b09010e0a06020c011d0d03050d052a0d060906060c021309170310050a030602040905070f0914030c0d081c09020f0d 70
    0x20030b180c50707644200d5407001d0f07221a02417841940c2101200342030b4414400688070303950a0005405034040041d0b0080d61110003558802e00c81d190180c1c42c03d42d6007017006080031080e009041c87c40c40c0810580c3c81d03540c0c0100715090a40f42120903804007442c1c104042e45800340007070420f0421201018010704481c8144080045480180207441e410302c0d5410001c0c5640c010390f001491040c10040461410120241920991855050902201905c00305160200d500803803d210400d0707143d9100281004461040a0050041d034581c009140d03001d01c100007240e050140c03041c20b09442c000c200004107080690720240b82034424046036580d2070b684c00722100c803816988101c0d8000200c1c48044204031246c0c01070012184040002d0240b9110514141c8200404010f00c40010341c0c0c421042181e40516080302d404560050141d9951b01c040307001141080ca03101109071440c1c03000041c07410108849440c1003110613480ca404000310710f05540010603402e011050309200d1340350401000c0c01e0210390480f6404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434571124 1250 434569874 434569879
    0x40302060a020a0201020d020a02090118241502060f040f020307030803150109060305190c1407080c0c1c0609020105161a060102070609090e120a02030d06051e011409 73
    0x1100c10711114000c0da1a018540203e0060040a0705a00384500016654941c00d5005240401c1e503800c19100310480c104e02c0c940a0701c0c4989441c1e602c1180c00b40401103451010446100c0584203091400d0308000000150f10002194880c5d420400030407428400306400903808018016401e40d6400040e2a00701c068001034401d2600000f8441e036001c0d948180d0021402c00c1c0c071403c005559410083c1c0480700200c0b200d280412a040d030042d09903950358448814200346080c07640e5203e001095803401078202d4502203981c410001200303c0402e030f0400c07001c0381c03200003115141c01202c00a01d4883c0c60007030072070008044030744030003a841c11a0b0192065a10320151801c189407180b01a0524240350940c01b12a03003a8081602d0210303031f01c1e51004c1808411350f285a25240070340d0303240c00101070052100390a40c04503801804200401d1580c440010a426801c0741c0c01503803111034281c21003084a8050340060711a0440368503810f12685e0100500b4140207003420400c1508142c44103e110b103210f150961035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434572374 1250 434571124 434571127
    0x60219050c0a18050c0a1706040e07060e0a080102030c0415031e15060e03250f120b2a03100306111201090207030503011e1d0f07030b010504051504030206 68
    0x190702e104100d18203900582103409004c1e5403502c10381400346201e48416200002d140500000403038034102d50707054000501900000341080b500810908160554010a00051940650501c1c0e8540302c50750602500034100210b00c0d500b00611420f4039442031348a07800480348120340441e2824041d0780001d52020702414040340c907100042001c03009115100d80b481000c0c0d5069400700700755115900000001c00050018011180c0344401144130107030040c04c981c0720480010700410600110b42e147d02c0140008904a46404490316160385150f01c0204220194400440d0701c0d481e0f41d4540d050043d2980c0050040740e0382e511582d00108100e01603820190440c3d0415422150000713a1500800000480d0f500d2006640d0700d4021201c10b900ca040d1026001550510040c800000005030f02418025003140010b42d03030740ea4034101400d00001e01091040c1e0036218040104424806684030381c008043c1c50704005010802c00040e225004600801c0d01605241072000040084079080300c02440c3c00a1455 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434573624 1250 434572374 434572379
    0x504031406090a24020f07031e0905040f150303020a03081b03070503150a030503190503060603010b0c10050a020405040b030a0308070809010204080a1b0f0e01030305090f180603070f060219050c0a 86
    0x706d081e51001c0c0040700021803d010440082c0100038a00e900140c0998803641303402d00d441c0411000d4001c00c803000c0070f07159640c010350700011440b4a10380019031007500581008c1100d801d0141070114020301070490506c850b00100700c2041c48200302c907030100048c2040c41e00c9071130349981c401210551042454211200c00c1c80072003440b0001000d06941006036103000b0038900c1241045949001c160341c10b60304103500348014414001a070307000c2c0907541c81900031940ca003000c80d44548240e440c140c54203000203500141c10f002c2e42c10140640c8051240650040c07024100d140e4001300004c00051042003041449004545103090a4048400406403a000c444031210340c0d003001295001717050200c0f444861880000960104d0103084036041b0740c0c003a001829281c1c81c40c1c5081d1815803085642036400248003252000680e107080103480700c1c07052030714540307503903c2c1c800d05140c5070500507000201415002d100810440da4001410442c10100d01651100b01c403840c42d00525107201d0b80c680a62100104001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434574874 1250 434573624 434573647
    0x10c1e0504051c1a16050408060105040b150304080301031a15040911030321010e06031009080f0c0a05070501030b03100e19300c030e0f060a0504031406090a2402 71
    0x4417401962903650b12800c1604904003502d05108070310841d16140c02c0000104200e16140c0d01190011802401c1040020300d485804e6000c0e41c02143c1c12a5940808001401031081034000640007018201c00070b8440c0c144820a099540703000c1e035905100715110307d2480c0270050b205c0c10001c0e0b030403809800c403a210b4144910210400c0704400c0e0203540300c03005200000d011001807140600175070010340540354004c5241c0c12480903191080c016142440e04000502d0800b442e84d005115001e030b1030001d0042d990701da18103181019502e9209504041c00c110702c03a8250f030317008104280d80900420700025110701c0c03040d4050a000c0041c0c5a202000b0385041c0e4041844200b45003030748281105206221102e00c19003c00c0c61b072440782e1442000298004907040006405100400d000603401440301c3c0404003040000342d25039004143c1500041e8000c1020810020700b40d0410010b10483d0f00506143d24042c0e80711951011075007406042901041500c0022142450010700b03035400000c402c0d90b603030328030451 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434576124 1250 434574874 434574923
    0x20d06020c010f0510060503010521031b010e060103170c01110d0203040b071b080d0935040b0906030c1204030c0c12030f03020c070b0408010c1e0504051c 68
    0x2d03e0b1107014100400103001c01501d4520b101034510301d8842c941940d08200c140b084bc1e074404402641ca80ba903000000580f07007c01c1015100040403501c441c100780d480801031500b9582201c1071800182e0008005000080e581082d80500803400c0d01900d444401c1607110501400041e0301006240100103407071410131001e5001140f20314011580c810043d00e03072003003c480e00200c0d00000c1403001100c49000c4000383c5220020311520210101c040b0795030030183c551015a6550816252400d0780c0c18009201800f46212415903500d284000c040c03e103890700203d681e6074441c0d51001e0748290800030019100003085015104012071215214455151600e0003601c0e4155119044d1203550002a000511040080c10320300119810303902d0401080c201e0b00c065020b508003980940b00390080b1100801c2c4021210090001842050004501d1040d868805000f400182c1c0b030200c0403d0114003407100d401d4100045400701d40081d035000d80112504074128500b4a1014402010b01070381013400f091800c960035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434577374 1250 434576124 434576141
    0xd0212060301050609250c02060a120f06061b0c0314010506030c0d08160c051003021905040b0f07060b0a06020307031101020c0a02091b030106020f190305040e04020d06020c01 77
    0x70003c00c0780b41c0f5544100038640b0400c881142c0d140001d403080c010100c800d01c144030303100186414035010b200c0d00782c2c0c0002c3c16078002820410010300707034400d19001150750380154010407410b20001c00c0082d041207402881d0464584001400c034013072034000b01c1042440c011420045420101c0e80d03184e04800c0081d60b002e05025940c16210703200340f04d00080c81d4a0030b400700f00c00039588910b00c20328102800c60050f00c0d641c10100152181034001c60b000469440310150303002101490f560041e80c1d07000c15603041c094076007000d0003d42000814002448580b2010003100d055134800341c0c0c100c1e140c505514000c00606a01150550403003d20700c00002c8403900040030b040e0092280d04c0c2d0180081e02007400e10300300e010700e04480c1925400710b602100941021410700c1d4100080944c000b40060001c0d40c076400990080c0d04c0383c0d006a2104034070b1401458240f0126a148100368803000205004c0e0302c0042c0710f1f00560090f83c05800c80c60b004101150307120b0b40030200c11640f26905548444044014500070070044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434578624 1250 434577374 434577379
    0xf0f042c0d030606020d09120c0306150806010b0c060117030c1504061a090c0702030a12020c03070603021306030b01022b0e0415030f0212060f01050a080c0a03080f0d021206 76
    0x61404a8036a0001c01c0d00110005147c1d03a41102e140303481207000030b031108a4415580e80d0460b140210100d1020702444007000e611255098034246802d0f040c1c2c0c030340031050307000111143e01030159010300030b00130940b641110071940c8464800040b001101342076108006203000141b09041040c001c1d41524405544a0380c00350740100b00e14006021300c9242e400c8a000881c2c0c0c811043c80000311681c5040010f044070038005801c0303d424084541c2c0b00300308410741d03940c404050383c1b000b6015400c925080221030060b09072494190b0411003e052122049202809404240358441c800d050159108101003600362241001c184880c44168400c04801c2c200c0a044030300190401d40c40700c40c0e40c200750280070486004040e101894910759103c10750030101600040707034040f0b403003000000780c00d000304941e500030f1300990360020f065450a410000d24050325400220503800c814a00c1c0010380e18a04a00226a046000595904202da0000400c2c4c815100007010b21440450840c2c000d8020710300e020701c03e4405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434579874 1250 434578624 434578631
    0x1524060f08070201051b0a0201020d02040f0311011b0f031b0b160215160c0213050915150906150a02100b09060a09110f040b0c0c0f0f042c0d03 63
    0x1603000490907034608486e00d480f40e03025114030207400701840d002044880e400d480010f0800341c1c0080c602e01030307038401d900c102080100b40d40d09009102c500b00c2c2e815860442428040e2a8485151005c1c0700142a100d0242c101752070304d00c0302418140a03002a081007505c4140b0346081c0300391460b01c44100401551070390124242000080c040c2800040c0c0c00200040100c5042e03603d584c3e03100e04500e0011032030003080412041865460058559428500000318a02c4010640d85040040b0754601523040400d4614030300c980c814070003c9402101900e046600a4a003034141d551070601103002052840c0d0894910322000404051030365021901c107001a1000905104c079500c96410001c0340c0000340c5a960340501d64507410003490b1501c0c0d004c5420302e00244802030415040580d040174030382159000030180f61f0005040e40d000d2105102040c00c58808840074528820800049086410b02a103018020707542c522100800c6a1526504141012502080c84085400fa1242340d02c560020301d42c100843e04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434581124 1250 434579874 434579881
    0x30712060812070b0c0903030f040e0705091e1f0f08010b0304081603030b031204030308060406030506061c05070f0302031203130f0609150204150302071524060f08 72
    0x20030000780311925a0700c8541018100d4460004203c1e0140280317280550030082c0e1051500c040c80a86010135040c0d0003107840d80d2070004080600c0100400c60310400100b0000612103030745400088000100c1c5480c2c2c02034040d40c64001c141000f190800b0032605070340e5803090a840307071791051451015400650b1943c1160b66a00e41c05041400251001480003000f405224090b0b800c52103100c0720103002c1d2401181051410300442e0800c07803030a85000d00600c0005041c411b241e0404a501c1c2c0060080d18100202d03403a54071407540791640546054408e46580c01100d084040802043d5005a001350585000603078a964103401c0d8942444102c1c000d01606c04589104030b10503054074441d116401d483d80040071242d8420310b00d021101812112140d4949042005c250500d03554031005081c2c0740c00607521418401c0c0b08100c4842c8201120030540100606ea00113070204041110303850f01c05001184808110b01d4150b0300740062950f9030000c05200c880002d191398000c58039544003d81c2c1c1ca43c90090f44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434582374 1250 434581124 434581139
    0x30e1014060a05010c1a06011b080a0e1e0f120106090204060201050610020a0f03091503060306060803090607060e03070b0a02090906040b1f02030405060711040b040c0c06020a03020f03071206 84
    0x217420800b4003c2e9040b50540740c180400b5000c0c056112805140180ba407a0b07042d0b100641c405050541a0391003000498051a6290046101800c1d014211003080c1d00060f1031089030024140390f00c40d00d000d12201240f04110707407030b00e50582d0302480c402c200a2148a8071035500b40c000350810701c40c4000542c01c0101140640c00c190800b4543d04249a0181c25291600c0c0c40309102a1303590070742101000701c4c1c1800040d140300b0440c10041c8502d040c5c0d4010030b0040c9103060000c01d6503016000b140b115081008461248d80c4c80000302c3c0c110760340c82038010810f64000380106045000d4101d0203040c00c50f10104006000c24254024214031008440e40e20454882109000072908444a500d401c1184518851260303080b445005c03181e01c4c1c0501c100c0c2c2c40c042d22034022030910740003004101e410080318610342000b03103014000e02004500c240c1e810400364846000c0181482c84001d00988455400506100000e219804561000000408a0380d03a030414420003131004018944c80c1e01c0f040e1420350b0204181 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434583624 1250 434582374 434582387
    0x150b04141905150f07061a010f0305270106030b090a0611040f0509060d140c18100605070501111204050f0f0c040c2006100b04060906030e1014060a0501 67
    0x48001034206040f0303905078420420180d101000c3c51859100a003c030400040203801600c104c0b08444d00e50804820071b000c00585590b50002840381458100010084207060302c0b000d01a070a800d4240c14051184c01040840c01000d10360006412140010308200c80c0c52000960070f0384081c4a40c07420801078a811505080c203000c2c40c0a803402007030344070703004000620742011141d402c4400104503010f1010b075551402041d6101c06110881d54005110580951522642c0100d00003038000010b45030786020a001018180140a00c40c1441400720355002440b400b54402e910010303845101d66a103101c114101650050204e40071a500c0c407640b481b6a05544010a0702c803c1c040c0804014811082d200c0c0821002c0d21400c08041c0411400500031081c43c220051800c804041c460054101402c00c0c4000c07090003111504200d03003218042004206059111103660111203103490005025144801c5950a104d518040324650504052130401c8030b454800495004100440316802411394400c0155000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434584874 1250 434583624 434583629
    0x3150302121606140909071214090d0e0f0108091006060903140d020a021c020301020d0b0109051f0c061b03060608070f0c0803041406040507150512040303150b041419 73
    0x10410248940b028901b0000c6940d0b4110313020341081075a030281880120308881c010b46444000d0882d4500b4401004401d0110440e00185458150748840d03007040815620481c031401c4604000c008000100203901c2400801055007141c0070900444e07a85100044c031186441c04156041c690f09514031219200001d90b201030400e46070044c00080d0559000c216500030b811070304c00da10300b0700fa189401c0107960038030080044413648040043c0348a04400010216200c43d00114003d1842410041e40086010031505080c031051a00c603007900002d04c0c10f607024000710f4110410480b00a201403800b20b030141c2141c1c0a640c2240e9590300250f0701d29a0480307500e40000c003150042500304407540c0100f014000255805030040d507029a00f0f5030500b0143d132a000080703509590742d8020325000d005502a0102200040c100f514140b810201e60565002e108040507000030241551103065a40078070551100c8402004d0310425251219a88c6420041d030054000c00b11b4407e00d04411141c01015642440106 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434586124 1250 434584874 434584907
    0x705061b0315100e030106030b0a050108060f16051e0306040c08060627060307090f051e040c02070b1306020106080f030a051e0301030f060e0c1003150302121606 71
    0x1000500d0060041d031203c2400c11104201981208403201e0b107003401004010740c81015a0451490700c604010122401a007004209801520501c02c03880740b0610202d401c18011790300480c52441c101d030300380ea691140e80c010010202c40040e603844544d101e02b02840c4511026101403084111007503080381c03803503000c4a2455000342c0c1400180780c880322038065201c0d585c180203d50078500740a90002042900200c402d54001a10380c041803000450021044006140075a0b02075608a500441c1d68440300403c1009402166500260700e582d40c03082044100615445085540d1040715894051a03e9124000c4002545c20100001110440000c2c4aa03076600080c3c040d50a01c00c0e1650122046e074011900702c03006411707007901161803c503e140114003c6201e184d140c9004100740c030304041030312100100004070360040c5408908a44403200c51100c00311461900094072402c080b46043d040d140d0380c10103500029105034030085444005944502078442d89100030100e40d480404403004c0406050307084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434587374 1250 434586124 434586151
    0x105070807260f160507020310230403030c0f090b0316111213061701140406080f0705191a0904090203010207050a03080a1a0607060207080705061b03 66
    0x8082621490400c082e040c00003100000e00200380c201e511000c581982c0007400b62500d5020301c2070b030001a085183d020081401c1060420341107400180d120b0203804011b4480b980c0b10303809100790300b0710f00c00100b03003000c58400c00c800f040c245410001c0040c0a50840040858900350901941c1030081003050111250944494515600c08211440c01c000711134141c414000200c480d204d103c0d00602041ca414400d203241079403144198501d510740039903030343d0200060003601c01150b28140000c050141c19106002c1c600641000c6040c0810000e00c01d580c4880b40700d0080806a040524000c0b070441c0c21a00c0441c0c01c41d004d040b940d60300c256010400d106480382204030b0040d484d040130010b4081d122140300104005120034403500031a00766840310000303c1d12500700b40e02d804105604101d010703410409c00f01c4100800c80c156058003112604100019100e0b03040450700004200c80743d0100e42807164821a1291107007054030b0300c295680c0040c0e07095021240541301650380426901c06036840b500d6600c01301d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434588624 1250 434587374 434587381
    0x301061214010204120506070f050c0307030e0a0801090f021806010c0b15090a0906050c090102070e09012301060305010803090609040e07090e0718090503090919050708041401050708 80
    0xc0c0000790100d0141c80c0c1d99502480000349000c0c0400c140c4c0c41141c02040903000c0e43c504060024009064020300105201050156070310742040042620406603142c141500d1444442c2d00140c42d8108070781c845801903080440410070071040c10074450b031483c82514040300b0000005c140c580030400c2240c140b40002c90b0000d0b48004120054a41134014098102e102c040e00045800f1a440940131030b021107a241c1c480f0514410451103105c0c190340444240510750905407001c2c0002c0d01e480c05403003a00110300c9140d02042c60001c00b0351181e544401c0b0300c0150039454000c0c10852401600900c500c03004070b40707454000546040003004a428540000780142d151179034200c200002821480302d100b0f45807159010105101855105031300800f561070303008054080c60300210f40c5c007071980c801038000d0407030a02c0055400940000140c0303151400c22140045956030b82400312030134014096522040f18180424480c1003a041001280143e000311f0b0603c0c0c0c000b902c26080d90a071501624280002011080007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434589874 1250 434588624 434588633
    0xc0a0909111302040302150703020c040c05040611070b04030c0f08011806110918010f0501110d030b010c1e0b07080f01050f014d03030609040c1809020f03010612 71
    0x380102c0800010014180b50b2660042000c502840d0404a00081c0000780c040905404200000c80d446040f5800d121500343c02100815030702039807007040180b082903030740441000420300011019210500500d922150707a8184070003601514401d01c40c85110b400d02c04901c0f2641805490500b03041c80c00e85500085050307480e01d0003414000c0b0b400c103400b0414803103e400c0b0340e24900f440c5800800c950754070075154140607581147c02c00780e030300041c14170800e01c1e025103003c8400316000410017241c2c28001041d0717141e400103031145500400b0003005042000e03440c04803110300d8180903235082d001d0b040007211581c4095054401060a484541c1030400c440300400240c90940c00c0010958010b00d041d02c07a0015149013250f1031031030300344039a400d59111030a1100540501c40c003a5500048503000310800d108500b54552a448064440b5000b030340303040005070500408448900040c2004000d004402080b180904010a02c84c2e4040744180355501041925150500030803082e2840400041100c0031180d40f03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434591124 1250 434589874 434589889
    0x11070c0b0f2a01090c05100203041a03090a0c090207051218131d0345010905100e03010c0509060a27031202250509060103090c06020c0a090911 63
    0x103542d40307941e5a280650704000780145003030f01d84103104804003d030402c0b041103064450034000b0011548103100800c081d408072034440740c40514042c00c2c280d40ea11003006160600c2e03c1408040c00035056011f0020b04080c0d20717401002c94070f02600581742100900b17034074012a480307056032510f1907030540b68101c0000d103031107122003000a14480c0c0005010b0200400c240300c5501c1400151001d030408100300c00c0305170103400600300d5040014041c42c10402c119542d080b114a0411030700c03403034012060f5442126402902c0e4034014045c010501c16441d4244400107001500c0120118025400d1030002e810860044040d9001244014840b90504c84c007100c04a6081103480d00c408a2449204409200d100b200e01d0003401940c042c80d5280f00d26081c400307019141203510120145031301440e03560162101080000081035810443d13031500b0607100c52004a015080c1442e000e08615008000001e016400003000d81c03603c007041d601d803406103130741d165103604a80154001802400702d603000c6280510340100e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434592374 1250 434591124 434591167
    0xc060a050618270109060e06062202070537021003020c031905040509070c020607020904031e021c0915080c1b01050103032c0105090102070911070c0b0f 67
    0x40c100ca030f0040800404688503490380c8204859a55075803404002e00041307000e0316845529480045c88c1c1c0d400c0c420302143d0041203050060590044603851000c03101c205070120b5001d01e0b0084119000740d60903d02c40d040741d035803013050092030703003203a4000300c1180b00c441906a2200390010034000003c041a00290065801a0000685400100984030f00b250081829041d4100b01d40c1d1040e480b642440e081c0a20001c001d0005c1c1c05018400b4220401a0340e00340445208503030507130b42c0058a45440c40c068808200065943d170202c1050300041082660014410481103d51418140c2c0e000c6604000e03101d02015004041c46413400482c1400b52038001e01015030031140c0881d14030303c1d14002c121025240020079000001d1a5101c500401c05c1c1a888110356500394803880106078903031340c0400600e12141c203070420241401300c042080c407031320781c0248501d0008106a003018400c001041071500041d91000c0001c81c0c44007051000450401d0204041d5038545010307060071880c1c0fa84c0031002168111000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434593624 1250 434592374 434592391
    0x120503060114030118061205030d150e04060b100c020102030301091808032a1c1a0402070c030b0c0915072102030315011b060504020307030204020309030c060a050618 73
    0x1002d8030590040c0c100c00450081a100da0710340e0201c4c498403c00400c2e103d496104000c0720039890060130201c0c0d8080101d5456415031040020100096070008a904e200c1e5400220042d00440420040c01070540285000354002c449400310100746034020b480d82e84151030064010ba10600040c0054482170388a201019030b45000c010509803035981d20101580100d60080f21016001004010014040c0440345410105c00f00b032802d00011707100042d20a05c0303079881c00070034075140c40650461400910340d10710315504c051b00644d9101e00d02c1c10308860381d281c50b1004031100c0022800142c242e8541d0001e84250b588010400b03025060383d5550000030750064801030754038907071b02d400a51070340c4180706070080c0b012401c2c0c01841d16454802070500c000741c10390440307034180650150a1410704119a001e034101c3e542c4070100140079107550020a2400324181c2000790071510000c14403080107030010246c010540494126850f80d6620300c111400d4804c2a20480e030030802181d0380070b40460094845550107000d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434594874 1250 434593624 434593637
    0xf050607150c050703080106020d0512060118060c230303041511072001110607031107050d080613060807090513170306030106170a020f030316030509040e01091205030601 75
    0x2601a01070071104201d42200105000180b010101504511024010005800604081184210050450f01c51901c3d1007060251807800200e85078024602c3c46051400303001c0390414030f501c500d406080d000192000741c40c2c03030a40c501440c4540440c20400c1140c0d0a42c200a1801d40d295541d50b00355144c0c0425141c3d04081e22039441808031000c0ca400740c8920340c091340254941e05045401606900518100d0310b042000c2e580030519000d20014003980c102185203000038560302c005c0c901d11021f020b00d000041444c01581c50750700b403095006c856a400b4000855001141d840c9080140c0c0031600305120f95203030b5402618013003003850400c0e88569402000149a00b214000a039512103032101342c200700e80c02c5c42c070012041c03000c2410244074000160043c0000350444a40e1841c1d2550754a0340c3da80000d1041c4940c0700641d4060301c042c81600d070340480317509000011182510380548039130401c0804074080d0745081c004030b0b0742c3c41c0140900c400160300311220103d480c80d070800c03c54240d0300092106050242 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434596124 1250 434594874 434594903
    0x30304030f0f060e0303041406060d030810031b0f1e06080411030303190c110a080703140d02181e0f19080a0c060804170c0118050c040f060f050607 65
    0x10140513107100c0c410b104c4040e5613245131500c2c15182008c624200c81c05690300610070044541c54150300001d00726054142944c0315982d480584808bd14160001040700280c1d40c0c900c6816000b60074041e0a544d0520b91913214251a00781c410300111001c5660002a003030f4060401031240518040d540160103011005540140f8402291455000340c816a40301c04c80e21010018030845803240140003042860309031241da0404146d11ba80b00704000014000c04000901c0904240c0140000080c0d502c0c0d00756415108d084903200440290805000880346041c080e0040800345040f07114107030b040f09961300c03040000c3c18150500c0720002e403400e001a002070790310303107c07903940b500480a540c001c00320140103002c6c44071245401403085406a0101c0305100c520000c0c440040c20320400400b0b481924508540c5030f9505429040c09049101080003565101c41600c3c4144400490800504001640c0500c160144002000216107252164401e09000c105007030140f450300000400109005a600602c4440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434597374 1250 434596124 434596133
    0x91407050d0213090e0c0301050c03090d080a090c1502070803041809020d020307120204060f0b09010503102102030123070309020a03051002030115080f0705070203011506090807050906030304030f0f 87
    0x40c08417480402e40d03072104040d1032040c074090061a07409050150100e00354101044002e94a000d88800e50342840502400540b20f10b04550005822580040c200f14900c0c1d07550204119002070ba10b1440014066010086040c3d03100004442c221808020070000c0036060940c0c003c0201030b03031041241e000380300044040241e40c0c00c10040d4041c00380301c140d0190845a42c41008103d035000e81c061480800081c1c82002004c40354003d882140c20207091141c0d481c1c0d1400221041c0301070030707005003000040354a810102088001e6140c0c480c144260020031440c60f000c0700c00312000c20036000302d040c51000000040d80c81440f0b82c1009149601c05084000d4564407980c0e114148082c0c3d84501030ba4030340c040010440314900e2601004c0d07450b0942880032090500100308400103500914850510100145d80e801b15102544080c07a451403540e52a600280c4a000042165801d84924200b81c80f50303060100e246d190203a00d035800b40d40c1c000c2c001d500c3e281c0f07159a00c148240c1c20b10340c20390384103240f45056004035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434598624 1250 434597374 434597381
    0x30c0a0605040503070b040b06130b090403050703090902070803040b1e01062006090a0201031b17040f020d2003011812031416171e040503160c091407050d021309 71
    0xa83c81419235a00f1071501400f13004070500d8852220038194285050744843d40c840c001c00710b0700b281d00340c0381c415543c0c1c11504042d14444d29603130003a6400e0340b0028406c0284038404000d03600461040f80103012545030260760a01010080c011040c0c1c0701550801008114061407560615400b031034100310360400c1c000c001c181454004c54035003c03240c0086000001b15a41072140c04540b0750614141c5a004249040080050350541811525070040c0ca01140910900300340318055070350300611b0f1194001162400300c0038141c0c1402001101200b080001020340b4040c004c580004103086040050060356440b041114a0703070500c0401810b41c3c2e42200e16183c0c0008008034031a0a84001d000040c0c1420382c0000e040c0390f00a032008464420301014000c040c0b50012072140001c0d68002050000c0c0c60310304001d0300314801c21403090788015044049004000005100200729100c0010812042d03400c5841620030305000c441800c0004d50410071140c03c1ea02503406883e440756600c03501c203049a100c001e1a800c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434599874 1250 434598624 434598631
    0x130e01150e01080f01050103051b060d020c010c0e0406081005060409020d03170f0106080103030e04111308060603060606090907020f070303030f0c020f100e1203010b0403050f030c0a0605040503070b 87
    0x9103210042c02801e030f0801c20b60240743d2211000300601d61468442c10707103c40e1030764891050900c002d40000e8269403001c042d00d460444d001e500310f40c0e9a00903c03c0b135000f0714410305e051740400c08404e1000c07024a41403040104a5010001074540404101800c600400004107050fa02c141c0c0d0309030140c05601ca225403618014829155100759035003040c00480c1021004100c0341c41c14104400500000c2d50183c1024116a850300f02240303441e02c000001009041d4034606070401d041c020500c900101f000038049404c4038010f0781610402d8651300241900c4800c12580300e40c00c40c2c2c00300080c80b20b84c2406400240c0c00202d51042d5002589140c1c43d05042c605107a005800094450200e901c0f00350b10342c8144942865903000a0a50742c456010b1b1645403211502c0c0110169070700c0030708000610381031111040204a0321140c41e943d40e1200c50f80c0341c96800c103020540f2648103503151200400d40001c01c581b44400000000d00c40070b800c03940d420b0040c102c02442120203000030700c400000107154040d5a0702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434601124 1250 434599874 434599889
    0x180b070528020d030f11012a09050906120f0d021608010b0d0b0a140907080d0c0b1f03020907110d050403031d0402271905130e0115 58
    0x80412024020300340d1401d81140d8400006581180140140c0d900e0800090150749410603851600101006072041d8016030844840ba50a10002c0d80e05504c1020f00c6041f602c41ea159085105400403c0885010000380030740d54101074000c01013012840e01488a10703a0901d01022200800c80b082d4001e03041032403400c0c003000541d0040c01d00c1810404210510f034090301080e00200044007035540094903111081d00060300d85c1104c640407913800e840c3d80d00400c1c42500350046807041414241e00e0f203613584100d841900c10034040c00340c0c200c2c3c87d04c4c420740c0320401d61038020040301c1103900c0726428201103035050120310503e00c44801000005031078203d145841040c164442140d000042c00d220b6007001c0b444181c0b00300300700080005100280c0c000e0a0004e01c0c02e0b00d04c0796044030102d0003000c28024822222000144140e034001e003905142415461030406400b40d0b060550b50504046080c40d0406500810303a2007540300094901c800207a501c103c105115990001c6500c0c00680400d0105000da60440360 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434602374 1250 434601124 434601133
    0x110705030a080105090402011706120f0c03070911070602160f080c0105090106081009020f1f020f030403030f031a04020318070b0930030301060305090c01030b030d180b0705 76
    0x40c841d640010310b150050005640244461810b0741c00203214030641c0c0c500d600204050804900281c0b100e0042c905040d040c00101c4080906108050f41e03111005801036200348686ca0002c250444107000380310300d24003280d204d41c1c1062440c0e5200f0011b034000c00e222660040c403030046200031843d841d10b40c2c05454003c6012540da85100c0007603508ad60070080186405a0501c2c0c000c021420700000c00080c401e41e2808001641440fa100180c50000d10b034900d180c0c8083c600aa65011344860502800940a59004c4407030614000507040d84a02462001402213400705032801001030081d04040b44030010200e01d50b42256031240003c049810a407024040011080c2c09034071040b02c00c2000a002d494103100c40ca05001d1400000340c049240a0703a0701d00501955044c2c801d00e1107850741840c03810171641c8280d030f803a5a16064010000c14048510f0706080c070420768528400e5000b84502c500e4000040e0262000b0f00c0e0740c0348240c80c00078034a200f01d8003084e425040024042e00d5000a028100c0c031900142 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434603624 1250 434602374 434602387
    0x312050f04060c080108030f0c10050106050a0206070f080402010f021f0b03010b030111041401020f03281b08160807050105151203120a0f020a0906121a0f030111070503 74
    0x203003c0310441c801d00004c0c00800801400760308800030588031418902001ca507594940460803604000e0740556100e01700382080700110b5425080006070281507841e034215819035941e010308030b802c800d10340148030118000381d0100e000b40d4403418008181642d03500444200c040d5030868081c102c0260340c24030844a9680c1203282d41c5113828080d0b9200d082c01103009010708511103041150074440da10800e20401c10140120000e40d00a0013121070003e08002034980310703503400b0140740035498551080c282221040f1014039506019818880e0444221105d0b600100b13010b650303821903648126145502c0c0040c03c02c0c0d4000003484031000300a03c2d07100c5c0d000861103090464900132405090000c85204600384000300901101c00004d6031000c00f01d40403c01001c1d101e0140ea24001c00381c030281d00b02007c0c000142c0d034a600f5007118643d000c50702c50b5901d00403801001000d007000c40300c01907404200184c840c41581443d1920700582490307402c1c0180001070481e0031030907a20036603100e180704907004d070000f0544 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434604874 1250 434603624 434603633
    0x1204061823061509060f18190b0d03080703051f0305030c0d050c0a080d140a1505100c020423040506100602011b1209020a0b3408070312050f04 63
    0x142c0d500042141c1c00d10015107541000100440c8000f86100c6c0101c102c07010003030880da43c0841c41c2035541301014241c1201c1c00c00c0b043d402d02451162440c1c0d0889414040310110600300f0980e01030215400d1303681d420098a4511040303001d0017026040d4100c103d1050a00381d442280d030b01403080110310840080d507403103030011030b01030400d02614009024000d050023403850488000c204102216402501d0f60343c0c40340d100380b01300f008242e11001d580300c840f107140c1040384602d0158001c400c2c111030001030362005071b0b84008002c4080180010800000c05510003c80142401d40018200c01060341b81d010420000001402e518542110217882e1030b0301a00900102424064614018007258802405160b05000700404803035206c641180c01c01010320802d19030355400b5400744a9183c1d00802d04036099948150b6001150030415500d40c00045180c10700410405905200e48404400c10035000c0b6514175031904201900060343c10b90a00c00d50b82400106a002c03032041d18414018205030301c0413400d09042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434606124 1250 434604874 434604883
    0x1204140a0f0b04030b1909031d030601140409020609192306030f0606160506010f0506071509050f01140f0c070b1b0405060c030301030303111204061823 67
    0x1041c0307030380c110380e400902074001c003801120166a00f140480d11651038141200302d600408030008101a4603041100082590104200e0030045594039082d80c001000410183c85010a224565090510440c1d0f14280d060540000c003540340010011810011410081000d01d0f07450b040e020807a0700d01c50418041d0f03103018040081000800422200408601c0b030214a45110285c09100d003800250002016a5241e4088a116054840c090030185419160050759030101f805400c25400e44003a0120701d6040c60820389580640102d0f0342419005907005041c020425084141c440b4002d8049003022004240660b4800d8000b070000e4951900d001500104001ca001d000030301d1a15040025001103045100441d0300110300181200400500b6030240c40d40c1d21840d4800c58020304041001c2c00519000b1020754100c0e030182c2c4040c408014035071281c0c6185c0c440c1c901d40d12800508180414003240e42e50f4032800b282030314076918208800854480e90420f41410968100303d4550640000e01c5041c1840f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434607374 1250 434606124 434606129
    0x210607020a0305252405150d0611070b01150e0405090307020f0a0909060f180f030509041409010e010e0d09030828080103060c050a0815031204140a 65
    0x3010701000079003540c00420300d110f030107030010040c1c00f04008806032803400158104400c0e030000c40785d1580c290503602e01d481001c002c1c500304841490000041e40001e4041c007503900400c0018074850103094107588000091060510a0640341014051440040e0713406280c0b902034001a8200b0100307140001c00100000c041d54402400f072030401c014050020b000209840640340e049401106812005010030081019580003592517410141c03454107100303540d807103000000c80c2c1d164140502c01082d0b8054035000c909d0301005000b80b071355080b11300100744036402030b00c109640107001040035040ea441c103143c901c0d0f060f201220384da59507007100d4070304003001d100d400d943c041c5110142004035a5400302520980451201804103076000552502c101e0710f1300d0031000c61010380c801010355684050001406030b6400d010031109503107403804007201c060041c0c080d00c020340419690014580d9a4955124405001600c0c0681500c46c000010383c102074080c016002600d10010840c00500e82030b01044441c00f81503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434608624 1250 434607374 434607377
    0x60e07060903081b030d090b060a0503032215170709030803190b040c0206100902040807150c020d030203090f09060612070903140c130e0606130b210607 67
    0x124010062550003200e07203000ca0b070304808002d841e0418245218602c01c82d41500000501000681c00b101d91115030010b00742600030b001001c5942d03540740a0040a00701401181da140e48288114400c1c9003c0d80b14090910400c0540701d01c0c0f032a5030b10700c03000c4c420014044280203e0301000000300081403400d141513100f030b90b51030642c030702624644554056110140c695001002c0354600307217400031500d401c40c280e80da201410802c980461502e00035194001034408003107548040310001400d25581c000da070282c5200101401d851407030507500200000d44442c4042c1484118410b41000d661a150701c00e00701d50094010755510780d0701004200d40c003180c000781184a90340740c80c00e0245903281c200c00e458210f0007182c0038444640b00ea00081d590504194001400d43d01d000c02046104c00707000c141072501c450141c9203007880042e00c9500300181d41a0852800c1607500c8280011170900c2d104000302e0301641c6e6070500040801600c400b1810450307100c90b526891004441c070b2a684420b0800003c0e0b401643c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434609874 1250 434608624 434608633
    0x11030f1507120b0a0b030606071707020907020f191118060a05060c0606040207080c0a03032306010f080406061503091b030c0303050304020f090406050402030d0201060b090402131a07060e 82
    0x10f890000c3c01401c064010120481d40220004144d0b44800d0100c40d40e064102c0040310b00e620308240c00d04003603400500201c2c02103004c40d020405040c0001501561a04882c0240a0b04004400a1307002041448415103108610130300e910381c10749821a2214410340c050403513900030b2034800d05010700d150303140d8130481c080c0c0c10030007072150314200200c0c00c0c90f0802c02c1118056074038502c5040101d494003c03106003004034040c2c4104401090b40540c020960002d10080780ca90964003c6000c0d8005001100c0d41400300c0c0201000002403031280d0101340d4028411f200c0010219180c0614481c02c0c00d40c02000d10100c1d03900c41001042c000040803040c209458034191a408030f05503694101c4560440c88010140403003c40454210340c0d906503100100380c000b400840044c0303030500b0054040d000031f0760140d010b03010301003440c040075106000305016949234080c070318178100c113083c1400001d40c801851041401035660010500010030321406062442240c0788580302d1016007801c9007114014503800c9181c0c5d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434611124 1250 434609874 434609891
    0xc0c20041b32040918080a020a050c090112020603040201270f120302071509030b07030911030606010905100c050114190e0a08070302031207050d1104050d11030f150712 74
    0x52502103c060b19a150b001040e003007903000f65440303450034812005003041c402081c0c0421951380050070140c0341c2d0140f01164000941e400a001c030f07401d800c0c01110b071503c8103c603000025080c000d0056803c2407043c07400001c01034040c11034000490842030144400ca29286080001010140b80e00300502201d46030708010121036030b0040c1d61501c40c0d00c6000414126008e600940da40640d40900080d9003211608550f1701d0200002070003000040c4048130403036030240d01c0040d641000144544034580c10307129441580d003008200a013203010082400104010000070074001030003802004005040ca003000540350500c1100c03800c40c2c254494415008a1500010500344103000800c0140142c0003003400e80d50b510941003c034214071070708000ea5280255038051100355580400100441d40ba01141001454106a0861440c6c41540700d415841139112400b180400c0107400302d140b09203402021142046041002d09062201074070070a120000c1000802c440940c00c207901d000c00c581194010403040c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434612374 1250 434611124 434611217
    0x2150909010e060114160f0224190201020c071404021b03040e06030604030212030a0204030b0907031b081506040209030f0114070804030813110d060f0c0c20041b 71
    0x400c1034016004800009070a01075448107440c80e0300081490603c5c403441030420600417115400b038032000600303c02b15040d010a00b0700c10310076036624244510107000480d01e0300492441a001c03050001e0351041d400c2001d00f0750807407590002035a05511001841e19035181c161000281d40d0002d0145009070420b008210000b5400f0075005c0c00901c0040d145a12074550383d000038020700541d0401084000c1c0038082c00045940060040c00f10f0380310301071280384420010002c1c2484462b500c01d00c402640b000341c032184c850300103050b4560300c00c80251005040c803013100002440c0c80504902c081041e591500102c01d640345245005601c40003c1c00d11640e80c0c241035030010000d40005100300c040303421445082e0104620002e8034000c220380200310810400382d0303040070401480148040c04000b407038450f100324014020600d040485801c0050b2000042e20701c0b40e100d0b07160b0002c0100382d90299440e55404045a94032090301d41c00b4449980700c1c2101708a45460850ba1410034000c0410700340603c04610700034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434613624 1250 434612374 434612407
    0x106050909030a08071b030e030c2b02031203070504180504020f040218040608030d0e0607080c1617120a091509020a1502031207030603030c02150909010e060114 71
    0x100d881e80b824604503692002c01b129a0a403070005400305460020f02d440134968054001a00c080d0100c06682d064148007003000009108000600e014890385152600c1404180791803030512800030702600d54101510441d140ba40d80121841070124102103400c0c4601c1807044030918102811040401481c24990009041c0b8a42580118440d50f0001048110741d8131002e40b058040b00043c0c018030071280c0300c01c40b81d500c03900040030400045140c1003120303610400009a16000e002e15485203021500c641d0710401d02980300c5d45072040b117004100c1c1c1d5100000c0c460210401515034034524541c444210041c06008400040d001344280c80c20904010007040050b1100c524140e074600300010100842e01c00f1402d011045c0e8050140c86840da01c01421680c0c02100811000320039142c0c0701140e40e81d9020950840303101d4080540015103162200c0014100b4100340e6801d98030900c040303401e000101000414540098002401c0b10207140b06000362560008225a414501e0400007400e122003e0040c660a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434614874 1250 434613624 434613637
    0x602060c070204150b0c0d0206151c0503180f060a1d12060c03040606061b020411040b0a020a06060b09060d05070c120503010608060a03120e01140a11010605090903 72
    0x5200021800210f43d62030b440313031910782100c10801c00110343c1c070600104c841e00a12210794060049000c100d10300717403012801c18030a50320b04003a8914140c0030380c00c0c442080103a0713440325480192070b40003c0100d141003015018011807600b20045920031102804135010041b040140a1401131000500994014051201e00d181901b250785200300c10100140c90f00d0302c160050802070180b041440440c2405500451203140518020300601d641c64108a442c0703050002c5030380800c500003a80d80d00505d010b42140055070440c4440e0350505482d030386007401951040d481d4501503448a14210304001e200e000c0c083c01000c0e0984010b040440c01c0010070745502c50002c000001c1603a0310000b404060040e024042110f4003c120142aa01e101c4070182203903000f03008000100c2c0ba41c4000544074984210104241ca41c455000c0c0c01c0d9807591542500c0d143d0f010600b950501060581300d1155043e030001802c000c3c00300d95200507541102c1d00c800c40c210303400c507000780d0b000f6641281040365055002040380d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434616124 1250 434614874 434614891
    0x308060f1c20060a05031f050901080d0f020f03090f0402042615040f020d03092c060405041a04050a0c09020408010e0c0109050118050303030f1807060206 68
    0xc01008030340000381040201c00032040c5510300d03201c041060281c03100d41921440d800706882c60b8421016800c0000724002c084141001400800026081554070485401071954203c2038503503494507140040c003009000d8104810319070007401c0c42c0b090103501988007a54400c0fa400a0400140340742030b00c6440e846821039482c000c90310701c0c2484009803502c1e41101c0c0100380c2801c05581c03a185104880080124a034107400c200c1c4103040800018401d400903150080740d2000c0f003854403014079400d0003042200e000090301444510103000a000501469400341201604072480c0c0d030710718200268403000c1000d001240914a0801000700213180c00010301d11084d164100c2d10310b2a511031800b1440c14510b80300080074000042070000d8085141e4000d007096680340002030020004140707a060b0b40b86c0d010b00dc007900040d40d00a0800a95000340c1240307041c0c0580300038404005d52182c0109282d544161031032004000c5a000301300510300400441c150036034040c1d019081551401d64000d584103c003400f4000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434617374 1250 434616124 434616139
    0xb030d180e0708040605060405160c02011e09170d0c0f020f030a05010507030f05090a024b040c140307050c0105090307060b0a03030c081605011a151606110c0f0a02011704030806 78
    0xa581c05618020440040b140d0f82451001c1b001100034030700d03500d40c818480c086009510c4c1f03001200000c900c113024860749170380b03021f501c2c20030713407a1034a100c03060f14410790308010380c0c402c42d402c00e4906101c003102d01e074020750001c40c0320b04003880024101c40b22507003480b800c98a060103010800c0d42c081124000c0d65011610185a03010716400100941e40c04002c90703d00340b020b03036034031014084503003009445024094102000700407080d0502084c0c2d210303001190006048a1080c030b02c490180c2000e96004040d9107002c40c140081c03000c1007800c4a406451060300b9034004a14101005454051503540c40019521070341124034580d0041e00c50083d40000804400001c00e21040e003455140c43c2a04183c0c108000340f00100305030107104400c412645080c0d025400c140301d1003903860300840484031419044001568100400d850390801000c0301c600004885204000c0501a54001c03c803d0f550200f0210103086210824400503000c3d48002800d40c902410a504020110350443c2485d98005000d0b100755 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434618624 1250 434617374 434617397
    0x70b0c0711090f07031a131d01180c0906061205090a0b041208090f0a0212030706020403150507170103020118030230010b030d180e070804060506040516 67
    0x71010903049040c81c0d041245003003000f0440e0710b41e500880c05070b96161002c120100341d502582d800703810040c5031603030400c26031400700805010a602a1512680402c0c00c2d09100718030080e05402d5440c0100d049221011110407141445904090390b00107184000c0c0404c84149090400f800080d0803000500f24581e0341d4001900c0d5203014800e4450f0a41d0250000f0345914240c6442a003130060146440b000841000000d01c000e84009410070100c4610f00050908001c90350802c00c612440b4070203d0071030300040c00075500080380c1b0300103000514454208401452582c1201d6402c0320001001c803000c120b105881001c404110107500f47c10b4030340a191a40003d210002c000c1d10041441d40b009400225440c05040e8403080080d1180c0010a005280346602c0b4074060340c2d85c02d84062100c120783c03540040c40c0c5040302c00d006041140704000b202d03c100b510310341c0d692411000c03824105c80810129038140b00b00000c1103d1445003591026088400300f0081c10090b58071204c005190b50100288200000700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434619874 1250 434618624 434618633
    0x4030804020d051207081908010f050d080c060a1e05010506030408091c05060601020d020f15091002070b01030c06210b0301390f0807080c070501020703030c14070b0c07 74
    0x29560002e0b10b4aa05a170721a81c92400300250b82c0180107400c10100002d81c0312040d5881520080d0480341803040d200513050420b002c10403e40400706045800720010018080c00134005d0200034070400d49600001403848011840f002407030001e65100b00010300e023230018000351341d9590603243c0198200c10701a80300e0f0080d9011903110035081498842ea011540070240c100500021054030032402039082d90324440d1a0102a070741c40c1079000f00301110780c0094034144a83c021036454164800c5c0e03a4003c4441c58510041040c1c201d91200b101075400d0070b04140140140550400104010718807840c19250200b00800e280150107459110084450741324924250300da50250860620318003003891000ca075042c641c00360480394007004004001c029624084503112030090161610481843d111403445c3c0d641d040040710074980c0244849110342051013034501262091003e40225032090324000b5942030520409002c010b0030707640c6400503580401414002a1002c8200743e00a19a0116180c55a640b40b80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434621124 1250 434619874 434619883
    0x10e16030f0f05040b1b042105071802070501320a0213080109150504080313080706050106081005040b0a06030504080c031c0e03160b13051c0905040504030804020d05 73
    0x103a144140f81880c0500c41441080301810f4041d00d6038139442d50740e0001080340700c01720380510710a1440303141170084160311640f9034600141c0381510410603501030039216140e03000d03282c00c1060341f900807a0707010030100704010003441944514280c1e0751190184240c0380a02e145452101050700c3c0b442c3c150390001c00d602c0e40490f01964807013a00514002c040645501003e8000d10404030160303800107510440b010001c1da640315080c051908181c1c1d072450355a503100300340d8803840700000031909041c04000717070000314009110b680d010f01030941e1180b0143c28118150440f00c20a42c00c01c611032440d10781e002c6480e0b601c400c032600484040b4180442c555469081104007800350718034824140c0400a14030782107031a08100b801d049410601c080003140140b6000a41d0790156505c00c0e00d10041d100703415004210300321852648061480f42090092440d0b645486c2040c0300d203041002e182900809907003026420a280d50050202550b040226150546004094a0000c0c0001e800380e003940001c481070003414003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434622374 1250 434621124 434621141
    0x331030c060e250e07050306120a05030315010e1008150103061205030c1006080d08090c0d0b010f090509060a1107051506090a051302060c0f06090a0506010e16030f 72
    0x1550710007081c41544107100003041901141058444001280245418508500174078050740c503e41156154010b202c11800c034800682c01c02c0c4148002100010000c100949c8103013000c50300100300760b0202e000904900d8241d604288103a0000340039940056102160300c4d030001c0c40c1c0e070303c1d054200c0d52b100043c1d0041550741c100311081d2040b10030a009122001004210040d41074040f249041450440e5008031202c50281c40c219070824221503021a00c240300c500d800c0b4104806440e00511504e000071003000200c901102c0c06411100100308488105140600910030000c0900451900c08032403038442b60010154507450b42d681d64110340c0403c4820948103182d40c0076080300c00c01c2e4201e00704ca61819008a844d0781c460703c4400c000859120440c040c440c01070504019441ca224116802c0207140d40148200c0790162280311401707440010100301a80c01222550301030f05200c1b40c0d80c14000e003010016001190382e043c4c15008e02405201c031801c9001200c3c800d1500190349108285150094400c90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434623624 1250 434622374 434622401
    0x41109060f0a1508060a1508073005160203030402120f0d030605040506040207030c11060f0406080a0c0302040e01030b0702100227090c0405040b060706060b0331030c06 74
    0x355001c80e521280342c3d81008010a652104509540ca10080060320400b03400368140800c0c0c140c51858040d406490900d41000c03a900f049801803502c0c005444040152421030800c040b004c0f042d87d001c61501d40310322500514002508042958500d83c0070b9564800900000e0003013141020400111100f40b1020149040d080140d40724500d00e040010080c050324020075100d103150101181c0703d450984200d940f0194183ca507100c80c243e080d1100c0c1d0b108040c08080e507070004000c0001b0409403058034010f0000d04600d0b29440f1040c14804078030b0382104d501880340070503d48100001e1096861034412641143e5101e403500741c081e5035003e412402c04e00940380c0d440850340041244542842c00d02c9004155200d500fa131043c00c10782840400c00f000c20705940700380034140e0800043c070043c14240c01c0f44545c5100508030350301e1700e0065510041220025070040003400350200c2032103189100303600340f42d000d40200e070380110410003134088600309418018001418480e00405850400c080382c0c10104620484 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434624874 1250 434623624 434623639
    0xd02090603190509010c14131d01030303060b1201170f0d0c050705061321050313050306060102281713031e080d0e0a020a0303050a0f11190c180209090f041109060f 72
    0x30040085000c027000c1c00100d000c24205000420039a1480b010780d03189402d1030076400c91a91900c0b003040000741c140061416540030b100e05c0c403404c4180c100915909035001356540d1120450904115050082c0c036080580710f440c0070001d251140c0c0681d003600302030b280040721100e60a1489518541000080880100a404082a0320403140144081e200440c1c10990a40d2515507038407004a0b124248076480c6500704401c03e0005007075445040c0b04c0e005462069201d41e0640e510100c800d001c2e03802210032081c443c84508030a200b00100007481c180d0701d154804100042000c2030b550000c0b41c0c00390282d40c11a042d9500c2110307204034820030501c510145c0180403084440d0b164100148640d00860910010421a0018a201d18810241009440c0d0528007038000c0c003059440304070130303118400790640b07224004260225810a40880b200540c6506100040e51000010140304500100034140414070900004100114111502c007040680088681d818181d8617500007540100500c614540c00103179 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434626124 1250 434624874 434624909
    0xd0225030b0903130e0609010e040b150102190c080d0c0c0509040c03020d0b06010e0604080a1101090308040909051009080a030e01020f0f0c010f09080a050d02090603190509010c1413 80
    0x5e21040f454060b86042da2400e030755a8981c8201c806048082e02c0040c1030128100000d003444141100318091401705205940c028046441da001045050420603503c0c2c2030320250400140c6d404010b00c02740c0c4012030a000c45442d0f603035280e00e104c0407510707c80c0074080c8070b0342070004007004840034006000c0d60340108002d003160f0700740c1018001c0280444140d4041215072402d2000351030090700b5103049a101c00010b000e452400d40d41c20890f00700202110341480448180030001402c0d01c005040a0b21916400280426450400c1450304200081030f990345841d000010012400540894445030b1179400c02203084010337003039401c3c024819418907a80e126404590340714900b071080020501031900c8402848102c00109001080313034800307100181522001c2260001c800e0192020b801a1144140e0050074400e180010801580c003c99180780b1600b030850380c0304418030041c882c0c2070301310481c070000700941e603005000a010b0000386081c911100d50049134070031507004074015140180244180d031000c240e2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434627374 1250 434626124 434626139
    0x11202071515080717030c010c0c0b06060a0e0402090307030204020c0a0605091209010c0812040f1208091f0b191703090306040b06210d0225030b090313 67
    0x3540740888103250341842001e0440000003070510003070303a030039002518005162049103021000159040c0009000600038212038090a2090f10f401d41e03004d84800051108030303c0c0440c003d80008291a12507101400a4514243d000c02c00c101e0080c42501c2c0107039a1910040001c1c03038101650b1009500c9800015603c000d94408941070701d0003881180c0600403501c1d40b03075072552503c07003410603008503c0c402c1c040c0c210a0b40c0b00785c1074448654020480303d450110030280c00034007010200c80980e5101d03004100c0404001d1001c491904180d1245800c9205042040300b207901c9203a00f545400601d905e00c2124a0184040d42c40460b000c280180b1040b0050070030701501c0d400e03005a2080d075491128031200b04081100c04011102c2f1404024050003159941c0c7e911001007401c058010382d04100a544682400b2400100003e01141504001c210394110003e00900c1c0c48120741c200f038080001c80d0b00700c00881c5481010341d01074a622940f02c00ca169503000500c2e2640c01a01000c1d01581110740001030301d070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434628624 1250 434627374 434627393
    0x10e061b03090112060e0a0b0114040621020315241305150313060f09020d21030b060f031f0311040b06070f0b0406060504110405040b01080408071101120207 69
    0x4000a1302d5007940010b404c041c0d801100c8261261203111001540001c00685255100c0680c000341410100c0c0250164403010703d9680260300100d000c40d482008042d000c595032507c1388054503034004c4c19407841c9042c05540348888940100a030040d00b0780c0c510040040369901d40d000c0c9401010b001036440b02c22110864203001060b04c03545000e032240c0584200b609800780122841074065003030042c041400d542c2c0340c1004210102c40c80300c02e140c1e02c40103000183c0d214100d01043c54040c0c030440600d0aa140003010070100000688014103203090380705151521303000c0a40303084041d41c003425600c0c6d594030441403466007041ba00188142c0d08500f800b208010380e800303a0012003a010340d0f007000000345031414004188035410018043d045100940c030000349051110507806840b58401068556842010406503a5214107801440f0342c0820188518242131041d80040c0100340307410202341c1091745800030248225800600450320308900040e243e4000e500703c1e00100e005000440da070b40700e1410005c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434629874 1250 434628624 434628637
    0x2d0d0206060f0103050403080f0c040f12020405010e07090b16020d1b0918020f0a180b1f1b0c080a0803040318051c0302010917070308070f0e010e061b03 67
    0x42c04941ea959480e55109100d00ca01c160f615458540c1e90391141c2c0c000c0e102c44840141207644501003004040745401c001d024103401000400810002a0b2892041100380c50b016040b00c2c46280e40325003040b400039884001c1c54101c0d040c02e1841551080322000070141e1980c4000081d4014032118204130401042100004a0018100c81c181d1125254203014080d625000e001d104019420402040903203061444d10744d00280080003c00c8440e51006c032010b0751915222200200c6a46003080c52060410300d07003070500c427010340e801c2c040e8822070f81c100034000b00d1300d08040d51400880361500100b002020007192015044080440318000790740d282c8030195030300440e012400105903051a039640c1c0d100300c1403102501c0c0000e00c0e05408502e5507101d6111644201c10079401c40d0749a0041c3c03008203144008940f940c026a10010b90b892000e818098803295000e0000001c215840d0180702003264400d0702103040c51800d203001d90146080a000036072902803820481c41c010429001110310ba600040103241 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434631124 1250 434629874 434629879
    0xa0c0b041112240601031d070915080a0314070507030807062f0307140706090302070609230111011d0c010c020105041403070312050406091202032d0d020606 69
    0xb01d401d00c61a494445502c0b01d2030071064100e011080400750684500154852810700d400520016034581c190901943d09003078014a03002080180400e850703601400c0d02c3c5c4c4c0554145200620320b012005642c410301c2040c09010050080c18a040213111542254500341d0090200d414440d140d06280800c0d038081401150f00034901088800044410044004c81c40040e110041e160a100100c81d60700b580000c10040030040c803003043c240030000c120040c1a036140100c0b8001662642403501030f250200c160000400d000c00200c08201c880b80b101078021560700180400d9000039048401601c0c030131810441c2c00c8265007400003500c0341e20409911380340c00300590001c5521012140b401900d405070311100103400194200421300c280d10446000c00e80c0100003a08556115503240c8500030802c10f1694554006200002c00f004883c0c0e200b00040054019480122480c0c0d00581c00613a485002070241d4200304c2d010040400002d1800150b402c0803502c5000b502c1e050404084001d4681da000c079030052 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434632374 1250 434631124 434631139
    0xb031b0a0e010912020105032701151e0b03070e03031c050a0b0a080d08040f0f050a060506041b080907030b010f180e06040308130c030c080607020109170a0c0b0411 72
    0xd410740d42090f103003100d107070180c480e40e2940c0c9400c0271b509141020070000c1600340c0c00802d200200c441e024072550940c2a80030890221007410290080000ca0f00b110401a41d006112003c0c080a0191001c07660001080d04000b501e411201000c20f0860241070024503c2003054900580010596082039124544d884030410001424404001c0c24400501503104254001c440702d858032402480306507005070040d4614066010280ea89040040d10342c001107030b0542016515208001107801942e40004007280c0601c500c003600c1917100980319081d60303544100654140070595051040c400c0c1c401541c2c2181d050b00e59503840b05840c5405032100e00c00c400349104070031a07084280700d1910a000e18807122101602403910b4545040350741080250035095024440421900010301c00000c070001588241d00031704440e413a2000c401d003011802001a001d6904028442c800200d0b414040c007154192081c95540768001d400341102c4c00c1205910040401c40f50303c2c2400284811000d0314807a0b0300040305c407203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434633624 1250 434632374 434632379
    0x10b01030c051b0709092a05030606151c0e190b0a0519020a0207050111061608070c02030304032001090815060f0306040b1812040b031b0a0e0109 64
    0x44044410300842540041d10910000000010b61051020100321000031544c04075250303001d0008481342990210b80c1c481c918620358900d520461203482550fa42490340c030121314501404242ca85000410851044041c000000603000d0742d401503039512020a20022012082000320700001d0441c0c49058515100b4600103081c201882030180681070703409240d600150712042120070161101400c942a442d0102200c00090002c603c080c000440c040e500a040e494500000076102c0d08140c9011350094201c2d43c20000203000c100c099011800c0ca070302c3d00006541e112101141c410051810003035150000180000c20320061000d1203203402c91200d40441d01c2206140150342210480c8034190940c1c101c034a280c0100c90000411580c05413010300b00004c41c03103c1c0d90020303003449004c4400300c45548201d010302a11407006a030101c400402c40d001004c0e0807000030403d1030140900d125640607040c0000029441e0407541c0300c40c119650890f0011900c5040000f00946042c10b001c0003280050943d0200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434634874 1250 434633624 434633627
    0x708070210110f090a080a200a1410030e0d0801080d0203090d0605090c12030a0206010e0c0702150c0109050607021204030c1e050a0f050405060301020406020d05070c1503090302010b01 81
    0x3520680550701d02c0161400c01111950103441d0000510250300a105a034005403900f0280440000d0500c600710001c44c4800581e0311150803150501c404d4026914180c091021a0112005200d101c0003158004c0d50244400011800340284c0030304a5018001d150124050725080311280d41031790f101e03100341d8016500d0400201c1e0f42c0d000e6640c80d568084206c00032100800c0f9240c2c440713034120500106403200c0700c41c40300100f01c699400340c03008a1140c0c4000f07804003440380d05000d4940500041042c407111801c003020700c0407042c0100c0002034401c110800d000a0090303140801c5440294000c0c00a11913031101d801d113030740c072004200c4100c005400345081408064804030102d5055a13030203210110900d0a03c40441081c280385d20314060b10711295071010440c3e540e08081d503c0181070503000301c001c0c0342c184801c2c881a904003600080c0240c0c0140f000f84500354002c02c21890000c03c504e003064440c01a82800b88030909a0b90003510100c00c1c40f146075200a5041e04139800382d5010350001d02c41d900c0036900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434636124 1250 434634874 434634881
    0x7020406240207090e061801110315010f020606060933090907020f03030a1d100e010f1e0e031626030f010501050a0c061a09010b0c03040603020a03060e0708070210 72
    0xf1034003501e1b00600c0004880c032008a0200741c10312410303400068255480444080c06074001d980315288089003031048120303503900049421443c03e03988090811ba007080408240c1c140200c1182d81d01c00c1400d00c1d588508a80414000d1014802064a1880044001d03050790290b50051034003034000e00c4040009a6643e000041480103218920010f52542c0d40e05514034000b046403089000c00182d240031401c0c00312804100040e085c0d05030b1807001410341c0082c40c1c00d0742100c61400240380c1807814048070698606c0ca1080001d40308140032008503400c542c0c04100d41c00c3d40725918881e42c2e036a441e20105014000000b001504c580c00681401c2c40c160307580d01507000707180800c0360840940013482006102c00c1d481100680b400d01d8650a02c0031074401e19a031007009550110004030515078004a4074a00e0385404480341e40104010340520f441c0919500c9469100d11584c01103406040d000104c04004c035102c1d0f40000c0092660310346611260a059070010308100d000e4502d41c00611034122a00c211340789a21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434637374 1250 434636124 434636141
    0xa080405040e0712021e0d032012042c091f05060303160311010218030123150d0b0c0a1716080406090c1203020d080601090b0702040624020709 63
    0x15130b04100c4040c2c0e50800c44014254000100d6014248141342a580c0795620f0f241c07403142c13103a103031842c910320182c2c11031105000c400f1220400c0d038031045010707100a00b80d404690964030300c40d121702e1607510003c041007400a100e40e2843c4615210b6020044400d9011403080240008a04400c00b014a09411202a142d0036900103606030002c12444522860f04a00364101920030b04141c0352030344007207a1007422a044400500c010302002d108000f260302c1c0c01e10a061054000080703003594070200001b815194100204444256682c407540a0300d290303100d1401d01c412680c0f006070f8440903c0c1c02d0401c290650803251000010030340c0040c0289c01a601c0ba000341d4801c3c8010641040301d410300140440e10400c01910945030280d0314000780e4041a25010b5120191082d0f41a01c01d40c01d04514000303142482c42084202044411028030016a920036281c00407501d10303030041901c030b0489000140c02800c2c1a40b00f40d5002896005045800a6181c004480d01d0301540031380b4031007540d0701e800300c00791080308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434638624 1250 434637374 434637389
    0xf0105090f06040902030d0c050c190303180305030a1115012301030212070807140309070512010e0703110f03010207020f0d080730020328110a080405040e07 69
    0x10300140841521118030766100400802c003083c40006074010900782038814410100151103120814140801049904549803080d00c003200b030b49809000520001c241400000d040050400c030b1814200607080c10203014503003110a80b80c2c4c8409a00000e4000c1d2210b94001c8807038003500c90303d41c50106010a50394103c80000f43c04030741c081004501104250400303003916040c15402d2001481680c0040c129503c100c0d000e86030012582013201c1d0241101d1688010346204e02c804100f04410000b020034079108a03270080d41c01749141e00c03500004501400422800456034801e481000082c040980c0c400140c1000903902c05091250b814241070a0b4800c114001e504006103081c5042641800c100224507035008401042c10300c000d0344d0710440780c0d00c107449c4902d21041e031151408100da19045051410360b0554001186000c15580082c035120030880e141441500009448440c150700400604840451038070a45020181a280030403098200d401403e00440c58112080e418981c000385039020358141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434639874 1250 434638624 434638639
    0x1101050a1413030807080702150c03040e0709030803070206011410020a120309020d11211c021c020f0706020102030402060d11070b1602061f0b0310080d0c03080f0105 73
    0x41114894256200306803020a074000d925000011a05510117081c25520a24009903908010700401001480050700d0744107008003004505480e980001c100d90444140401c004401c0e690203405440104250388040c080b48800020801002d601192a5045c2c3d11080262600e503000c82c400d0203510104060500056402940d1000102d0100141d1003c0700f1180c2c5808510100558040f810890340722104460ac8440780200c5402407511400c003d109072800f45220f201c510072110300b10390790454a080d82d00c04402e440c00351000e0310710910240940707802c007403005880107018003030082d80e82620445141490054a401003103007072060007140d01403500240a141042440f1754020010802d84450000f40d450402000c400681001e212600c913014076090710300140014207010f82010b03002000008807070300450600501ca460007030202d0035620040099612661444c04206100449400450991041200d0080b0055201d10a8264140f09544200311502d0340f6032411034413442070195907402401d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 434641124 1250 434639874 434639897
    0x50403060b0a050301110409050a090b01060e04110c0703031b080906030a06123813051624030209010c06090516240e0d03111c02010203041101050a 65
    0x410341080c800301c01e004210b034201c01da03202d00083c21250100c40550748840041402c000000075031207201c0d48030b07001d00c40607c0000d01030703500d961800d8014011030080c0101c1c0501b65650ba11641d105501c02d5400e2a0170342c1e900c921202820303555500901c0200c0c0080c03100098243c140441c040c05101c3d0991142105042035590401c014031504010301d05030741c85a5074076000030b0340750000500140080c083c40d080c039107070141c000c61060306440765841064207800c2c0f00d0140340c02d156040000360b03001075070340f64452005400f80f502c1800c1031502c50440340c81000c039240200710340c114001050448020311003218004212080b09409902135036000d1070210320003005036400b10b02c990f001582094810740590b11004541036401c0340c03482c4250001f00440e031108641100342401d008c403401030003e150401458400d6030000241900c1c3e4400c40040401241e85411a071826007005503040160248014450341d041c40d2200034000e4004560640c0c49141c0f4024004080d40a001200c07c1e4003856a101e809814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 434642374 1250 434641124 434641133
    0x4090b030c1c031b06020a1e0f03020a0c0c180c020a1a18011d010b0a1a0c070b030408090405060d0203100e1c09080c1008190f0e03030403090e07050403 67
    0x30030500b002c0d410b100310810560040e000c5030b441226a03500c41c03000140c1310451818006c0c00c800300308044807004d401c1ea000b01c64840d5080003002150f42940e1802581d51110f202003101c90b0300c0c00d400020001c0070541c6001c10021180d09103864010b00049080100d0801d901080380d94800041c0c0c0a410400c92f120100b501380070140c3c401d940f068409459551088030fa0405c242100e0750003101710747d51000e0401c080c1600d8000e000b0391035002811140d80c10030600300a0780400c40c404076502da0003c1c00c4001543c0d000a003090001c1e20050041e0488651a803409050070310700359001c400c40f14455403070280001e58918001307000c8400787e03401500800f40d4034681c213003060043c00d123a444100340d482040b105920f415461002840140800d542e40b5642d90702d055610742c905010051030b1fa00c201c07405180310b4032450380800b8150703205145116500501000111203401400450401c5001d40d090081c01c240300e010000096000e14801d680c2c50f1242c5c2d58410f075003160240140d8071080019020042040400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 434643624 1250 434642374 434642419
    0x405040c1e081e0f100f0b09060304061127240d0609051003150203070c02060a09030b0a23010303050906071a09150108031c0f0b0d0804090b030c 64
    0x40c0e200c096188000083c40011100140840700124411220300030000c0c00070140b21a8001840801d0307000103000e003040201060307802807a000354010a808400542030000d1500681d552401108005a4560a10300e05c1d5108051801c0c98451130013010101a180d400c200450900b060f440c501302041d55510721030201119031041c401c6541c0e8548942010562500b18810140281c00001f00446480c1c99868580e98410000040c00c2c0030500c1072040000d0980c00a428088003681150072681d690505601524007015a42001d1310110422080003510070059000c61011800e26000e580c910907a84011f44141d0001d0000070002081407080403058105003000d0031700d0031700c0b508810211151000c050500b8074012a1108801c0c0d200c10308142d1032040740380178240501070910182d4985918500b005080c0c000c00750b1024011076803007020310003480071707a0302c1a0b0000f00010700f0340e9030b4120582408203aa0b0058042c40d075440c0d107042c00c0801245000910500b52600180284480a1714034400400342c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 434644874 1250 434643624 434643631
    0x504020f07061407121a15120108100b03030a0909051306020309060f010f03030e01050f0f0703030b0a06170f1815040c05060a0c151b0201020405040c1e08 68
    0xda8005200880008155004000b2028410340c411462807a00180003002e01040125000c100c6240c8848031402040354080e6012000d02560540300c0c0d003003464041c01d058416045441d120003901e00010400c1d1348041410190030351312860074000c5465620405450707100d12079008010800c10b0f18208034a00b0070340c0200d43e02800d00074508841c4012501c0300c00680c0d0044600100381c0c0c10000410640b2400c030000c4902401801d010f9681550031543c0207000340005d0081d0b24140900801c19488110b500d0702150b02c4000020f1506849400701e00d0094090a01102e0032442507407032000200e00d0030700c1502c40c462003444114070052540c0b80c40541210ba124050110b100f58407a07120040c00b103076810010b01d50b80c911501c40c03850061802d0f00b03101c944481d1070b0700308903c0340d50104566602c543d8004e403030500c030a400c03080760400340707940b023082c51300134034011004161701c07041c03800080d5805030190302400448109130f80c14820b014240b1021503002d00222110044205880843e100c810700c00e210b855070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 434646124 1250 434644874 434644897
    0x90203010b1602010306080f07030b010905010803040e06130c0e011e0f050c01090b1905090303072703020a06050d0e210711150d1a09060d150e0c0901080a030801050402 74
    0x1c02503242d07c1d40504200001d800c040d61940500000c10822540642d018010130102c3c00c104541d50401010b1038803407046205d0070441030f1010011580e01e80e17401e0155400075602610800040c01a80ea002c1c084e032803244440c0b804980b1008001c2001c081103030382800303c000c0c96a14914a1440e000040c0d80b29003040703120101071340d601d003200800034010f0302085005103880c82c0d041140d0703c900403080054403402081800c86030000d10512a00395080103015104a1203504080104810200340c05624030150388017940c418031010001801a4110004145003103102c0800e1150301000745009640b87d050711060281680703074ac05444c01520b00303030000e031030380343d20a01c0c1e6480e845090100144280100c10441e41004900040644107050503128501101801001c2c81c0c142d21002030020345840300040c40e55016044841d5080100709160039082c12602c00c2c1c4004100d03240d01d0304215a51880004941801b9455400012904120014031446032a61544d00d408041e82040140301c003079002080c0300034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 434647374 1250 434646124 434646131
    0x11090601080606130f0602030301240801120204180b0901060e06150a11010203070f17042d1b0602011d25080109110a21021c1509050601090203010b16020103 69
    0xc0c4108001c20185c010a450340c025500e07541010209600610031400c1030803a44c49043d1403107141504031070b440e411501c0300460f1040c006400d0011902a29150b46140c281d2014540101c00308400312800d2801049024005c0005c40c0c4c807444140c5000209582c82540609040d101c10b00c00381200c0011300c082c1015140ca00c8115500034442400d980080e20948045074240c0700e966110355010000200d9801414914056420180c481c3d20b042d01465800c606000f9034200814091802807a000711107550149818a101c450892503481884040c02000b0055003480040c0200710700042c075541c2c54079109405402c2c04ca0b00c0e21b00304081851803030000031801c142c800300003074000e03028451b824125004107240c607070120140c010000c003055140c00100102480200c82c00c05944d5009001c08034a905940d104012821816410a10380c41310030300400e142034244040300d040540c0d401809119202d070302140d4050f45c032404c40400764002405040700c0e840c03090003411002ca0807460602c031894010f05000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 434648624 1250 434647374 434647379
    0x903070203061302031614040c0e130501080c0a0e0f04051627020a02030d092d0b01080a0201080609070908030a1706120309220203131109060108060613 67
    0x10707090840480750b0502e03850340f43c0c04040960030180304140482014400002d80300f414816011051001044000e005941c1c44d00317107802d000d01412030f0381c10b0050b00403d1146501192812540900b000340580540d80c012080005254201204100e041d60700b8101116000d55601d5905442d40380000c1c42950944a6000300d014000120340040d006000d007039808204003200c01c0120b800030541465050801c52042014441300f80e400b20541f6200c000d0482c001c61592407a0425100034610105076130a5002260398031150700c0003010038120002c3c801c0c031b0f420380540e0343c804185841e079a1440c0c0c049c0c0444c0f9100002400ca141c081340c0c01d9130204945c103041c0e01c03042d19102e0b407620350307008440a8400300d50003040c1844042d011104c40742c2e10010865020b4280d8204000315901c0b401101c0040c3e000c0d0165003400c11403440054800c44401c0ca039410215220b01d01501c0b0101c0c031125628041e01c251101d4142034415041180405110f0241031f1103182031030f10341100303000c05540800c080c500002070350b2101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 434649874 1250 434648624 434648629
    0x10b04020a030f0c080114012016030506070c020d06020a0c120f0e22023a1a03070605090f06040906030302060f1902030705042d170c040509030702 65
    0x350501c8a05607400141110106101104844c003154544043c4504840100610000895506000d07107081c40c0042160064500907070382c84910081c01c0000c1c1c0211110003100500003881030045900540403210340e600c80d10b20030f0310fa0130000c40019412441e2103002c100402c41030380041c40c07918410b00e0a0030506489807110614031100c2040d41d0300150300981c00080881e40804a0300407a002207070f01e002c81075240321486c050f88042800460843e0b130041030b061524500808905039400b000c84111494401061000401801c0d0380e080540103403030150210140040420b5400200344060001c1c00c2560510409440a420070704085138040130040741484da98403002c0c01742c00240602000858110300354603010b401d11030000c1001c41a80b415408100221012803014801c0d0380d0810300c01a5240c4404c8401c03246441981c002c0c48460410140c0d21a8003008007032420052001c00300c0003030545407100c07500f4600103070010071000c041d8401d04160a503840c1a50103107070461030400c122031401b0000e502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 434651124 1250 434649874 434649877
    0x1c020607050f070204050a140105101e030b09011701150302060702011812050f0106080a0b040b070507060e0c03010e030c03040605180904050706021506011d0301110415090b07081b010b0402 83
    0x2004140d41b40c0300c0c001004070480c0b5000090141502f15540090103414500051500900d4007410004050718050100a40d00a0703124050003100944038034401d42e114000200010400b2183c07040c40d6117840d005420030060030a00c442a282d00905451604e8119001110145200c19440d01d9284c0400c0e400105000b10081300c0d4070541c4070b0400380c0901e03007040080d242142d109910807660b5400c00d501580005801c0001680d10650200740c2e4805502e0744a0101c820b406103100083c500362400c2c2c05040980d1000503841c004500440c024450182c0d600d0616403640036034044d041d00b0398420712060102d6401480988140401c1c96184240a03100b1400140c1054040e04c040d503564102010602440d03905100e007050f0f181d0300f107445248a05120b00000c0a021341800100300825104004203a035aa080d0820900d1109a1240948440d1035030058100700c4e00e1503a944001c036041d0100040c1c207000450030384050942180849091086514401940c0141105921041c2d580c42d160301501d0741c0c1c1c0c1d20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 434652374 1250 434651124 434651131
    0x5040e100512071d10030212100c05091e101211040603090312150e180d020606010f02060108030301060e03120309151e06100309060608030703021c020607050f07020405 74
    0xc0040055529002041e88034204084d041e1940001640c1000600201210590b0460350f060701c0b01840c400030780d840c080c2441c0b01d0300c010042c99810b226006c0300b41d90f40b01c00038249008045400d107071580424810000d140c4503624166070081109541480c2e1640500040c0304038001042011a568600f240c04003616032050304140c002ca941c581c030310402d15610580c90080100318039010003640c8480881200f420300c032807240d0b000004421000500c01078900c2310311214040c14504461003d04046006521141e00f2100940062612441080c000b48001040d07412550000082d628590800c0d504035031001c0c2c4004103d4041c4a251200e41c03820540e140254440c6100701c002c1c1c80c040001c2440080700e4a0054400360b0b031950107400c810581d1002040098000c00102d070ba12040c141e01840c2a009400000d40107806d00c1d1909000064000001c4000c0c00100e10039402d136800031000310003824a03120407412940040c0e00550020310141e00403002440354981400301c0b04d04040140d40010142c0328200d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 434653624 1250 434652374 434652409
    0x503120103110108010303090b070c030b131707150c0215040c08100b090f0711031809090304060f0e030304030b151212091e03071706070c0305040e1005 67
    0x660040061140d00701000340240c0e003d190850440d45141c40040c003404050289074154400080c1000401910b00c94020045a0182e084442c80c680441005076108106106460f070060001d404100100c5013401c540b00301d03034400b0352003a2040d859002c64004003080b0300000154410400030310316400d24450554072070392041810252490400644605104c2441ca008410606094400456030f03074550030658800103e0b000c10096942d06442140d44640341c640d50b82e854000000c0e0309a405441000303061700c1620560395030615072195514543d0342d00c01c900c00d00002030382c0c4000c003c18681c42002c040d03104040003011179050a0700c0392503101c81440159040c1a805860790142900350070b2200604064100d04805040107102c0130425441ea8458004820301c2904101564905007400c0201544040c1c005411140a07a03201e6081c12004500301035012941d21420002404142c0b20f40f11056030f11381d06580e0380d424580b82c428100641580a4020040b1000c1141d02054034cc950201414540c40070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 434654874 1250 434653624 434653657
    0x120303180d08010b0403030302180a0801061a161e020907030606110105090c100924140403050712060216151a0603130302030d150e0601020319030f090503 68
    0x10190281c41c04584075214014014140300400090030103405903401c480e014100960b5900740d09d942c001040744140303199a40640184030200e4250340543c00442621204401d025505540c4039016003640554203d0b40d05400c0f5003030490b40028042c00034099601d5841075105d00c044010b9001400010080764850002580c030141040203543c070400c41d0450080fa90000c00080c10800d03002d0784ca84c4514503080d03001d05220000400c000d481111a180100000f100308456100804841c40150403092041d80024071078521003405045a00100c03000c4030f512900a2120516000e6218611947c020040d609258203000081c841ca800c1c0107070305106407140107504622524881140304a030304221010b444400403100e5000d154071448104c0382c1001030071000c1d100d120400c0c0b40c121316501c1290511075009083c4410311602000303c0041030b080d40c090250b112440e40d584401280c1e20b005240394000c0c4070307032082136104615010f82d02050400d04443d9010403420b4540c0c980f14030b1a8040760f100301900c1e11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 434656124 1250 434654874 434654911
    0x4091e0507030504020f10020c06040902031501051303030c0809060d090314040509041112030d1e0c050d111324020105011a0309100f090c0603021e09120303 69
    0x115110303040c0e2100380790030100310303508064003c520342454158100c0d001c0c2410040d80400789008011030050350000614040c0d4980e01d0344401c0000e900203a900919030b802848000d48951f00030404d0320086400112001a15899901c1c1141c0d501540b0340282c4000e14100b00080c034a8998800070007000c02d03206004500d2503014900245040084420704480b500144010301142d0344002c0801c1e041038000c03006d51103520071301001645400450600700414400068801c0d964101500418405200300c0c1402c2b0402031a0140b001c29904555850000507070108030b41f06600c0c500e070307104807880b902c200b21317450500703281e01074800e41102142c108150100b5020412400300795928600c040d1581e05200a0000b945000d90001e4020030400444030600360110004003245d20407c401c070100d901c1390a06118001412051400814030040280c903401c2c41c1140114050303009008032901c0c040c0b140010040700e901d10301640314a4000342d55050b0710a416100040c40000204091800341240c0e840c2100280d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 434657374 1250 434656124 434656181
    0x180b0307020709020405030a0213270309080a030e0d0606031202011d0102070201050403030804060207170a080a1512080702030604083004300f23040303030209060409 73
    0x60b6180e00030b81003c0d0042200744000d85000c40c8424a00d0341c1503508919031f818040000000d07000c03010a5061101842e541085140003441c2d03103031900c9002c3d40715010071a890340800c5884a1000300c018000c038038402d000807102d0030035034880e000c213a00440f80019003603140e503607403540800c04003803100050307445000071400d2006071881c40005101483c021468480a0380c0003801a00507840041c090081e10f04c0024144440c640444020175071140519060f616a40010f004079042411000b000032100d100151060100c0c1c49a510f80086441d079089001d85445a00504560552000c0f113201406001e51300043e101084554001c602c51101390f61558080d000000010004203c100e0203a1011b0042192075a080400940c0060f007000003101c08040d540030504068655184101854001e62000c0b05a41c0d0700c2001003001e402e41c4d5642e42d02a0201d8619041c41100541050307084c000e0070001000040d000340d004008285001c0c0006041613510210141151300000e1000052541c42800c0d8030110b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 434658624 1250 434657374 434657383
    0x131b0f050102070f031101050c0616110105100b0c010e011e0c05130e0402120a030818150c071b09020a081e0a090602090312090a05011716180b030702 66
    0x2400c0a1004010040c604021000d81050b2031202400150070014070105a0b4800e004860031444038404542040c00c009d100500070b6081030085100044601201c4e008220341030045c1c2c0c1c05425480b9540e1021030502c9804070417a4081084949190341c1c0301c009141e1440c2c01c3c003c0b21000301080b003440404008004224040c1d5a04084c00401c10000f004142c2c0121b186090031000e41c0c1e0000c1a0110b03031344e55840458580b86121121040c01d00c40c694101041542c0410030a01c204041011004c46c4a41d5249071036494090a210214a085050004070109251005084124002c10300c1e2140300b11504c120740006d047d079030031019046070001044104aa00300300200d0300845030140140014940c0030b035010781400040d0480181e01d41303880e4200e051040ca40c05650903c88000e040d1580d441c0384603118105d40d07005a00d80d50041403480c030005a80d600a10442546107005510f0641c550b0740c4400310313560b42c420341f1100d00910060a45a032801c0001d03035046c01c0070b0148071761010f58906000e400a0b140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 434659874 1250 434658624 434658629
    0x100f1e030b120a0c1e0e040602090109080613080d150602100614130b03010f060f030b06040612020105030709080307030908010e12091c06050a05070f08100e131b0f 72
    0xc543c026282c100c0080c0c1d58242c818100c50340e81c0300c5011000103166514152607102c1c0e02048402500c141480203000e03407940100608082601d0b94000c082e80c4005407911030504607052601032845101002c08901040010079500300f511300009411881e2010400d000c0c0c0f6039410020059110a201c4000340300c1c0e40c0305520207814244001284001c08200007416000165810701241c1e840d1079402240d034030250040110b080014900340401502d4070b1441034024202e00c4141d6240760604081500da0801d480f920003590400496900c2a95054006480304e83c8040c0c10340c3c3c10455125000201d800c0f090014001e514802d0756540c08003032504020358207480d012100e0a0300340d0040f00109144010960848140180030b58982220445900c4c40c03122050241c0c0003d841d8500f04020000d000200b684001e10829498503120071201c000342048500800417901441000741d00e04061005001e40b20350594007840c04001e042e82c51800341c1e5400180641c1680319400c40030f101405002d496250841d1501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 434661124 1250 434659874 434659909
    0x12020612042909060c0a0c060c020609120c10050603070b0c0309040f0e0705010f030b1c0308090607050720120703110d151d070803091e100f1e030b 65
    0x4103042580080d504c80b003001d451100c5052000402200650151030401141c03a00143e042160445680c0047d48844040307a1100146c000c0195619400d29281c2c00c0c1c5800c00540340007840080d1006201000a0502400056061041401c009001c0140c84001d0040c1c09000010315103c1558905100a4070294400c04803024103003104100029000030b50501251024a8200d040580d1890203600a10f0a0810030340c01545090005460013000742c48030605610990350301c2c0440e9280302113075846000a0340c6040008030100b110f8004104031400d00c1c2e810b1184103406465440300b4100152403203e40194034246a0030040b820402d21240c000d18005016090341c54031120072450fa42d51a171417808508032291a5541c83d02d400381c6805c0c200100395000b90702c808480006854885541d600c1e0000301006210350080200011800341490710030810080207002e260640046003400c0c0e90301880c5a442100708010f07000b042c840c01d0f04081062070000341640740051200e0400301400203a002d00141c03110b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 434662374 1250 434661124 434661203
    0x50402160b2a12040303152102150c0a11030102041d0f0615090405181203090c0d020109060507020f04050a1d010b0603070c03020c041d0c100206011202061204 70
    0x3c00100d1a00d4260303005901d80b800140740204081e001e841d0001c141c211800c1031041a01104454601280d40c1d814180202c80300008a80120411031961003443d041c0180d64010981d0000011020007400f0300a4034018000b41c00c003038540c100400c000f103604d0400304044a914041c403c2c120580035609070416402c0c0c0c1c100c0145400e40006954901c90340c41d02c0350040c0d554500140580450860464034840800141e507044803138411b0401c0ea503001034442e00a0b0b8007a002c480021850420702c0c0203c05075045e1984c400325440d01e00e00b9640c6401c030420a036000a4032440c0040c00343c0e200d00c9060301c508512840011850071411401c3c0148440426022175a031400b035242d0115070703403003003607903803241407441c04029000651904a0408044040035600316050182281c1250240c480714607034040300303904840c03461026004018901c144040ca090258000300c005005010420000c4d0f00e1150015080514003052981d0b0020412021141904c69915100c4605010012902180010f8a040d1080e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 434663624 1250 434662374 434662387
    0x209040624050f092a0c3a1b0302030d090606140613050f27040b090c0a1a13090f1404150902010c0516080609070609050402160b2a 58
    0x81e0f0340c0303903401c0c0c09041794040488054820140b907805c8031119108142a0303030741c40e0301d0440b0240c200403a0800f000100014000d1210328070003030b0404502d20080e150b607940349030b6000d8031601c014160102001d50850004120111035281c103405860980e511070000090901e18008050420809009401d44a00d000708070202ca6014401c100380c0c19610215998103090036500d00080f4007a103000100e140f10b0048034074098080c0100e041841c820340c0500541001607443c5017410b41c0311100c5074240703070740030003040f00070311000510f03040c4800c00343d02000c01c051509030030420001c0d50442c15130004884588820703c240d9003105d14004c40e44459807480c0b41d50740600300342d41d51320150101d02d0030004c40f0594402c0b00c002568481d2000b003140581040684003075a1850307803503142c4000310340075480b91440750901180b02000e0001d26282250510342d42c0b60340283c18901000065402071041d0701e05400301a01c4540802da00303080f4039000d410310480401010440c00c0444000c54a40b030b0000380c03118000d0081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 434664874 1250 434663624 434663641
    0x607080115050d0b06130e1911190207080a05060417072f0d08070308090d0c030c0804030210050a0206090a0309091e1a04050f130209040624050f09 65
    0x5444a41c81041c0c0c012501c0011040400c0546c003480502c03035505d4101c00700000d50030380c592201500a650041105407065140c0401030103640e100380d14000e0580d010090154242403206075070355804114410381d1226940c41090a00d40000e0105c01d80b0070340c00040c184804c02a07a00000c602e01340300d11104900380f14560b01d6800d100300148444030384607400303007108400005000b00b502642180c0145020002d06c00760419103001e410840085003c9504d80700811424000011811a400c50f40d40d1b03402501002c6541c05c540c216031002d4101d071000c038140300c048010794800807401c40c5a0410307600d154236011032440083c68000003502c22026a0416110440801e03885800e40c0c0030307550141004622800c0d01640448900e44d480c443c01449454404601e003030000b0194400d03880030003103509002644424444004c016401e450001a01243c5404000181084500d00b0b5005001d0b9034000342e4001428601c540a00c461000011089a049824441c0d46400101c24045241c243c800e4001c43c50718110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 434666124 1250 434664874 434664877
    0x5060405040b0c0703021513030f020c130e120c01021e0a09030b0c130b0301060f0813030309050f010903020109171c1a040906050703060b03130816060509060708011505 74
    0x11000b03c500040744800d15008001042031208501c200060615040b254000c410320140c07130403400a031340e201301045200c2c0300013803140320380c0c60040081001c00864009a401031402171145c3d0360500552003e030402011110190014442c807800250380c0710f000c503004000c8008c02e03d070941d4030400288007969020354410203900c01c3e260300c1240c1d16030740d890340b895032126070082c00b0049681c039051aa01080480c1c540713000e18125101c0351500001c3d03405d240c0b0140c507102000c640030340ea0324800e00d900d040800c0c4250000103505014800707a42d25081111501c0d829121001800d4025039100d4011108221112000100030401c0c03d0b40c0505024803458014440200c80205c00d00c2d2640b41e0301e07840c60009280704040544100100308029201d8549010409040c0413100c440c04a1729042d40020102b038000200c0e445146080b40d082e8040318256540310440c2c001c1581c1c400b40802410b200c0001565503c00c0724020040342e0000d181902c1c1000000300000016005007002030341c219080d400403a040320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 434667374 1250 434666124 434666131
    0xc070c060c050307031803080703120b030708031c060b0d050402090609160e19030b0a0b030a0c03060f0609020a0305090c0109050109050f0415060c0606090204121509061d0105060405040b 82
    0x1400134644288502202c41096003900090300c0e02300001900790825420400340f034486d007220881807102d03102c51020503842d06032a20940915410400000c03106608904001c0c510000d54540017584070340310f0460300d607107800c2000e01e4114039568005000a40c07400c01c01040c1e10400454001d080c0d85040242500301841201c21070301070058041d4020207a56600e201004c2616801203840c0025581e8140324204003825100d2020741d51501d000790804d828041101041d030b941080840f40810b00c0d550f120002880c040d5050384445075100f0303012559220b5800104148182d940d00800d0500341100310a041c50401202d4505005484008011a0340c100c0d0200c0b0403140b0480301d615440d0010000305000d8284040203c3d50a002000c010030815080040704075168003800c0c04118085d01d883c5028124866801408603804801106400103090070440712146c0c0e030450800b1552502543ea050b0544881d10041821490002030540182a00b4428291720440448040c0041d00302521031000052028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 434668624 1250 434667374 434667377
    0x3070201091e05040c05210717072606031006080c3d0f0503041104050702031b0c01030f02040b030402210706120e03090a05011d090c070c060c05030703 67
    0x30702002d40d69091064940c0b00501001e0010f20003151a80ca004006034480c00c4000402c0018506141010740c20182e618450101a141e45055201321840004001c5009050703d007007141400700c0e0301015030840e0340078191580c00551a030a90810b0f41c105401d00110030790214140f4500741c400c200f4500b000804003941c06064520502001c8554034010111504039030212000c000e80000300783e104020124a02040139580d1403802c08500c0d4078044400d0b1109460180209101e00c005d1403d40c038003540407a420800c240112484d00d903400c04201c0e1500c440e41c0162000750000114204256094003500505000d40d0200310700e0103003030141d402446c0c000a0000703405410081c500340300340002e0300da81989601004040766140c55807800c0081460540d060749071980b80c00c207a0700340030030340002040c1c074000e19006110400f0123003404011a09030740003504094030a0042078580106803211b040d22401480c1e243c1031166503400c07606180c01c143c40345600030810490105a241c0c00300780040103403810168103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 434669874 1250 434668624 434668649
    0xd090306020a03060506121506030f071803020301050f0a0e07211704030c091146080103020a05180f10090606020c0a0e06061e040e0c040f080307020109 67
    0x2c104120010241d036000700b42c0118000400c1c01402404100d0039208042e1602410502d1b13021500707000031390005a40140b40f040f081e05c0820001c600034004184401030000301400d031345070f5940010782501c2c03080d5402541a00504144800480140120b00441c500280209105890540c2234840078050794120854070b80600714400402034510070f11003e0000c00c80d001600c4a46a00702106c940307103d44208000145048402d0911901c50420740b070f400030301d01c007902c0c6406d030110115000100e0440d0140303034142d0403a0342c9444411088000d00d0528680b940d0396814541c11481400a802c0c80303a00f11911490032031202038210b9103d8022141d00c071103005e59450090302c422003d02130581d986e0b0451030070726041c4900800e10030341c000b0740150244001c507840c1a005903a5500d000d1309201c1903c0e46034000c001003001032030b10140d4070a00c00311004160740c01c5180945d00c030f00300781c00141c05076142e21814800013010801c862814030f5013030103441060b000e075180c0300250f40044d204909600c40c0c0e060280e207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 434671124 1250 434669874 434669887
    0x8030a0c0b0a0204050315240d060b210705030c04110f070f020919051806060607050f120316030c050901030905010b18010519080c01350103140d09030602 68
    0xb240c0554005190103030844440355480404d2504102c0d013200c002c92180300b413500c0340c05050100d0401104146014040042c1c40d92903031140c0300a8010940465044120034103180c603110182028001c0340b00b8814060031503207017003108250403c00100324603849241020851005810103d04032078035540302110303041e510304940c07070b007290f94400c59400a54030405c0c00c81001403504058007451030003940654104000d42d2190300e803014000381cac4038548030194018000030383c2500b844401400d880e4064011141c030940c4c5909041d203401c0c2c00c1d542c18800081d0103c14005444041d010750000c00055040c10310064490303034802090341c01440d0415040540754045042404400c1d40210141d0b0000341c46c901001800e611240401a02032040d580104031282e400a001e11954080038143d45100c0d014101e003044c44401100d817407854007005552560000784070580c0b0100700c0301c011003400340c600b80f50829602d50f042043c15030040c0000760010fa04041a001d03000c640c070010103010740364481c20041e00c41c01d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 434672374 1250 434671124 434671141
    0x1050f030a050601061716020c0105031008070803120c0c1b0d060f1a012f010e19051501050d0605071808011b020d050706020903010b150304030908030a0c0b 69
    0x9854070806050360161100116229500a01407070034046034015030400c5840d54401c0c0154001024803410042e009140350107100d40c0304400840d00f0854000451134502d86452032141002c140d50b005c524580c1c40000c1010031410340b8034185520255a0b44005e0818500c00c4ac181d85447e1001800d6440c0180c1c3d40e1101490340d00c40400b2840c0a0300000100801c141843c482001480404c20704560075024140401c0303150b102e86140160542440c482000c81d8030a22520100c01407001c4814426549410181403c03600410103408090400130744020081501d083c030340d040014020b50701d00c02480440050205880b1004040d100c035500900005403a0307038842d82115448000c40caa140e003104501c1c0d000a054005400c010040c0c90740208100410142450580c0d41302d2459480074042030303080c003110020aa0725806400c0800000c0d0000c1400b0342d1500005e4a0140705c43c81700c10030b482d4040180424168040c40020190407400011803818503480e02c00781000302c00d05401421420f201c0c000880c0798 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 434673624 1250 434672374 434672383
    0xa0203070b0406050601020c03070b0d1a03190c050913020f030709050702030a14091c11060703030f0c02011a060a03060e0c07140c0109050409110a091a04090b01050f03 74
    0x15504554001c4180c2001e1601070003421081d604203006201e815604101480c0100390f250031220142031442c81c0034010f00401c005811405081c910700071405000b00d520f51070521420b140c2420760744c40c00da295100340c5014114028142c10650107588813008210f2066035a03d0f9080f480c0b601142c448092140d2000024905141500b06104450030704042c8a503290b00000503181c45049a101c00480c1c45260340e8031380441c01042150f82d4004505049054000c40380341510a2040c080c1d80401c0c41c8034005d901080d41c55202210483c00a55141040b1801031010300c2400100092803009000340e50503400002c00c06040c08035114031030305000400c2e0801500039800017005141d42815000ea0340f07400088401c454100b54000e55401d000401ea0034846c0790b0115444640c0c000584403071041c075040c6070034040140741160701240e141c04800d81d102d49580c0c9e007400840080881d28408141f0f13280d80c107502c281340340111280c13600588c1000c40c0500040c000a07a0310b819a4000c1e12080c81c0140d0100000313291 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 434674874 1250 434673624 434673637
    0x30b060903100c1b0b040b040302150f0403031406030607141215010905011b0b070306050904240b06250f0b100b030118051906090b03060117060c0a0203 67
    0xd44110b580c402404500c0d41c10203000e056450701c5101c4500c00903c01d500e229448032200500070b4064200280c00554504102600709003e44100c0341184555030554488076001c0d10510129801102003000301740d0315008004416011107180081410110042550b545002d8071071810b00080500306c0304500e010005450b01c4c0d070030032096180d480c01c00c140030070b9070000039004c00760001d400345901140d41d5004018002500c80c40100c1d02c949481d6a07140c0130b000c0f13032010b03281b88109038803a10700044d00e070343e03044d1064000ca000b401360800c0310708a440200b8040c4015030300c5026440c1401c044030b10655034001540c24055080b110b520f0501080107540f07902108242000f010341c0c41c103000c0c010a00000d5010b45109100e1402c2c6503140a07169858a44640824402c83da81d90300d09000001d551038990701300781d4100804009403000c881000449909070703031064002550365030b5a014180101d15003003104c24010030203402080040450100c425445d00f80081140c0b0200c080046e01e0040c00780308104403040e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 434676124 1250 434674874 434674879
    0x10c1106040308270d060b010210060b0d05100602030919030b0705030a05070801030b04080a140307020a06060e090c09100302151c0e1903111203010f0f0302060406030b0609 76
    0x240d56440c0d1502401540150404040020080b00c3c03482451000c10140d2402c6040242105c020305110b0340d600010b403248003103071030440c029949040ca41c8034075401508040d001200d81561214502d1826008442e0020161400c1e45078401c070810105402108030307101403070107440a02003020781c541c1034042d204407a40000e003406107a1007000720155105001d54041e140e444070510154903081070840702101c0038000503101045200100b00003452100003040d03000f10605040f6000c03c030710520491540c00480d9000b0151700001010300400c46107100318005441010f480c4030b00c5003003800505a5035040c0042081c0036094420202d44003889000b41c0c6002142c0c000e1550341a606014102c8085030860700e418490300011b050080d480003000d0196a143c0716084000b00300b44000000820261240c1c00e0342541801584900f40010007c180910341940154003402d656079454113845d500741d205c0f140d001400c00303040ca140078001030f55a80c0c211000c4503d90f19010800c001400006440d03480b803043e900c0d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 434677374 1250 434676124 434676127
    0x90b0a0203041703030402030f03040509070302091c12170f010e0c0c010905010209010f0206040f111c060504031b03020d05090604120605091204030c05090c0712090f0f0602030306010c1106 83
    0x10f48000011881140309800355a490b6518081d810340c0c1f40650b02446911411180025050611984c043c00030032200a1400795048240080341803100e511003000d403002e0011004442d043c0d0740101e00700184c010703a08640041441c1003032a19103104010302840c0d244400a10104070f0f04c26221058485141d4444020025102145800c500075400300c41514003040090300700358812800450078074899030f0001000d040c001403594071510000620304005174403180c904a90036810545007005c88616100c3d07580000c0904241c1400390680d031248603800050115603103003500103640403036a14800d89030741c1801501e1341d500c040010130b2030161f500a5100011020b0600b4107010039500542d0040c210142514149140110080d4031449507000c041c00c4006e1401c403c104034101500810742c0010041000b038108410342d41c1d8242d0700c20007642e1810000d034031a50180a10202c0002c40300040001203080003905250010194403800001c00740c505020007120101c0900c041000510b8401c0d00007003202c0e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 434678624 1250 434677374 434677409
    0x80703170910060b030108030a030906020415090306060b0301050102030a030f0b120d121803050c070b070f0308070201180605043e06070f1203020f04090e150601090b0a020304 77
    0x1507070350329002a02d2441182407400001e0140000c00842c0c2c16100d441c400f40d46007011042c0c082e400761500c100700300d80310780c0c1c20880007a4242c10b0202034440c1200a60703c030403081e455410085c0a4500c035405c04024200c2c10001008903a0b0000203d40450b5608d0a000c1a03400141d42d00c1e800030050080c02d81d0708008442a40000c50321b0106081044840310744516000301d44a00c40001100c0d42200c01041414054080c0001b2030302030b001030640c1906890443e8000780d12108410740940111104407028110b075501c14040540040c1142d40c040c010b84020020014040240541c4000400c4042e15807956400414107000c601950300400c031030f0401e040c1c0042e01540060003444200000802000079200c25500c480d490510212070b50b0316003220920743c2c080c0154a031041c201c03001c2c4101c0700030305508011010003000824054001050b0900d00041c4241318210742c0740c1082d441c1d02c808501154450200540760381c01107450000d4404444605840d9100614281c0c074502c905e4010b040e410048a409 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 434679874 1250 434678624 434678641
    0x14010e0106030f021906080106120b060d0e06072a020102030721111515370501030216081803030423010807050910030f1802041b080408070317 63
    0x44811544240c6032180c90107602841c184038032009011b42400a0000b5004001580c070401d0030041c48800031500081c40822900003584660248142038025134880d07110407505882400090352211003424050071a240003804003400441daa001c51903000b5040c120f20083d644200203a4900c42d0b807095815040303001c000c2288081c40e095000090006060584520003c400801c00ca940042035501c0c000141d2903480029039012000c80d2000d412410100641c540d00c114054040111241d8404e64050075404100b10304010080390000c6040c58010406401000c288000d01c0420391b4011880c1900c40c80011005c41394094101c0d07107140e2504c000310b004502c0e0215101140d191400c1e60342002c0c01d1801440c01515403000c1211020081002800b480070f00d401d1602c14440c110243d0705c3c0015088046100c440e00321281100300344d07140c030b14112280302103003414400c02c2c0c10349200d84030500458011001c001c0c8030381d400030001030040b08081104410980140e241d003210415080f4081c00034a0700001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 434681124 1250 434679874 434679893
    0x807030509130b0301111c0207140a080d05220311030d020d2a05030106030b0f1002010506100311040b130e2805010509070528020c0103060f0b0714010e010603 70
    0x43c858480e52a000048820021380c40484a100c0a01c0440e81042000c0a901c14020f42000d101540c610080303000c0f0302c0c1030440a01c031840c81e40d40b05140c80c03902ea4500d120050220340c0000c0c01040d10621a0b2070300300c007500504003489602507240c40c01d4201c014211100728214081c41c980100382c00d0002c01c2c441462603054202074000c519506c0281032045107101c44202c000076842c0c426011031700402c01802654441d802880d4040c0014010050817046103010800417101090390b080180d5440003030148078942407a41da081140140b07000d0094801400c10020144264451840c24020000d14011510302541c00c0500402e11481800e200b882d1201c00041c20100d16403613400303003100b80102d1034219201407244030b060b9030000e0b000c501241d444039429200740d0720100108600100f24a1540441b10403954241c0366038281e0b50240035162071020015081e038104d6005802c20804421051100265140a54646942184114190510300c0901d030b4010000503442d541c0313079428400040288002c021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 434682374 1250 434681124 434681141
    0x91801020a050936040f02150a0f0801030b01091508070611060f01030519030507060c0f02191205030712050103120e0f1807090e0f10080d0c080703050913 68
    0x4034241495201e21003140c80d80c10b00f404041c007180025030004021035aa40200310340c080c6c4a804d1642002200341c00003403840c43c18411b40d90001800003196160568412031a0485000c1410b100010354156a0360b00302c030b8981406001a40b680e22503007408c0d04142c0c2041c00b0b004241040c2075440094a0300303001000c442d1301c206c4d4054180b080c040802e8209840e40e440c18101c0340c00202402050301c40d075101e031220001c84401a0100102841004085401403041000c05421030b11601c82d400705400c03000e428004000349041e42e0000d03582c10540800d0302000d40a0b0f600800e840e015540f5552200195040d2000311a200e01030f610708070020007080702000c404804554540c0b24007072040c20724400c016480702004211504100140031110f2140e42d01c0700c0d007540080103070424040003501e40300c441c2c11031241150107018030880d203c00d0205010440d0400741c0a808218041c0041d01142100502300b0f1021403001005e030400014030030103040c820300540f129240010445290740f070541d40a44040c25060707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 434683624 1250 434682374 434682379
    0x100e040510030c09020d060b13060813150605090919060b180c09210c01080703060b181005130e07021005090c032509090204060e010e040302011a0a05091801020a0509 73
    0x4235041d0314000a445280764241c01401101c0d007003100484080d4005041c1e00703004400e48001a001901c5000054000400c010780080c000386440100552020003800025580e04856401415440a046400450364104901084a404042c081611302c0e00ba1f181ca07107102114181808000d1110314020180c0030030864888008881b4201241074400420083e60710b1a0703c42c07001c500f09940207240f081e5101240d42030005a2035501c1c4c00343c114940c0107c201ca0440105504165540d140070001c80d514103a5500d0300c4d600b818003036000707101d8940290003800c8441c0080320000c0ca0300782c400c00c4194552503004100748114204012401c0d0f40e0b000403184644a0b0007a8200076590211038501e180380740807007500c00b06850b8074201e0481c0007040820010780e00241c03a61404a1100000c0c07006600804178500b114440f807a050a00900b100e1500451111014084d010140d048e070b55a0000c40035521308a90054054031018068084403800442c40d41d219400880c01c80301781500180078100400c410b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 434684874 1250 434683624 434683631
    0x260a090306050108121804150f031704050a0b0c0309041803300b06071406011a0711210d021e0303310f0f11100e040510030c09020d 58
    0x9401c1e10380c0c0c031402d4803085110400010310404001c0e011021174080c02c3c3c40c6c09800010060b0303101418101c0314243c1e402444a03400b216904208204416002c84034035884442494201420b00000502424051180880d100008540d5003c400000d000301c0c0c500d03103402001080018001e02c040d215481d01400c00b640840e109036944412048160f0b1110381518201540040c09601141c000c001030109c40303c2c4640225042c06080300260180c1a01e500107070098000f003070035616100d00b0a141d11100c194011b0300381c106103e40310006a000286108001701210b000c03408600d0490072203400d9000c460700e80c0389480342040300c94100781c010480e0138841f8460b03000c0c061107507c2800701650b40c1c44181c81c0c2011466001c6404141c0405059404c0c19600108512403554482034440c0c0584034400e4409070f0301c5c00307144401c100c2000f0070050f009001404c10307606500221076007007001e088901c1c0c0703202c554040c4d41c84600003191030083d12000006542d20200c0761505175210003250000f504240f5003160749030f15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 434686124 1250 434684874 434684879
    0xb0d06030c09150e07140f030f01050105042336090d08040f0203070b0a03020406030c0c2a080a0602030f10180f0f0c050a0201050c0a0c260a0903060501 67
    0x1010700401d110790240003c1c03150650318002d285803611100030b060303408205203900c10140b070000c3c00004014400700901c3ca1916401c065403100d070381c140180c0c0050b041c000200000c20864100207072040504405e4100500c2040c030000c082884212960018054a84900314113070140030310070098141c5400410707201045640d809007480c0d5030390303402e100c54010540e200700090010b42900b03003030800d6078400744c140c3d11510364840c4200d205030805110b03100880d80105050042c3c940c58400c100075a500c40c5031032207003034903603072200740b2010740c07040d03002ca5800c44d8095650041000c1c0910b1000800c640c1046604400e01c40c204680250010703503038601c000b001040800d00001e03100f1480c1d4181c881c140c004030040c1e110740034850010081050040001e036110b11105038402c0292160703103a42d040c15118690380d069041e80003400c40700028030446d00504140708108080d80c1c081c0f045034640d07a201810190303030381c80e414107410070f042040c000000c0d900c00050b5008031254804050b00c101e0b4410503090042d80d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 434687374 1250 434686124 434686139
    0x1906120b0a14060906070204060303210903140c070b04080304170d050405091015091d070207060c020a0902220807060c021e120610050402030c07020405100b0d06030c 73
    0x75107900c2410545003841e04100c005103071241c02080b01c5940200309074604209680440d00703445182c0d05c00e03004540502d5801746450301c4030851500e14000d40200700000a41d031380d0040c013502080300050040d14404034051b283c40d401000300c0c0e4045c2c404101071503141c0355202030783d640c1c035800f50044108800070310b1034117400c071440001c040c50b516a950f1906401d00d800c02c010311026940c000d02040c81520a2540001e01081000110700b01942940d03a550a01d403c00c0d078043d03000440b10b0244800c040c1c80c101080303220b542c0460b10700c06664541c86c100f007400c0c14070300000d14040c990340c2000398041c1c400600c5064520010030344d00c2e00741d00750034943e1941942c0c44c44100d03100d9400f8070030b090124414021460040c90012502c640c1c0310082c003e140060040321f07010808001c480d0700000100e500c20024011010303d19a1100000c01046609500e189891041c0c0e810038007030420000e000e41c0e118404200e9403200380301008060040d00c0e40550700d4010428031600070b40403611003681d40c50b403a10300205214 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 434688624 1250 434687374 434687389
    0xc02061b0f0f0c031c18030303050a050f0402010801060e0d0602030f011508040305120a0e03030a09060b192306030a09060b04050f0420060d0e1204080a111906120b 72
    0x21040140980010124024400e5904d101d1724404020400c01c20214844080072114510155000b66070004503441c0611001048a50140500071002d01020400c8010307a071081a150640b002d514060b41c0c00701941e00496002e090880b00140480c0c00441001400c4080201250480b1000c24010709041100e02c0309035034a4000352805400100c08202d00405004401c8603c0c1e08500350400000307189081601c40d509542003902c8500700c0035215100c41040c450302d4003038050f804030121503103140000709100f03866010030680304482a63302e002c4000525101c3e8a107403a404900050222940c0b46491407841004120240c1d0844540d854100c0c00689030900740f048601c80e400c02c01018005440390b454000b0b0800d404501e2100c0e03404504042807860b12142c000d407120302801c00700460112101c800e494200341c072070200d11a10010501040080c048000b070140300980d00402a084822483d402140c03400340c03060307502500415440070004129500403c0c6030087d52102004120181c0f5100030810310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 434689874 1250 434688624 434688643
    0x2030c040629040512061e1614070507032102070b0304140a020424090903021c0207050901060504060f020a20060702040f05040308070804020306070c02061b0f0f 71
    0x1007401e1a40c1d00022a2200094601070702060860500381d841d070018446481e401e040c0391060704424140846501c2000c03010715480038058121a0a20f070800074034a14000740c050400030450782782d0401202541c1103003155010380e00141602c14040d2170741050300555800d0036545080d4048411501d80040c0b0102c2c0200a4400341540c040c07841c1c40d180c44907000d0402040c40080d26001d000002c10040c0e0310351091400e10300303103003210707007070501004900381b003c400b5507032042d1103840c01c109006000a50206051100f080844528600c100c0c503c03100320724000107a0000c940004022002003400d0f034005014104a640540e1010761000b4108003c07030321071803240001001548500d042c2e400004000341d080718a00700140210342800090780026013030700c182d00c181d485c074079070b40c2d0040c4418180c0c400000741d440903440c2001074081c1442c1c0c4c0400d07a0f03420003c0051b020001c00341a08001c43d9601021500c1c05185080b591454660b002e04140d119840400c8110091040c0d90000c64a5040070803200031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 434691124 1250 434689874 434689889
    0x15040303030506100f140901020f07090b0418020a0302060f12070e0f010c050d031d01150806010602060c03010e10050301020a020106052803060c0306121b06090509131b08060402030c0406 82
    0x1c070340c00c10f0910b414a87c3c0058040b41d055009100c000320700c169041102c00e00030f16080300041210f080c0b1005201c1161414aa0345441c40001070b2508c015031128008401100da054030b0569070340c41c1c06a041806409203c000d00103541c0041c09024101e030303000c1c2c00b403844a00110342d4403200c290400019101501604001010b503040380c031000c02224081c1d40502c5412110340c14520104c42d0455000e400c440084801444503482480f080c0110001005401c0c00341c1114002044642072442044106020500c103204645402c3c03c000fa940140d880d09040040002500a40d15010841000381c06010107011b014081c0031070042090364555007242d010390b1101004c00d000354050031603d40704064040300c4c2115090548030b03580010f100003845510000a400703811414a01000705000000c4200f05600941c10420f0340d50742489156580643c580d0083c0a815500074a5929071905c03503031808142c40302440085840c1e0f40010190000704805108900c00c4060340c81c0702e1448403c10040320b00710b000c0c0c0790 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 434692374 1250 434691124 434691137
    0x10e040b0f04050f0d090e0f0601210b0603010320010201020a052a0601030803010e090309280f12032c120a0501020406050414040b01050d0b15040303030506100f 71
    0x7003005407400e00d441d402a000e5803e880044007058426882d01c3c40110b1840c0000d400d5080c108002c01d405075500307801c661820710b0f8009a0030600002488016140d0b5090084031036008004422040d660000c3c08030a4041c0840e51250ba507400c02c003081d500c1c4019401c0e40c1d0800c44001ca0025072042c42201c96041d86529180d080400008030202c000c8044040040c2803842d40b40c0200c40e400d410040b0324021407103202016500e40c10040300031450a4041c1c40040b05900030700a941141c3c0d0360070501b105c4202640e048000903031412200d0848a0340551003141e4050441030045422032840e0443d00c54140251100140702d802c0010903560600ca80b0010842000700300701100e06854031310880200c011001040320036654042d11040c0c00c980c0b06601c19804071702d000508210080000d454003503c0743e030403601041031812040000c1e10364459640c01d50640d41d61a640305040303030b80b4044401d1b0841d01c110030560b1610386900d000f60041a0030b80300a4421518012500c007918815000040381c0500c681c0c498 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 434693624 1250 434692374 434692381
    0x1603030801061209060f1506020d0203030112110405010f0503010e07030b01090908210f1e1f090f0902011719020f07050105090a11040c020c12011404030c0b010e040b 73
    0x40300c6050f40740341e104104540780ca03000c40102d540c0703025804040c800c4080002d444c4403280603190300201d10b64021015500816071030070140360080240c1c0c0c112040d1000030700d142000c0346040d182c001100382c2025805440c000000c0f40c5400d0741e841c3c0000b0794005030000c1100410001d03849070b6403421407000805482864005102e000f116810054183c0d100e003071010b0500100c40c401c501b00f44004d4084002c08000102003000a9a8481c1030903080702000300050980c619000c0070880c2990010702845100020020b004800440032003500000e0125034020095941c26000241c041c4c0032000381039000400500b246074026010340d01c1940542e44401c200c040f003000d0851000081e41104082c40c1d00742c8014004a80401c00038050903201d81d000344050a002c001034500440100f400302c03c0580102d19128038845c50301c0e00090701d600d031400129030100d00c0c040c00144050240c0101510019031001040c107120030140c12203039030301503984a000b4086090780c07940c0b245003450104035805003143c405c003c0807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 434694874 1250 434693624 434693627
    0xb04091b141e01050c1902040c0809100c0905030f01090b0601050313030c05120316020d021204032d0c080d300603060e0a11090f040210030905070f0602160303080106 73
    0x200b075840704103041c40c81c188000c0100c42401c11040d1100d100300000d05110103011494244108a0340481c40c0c10002c0090034840c0c412903a0302c05150300b600700070f1b52352080d08510303a000e0f26004d802080018111104000845138803400703092000c00440d52000c5800202c0c58941c0144c040d00d04c40d0082e100100400c0c181600c00b2503a82d41204015226800b0b1500907500580140c40290b106480280c6008031904861070001d1074488a004118115007064500791041303403105089400322900500d440300900200d849040c0201d01c850000001c48880740c20070303000c01081d02e00c00e4003214410300a0f0380c02d0154001d000d0712600345c00c080711005010503109140104c800041d42d0070100068500018042e9101d99540c030403a02e0701e440011455000103005001c01c0500c040b105a00c0b2005c1e142001e50f0b04201c10a0740208001400007071086501c0c950700d20001c8d03c20b511034083d6a401004503502300ba82c68076030350700800050040900501810002005441c03030760031010222540742c1c0d01c0e900381d40e103803040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 434696124 1250 434694874 434694919
    0x702010228210608161809020a050d14010e250602030f0f0c10060801060515070b1906060e1f0f031505090c040e0f0114060306040b04091b14 62
    0x1880d001140e55043c0104201004110209241191a00070341d5240c0c1440c084d1043c41095411803494141414002070068490702d403035804440b02560b8110102c0c84501d40503200c020b440100003640c0d8680b942100c4100380000d0380290414511021425a05280c0701e5100e9901d0b45016001c003590080000380f9012a0b888000c003100b00b26403061504002d40c02d42518103010380444640310444c5c4414083c4501c64081c4140b900a1004940310110aa51954840b405006060005c0c00340d55040002807444c20a4144542c040c0c403071007104000761034541c54041d1402c00503803441801803900f0600304000d07043e81d003e5140b0090311921045d113102034881c0201d001e0300c45055192514116980009a65194881024001d01e80010b0780fa4a45090507420313068054010310380182d468690004004480360104200f40d40841690801da495031114082405000c0081341290010b14000040d400c1c016484401d0582140041d62086035640e11003421180c16808401c5070350100302841d100d090006080f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 434697374 1250 434696124 434696177
    0x1812090a0305030a121a0a120318031209051005030a0506120a0302010203010512210d1104030b09061501020c0105030907091b091e0303030905010908030702010228 72
    0x41209510a480742d6401d425a00000c50102c04100b801194600c843d0080c06846203541001c62042e4441e5240c3d00000c4141d0020303c10b031180c00080040e04020b051094039004d00c4d41c40178030401d00c050ba64070b20f010340c1d1030000c4501c4500060718240e404142d030f252841e0314440c0802180c1d80c19041d511240320317a00003440d0260102d6072004150100c0d07c00f44ca000d00040004034041c5d0001078880d85420305000242810248600e17003070704913002c010b002c0c00080d01d1800100b00c00340040c03a101e03085920324000500840341c02c90318019010400004009911070020300c103d0309501a6842525078015101014581c5880240907030045140c08085520a41c003560303104501c403007220020f5a640d4160384c226000d0340340c0d0485015043c4000104d8540000320b02c4020030081d04a104140000c0103103da00380e8560100400301a1110403c0040c000250016000c441d0081201d503664101050064000d5000301030020070000580010707000f0708020340114801141940b185500c1c1004480030f65841c0c1d1280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 434698624 1250 434697374 434697379
    0x21506180a0f050702010608010506060313081b010204030804180509282001080c0a020706080a140106050901030b0d0503090f01050d060e181603080903010204030f0b040209181209 79
    0x5140c1d00e0b0342c0c150039000d550f0141e142c1c1e40000844034108801c65081d5a00141141d0245804106101c07103d0743d0041d080c4000d5030041e0865881703140300d00201e040315112009500c03a41d0b001180100a000c4110024401c83e400d00701c1d054041201280b4150598004a8201c610303500300c1c611841091700f201d5012022001101140c01042510341d0301c0c5004200d0a0328030b110411000040394030075581100d2195004001c400c0082d08049503807070001c4d55003c2c68010300b420030620b140410319041c0c00d80c0140d000d400030302200080c20741e1200b000500d00c2c1c01c03541080d400242000d502d810703d1308ac001d00303690100d5045405503140a500d142408081c1d4240e03d20141042000c10100161488511804000c0e090140488070b0381d080a4403100f001805030a03010050750000380f00781d82c81d24800c1e060601181d9201b150300d525079814400090090041d98009000521664032590070400c0f80c0c2803492050b4403c40d006401031703c1e07040c5840b90780000b5800540f4036520802c141c074410501c0101804014400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 434699874 1250 434698624 434698631
    0x81f090f020f01031508030a1112030103021005120717070504030c090903050c0303011d0a060602150c04170105220803070c0c1a0304050c090705070201080a0b04090f03021506180a 79
    0x16482d00381c5c4140203900020281e08086214990141e020086494031510700b0b00074248000f40400c040918841071000a1146454070031840c0740e00e01440c16140362400d14a603d40c2c49151801d006001a1480707094203402014400014036018000c2003541d040c0c1c1e0304042400d0303c1764106056a4001d00c9000829010f100007030006501409040001350702801c1103120040f00c9440100c404040c100d40542180c3d0b102c0c0c2443c0003030005940c001805011243c00c080500501c0c0c480b034600b4800c0744555001401c07075007600084900c0b60034054005134003a810306c1c4414840e6440f55503518552000100700241084000c002064040d40b00c0d00d200101d0324014010080400d81d5840e20000c0e10134403a144c8500d6503000700401c17045c8401440382c01015201a2080002d40c43d00b00401031140c400d101c0000c1c1402101e03000306042409690000c041383d0b001600400803240d407410840c0e95001450b07801c4006200305c0d42c0d8180034402d44800d141c00b58001411401e201407501c980c09109000040c4660401581c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 434701124 1250 434699874 434699891
    0x272520070b04031410021c0506120709140a140f040c0513240b0f210f040c08070524070605070e0a091103060111070f081f090f020f0103 60
    0x1040010b00040d48950580b42c40228000100350030800a06900f00000344140b03c0140070350200100081301d039205c1100000c42d030399187c00290365003c01c041081100d100d80d210201c2c040c10594020b100d0441284128600f0b41e41d01c14061041e21022543e0003a91400c60000c2030450242c1d4240540081c401d10602d4095910307103022461105184040e24007403511850380c00d003019100126482c5030a40b0300e079840101c40c10504c09286510890700075000000300020541211502004180492000001440d0090800c0c0c040042e40317450607142078030030301c00440d40000c5034a80010b0340310480b40d000d083c10781c0689607121540000041e083e05107281001c01c00041000800d180300702072080207a6140e1007054014a0140142c03407a0a0300188a482e180804401002e1041c005881d40b146091070481c100300100ca50550400503250300004410310440404640d0800100301d03421807040700000502e1802ca113844040903a554044083e04100c5001510030243c209500b0441040d40c040c10003082c50b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 434702374 1250 434701124 434701139
    0x30a03090206160b0105100f0e1c050a050f16150f090b160c060c1106030c090a030506060102010507080114010c0501061a09040605040b06120627252007 67
    0xd6070103c00b1280140c240b401480075280c1120f18018141e01da140c0300305840c10380640500302c2d54540c8409403150b40d8040114a00c541c83c0e51303420040301d07486002d407280070318030f0b10345141c0d101058071071580c0c00e0040541c091504c000f8402054102c640c060b1208080076622441540c0d114092001c4001308170f403c82010541d00405001098658920804000d40c582282466030040040780c2140042010b0210010007145200b41c02c0e500038002140d819640751290400c1000d1840384140464000000440000030303c4000304e503442c4100002e030024445603489000c2101c1000013409109854114014076080c11751213074610f602400d206000006170146c03204500600040c0b20400c10744d01c50000a00c5c1100b9003440d000f82802814142e400f80088900b4400140060066481c01005003032500b0001e44240d8501c605100c1d2800f90001240c55844081601b00c01c101044802200321401a016511110500500952480a01e0313441c44401414103203180a101d66800c2c0d072078018420580d020072003a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 434703624 1250 434702374 434702407
    0x9050601030e150441030c0c130b1504140906060d0b03071a0a09170c0105130308030a1a01080c0f0d0e0d0201060e0f15060d020d0f0501080705060c030a03090206 71
    0x10210084000035007200741080d005501c0c1c05480c002d2250407d100001801780000f8240c001c840048a00d0034000d00c0484550005103030580306142d01c5243e201c0032610b11400132000304151000e908040600b418032000340b0a00040075250150032031410008007141e09001e62117401c02d510014261076071966900c8040c414900700310407007a038120000800c0d50a95400c070b56007100500c0301e0b0114034544090720741ca150300c504102c424217041c82070020700d2800010224086002650b80603031480c2e164140488402c004110995007005c040036a008e48160540c05845100d00c0713104c80310b040307034a420315140c2150400c0c0c016200d9620343d1921140c1c081e407803038014044e14000120560001900c0f0f85010041030300f00a02415a0900e484500305201e2030f03600d481d940700c40c40c0006540c2c05940d04030840081c0c000f40b0824010740101441c00e80c1172107056005400142c120b8101008803941d01e40c42d0720400000b88210321002805600c00c200140d0054007941041c0c0416000030112030034406034500b0515203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 434704874 1250 434703624 434703683
    0x70c05161d0103050703030c0c03060e101a0f1905041109040501060f1b031407110108010b210a020405030a030201020c070f03020105033c0109050601030e1504 70
    0xe54000d0341080c40307100c8041d2100150700c042801500403030352654079220349580290101030104510b0390031040a005680f0100340041d50702900030001400c0308030a484d101e4101c444d942240f01d04110128000c000c4200c420521408010701d40494445414104440c00c2e41044084100c640c10710000075850752a4840c10240001600d8002c2c0e650381e04108120446405130030690601a100c40d082d1000750303110a00c1c61911101840c11610102c0e241400d4840c005810089080b4507400120001000b409540c2c0c000e1040c802c0e01c4400321a41c94529651980c0243d43e070207100d039058014607070300340070b01480c0440d08006c40c10801880c0980b10400309040083c5084240c015070340001e41100e1040d02002940d00800c0009440400c0710f0955000800901c8060292038101c0c1c108129182c599400f20304400082c1d0513140c0f18012842d80c031801243e0040309124042c0745c90300c2c2c540020100d502a024150108540f080a480e280c41e280c0220a00d410002e00143c6607000c0041e01c140c080354030064007040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 434706124 1250 434704874 434704903
    0x10110403061d03040627140307080d020a0204090206160b090c0a21030e130905010506030106080a0f0516260f0d0e1f09061b0803060603070c05 63
    0x19164254102402500c1c81000a003010794110803150255410110984068425520b03100041d0302d0050700b05680312441a03861402001c00c0d0000080c18001401013203442c03941582034034621a6680003175520748400302554405038001945c1d0304c0c01854541c0c402e04070381d84002d0661342080340c0d0610b564186500c2c0e0004035145440f4009000c8443c0040011500e1001c00303c99403210141410841c541c000200e0b04104886107196189504140c081c0c0190f20340580b003c0c00c12540c0b040e01c40e2414014000549080d0791035482c1c400824002d081c180104420b03036840f080203000c01c080954802c40340c01d80d201da003035560340911203980c0c04003428aa03510008141c82450340e200c18052100040d440d04480c1c1107a40c0380e0b440798100c0f62a800b000300b03844540c406103003014400504900003184452811144102806091001c0510155000000601604d026a6501c0c04c0726a07100081c20200101d40ca01400030401030001035024030f0000c4c000c60307010806140010300200c00d5030319180360032146000c030074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 434707374 1250 434706124 434706127
    0xd020609100b0d0206090310090b061002010615200609010212060402090f040b010905121005060d08030c1c0905071a280e0d060506100305071b03021011 67
    0x400d912040050301c11002205400b00818090080012401048000024050880460703040c2442da018030001d9181e050000303083c425200300d86040150fa62044030303140e11559541e19254003252051040700103558280704a0810031845001c1a100740c9910140d082d840d1181c3c0554403510442400030034003d20002002503105c2101c608015020080200154040c51041c4850300c0180d654041c1d0010b02a4141c2c0c0004d1f10201020040704d541c030460308519008100f103010351a0210000039035080b0040da940b0100490340b90300301084580c0103246405454601e081c004200351140d030000402c14941c08001d8201418000c91880c415200340d10420344090300701d40d030100502408a41c08447c2a04510031007403a006103011403004a40c0406440c0d640c0300c0d801d032044004a0b0044400b11000d04c001400c400c4400c03890701e001f1016110032070b9200d000e80d602c000a040628040d00442c0c0c003c0000e82c8910801c450042c051000c0b47d5003000c015803c40c031400040c40724461042c4200c030990b407610318409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 434708624 1250 434707374 434707381
    0x2040314061b0c0c150c01090b040507050f150903010902100c050705040501180e07030228120f030e15030108300f07030e03060106030603060f05010f1a07050d0206 72
    0x40b280d145084040100420042210103052a0f0120f50000c3c0054100c07407640b011180040c1640560003202410b0700030390b10307061b102403c0c0500000454410381c418400c441c00c050700c44041c8209609825001d035005030101481c582c01c403000c00094000001c010f00005400341c060340014854000d40054080820f000c001d4241c1440f2052000358060300050b141070040d540b40100fa1421240302100268000d03554080c80500b422003402804000c5400030304045a40c05168071282c1d14001c110350004040a0750a000601d01600e2a4584000c6420502400d40950315031030036514076907205130aa5102c1100c10000c070203032240c5000f441c003802c942c0d070040426615000070915440c401005032004801c416258000640c0c011080302d800000076441d46803119414501600c96420b41200590700d4081d840c004a526641507002034104d90182400748000081509480d08071002802a0000b4940800381880340080c042090200000c408203401d2030403031517455803810503a0724000d031070041e003198052 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 434709874 1250 434708624 434708641
    0x3120403030b0108061c3f0e151b0a0803061206041203020c0a0c0b0a0e090f040201030c020f1005060109080f100b0a03060509060403081303051605010204031406 71
    0x146070707601c1020b080407480380c00c00c1d0000402d40d01c1046150a01c00403058103000c200004441d058003451001000c03200c7e14585a40e0350b0420f58484034000c0d8950940142d9650020b128480030249003c018100c001304050710315100519901504c10540e5000072020b00c81c03030441e42041940306103030088041c1500c9040c404208a200c00000c0b102c85070366840039080c8000b198903e040c1b01050708603400e00603641d0f14404615410100b83c0140600b800d410749100080400c6108001d040410240c0d50300d0742041d007484100b1510b000251400000c07800c1d00000a40194001c1d48203a9404501c0d00484418080640480389002c84c000304000000b03855000f0300480b0b58225050202500444002c0c000c0644411042c9039942604050305001507102c1012141a49802070040081c5820480c2440180f418a05c841e641e40d80a450032400541600b0002d0382c0c4030810949480c40b20703490380c0d40c5454403144c82c4280514856115041c2e907d55820480000080c0b001c52800c110180b41c1c801070b21451070b050a8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 434711124 1250 434709874 434709881
    0xc0d02040320030c0109081504060902030a150b010309051e01180501140705030f072709020a090b160b04060b04090b0a0c0203130e04060e0f012004050603010e0c07050312040303 78
    0x3185e0501808120601285601080602c0343d0801d002c40180265294145040070703110034003000c0c1d014007820460b84240640740c484114440c14540042c803aa2070000c00450454040040241003504110090708001501010020128200000200f082d00000031314245003240000d00322010f80d90f50007115110300c81c01d0319080c0d0148171414004d003035150004590881340c4000b0030312800c01002d030160481505d0100c0d48000d00c6128180e40d0000b440d00c66a2940095021020f21400b08103c0840060b40c0e8590300c04640482001102d08401c45109507501103020300060400c840d065242c1e80f10300100c5c0c54520403034005030700501c810005410300001c400c00f213a60210a11085410800007010021000480441140d2114048907203a60b2941450001810841d401400d41c0c000d00300e0503d110074054003c14001d03d6202d03188403600c10f002c800752800b071041d807040039001502400108000c401100e189079004141c15002172400c1281e59031075086903c618007523894110740c0014001810350511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 434712230 1106 434711124 434711143
    0x403020910031209051c05030a0e060c010f090c1a1602060702032e020c07060507030c050304080105071b020315091005010b21010b030c0d0204032003 66
    0x500204080580d20170b59100c0d41a00341341411000c1108030034068030781d0041c003d5182c5800c01800ba11110000c1c012140d10403014000246806001e00850541d5070b00c18000141c424900c1c034007400445220b400101c08948072404a03254621464221141d0710403076400641d4100691001803100d11804d50025014083e28820400724088400c04989100c90741c079010303841c0070000c4410f40407030240181e0b654256102c00d80070032003030b07005000900d5802c1c040d1808028000e4152901c5286901079800072805030342d10400c10005035800318008100c002014080036085a0303540010756250f0310300e1403000300c507001a804291901010840003100f0100b40d80107008940e907450140d28250041212401005403008180c1005801244043d0680741074404c002d003151102181c01382d8a401c4070045010090b4200310100110302182328891210f5020304822440305100000d0500b42080c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 434532374 434712230 := by
  have h0 := BRFrame.cov_init 434532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 434532374 ≤ n) (h2 : n < 434712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
