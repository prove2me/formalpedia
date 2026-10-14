-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:55:59.174194+00:00
-- url     : https://prove2.me/submissions/7e5dbc95-fd2e-42da-b2be-4aec78fb6f84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635071942 ≤ n < 635251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635073192 1250 635071942 635071951
    0x102040e0f0601080708040b072a06060b130b0d09060908070c080715080a0608030301060f0e0405062209080703050318060103020a0b09030709020d0203041b1521050708 74
    0x21aa074001164095108540061007100c4075203031160f00d40c440f6a031745000304800074150800c100b16100410030007260b10310b2807070b5004550140014a40c8450a245e412074980754400b5158034400c1100e840c0a1601d4003803c0100c0f4840d64502d40c494200180c440090f00308140c008103120302d02000355007004500000760046038020085008501e1712075401c0b603565021402050a40e20300c00543c12045482680000d90041071a540410100d50fa640304510f16002a00000007050b0ba2441c2038045e5513000361810318003a41160144100c1c1030110105282030b10811140311004c1d00c40b4203e080c0c52074180c01c0845440e03405804142d6484850500030800d030802c0c1c4596000341c021069200000e40000ac480e41a260010107180645141c030b03203000d4042e403000581035018014407400003007402c110320107066000e549110241e901e00d440d26040050140e5103c8070380d80929050418000321400c2d000003072800c8182d041800c900807148031070340b40169000410344161403d0801b000b40507a803084800340036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635074442 1250 635073192 635073211
    0x5040c1205042406060806040c11060f160206060a05060c0f12210601121814030403110d0507060318060219080912121509041b090212040f140102040e 66
    0x100c1d50015080035a82c4c0c512035440000d40030804501d80d03181c00d0703001c1e80798a18207041092204241d640e41c0b42c10103204a40e507087c0d00b04071504000c0040f01325900020041443d2015101c1890300a00103030481c4a18050b050140c50003052004800101b088800c0115143c00c040b16043c0314560700d41125503216903904c034000000e45031881108182120040d025810585610400c06a400009001008140b80a40a2440100001000c074540d140368500060081014507a51819410024148260600040d0094082c03940f41c00200f04042031400c1a21700c00e01e00801c442801d0946000e00c00100100908a9407000403890782c01c4511810f611701202c00381d25046895510510707016140d44803200c10421801081025005c2c2c1c100f68004180e0020308404880c40c2869604007280a0032000c0f40c080740c00010700043d9500144803403030400700030485040154940350216441801c600c80c00344c8000e1003200c50800340010009032802039500301c42400021900c50f9a81c49404035406010f48500b0031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635075692 1250 635074442 635074493
    0x1020c01050313060b1c03020f0609060112060e01061a070614010b04090908070f1a1003030903080c10020d090c0504110f0f070f060c02100c02060105040c120504 71
    0x42550244050740e1040800411020b4200142e88036400540000e4081740e502000b400e2a8a26142001c01e81010603802640213000498055916915000000d4400308403580001d00400035041c2c0c00c0918291242d0141c0c020a100010001301405007955400424010794410100141102554007404005000e01002c0c020000c1c203a1940c4900f007004c2c000e010502000300006d102401094006141091042c040c0a00d0081d075500ca0903402643c01e003084464403654800c00460b5460a00565081442c134003015080c2c5195a0f400b901c410b00b43d100080200c80003040003030311a0380500000c1001030031441d0a540d203582103000c502c01080c4680c41120a081c803c000840d040c20f06100d0070582c00c0507805664500380c0c1200480d902600900c050342e007154000c0204800044107840c3e110401d612510020698984014019040035034692520221514040580f0712143d070009a4034111b81c0142c0b4001400c00090074200c1c4d01c0d00c1c4c410390b140c03241070030700c01800300308004903003160001c1501580980 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635076942 1250 635075692 635075713
    0xa320702180f0c1c0203010b0c070b0306010203120a090b27030c03040b090312040801060311030c010801060e01020a0c0e100b0f0f0310030b0421260406060b03150102 73
    0xc9641c405440703400303030891500c000450030203030000280190410318005201e1803d4150b880e6050b64402d07007144064000120310300540e03400070840031019140f154040350441c5441c0d00002d50340d001d51020390300e000d461280840e03c52900740c2e001c12045078020b08182414502a500300d83c0f5480d0080761921442c030061044610000d01105840c00c0750025805503290502e410040c03135030b42d00014200d9901d8024180d4090910387d07020010030050401300f0010504524509010914540e02c662490094000300004103c2c3da83c809604d5054500c0390134001c81d40a40c600040380391104800005041480b160004145803c00c00d8525110380102024403150030303110f0074504010300035900c01411040741800100f8141c007205d000355034001c00405030320000d035640392101264408207547c113450f5644220304201c0c214410641e89c1501c02402c2c2081c81c0707865460f5004542c4904460907200c41401c0c0000881c04100854001e0002059204001901e906001d03100000403010041c0d00c0c0e025107e240e8000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635078192 1250 635076942 635076979
    0xc101b090509060405040503041e050a0f030f150f0e0124050a03030f030b040f020a0e0909030f0711060703020d09051e0120011e0e0a080a320702 64
    0x3202961000740000300142c40d00410711000e400d0160089035140024840410242c1480301b05a02510304000b5003216185808144220780b92507030004007004a0403c014000700310352500030781c507082d405007001e07003900381c2c2034007080007800f040400c000c205041405031500c0280541000d40004900e41007190030402443d444d02d90320442d84902a0031000d940401c00c040390181c440c80145240504020603548030b0100011b0441d002040004902e5a0218404a002d640b000200a500c0b00548503405242000e0103110741d2800b8526221200901c00a00380c401c20840d10b044091350b190140001c4d0700c0d07408510b07000c2d495000003007105000600c0c000001800b4034014500304000c65040707040344402076280d001121040d0407803000040c5154003200403940701400340304181c1480c1c0c085482c0c4400038881c40c1481c0503203011607019400c0b40d222601b0607000c603020008940132002141801c0000340b0b40b451180d402c0203040c403c501210b43e0036180402d1171005000050105a1003162228009400191003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635079442 1250 635078192 635078207
    0x31a0406060c0308041103060a020309010e060403201f2007080301231002030301090b01210506120f1e1603080f041e0501110d0807080c0c101b 63
    0x101000903103410340b0880428015004030741c01c6401103460038452807200c000320b49011000d9170054803141d800010000c0703642c4227200d400d0652880c2c402401c03280c109a2801044566080210b182d500032040d40e148203e0030400c480380c041195901e10200c80c5031001841c02c01071141607000d0783c014154800c06030001c9241c078200e070b880c1d0f5400440c090442e400d0261040329000116440c0f8080355070031710485c3e15035540310003d03240050254000c40c1d03a5070500741031100b075908581c161410b002e910700303011400b000c0d100c103041b0b81c0c0301c610840000d03550307174400000b910381c03814211041260103035404520522001150b07030098800d204280c080090004202d440c2d8600c07202c09261001e05101e8424000101040300a2003128042c00d00e0504007520b0303140b1039081e103107070443c585898031460381e04104558004e0f28104a0104081c040c00c003c1804600207000ca0308028030303000c20041d440d8005440843d9560a03030b195691410226024551300d03c05803001000da586054180407210b80e01d00650b01d05c2600d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635080692 1250 635079442 635079449
    0x41a030610061d01090305030d091b1211040b1c06230a05061516050f01050c0d0905280308011a0d05130b040c0608241905030706031a0406 61
    0x10383c001c0320a01c01d01000c4000c0a0480d0040c1004444440040450710030070281101c10240080050414914130780045550079030411000700f0b40c8004810803141040341144011550000c1304034640d0200440020001c004180c4526445603178102d8001103070060b80c0012410034460b0307604000741c100d418444222410402001451042d102000a014010303680016030010300c042c0801400c1c0e4440b440440d00758100d030762800c400c1c801080045040c0807040200c11020400c0030000c00003418081e180070041e00c07681c09140c503040d23222030888041100c204400e1500e1440403858508814460180100c620303206002900050010800403940f04600704003404588000c004061424640c404d0350409408020311150116400798200e002017103003d103029114520070407060f9506814420090708041000d01b0482e0002c8104042c21a01c04403054070b0150500c003100c0d0640110001c58500d42d050310b05400054050080e0724000038000d0300341d041403408040740c030f815030040c2354104140022503071a8070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635081942 1250 635080692 635080697
    0x70216091a01051303060e0f15090304170c10030501090c09050109050114040512060f0c0403050c09090a0c06031d0a0203031e0f040806190e1509010b041a03061006 72
    0x75100d246036002d84010a0526800680075403c0355990311349008071000821101c0580c0c00810501000250900041c1ca40d0104209030100300d06126001941d603000360700a803400d215134440303521341020303007000703054903481c00103203c4040c80c1031494000300904003c1c441d002035a41428030b000c1025001340240800d0710010303507603200e41903c0c01c1c00441d0340703c40300f81d50400c0800c81004041150b850baa40c8c514608841d41c0d00030001c0342001541c4031601e880080521048180900c0300340f000450200307040d10502c0c4200c035690f180351240c003c1c0b00c1c101034074900010902242c1c1c600002d03445405030032415500ca0900120344082610030420760b00d6059000300298150801c110112456402d50b1864290107078030603559081a014816441d0b42c1e0380103401000841c0e1003041040362007062184140707802101c44000b4009034032042c16840d9100300b4054005803001e11032001a03c1820309602c20001510000d10500000001d40c0200c00b5803001d1000b068083e0250701d000131034200c102c5040004580c400d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635083192 1250 635081942 635081981
    0x50a030914030c0d03051b0a0f021c05030904111c0e0601080f0715050c1b04051005011b1104060e04021228030912080d05090d0e0103020c011407021609 67
    0x16581200c131ba500640e6400041c08404403002c8051f07000300305140045104104c0004124060700411242103c4544404550b0345002c4014000500100541704880002d5501150030294110b4280c05800764400000c00842052510360520b0401e40158510341e0b500c00a5442c680d032070b103003d1520388801050101465122000c00c0020751006940c03000c400b441c41c9049420301e8074680c080390030512202642d4461598610160442c0e2506102d4203130450400308490003d03901e4400040d09403142080200340c0c160305e900540c018080c02c0005112402002401004030546500030b64003264001d68080e40a0003240c4848008100c00207803400010f0491500300780c601e00302c4522150401ca06140c11010410181c40c001100c1911002c44001c05110742412500d03201c0c210060f5041f1400100700c020142d10130020712100c00d0304880030606554081c600569107900b079442050140c60304104035020b9081d50f8003000340d4682d000c276805070898000e90300b0454140d5140c812900f40ca0710b5154842e400f2012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635084442 1250 635083192 635083219
    0x504060c142110090e0d0212070314160b090723010933050a1d0a05040e0f0613020910030b06060d0b0a0803090102100213030807050307050a030914030c 67
    0x1d05028543c03140da1040107502072900da40030301c07043d6100852403100c2030b03000d8a04d078001c0329018004040801c02c945545804c110464a005000f810305501d0210003040028a00c0b070380003001c016540340340e508040300e84c5441c20803585440d5142503502c110f0741000c1016a5250a464450341c0411500505a43e8860f0742810803000c0c5d0b0384012100c920800c43c2d28030903007403101441c041503580c5003194143c03901c940300e480d146006407400d00c980b06c98a01c890b903419032068280c0e503484400f905850069400180f1707601512220307440c04000401002040c0305041c100084c03104402c1076410058820358145200e42c03210149101c0034400303404014401c3e41042d0000340182031450141044003001d81011480490000c085076461500741c008400c0c40c3c0000680d1042542c0410061500c0ba0010004502d0207014450000140455020040c2013500006140c001d0010800c1a00c8103180c002042e50b900307184a2a01070f01c1156113100700001062100346005e40c0e46000310386170034041c03400b81914007440c07803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635085692 1250 635084442 635084497
    0x918010806040b0910050a05100504020a0f050a0c050709090c1a09060306010e0915090709060e0d0201051314040c03020a0f08040215070305070b0606040506040905070306090504060c14 81
    0x3c000b00f00404900c16007035550600075141c000d150080180400000d000d0038070507149500c010721504118002c40c010070040320360319400382c4d042d01440c0482ca0701d00d407903c070070800c01c030b42c142d61101000d400c03481060400700d00c950080d0b03c41d43c01c03203200d0500020615550703e841c03016a2410403000080800602000c2200d050210046074020303c145440300800942000081003010180c03540b1007504050482070b08c1c5401e150943d5900400075007403800809240c050003c200120202d1424021840d41007904210b902680070350f07800c1100c900038000d00e56101c240c3c3c107181241c0c08040d680304070b0415144000d258000c1c421140700c00d01c556945041c54002d01d4043c1c41d1020081c0040384c0244082c1d446000492500e070107000765500c01c1e42c0c2d8982e00e0a003420003c0d0500009030100d40f01d088100410021540e4003422101101c8100320089030302c0d51192416401414035a014012030f605200802040146582c40300c05803584c0c0b0344800210400c045841c00080c0603c1d607034021480300c0c041d0000450031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635086942 1250 635085692 635085713
    0xd03030b01031409010b0103050a02250c0e070513090501060e01030b1201020f0c0129010c060b1507051902061e04051201020307080f130b0624091801080604 69
    0x8181000b0480c0300c4443c0a415140c4012180c1e0030380c907592512519295a898018560881d240290039130034080c00c610b51741d500f01b03d90304882ca0413510103072a0710100120b0b40310b0240189101500c0c45071501c1e19510181807030f80405603984c504919601e02060028451103010305a4486944118820040c040190000d100c06412581d01403e141d10b442d21a078801d000403c049010180501d403115031074a00c0600355010300c41c6d08056440883d251100362820000000701c5007000f4a0440b0300c1000e982080c00c0103065003d4000d03005111452500c9880714448001c0002c203100341e0458000a150200d8110210302070f000003275201e041040300c030030005030b81c0354142094154424954a03003560381000403c90038103440108400e075004030400109036001050707103501020f074508550340352038601c10b20a0400040322005125101d5200032804030345401c00302481040706403242d02d0301c003061440d2108268100d40102d0348242c00701038440e80c2c1b0410324240f0904071588540107100c0c1c0d8a4a41d2154050b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635088192 1250 635086942 635086961
    0x602150406021204080a090902091c030c0609030c0b010b030601080a0f061d0a0b0109030b0a020a030902030d080a110c1908071b08060703090206070b0601021207200307050d0303 78
    0x154003442010381c9204020f50f0705004501c281901a42c0312131010b0b01400c1205c241e4800706042d48144030800751070329490440b8100701c10794801c0400b22280c600d000d50b00004480e10242c45a0700e0f202c203860804d90424a0600d82c640542082c000c581e130f035003c00109621045615900141568001c15040ca040390001e038045101c0c004041500c5860320300004203030320080914142d00c0319031414041c2001d124440c01518400031720748910004e0075511604505180079084042960780020042c150610070703441803040d194000d058030059038000d000100740070700c241c0381008103a01e85898004403550380c1c4100c50b400640840a050201c188482040d0000140c0d403041c1d4090100f0010080058251844000300507200000e1128807401c0a81d004c0c54160024045810b044c50400c800c0c0c0176a0f6800705440c6182e901482c0035529948590040b42801442c1c2c081d0425000c010034034804028486201a0300022036282540042e0360000030940e58130a148030340d03904020984800da000c248250071420f000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635089442 1250 635088192 635088203
    0x901140a4103010315060b03040b091006060e13060503250b040b130e010f0e06120d09050301050c030c1207030207120e100305040512090d020303070f14030406021504 73
    0x40041041403030001d0840c581429900100000500804c0f46903900c02e43c00c3c00706a501001510b003000070700c109610000c0c0024103982241400034035502c808000741604036000d04402e00c1032035950705000d004504003030421481014005134a014002080c440e513811a40d0003401407180c039181c40c07042c03048812112101e5002c41001c1310003040b00144480280300404ad9a4552a980c11700070410f03c1520819801c10841d800c44036004100d15511b010001c3d040e00c00000c08840c4c5c03a2a50300014107002c40111034100d140c007400c036020f0110b0b42c00050510842d10154004e115660301da1a030684d0034401110b40c0340501d0310074408030f02d00c400e042070400d6004005040c0149006499290f04100d060200c511a0015403001c81030b10550800400780300001c40729003020300190401c3d07074440d501c5112215080800c02408108980e00e591107105e021403450700075003623a507507400303604240007808241942512403116001d01d212a8500000480b4200c0700b9503409007840604c044110000301d080644140c41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635090692 1250 635089442 635089517
    0x1b0105100b0d0617030a08010b0c0d030c03021606050a0609090b0703091a010e0403030e06070917010b12070312110d2115090e0106030b2a0a0201020901140a 69
    0x7001308850340e15104004966000b59164203028000509040d8141c0204400d1403003409091030740000058205480c0311107080c00710710344c070108500b200240203400b4400202d051411700d49051100700d511581c00f17000a0a400e01000351510b42542c19102a00c40c0100841e40410000d8040e034401e5004202c100c0c410724002c4ea004401d09101a0300c041c0a0b00442000c0880a0a00c020140c040c49440c0800b00c0b050080d10851404d9003014380186000d203d4020208403500000040b19000c3d0300c8840c1e114401031142c0d0103906d00602d11a42c450442c042100d0b07030000c114541d412540200310600140806030000e1a1100c0140002c50300303204265043c0e24041d0318030510b10792000741030048a4460704004406041249445440c4056810062944080e030b45080014004175001d420030a074480b0101070040f10110752000ca01558a40101002001c901e01150b90003034150f040d0018441c00c10f090381c80c08048005034003e048580b06411a031004154004c00d020120529500d020700b400045c2c040560 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635091942 1250 635090692 635090699
    0x10918060305030c060718060c0b04151d01060603050c030c131703220501020a0605130c0b07170310030f03020c0a06020a03080123010c0c0b0703051b0105100b0d06 72
    0x40c80c0d40c0048501010725004841000311b080c1d80312404000061a584039441030518282e00079041c081e40d01000381c41c1d0601c0c2d900040a110b4443c1c13030490b961204c0b20301007200c5c0b601c68100e080c1103181f0041c520100d500780100001d08074420f0180c0d07800340d5280b803d21861502da403040001e880d4020740084c442a141c1c240001020415002c0050001c0344143c00356540d10a120f40c100c0a1610028090ba070f01d001006e004e1002d82da000a0b4000d80c0f0340d200b84005040d40319070322282980381c2c1d0400000d242409021020031485041c2c405000d42c0c2d8440c00480c1d030300c0140b2514850117404111252411540d18840c20808110406920740505002e030054400701d04400b80031402100903508101d0169204400c11801c26510800c01e500521802c054002440461745c50310281c10b2202149034108035a002c80c040500050a00c1d03800240b10740c2521540d241c85a00e805070054205200d450140800c01807007004d40c1e00103000302c910030184d407420b0780c400c54100340b004001908000a0b40200f81d03510740020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635093192 1250 635091942 635091953
    0x60803280e03100902040b031209010c1b06031d070b0909040227011a07020a030b060105040906152703020103020d02040503010501080604060b01050c0a02010507080f0d060f0f050109180603 83
    0x11050f40340c5510100d454002401070100b643c0c170701900907019901054001031882d1000d41902e00d02c0070240b9084441c1d000c1c50400c1a02d5460703060241c9001024890001840e1b501684240c0b03103081d1056500c1c4540c01c0c0188079030f45411040c0f18400040908101e5241d03989030410000e40c0c8a88000d0411b08604070303036144001d036189800c0c05040040f0010b40140121522108110454084240030b0782c80c01c19036038003080724602c1c3c07480700505003142c1001207499a8016015500a020340300b2040041503624400c0341c2c0722003042448140884c01e2403d250baa090f01c1d070fa20810003c51075140c10003483e0720b5a8011002540b0580800719456400d12001c13840742c1e000e006090007041450300038403944c00c00307003015021034582803140c905000040110070b841030004102c034103616409080558a4400c1070900085510440d46c0035414a0320014840204104a502c01410b83c1d0440d50f0344840a0b407140c4c0c10051030281402440e01042c1d40391310406c40b443c1c2d48030884a10070901d20000c13654994075681c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635094442 1250 635093192 635093203
    0x803030405010f11180904020406030210050702090f2716031a07030212040609080d050a0905060a0618050603160609030b0f040b01030209090f070b0409060803280e03 73
    0x894040e5122200064446030324042c2900c049081c0303440a2400c3c4a405558802141075000c886c01545104005425541e03942e000b00d0045402030007041d480c0000c120300404aa00c02d0404a00c10400000410140c1603480e4a40d4800c250a100d0001000600c80c0d820768101c40203a111000c600c42d5034040e02d079800020032040001c0d0303c0b0308444011000c0c808007215920100500c10f804151043c0036600b540c44180180310707042074100c20002031202c95810581418407990101c1c00e046400c1074107000560402c5e80c80448854040c6003900d20b00e8841c680c13120181c41d0316201c0c1d285058040a0101c0303244a09500140d00904010103c88003900c02030b04415280203540d00030000f2907c02c1004009103c0d0b001c88550b440700011100504600e0550307075a110030740b810b0101a006001400014618050401c000c0c07000500c08070860b100c5c190b60310b0200d8065403241c000e88594904051001072814000000d448001401c803101502c076240090200101d1035a4081080410080584000c05600c05000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635095692 1250 635094442 635094451
    0x18010603121808030f0f0304060b06070b150d02091f18060f0f06090918050a0b010611030931020f091c15020906090a08030703030c0f0c060f06080303 66
    0x300c1c40b900002007840b000c07405029034025038290700f0801100341d038420800112888103c0100f03560b42c490b100c0d41055402040c1c00741a45801681c0090000c092115148800384503141d40242a004c08210030140075440745420002908400c1401c081040b480a4000e010001059001c180041580d41c90554110041d003610072240c0c1540d07414148102c0aa2102200241c808007804544061034800000c00181c642d1184010140c0d807400d022041100030b54805561b550020b080700d06410850401c000c1d03c100078807440c004288400b401003800c12000c0251400001e0041815200d00d00d40d0341c3c3c00300000e07840a049442010608403554440441d480902a0890007d444070f84a00b412020b0000c880c00245040010460b040305541c00950f481c10305000c4000700c00c40240c0c0701c004160104066001d0092000d901000340000403d0106c800005040700c64000e5909019210f1082000d49000c2a005203e40010764081030210100e90345070042e50141d0030902002070004d595207495820340e0402da8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635096942 1250 635095692 635095697
    0xd080424140f010e040c1401050d02120a05070c0507050f0303070f030309030e121b041107030206040b01051914030307060e1e1207021c05030a1220031801060312 71
    0x10b21a10003400007040e070240540300359180d05401d06448100a6031510b01c81c0300c4c00c0c0c0b441a04400c40c1c0d640300e60169092a10061810340d00c0e8540081e9030303002c0280884c0d070a40524070f01170020310fa152107070501714200c6030014017510f001c9003800188501c01c061105241e4141c0b000300121400070f03161007409011139001c1d0360001181401443e00030400554454041d12a940060054100030b502140c10840b11000320900100e0407440e001007009011080b40550070000045911010b01d0f03000701c2c0051003140b2803806586280c1e25400ac001c80a031040303e00c04c2d400712024900f4008026818501c8102c81f00060803641010800c3e52071106a407046068004a504060451442003404010707842074000c4100c098290740f03d100007003c0d15402080c0c00030388607400c5080070042c0c240d49440c0510b602d03070300704082c2c0e550745403441400790440080c20380d4038120a2412001d00106a800c000d841404501842440d01e140c9840d540c1034444000c6260031044d0b55600c000c000001340c035a0b04c3c0b0400114964 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635098192 1250 635096942 635096981
    0x615040b0c1e030c010c02060c180d02060d0c14160b0a090807080705010b0901151211030108010b0a08010c080601301a010c02030a020603040507170715020d080424 72
    0x300030403801c0d03581c00d461b00410340d4004010702840d4a0000b0507101903912868058402103000e00028000c5620400060f411510014441c10a80440d030040203a404241d1103200c180c0c00100c0a0366410721508180405602d140c901000006801e040842d03081310444001090025007511000c3c2c0582c04410115159840040c481040010a0144c00d09055044a1444003585443d1842400d1600c1c480c261041002003d0580c0241035280d20021a503030031000525201d684400a2900078200710391000e114492280340002d540405014251114120780d65441d83d540b1140c0c0190349002900149805251103024601004000140c01a404040440c3e0101d0030400e50360151342c80724a0761001c2410800348031320000150310001096044941d064800ca40e482c1e540d402d009007030502541109003c0201c0240d0101849800a039010568101720040d9000c04003030201a030380c901c6075040ca80c0c0070444280008001c01c900c80503015080c001c4540b03c0304645451212002140c6051041c140c1003400c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635099442 1250 635098192 635098207
    0x90a03171908040f0201030b0103110417061602031204140105040f060e12091017010b1c0525050c1204080d0203040303051c062c0615040b0c1e03 64
    0xc800c4201e540e0307026060001d5182090344480c20b050304040c0d0080e0606131241d03000f01c51a44654418428604420318040d244d540b10f41c0d00014002a19101ca01e2510600c0701141c205444c0404040810741c0a400862406100b11402c48c8120307801401900c100c150b0200c0100440c00c05c2c01581d11503032045104c12a03600c06490403104403510004c00032040d5001103014920700c5802d40455080e80c6080395071810310300c00540100d80300380015005041002c401e000014a482c101e00150182200b030f2008100b200360000c02c0001101c0c801c40d0003000841d41c0401d030300e444200d20b840000000a2602d00646010561142a4580306c04455100406540050200044d0340c05101d040f209194501c0614502413440d01e004125024990b19030b11711042000300720240500551040c0000c207006d0400140d42007070000a40160110b0341d0800000e0b84035034001524614000c9120030811004284044c10141050705482c0c05401c0500c010b01140304500701105405180140f641c1e640c1400390045949400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635100692 1250 635099442 635099467
    0x4090c02010b030f16090506040b220b180606030a15120303060506030408031b13090507110d0906050d06170304061b0b010509070302281d03060c090a0317 68
    0x40202c40c285054010711700c040d0450040c605a0b80407528404000300b4640c031003400050042590310f2209501c8004200352100c45800441c008010101c4000c041204542c84000d00040c9070b02841d40500021000c80040c1030b510b002005150082c024000005500883d41001441811207230040052804816840e5080541c0341c05048054141580c07203034214240341e0349007046e6002c06010031000e20040714405030189104825940840d91503011945090307580c0034114001d1505079904000103d0b0742415528100380010001070100c02aaa84004546801030848054010004050000b40c407048001180c4800d040030703040c42204e210245503107074900301016150b0301c0d141501034421030109904002040c1108205411a181551a076406655902046000748180c40081d400260003410310380e2640b0702540c01d050000c41503100c02d10501c045a0400722915400102c581c0c1c154010700008580080a80c05821455806808803d40d25100e660300d400e107106165010f40034480c0444c00b448500b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 635101942 1250 635100692 635100703
    0x130633050a030b0105120a053936091507020708030403030f0504031212050c04081c1806030c030c030516080c0d140603010e0d051e04090c02010b03 65
    0x10007241d421110510b56901d00d809000b05201e03e901c541e6203032200c5030030a08180303d404600b81d8020260703070000c1c0c0600f850030283c1850083c40101c52003165440005800080b07030030080700200504001030308141c0c1115503841b0207480340e0036000034135003902106c030700c002000c0560082c104917014004050420540191600c1d00404001c01c540c04070008100384040481101d05490b00362928803403504090701c05031010300c6a50310043c1642c40c001031002e8641da01c8a14055401c8685000780080e8032002041407060165008004403600490403243c0c0315418040420300034000ba084c60780c00b240031480d50314071040c03480d8894400301742c6501103500502d80c503104e0408080d01c1c9003002c00980c148102071401c1c1c101c21440f0042408010380201c2e010078407000582e5045514030f203081c00001c10030004e81c28245c04c189d45641c020743c20003403034691001c804034034607811000340e58a00d400c14550f80c40d89203c000b07108400c0003c0140400012415441c3da000300c00706040c1540010039407606032800e240c03429 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 635103192 1250 635101942 635101949
    0x8070b09010507090e130b01080f011b050a05090a0902031f060c0b04080703110607030b1203250326160c03080c0a09151e0306030b130633 61
    0x3a4503240410510790b41103142d40b800e49204440c40c000d42d80d06c1419003041c2d9004a0009031800e9029800001c60035400a0941d08003034000c4d0003800f81e100301d00f01c10455601007a1221005c04d90030f214491103144214090004040d009102c206000d0751840100200d80c01070351807c1c84400c0c80d102c0d40c90130140d200c1c195002000c89140c900c1d2580c2d655168041c41a0020b440284503550000342501414440c9107038088406000c0e0039600e06040041e000350007000c0d840400740c040c4050515903010600040140da42d80c3c01111244441210409090148615400c00440030b1003940402c2e00c00c245512505012414000560503145050060043e04506210410780c81006241e0090100203944281600c0c0c2014006100c1604d0f5580803000341c40c0768030940c00448142c6010300b00c030315042c2d40c0b0104d0306c250400e640d0703003449104000071412400d45215000241507101c01e1004560940b07880e20521000b40d000e8480001d1000c0ca40080303a105508810a074120080c0301610b1000c0c250308a510003008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 635104442 1250 635103192 635103211
    0x3060902040603051e0903070b06030f1c09080304080703030f120c0c11031903050306030c150712110a030f09091506020c011b0215070f05010c0909090b04020f0406090908070b 77
    0x64500913440321f64900c40c0410041900000001140d103d440801544016100301410350b95000c0c01240c41085a511404080002840f401400a030110002c4219000d950007680034001c15070030358800b40d0700d40c040c0d103026104020000781c48a25502452040b0711003900309542d0690003900d1400c0a40d181901001e0340c40c0300f900046007000c000c44648220703030442545418a203483e5500d081c0003a04040003c04925001440c00c000c810903400d003200100203c0d0b1183c8044254054444800c0311501c1c94000c00b0203040d4443c8080701c0209000350104c10340d00d106460401a45901c07056168241d59009100801c2c0030181e51041c05126018012074800c14030a00e42059640c0c400b600d2902c40c0c6c480840e000c4e00641a680e455003c448260040312081c1340c20403040f4544080034940745001700384440089001855040f404150701034a0300803c4000d581003119000d40d5101d0b42c08100d002e20703800c0041c1e90b01c02c0c3d0743e020002e0a54024059132a074140200c440c66142c016500780404d1000d001804400c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 635105692 1250 635104442 635104501
    0x30605010504060206060904140f1015060804260a0201020d0c081317090301110c0606090f04060b0d0c080c03101404030c050a08041403210d0b010306090204060305 72
    0x803d0303a000880540c04102103130b0566a548507414a80b400105042d031401c494094008010700541e00041c0c1081c20700da192001b08500c4207440c1190722500000d000c1e80d00000c4218005c140450403460640f4002c14241c84e07614203000030107850031802d0340400b80003000f503500410031021488480c03090004035002820588000e182443c01070b06400c0c4d0150009022610102064406180e40025180c0708400500200100c0203024142d0741e0341e4010840d1810075200d803400080980c1411001d884c01071b2450b040030701082d01c0e02c0e95400007a06445030180e03040381d404030003800800c1d50030b0384110060403128042c20f100d002c842c05060425049800c020070803070034402d5041e4002030300005980e0250f018604408950b05034642179007005090203000c2c107201d5000c500170600340d40a80408030985021030444190000070b0800d48030022420b071080d64407140c00d001c5c40c0c5100c00c198110021041051400042480c1c9070384200c0c0c100d0300190408400a50b640040050a1111041045a0015032050300c0f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 635106942 1250 635105692 635105699
    0xe01090f0b10050c0312100503060108150408030403030b0d06150b130902030603070b030109020405011b030206070f0c0209041101301104090c021b010e0a0b3403030605010504 77
    0x3100c50304040942c1c2d042100024680100c88424829606041d8246605e004c0c3c5081c440c041c0131040701e00340a00b502c03030700410000040c1d912000a003c40f04440407140060b40e507075140c81d80440703500014001c0c0c0903d07880382d5082d071965907410000c000c504c2c402d9a0005240c9802e4811084a08c00d54204441c81e640402c00307541c2104042e940c050890751780100250b9a0755808011034100310705036002e003200140100020444d401d41d9000380003683c0c404c2e40c4518020070903c80b1014001460203001d40560440c2003c02c17403044c811821103080d0b84603400d010b0281002e07640482d081c010110341c1558902c00d00e0303000f00303225039201c0350261180700310000803010884550300003041201001c0314030800c20780e900f80020700800342d14281e8004050600041204c62600c24019444061200f4401800c041c1c00c150304c2c0d4503600503580c068412001405001c401410b080c100c0740607038800120010709200403200f914922400d820112542c1240b040130b20041d10a5180107810b44000303410080c1801428807061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 635108192 1250 635106942 635106949
    0xc08090d03112e0207060b100e0f04021606050720010e0d0f080c0a12111201090536010c11060601091406070c08100c08060609030d14130e01090f0b 65
    0x3e03510905140c0050380c81c0c0a0340703018401064030700100b940056898444000e002c0d08202c00841003034003a124464410a1801000203c3c03107002c3c489022801301c8891000824059440903901c81d425081c22501d440100054542007500444140d010703a44543c0c07412017a0400303002c40b0a69501a0070188098100d008001d004540c00500880d824440811840700d1130b4401c051010340a0a0b0b41c00403c0000540d201401040d408600701180340d01402000151440503403103860f210300d426102410f43e0100301212000c100075408440a1003d102c031b03440c1c004400e8203214140c40f20f000d58460640300c01404c06001d084c900000c0480b070600241550400c81c2581c000c603030301a0350f40101c840b076540780381600e800c07419910b854105118034071851040c410b00a607070380c2c0903c1404119480345238030340e90352108000d4940302d1854102e8158212004040d03095004040c12a025a0441c0c1c401e410320082500d80d400c41d00d100d6000c010106c03250001080108502d02c503206003131903641418082c004100022 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 635109442 1250 635108192 635108263
    0x12020f12031c06030c0b0c06132103060506030901090c0e090303040f08070b0108010e12070f350910030b030d14070b01180b0604150c08090d0311 64
    0x28402078644084094000c0b041e00d40c0400003850740102940d0b4559201d0f00400f1498002003286c4200d41700d1080880c0e015400600524601d9a11400300c40044120400154400e19415024014980c44800120743ca9540314007075841101010000240700d6214142000060031603408010038081e0842448003001000c411a644260012110b40c1c45581c18684405c40e40304c1c0c014040c290120b5800049103040d419044200740f52902d2040303c80208454104000300d2080c20f0005007404416624040000c85801058030800a0b1448595003811308200b50340c40c04001e24494520800000341290f5549000108010b124200d40743c1044840c101e04040b99903400c14490903000d1011003a201c600c070000e2402102c7e58103a00c06980ea01039603440178500c0022240c0b0511680003030400119842505005050b038007250309014102100800403d016a00820b403280180c8654200704100c3c0389030788840f080c0901680c841e40d02d005085030059500c90502e0050f00c005403000031415000700ba05a1904003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 635110692 1250 635109442 635109457
    0x503070c021509041a031c0c060e031c0506090a0e100902031f050603210a030b04140f0f01090510050f03011b0c05101116020409060612020f1203 64
    0x82e2100503070308181000100f800352051282d40b00c1e08100242c90021500c0e5240802d070a01503003101c1082d081e0b2089111204045420940020f660194440c045022500724514a60010b001d80e81340c4100d9112040804070040b80d082403180e100c10a020003400d000d0404c42d484400c5030340400940000328100c80d110092046034151464451500e1001d41d82e0501090340142036001040380214240c100c1803029220403a4150302c24041c6008441d0400001103c4e0344951011641c0c2501d000444d10b001e80c024400e00110700cbe00281d4070302c00000019045020300380100c94a0300340100328a4646114a0602e070140c004422240c2130100b0b00c16546243c80002341518401c480d0303100c800340110080781c0106107851076850b0307064100c20800081e60300008030881d818090815101c01103040c1d02c4002c2541c0e8801c0324601c035184100980107082c4006941690741d103200030004100a2090b45505040c0c90b4035030030803540c0f00c0c24040242e08500d0042c90716445443e0568102040e413201d041810f031a80034880 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 635111942 1250 635110692 635110699
    0x31303050307022b080f16210c0504090c02120d0f020d1103090f06251101050c0307120b30010c05030402010909140604020c030c07080309100503070c02 67
    0x101c0e5031036009100300139100101d0400460015405000c0c901e01d20078010210001c1401280460408515100154400c815103414500405442c0808840301101440c0094001038040c4160410401e82d000b4540041e240d0707500c00b6180c1741080300c40c2c4210349000420340f0556102e003209010320f40a410503124224a0340c440022410185c041c010040e10a07c5c61695190b07280c6080251110090800340d4015a501811600c0056980c004035640e004240c8000b210140328200c0c0400c00148003885d030f8402d070110703e010848211311000340e9013075071020b491103070000c00701000f0171a070543d001d03626490561603540b0500400403000301084024800320a40d4041c1b4080a0f02e000913580201740003002d040c00d0000802c184168001c00404a41007078400f01d001925030640046c0d42c804a0080400349020140100a2030300c620023040029800f20f01200704601040c42490310344881031110000410b040b034003942d03403401e5200401440d050400e500d60240b08052003800501580b250b00c1040c001e9043c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 635113192 1250 635111942 635111947
    0x20a0501051e16150e010b0d1a0a0f0207030c0308060406061704020117010306050109110a050a030e2805150c18010207030609032006060607060207231e0303130305 72
    0x10b4111550180b01100140c858100e41303030f001e40100742e00c0d0f20800700c410b0b0140080000c02c0031802006001d50b0044409481003601001000c600111401002c1c0c22000c00480040c0c251907401040301a6004410290b001c945c80703000d000300341600100460340c0080200c4042142a04050001e0110840705002c1c0302044480300024086900444001784400ea0960481d83c3c0343d030f503078901980540000d02488448a08142412050660600640c0c61408241d01c9070b40c204244224110001d141140e40d40145125540d0b40300c00800302e05155031480181c40b04c00000764041400c090b03107485080815075004c1c514850400000c20102019505440000254007030b00c403200d680100c1c5090380036080982141e00c0d000080c01019080901140300b081044c041070350000d140c0600e20344070340080b101c0341d030030000401c5000c000647d2030f80140b04040c454003440da10054007103400307814103403000d10b0fa03616070b44048200107043d40d810355106c0b203600310407000b0f51544c50050350391406460581002003c0c440302 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 635114442 1250 635113192 635113207
    0x50c040311130603150e010b09010e10050405011211031914160e06030c0a141201090807030509130b011b051005100f060305060a051212070f020a0501051e 68
    0x960a402d60001c0070b03a0b07401c0c464180c40c0d0501a443c0d4580c6001000014505503084503110018012000d030084020140b4820760310305440f00785411002000614400d43d00c0c900410140e07218852580601249940854400304915001311b140440641207072280d40000c2c2e600915880c102e5901010a521400d140401d460f2042003601e44000c40c1000c1c01c120002e88004111000c11381c0c070240c401c072000c5044841d00000e031001c1c0045040180500581989c034800320815038207150454101100c0e02e800002501002138480c04003a400404084000030400682c1a105140104030000c00c1e030b1940b10100034038401000080d120301111466080c0d00c2042d4403100d03081c024140b00c0041d002c071a07401305000500d0300c0030b072911054601d0301030000e202805050114003c0e20a1042c68843c000c007030001403c5a0503c003c00030b901280c0200c8805a20a0078040c039104c06445028180152040c04003078140d1000e481000a0a1810b410160400c00144079001030131000700c008e440040480320080340c2c0d5011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 635115692 1250 635114442 635114449
    0x1050604090e120c1c05030709090203070504170105060405181c09031b08010f151415040308030f0f0609060123070516080d05040b030a020d0911040f050c040311 71
    0x281000c2800d250840450a03104c104030106400401e0003203884164000c0e11410b205031014001a995a030001c3c41c1200c081c49440d201e80d00954000442e800e0403800d0564901c13652060603010624582c0780d0f5103030001d12100341868043c5075003181c8030000504000b098400010341e40c1c5020409181c80c028080042d440c0540a4400c80d0042d40d0170590410303801c0324640b041d5a1046084c418200e0540ca0b02002c0b01c43c141d90340c4113081e101c050b58031400328031a2810b43c0c42d9030b80d490801400343e03000ca19170904101105504000700700a40c401c0b00c40c591649451011000d465100a00c4501a0741d0000e04005d03180c1c0d11304034041d5102809003003070300229203c25041a08600760001408100d0800188071003400000214070400c0c017140031903c40c1c0701ea100c4001640352031480d91098003003501440148035044100703001d95030002d81303503c00605240c2e10340c060741c0a07602d0504080c4d62941500d11643d01904081c0224503d5a1000d00705000703070704108030925a075205500c0041c2031114442c0e10f42c00180d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 635116942 1250 635115692 635115703
    0x1090b060a08040f06050a090212010e0c0d0c17060405010f02040b43051c0c081b010f0204060e031501090b0a03060c0503011d0f0106081312021f0501050604090e 71
    0xa170041c40c10091850031713940240041048500c143d1041317850b03500da402e0100701401400000d03030741c0320064240c1c8139010041c03001c02004180115002e28003608003040c00305c2c03404290304245110000030700090030035081c183c0c01c680c0542004180280104070a000c00e000d414101e9a04c112414030a002005502c103400d002e00340c4107101e0010388001014000e5012134840c41d0440e649001c1c906407000644403c010350038035603980540d0008540d84954040c0840d00000103402c24000c0040e0f440768060720080d40303608407106c0103000b90503070368042410f1024941c0001f20a5075102c0c280c0c01070146030103c41c01a1030b0030205202d4242c03c16100d201c003c2c81138460a90b1000103607401003013440b0034889080003400b190824028590b8500281071000c01c48541036040c24028056005001c100c0d07424503104484041c3c00910800b5041c08a01d4220002030700000543d40c140f0f000d0780501104000101591200d01c1c905586d0003d40e800c20340148083e55505040314201c40040d1400548070305210011030400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 635118192 1250 635116942 635116973
    0xb0112141f0b0913030f120903051c02120114030309040204090f0b0102120715090506070c1103071d04050a17040305070b0c0d0815040609021201090b060a0804 70
    0x1030140560300c0d140c000c00c0d91100c072001e0070040700c144103140c89101480415501200c803003902e03120a54000011034050300a440030340e0001d01d400b84104074a00750580540e06000d00481c00034000040707100b801243c801004100d801000c1c03065141680b0030f04d4501030301c501070052000d49404000c17001450354080017200c2803503601400c2075440381c0c0c1e2401e15400402c2d180d02140082d030300f0004080c6081d880030618080705072403020a1814000c039030316000c0400a071000c2100120ba503900038800815001c0003600d20031101951502002c0c042c0d071130024800d2202800480c0240e00c400f13000d10690111707900e1026402c1031902403880d59610740c180f9a1805108140250840280341108407900b1038040050007541d008508450b5404d0740d480f00d1800d244150301202d54982c001007520b00f031187c1300e4003215800640031f4101d20f118054150001c0d00312842d41e441091007d90008101680c500010310701c6006141c4000100a810000c1002c18424410341442c4000c04c10441d0000d03080199a1550fa000e9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 635119442 1250 635118192 635118233
    0x70f020907050c0d02100b0604080a06020906131511060705121509010312030612020a05060a020c100504030b0916062a0c03051504120c050c030f010917070b0112 71
    0x504016050182d2030b1003200c0c000148560901221111f14206102120211040c6200800b0040e0f2261240c8000750803010784141d02c128200031a4500340c0303034030300c00c4006088580c2008054400150000c1c02105070b12804200581008040041168128040e904c000380807200d10302095441c143c3d01100ca084003841c1c2a400008500080140b03ca00d0780c201c8070003070031078600701b00b02c9032100034881781e040550100070340c8007649a205000d60309008000d0281c0000138011590803a404c3d0700080c4070441c10320500000544040307820014008039081e1039030010803440c0174015600d8150704901800e4228061401030014110440c540c5041e00d8513580d00100c00075030b04852030003c501c0c108181000b548000d0700c040c80740c000303000e00d803061081085000381e03030100c600850026007686c152030b07c0c142050240d902e4040c0d00045140c0352014025103c0045250000044182242c40c00c0107040d030407210790540f901000d0000c00d000440c280d46070750548103182625040b0b9211468941c683d44000d0448418 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 635120692 1250 635119442 635119453
    0x50c0a06090e1b1c0b04050711010c030209030312040311100501032a15030b06040b0a09080f03070f1103100f1a01050d0207020105040b040e010812070f020907050c 72
    0x40255005841c0c0c0151040c1ca0281c080ea902c40b0b0b00d224a00e1034120190048501003003144030700c0c1c203204041d22004514420400f144080c06040000c1c01c0710343c00c5940c440030441014503086c0425080c42aa044c0c01e4441c1800c50410f522800807075070364003460001d810303d903d03840081070a040c060006001c500c0c0a10049a400303241c1108040701424082c8070880b00014458040011061000c2c0a94410f0a020034012501d514200055202031103104900c0203240d0381c0d041500194440000608c0034110207203a003a41d0f10000e150052402801e68082c20450700300105626241002000f00c3c0c0c60313a070304940c4940b0808454100011154422504281d052240c486110442e440715001074252124000041081d801c0c0c3c2140030164208503180d45000404c1041503c4d20f54403554040c0c407519006240c85c5061980783c0b05000030550154010800402c0080300420495070200b04c0c40111031141074020b800c00172540e8503000780071726800000b4412441200010300103842142034680c0c18905504489 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 635121942 1250 635120692 635120699
    0xf0316060c020a090b0609042c0a0c0504060b04270e1e0f30040b040f0b0415030507120c0e0a0906030825150b1c031407050c0a 56
    0x1c104216615089015400c200d000140b02e07441481200c405210241c4094a02102401000014004081c0c1c80d4400c080c00d600803a1441c0380c100858a20f00100c000405a000c1d007803c01c0c81a140345079014521841c1040024440e01851405441c201e803150003000c00000560111241032042c021804c1e205c0341c1c5001c0d075100781d214002030034160450321a6100780e543c000046c1e0050f1500c1d064032202c10f16510140140c0014040d800c180000c000301c1840c4124a20010f80307015005034055445000d04207000314060054403102c1510f00b004200480e0b00b946410f2800c4204010807246c000c407401856500c10006000a00904455076960364a442c20000c4440d0018090300c0e542c00701022600460b420000481c18228501c82c200551360003039210b40c1019401c1c40c1849031960a98003c0e201031400a00c04030000300c081120300400710400c08041202d04c0d4500910415001c540d07940c00303000031020b104a02081d0007009130f16003078200f009015945c0406040151500045010040d0010009034002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 635123192 1250 635121942 635121947
    0x8031b0318012d0c120c021e0a18020715090f080705210c120319051f030302010506041b080408090a03170702030105100f0b07021206090109020f0102031303020f031606 74
    0x40c500313540b0800c00b0007074901a0250841c1c0900303414800a400c0b042500003d000b945098140c030b12003910046c460303540283c550251004030b18540c24101007642d0041844001c00402c0e8040c0c40078100e208070304100d0f0301c10760740300c49107074440081d80038003100c0000403984140709052140035a01800070340310b1050032660300420401d5500c001d40f0001240038013802c0c40e40141c507400490740a040850289001640c00180b040000e00001d011402da00340c40800e1800f1622203401c0c0d940c0114001e40000420b0310780f00703040c441a0340621010030b81307101400e8035801c0c403242c0012000d50801e07000001c2c280c0320340d9084017181c0d14452640015200701260000c0818041b401d400503c205482a0000e1003151184040d4240140c40e5000304007205010300014004860a00080c10309540020000f00c0c8080030021060300784081943d1540ca0390f51607200110130b5042402d440340e4030300b9080c80114581592207002188150841c0002845038210000c407010781d0740d0421030002c01d80907d000803844a581c9001c007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 635124442 1250 635123192 635123207
    0xc03020f07031707050901050d02132c01062c1507080706061418040f020405130309050105030712050a0f1e0b0306150d02010c0c08031b0318012d 64
    0x4010961840b1000284413601c03c4080e20200001a141e2509040e80340007a40082e4001c00c0809020854401002424000e8000c0308007240580800e00b20b00c12407041d00030651900140c00c11424000c245502103850142c18050a4203521a01c480110900e107402c0014140d1450584004404001190150510410500030145e0b2445110204040f546c0c40800030054010b4084950344442c1c4a507840d6144281e400050b603016108244602007003100364005406c9510903282c02c1218551a01c0c0701c401c058020700c00001030402420031a095103413110000b0f1140564800040400c2d403a0030202d0100b00c1306811806072984021010301c150b4401c50742c90204018861414819503050500c544468100800c20900580840007402c0c404003642050280c60342111404a04101c0b584100c01c02003001c0a01c160003905940000c0c41c0d44880030b01306c84085200c1801050342d550010000358507500721014100c20307140400c1c02d244000c898001140e00707030a1038204480c0300402040d40301780c1135690311400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 635125692 1250 635124442 635124467
    0x7030606080906091903050f0f041d0c090409111e2e030903170c030603010c090e040b04020d0803012402011a120709020d0504052e0c03020f0703 64
    0x21441c401d5a02e403411559116815110201a50000110340341000450710905902500a0820b5840d020300311207101c1320707540841451503188074085810300064200e00451b00c50149403003046ca9540c1090409802d41c2d20980e03408070700c03a070341c0c0310304110410041c903641c91000383d0b00a041040310ba02c1403150140041585110030300c22441c08225a0a0b00614100e039400c1c17886c0807007021045000f40009400600c180007042c0e0500c642c0b5020800c180e5841a13810788241a01e908540c0ca909040c400c0c5030a503081e600103501403014104062003030200c4c1c132512035031081e001015040c480e251400850800c03041c0b03d00180c0100d40000000c40ea00c0600c03507a0b44011302807800d103003040180e0301100302c0c00c031000518070080007030315250540002c6c5404030383d0090f80074100060710201c5580d505007104036400f00e00c0040e1500d4940c400c01c0240001400000720700101c025540d616880c00203112161150a0000b0400d86940c0d081030710f403050b1195050302c0e944991050100d582c2d00b0710341000341940340c0c10710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 635126942 1250 635125692 635125697
    0x5010506040e0f060a020a120e010c08150904020f0609091005010206100806160306050d0609060e0111040614090a0305060906011514180307030308010806090c0f0103020c0f0607030606 81
    0x40d001c04038000d0000300000380b40042405002d25417210380140b4007941c04000e4060420100807039410b8148070781d04c122201c0e0b0205a00015030705901e10005011283c00915089180b4020300e100d04164036420505c580c0300d42c3c1221031040030010342000136602e00601c022207400c003190303604011400043c08548000e42d02c0c26021151580d0b07a03a8036810030b500b840d00500c200c0350480408145541e002c4100c02900d12000c1c10082039040c0c4071000b043c501c2c0c024105c10303145580c0315440c440c148113449c4981003c40b40120004e000c10388449030340c0c00307103441749205142c2080707a98800c0d09188141c200a6520440b8000c200409880c2e59081080d40c400007641e64494a0040c41c000081e01c01710341d94615003070001600c8124500d0002d03018850650000001c840080100071070303060040e030342440400e005d503200c0c0e01c0300e20b01541015100791408500800b1000390303520482e4181c46543d07a6084071442b50a00b4680540d0302d220340c2200300d0500300c104403060326074031520041c0300700650940c21070421340720141e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 635128192 1250 635126942 635126951
    0x5280b030414190209130818041b05040303080a0b03012310060905060706150611150603030414061c023109021e040609060e101e020c030a0501050604 66
    0x101c0c182d070b20f0722040c1000d00c6802e01c10728100b1006080103c03480b540510750241035920020607840e4106994007041d40a1000412000c5102c2c45207800d1285440d901201002c690340a043c8440151182c402d81c00040c045c0f051440000b803c42200e03400004400360064000c6c03010400e010071481c845512000d008100d6000e00000550382c0c50501c1003001220f10aa490011050ed06002c1c0015584903120580b91035490f000984000c00000c100302c80201000d0f40c6080b0020720000780e880c2002c16a2030040790100b005030900000c0c0c0c0c0d0010648003600e00d1010618120810840080e1980c81001c868490300054004c4007038401096901400703e050f40707104141c5042c0018100d030032404d010507043d41031101490801303010ba0b40b400d034003405500380300b107198142c441034244184c2243c1c2c001e5400100040c1498006000440d406241070940244c2615103440c1018021400341452404050380784140150301e05d14081d0f02e06c2001102c29444000c2c040e00d944891508000d40a450201c1d2840e002c2e40c01d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 635129442 1250 635128192 635128223
    0x325060801050108100501080714070b1807140f040b1206010501390606120b07090b0c0307110310060f0e060102030c0a0305090301110318120405030705280b0304 71
    0x2d111014405c43c1c852841000c032034100001981c0b81c5102400314000c1040800d00e20b800282d03000c1c014000540580740d0b6182a2034081d014609903600071004414a0300200303401c12600d8081003005c0710b030b200c0480306a181d80c140c500218000b41985580360780e02c00c042e115141410700021030702d141130720001c0e1f80c2c145c00c05004400361a2004040c0c42c100444035506448140c8000030a240d54200310712916010a00071b5541403602c0b00100c0440c42034850400e40c03820303c58140e4000c01020010049624030710b04016000000303980700c2c041c404e4050b21040210804020f959002e000640b14500c0c412000c02c40d143c0c4504800c1ca152010340103121807104410301048140d0300001c10303182400003010040800b190703540d40485290704664012074040d92180303246601c5c501900081c500c2684d81140d41c040450411005514200041e01c0b00c031003130001004107010544012030700c0015980d0503543c41046041e007100c902200d400200413940d081108860214429410340003e6000341d004807850030303001a2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 635130692 1250 635129442 635129447
    0x2508090a270b100509060705070807060f080412120608010e01060f050414070c08090301090308070e040504080306010507050313060c0b09151929030f0c100e03250608010501 76
    0x980342c51140d0720420401c110049648104003c1044070005040c0c242001d509542c1c841c40c20185411060154010010a0001c580d00880c80d41e11940140340c104118101604d4074240c20b0b40040400041080c080942c510382c0d2816000700d130003080210700800181d000300c02c400d4028602030140900021080000041d10700e02401540c14840240051030659116400e003510302c0708000b402100d0444041c0400021a5400c1c0b041c8060b2138001d0311021200c2c90540d02c000c00028105400e103116a00d00741c06d0001142011094030340c0075a007800c085a4402050804610318040e10000c1c080700c2c080b000d008500181c1c0f02d99800041031007164031440d05c0e103400d01c0b102e4071040d08500340c240481780070340050304012042d110b123650381c440c0600001c1c0c004a40c00035001402d100f110580c00403502c2e002c00e02c01e1800d0070084041301c06640c0d0b016201d582141d4001440c400e52090a08082245410b032000a039503040c00803242c0c10000050180c815070400340500201282c6115441c0410103c0e80001110f50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 635131942 1250 635130692 635130701
    0x60507020c18010501051b030310050922110102070e13170a0c080f07060c1119020f090601031e0f050604050c1603200105060f062508090a27 62
    0x2e40300002206507800c0c0401120710380c00c1070124a540c40a04052840060021300c0118002d9668030002450b19080000b44140902d0141440c84400e0081c2e4800d600c40303c0061030241074a83c40841c240548085400407454040207070040070740c5507103980500000d0450804d00155a42c81075408440e040007205501d20103000d90364191000c036400c0e21103e000107800360028507050760380c3c1a1840c01e001d01501e40b4412201c0307104a10000c01c0000d01c201161010070084150f00120b60340c02e1642c806529030100700e040d18041481d50056840e480440c1171030f8026040400d8020910300450300c2d01e1724015410000c1d00e42c1002980c000303489c0c00085041c40c1003900030944601c422907240c605e031000802c00483c0616400d4401e0b820422040300e00c084ac0303040d000e801c104003690040049818201113040010061110031020f10071101040307e0f841c2c2d00c1603507a00ca092044070440407c40c0e0342c0d10b070410841520500040c0780d40700c1081c000110750410342e04c001c404414101d02d4504034007017900e581c100498 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 635133192 1250 635131942 635131969
    0x1813140f101a030d0c0213020a1d0907020d12110319050f01030f0f170408031c18020907020a05030a030504053a02030c0106030302060f0c090a0603050919060507020c 73
    0x40c2c103ea0344130056a805030905d40350716031014041641c002c9492035a1401c80c1c11407001e0302c0005140301c1542c80403654004d003141c038400040b80d2542072030900c460040d580b0480304000d2010b01c104c80d500c118103181103610440c6402c182403e4075a503490900058400070903800d00c1d2004403840c04000c9032412800c150f1281c16254000410014003002e501d80d003031074082d20381041b101c0f0548450352805208102d400f8000401c0c61900650b22440c580c22001070400d226452501801e15007602c1000048112008407681501504e41c0442c41c0c803511001c03410404001740281031848005030081c130150381a81300510940c0102d058031507031041180b20340000b1b031035100c83d0140c1c17110707148a18000f1140b91401c180840e0040c0100c03440d000e40b2440c0d0070b0a40d200c9074825000360708000c04000c0d101d1141905950b10000f14030b049803403e090f00f40002c80b0306491f401240205551030f0002002c100b0100003550302c041515441948070701c510314254018050498a070310042c059840442c0c541d003030840c9400c625 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 635134442 1250 635133192 635133199
    0x3031f03061a182a1b0705101d06090d1719020c09071d09090a05060108030a0504091802220b0d05070504050606120a0b09061813140f101a 61
    0x8100c0300d80b0011502c1c60543c1e02c86451401c04012946070285c00ea4070302c802c50321040001d05034880c40c1c0001c0040000c1326103c5541403100000d001e4242d081c05458011041c1800c03518642c80b0981e003000b2071202540044014101e03012a031079480c0c5804a50080c10301e02e440620021101c40e40c00d20101e88488481c09801d030032488034000300e05d88601501100180300709048002080292307250004240ca04c1c02c0d10b03012101e4200014100c1400300034440107000d42080c40056240240c03401c0700901c2d80c807543c880c0d0840955203c211003100200c0c403900d01c0c852a0001c0900b9900c403940c299038201e40d080704240c1540c02d8646819240c180c01d2034800949119000130252040d0340c81e100a01c00036141c003c0c0800d612080401c424140c00d41d10000140c01102144400070701d07490101c05000c2442000b900041c03142494182001c40302c071b40300041c40d1303002160407040010b04100b45000c0f42c01102104a1042d01c3c09511402080e204d00001c2020113040040c00500c00f0383e0035014042c60103c140d0007032070342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 635135692 1250 635134442 635134471
    0xa020606010c0203010f020f0c0c0109080a15020423030c04060f12060e06250e062a010e0c19120201232704050903031f03061a18 57
    0x4003907002e210801c600600160002c544911088101412a4000018034141a002041c4600d08803401c01048402c44000e003000c060b668103050710341d81d696030349813402800320000310303021403c55a840d01540e0003000c04051460203418000c04812002c442a07400c5070103841944070480c0d540c5841d01030501214100d00d40754084a061110b084002e500201081c2e40c0c641d00d55402e088030794410005d0f1441618903141c001c0e1492081e040c1154075209180c40e035820424801019602a502d40c1c04840c1800100d8848120710540b00d60800c8000c00b07042c001540c0741d40391140c481011800481c80007480ca90464426001c0e00103484425600145401a00481d04550a001e401540261500c1044404549022002e00102c0040300c03000e500280c0c1035850007410000780490151f4800204152240c21a014006464015101e580e41e010040610b203a50342880304a041180d00b03030344440007940d08400b05014608042d407001342400094546103004500c0c0304c040080022005120300e0203844501d46111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 635136942 1250 635135692 635135701
    0x40209091c09051f14070606030213060e01091a01080a0b0306070504080c030a0819170103060b01110f0a020108070c21021c050f0d0f020d060303020c0a080c0603070917070306110a0206 81
    0x340340d1b400010f400c580641e03950a000c800350b52480540208030074a80d10202d010750030000e5000381c203001a4801d503842401c00700143c0709041d0002c6103189000c02864402005d80d0b0701000d00000c0c102d0711005a030180a0348040c02100303170740400104242d400403400c844030450f4520900d50364125028015060070070502150005551982d15684000001c3c030381048203000a091408010800380c0c41201c102c0d55502c2000120b58220310700f407a08460b50000b5244c4061030440687c2c858a0781c16009041206140024903064003400450110302d80103545d9044d0009102d04600c1d0001512000b9000362194100c2d042d80890810718006400106540d82030804020030001c0c0d5076a0058419080d0b45910383d04840d04140151010340348103020381e000444e5540c6075050280c01c0000031794245000e60f9004005200030800098000c43c0001d0a4900b00c4d900d54542e90203d0794081d031a04480070141c0e001040c10001d460006854041d030340544410046c41d440f070000d088a511032110982c3c0540c01000029 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 635138192 1250 635136942 635136977
    0x615020c0405150a08010209040606030c05120912070f021f050d0b040240050a171006081c020604030e100e1003020703080a05040b040209091c09051f 66
    0x6036080600060000301d143c20000000703040b408550020100ca80d40412103840340d24007806640d0040ca0303c2d040402480f0745007003005003103208086040740122060404203907008010800c8000e0044510b82054441409280c505010903211005030b100d902407581c07911058507c820440a1b40c461034a0300b5190180c05800d900c060291001ca032a409a03090003010f004929501c034042044c1c1c1c90102c2c502004044640881c42003120020048956440c1700c41840140c80d40010903080d9000c02601c443d070101902d200ea13180804510800c074015091242c00510207100003245d220700780c100254142d090680d035608a903512002c590140c0007405040c0c07032403e0303820721007448410b481851408103c0b02c80d44101180d283c0d411385060200186d4005030110902d5804151584c0103d04c11070103000310b0500342c031180301e600000341c4060320070003120780811a100e0040150640505100451003000205144043c0141c00d0b148030700c60041d0114420328545001494413080c070303480c5c030b901c814102c480121002c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 635139442 1250 635138192 635138201
    0x30c0c232b0b07092606091c14040315090c0909050d030e03070c15020c120304032a060201050a050f09070e1306050f010915030b01050d0c09090b060102010615020c04 73
    0xf1105000442101103880c1e0035201d010703d85080e0180203642e0560400c03641030b241c1a030043c200301c0c0d240c00c4805c42d0001c507500c01c0880c0c0c400320a90b240000c5802d0b007800c82c01e801e5100310344c0000c00098804600481c46206038000030919030251038007149450780c45292205403410141c0050440e040340110b5844a400b0340d01c5084014400c6d0110307800c203180d5030745071000c02996400c07013005c0d02040d2100c0214244d0400888030f42c00805d88078074201245644c101c5603680a9400000c00c40c2d44c0c1545040700c05001c0b800c500041030001007038a2912503583d64060b00078003098a04116180c01e0800041c81c584941058a010300380f118010300043e4505a07400c0c2c01d44c40c01904028103503d20060a801090141c002e03d4001c00c0c55401c01c3c4515450102480301f29902070080b0307000c00700c0560301040032508404049045032001d40760b180c500324843c41d01d488800c209070408800189090002428000c0307010447e84030310000e070020083c80351644440f55035a05900744920059002152500306070800343c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 635140692 1250 635139442 635139451
    0x3040f03021e030f0a05060c040503030f03060409020604180507031806090203030d2a1e0c02130203011203301a030a141018030c0c232b0b 61
    0x2251001c00c403960003c1c1c04c0404d001ea00501c2a0311200710041449024044640c000310032104c0301c0e1606213041c010a440e07019114202080a0300400000ca5544464000c40700d0180d00800d610340d6240c90f100700070317417441003000c8841c6030610b0f00340081c2d89a03001b0310890220002100442d10010f6096503628081d0483c0c407001c98060106200d6400203179014080c48003440c070002400044e59400c50521f02000041c140041c040041c11801c90f0312100f1042c4503000c4105223460844c0b032010690001c0380d6080321134006030b04440e100200001d01400a514000c1141d0300c40e9030b4070a20b40d6050405403216013820f40690040d940c640c00c001e100c500d0164014020001001d007030358100301850000a04244442006403007510040c485120720100a010882060300c21407020043c1008031443c0d026801480c0d8001410700071411030034424440c81103401c10003010003082e1001c0400c4008e48170990160f5030180a4000c50340803800c02c2c6140040546040c100044031040d14004035203460341a0000c10240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 635141942 1250 635140692 635140729
    0x614091c080309010903120209061e040803070c06020c01020a02060a0c1505041211010504030e090703090507080c0a08070b072a0605030709050102061e07050919090b010203040f0302 80
    0xc0d100400940c40a000e140b10712105000055260700b181005000450014024100c107481005110a0340e0341c1c1c0c0c0c1c19130b41d40088203041c0900e1411035104400e110310590300318880601c00403c415041040550032541912015804d407034909500d42c0042e83d6a58401a000758089001d0100144940c4100b5210301c00500990346400f52050748160788048901c00d44055503102703079404e0b00c90301954000007440c580329540c0b0000c20841c0740a0320001d0000103101c0e501d82c41003042402245804d417181d04803200098021094139099a510781c94103564000d1a0115030088141c0000060781c040701041590849540e10421481d000445d0b880102003070305c5141c48200409041c0c120718500500c803104e0000f90209840d07030395690908540103003210090781d001c5030455002c20100709488a003224028800b500584c4a0131b5039894046e030584485c01600c8034590005110901c511896030251600e90465003c0d4130f0421030400544012a01c83c86140100c18158007000403c0006003083c2c4502c60000a041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 635143192 1250 635141942 635141989
    0x1c080306030c19030b0c03010b0f03060f09090109170c10020904060e010303180902091014160c24020618011103190f020a0e040e071a030709061409 65
    0x1400050050b80346100031642d6003c516018420000e0f407400444e00451440701141c110340c50030700a1ba41c144100044807100c80d90100108066884455101c0c40c80c050080080c1d0709850b020107a070b402828401c0007920090700d54000007107408034007803c84100010f41005800000524511503001c0d601040142c3d4000b0f070340f001c0000b142c0449400d91400f031440b9070782d201c5c00d00c0e81c014600e01c0d0540194100c125034500c100046481583e80313090303100410039a8245802000c241e44403588c40303806000c148283c01c020001843d8200491100ba2509131040e0030302e01003240324102c0340480150a40c1ca104130250f8000000304040c0c2e0348200550310240c5150001051011144600319010340043d21850b030060000b01468003410428010018900c0301d4010840c101810600002c000700600c4002d28051755548408102119041c005580500684040d00403980b880c03801c4c0314280d501c100c60302000030f0f940610100d0710030301c5075009200c00070f0001181390030300b450a020858046542032440c01c0715a4507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 635144442 1250 635143192 635143213
    0x60e0102100515090915060f0f0904030909020406030c030e06090604030503040804030c1412060c090f030703081b150105061c1b09080c091b0715020c0304141c08030603 74
    0x1104d10b494480c2c0b2405018151106840a81d41c41c12440604020b10030081c002c4151559207403201402d01c050001c50312020070751200e06043c0d419200b10b400c030782d1040d8000100461502c0d0160070107401a0465034080242c107000016242d00c4070b006890030006500044041800f29103d40c020796042401a800989802e07920fa036004084030a070b5214600c043e10b1552442050301c1c24220b100c5440039038170081d114614041d0714201c018410715607018809c0300c07040105031031078504011290140d60b01c00b4542e96036444100c1d83c80845010756441e0000d500c00e05020340d011000041486040b114040e0402c3c0c100b10810038900d1401291103254150306aa40f10301017040140308048e02c0c8420344603201d40030402d0802c0c0c034003400c11200b4000f070760007416900203000203010300100350109c44618100c1162100710070b1030003c0c2031140c0d118407110a103001040c8884961004401402124441c08855003015070717602c20311204400c140c110050041400c544000860700000096520500003000c0d1000c0300107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 635145692 1250 635144442 635144449
    0x905060a0504171818091c020a141501050303071a0403050c06070806190b03010b070611030f090610030b06010f09050d0b01031b08071205150a0510060e0102100515 72
    0x4100102440700130040a038480a04040c03400150985614411607100d241640d2029601c0280200e100c0c8003000c108a1280100d10034070540c2c039010b601041c000e1903218441c4451755208410480c03011072100910000443e840d0010413107080f551320000340c03028104180c003c84101040100b06406000042049036103da07018803035240300320301c0394881c0007503818480c040c40015444d5001c50034614803001014803640e000441039a04580e0944800d95485d4007070b29180c0042e180c2441c400880c0d10010090050380b14400070a5446105080200c3c0c1d810b58505501500340750f001d11000d0001c1c03002c9000f28219504c103150030421007080e0306005602aa4078000b00d8001c01c01018191780e84041c9034014020448038161081740d00800328564480c0b942030440322921459541314440e040c0c5007107000702d003c005041c000c84c0080300440903621400c3c07803c2201400a02022540b018207a40d40302c1c0003080850003601d03002d4120406a00404268400b032071f070007000700b101070f240280d8030411542c0b045031541d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 635146942 1250 635145692 635145697
    0x10f1d040908070b0a290301061a0a030b0607030c020415030209130204050f010305071e0504180213060b090f01020a050f0c1f2115030b01180905060a050417 69
    0x620070700149554001c0c904006101c00c0025040d4a0942d05001454410201c46030a10015011404441b030030031502c000024014203c0740d11911150340304035000f2450420001c044c2c02c0200d05900c0508c8030b006501c080010354816424000c2c03708001e010960058102a07010450208045012900c1c140d201d03000038182020484031003452020b40ca800c10b04500b4140101c030f03004011605042101d50650342c1d42c84d2568858014428410a0940c4800403821200000b81c02448003400420a003422490038191340000080168002c2455104006030201d01d4400c003012921002089805c2081e200108600c0d20003500e12241184521031081d0041181031051400c1d40c40100000c10445a0000500c00c03803580280f40384448180182c41d8078095a0041000c48500400c0020400741c0c0180f8440d5000074415001100020b003d403c0e4007208100c00145000d0603207101c0c0079070700b0b595020409014269608207400401c0303a04102c010032542c00f001d03001141c1051080981e42c00342d40d400d00c5001c0158 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 635148192 1250 635146942 635146961
    0xb07140f030a1103090a0509070c060e030304020a0b03061e0301060e190501170a06050a06031b06021b01090e070c1a06040c0e0f09060f060a0513060c02010f1d04 71
    0x140c00000d160300c14643c100c104a4001c01e9250301071814466148001695013280d40700d9240250141c030300007031000380304004a018540d0b0081041000d561101c40e11984ca0300102c8049002d241c280c58085200141082501e1080740010035810b122154500c04001c42d0010510082c5c26640361040464000502c0c401a8410503803200c03001046500c0321807200139601e06a001c11b241c201c41402042e2036050116a041c0c1494000b10045007948a0080c560014090399001030300401608915450058800b116041111a00d41c00c8454074561001c804c0c610360050301c2c045012440d5110304101c8a541119115800030702400e0120840c000c076101c00054a000304016884d902d041f404005151070240310301c0d041842075140012010307403d2070206400c1010480400d2155500360b00240b91f581d20303602e089412501c0074240c0c2c0d8031250b107030340081d001c4e030004980b444150303088800100d0024403c8040050b42c40c1c0594645c41281502e0109440001a180702c207080040548041219a21240507032803d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 635149442 1250 635148192 635148223
    0x12040902030618060105030406051512060f07030506030712170a050c06010806011a0706060506160203010e060705031f08010c080103050d030501030203280209090705090f040b010b0714 81
    0x120b18081080248003510780102c40c3c0c0399201038081c0030203030744c5c4002940e0f0f2141c6e2003000010217448520000340300005a0308404e5208290384226030110501240d9a0f015504201c0340d001c1e40d13101c226084d4152442221516010303480750f8810854008c1c00d40e200101c690145844c2c800c0e04000f8018100c65a04c8002003401140300040c22031a00c1d4010040e02c0d00400c145005001c07a9410844440312001c00d0440096003250f011a8a0f003c1c001241c2c0040001d00c0000e01150369034680c5c003c440e40320101c218042c0e1280d4a04a0186100340012401c3c6100e088965a102d01c1e5646084240b000d602c05031843c200c51134011540402d04600900c5004140d00e225120700420758503501c0e00034a8803810010940816041900401c0180c80004800040046030206007005020384087d075402c2040b003000c06503201c1210f505000602d03c01007040c00960701d065500e04d500c3d55074148402006482603400074440050746004006034401c2d0400307018954071644041c01140345030150f440c070381155143d85020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 635150692 1250 635149442 635149447
    0x191517030702100f1b240b1c08030f040f30030c02100e0a0c090219080f0a0b0a2606010801060605070809060f0a020124121412040902 59
    0x5514240c041084481801c0c5040c404c041e0400000410b0400c4410a40806490140140042004004000e04050401482409035a02c004910005460b1010030316004080300b07550346280d04640e401c1d070030805800c0825140b954075003440100b00d0070401082619411450380d0200300040165014891102d40e003106048440001280400c20900d00000c50b020300d45441418902250003203a03a01d5204905600003811949000c0d01c642410b000080041c2440072144000c900b880c0c0990203027901c114082c02c4116040319006c0700b41e0341010240d60220084070b0100028200758074640140c05010005401e03407400d60f544941c8942d03000c0b20700d6400c0041480e80c0c030303004145d0070017002264010500c2e080240080c03850600c0c00340241c86100c00142012000043d42c101507210b20088600c00124251225a91030000354003c0c02071082000314040d1041d0504a201402402c842800c10f07204520103840420a45030b803120840050030a42002c68010408100035014501c005400208074440b0b001d81e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 635151942 1250 635150692 635150707
    0x12060408090406240309031e020114010f06090905060d080a121419051308130812210402011e1d04020316050c0703080316110619151703 60
    0x15a0f086801400f08012540011070304094071514003aa8541941800548030240303040031a240903d240b00c42c0710140447c3c0c0880c500c145d056200300700e050072682210039240d0300c5022403801445648035520018000300001c0c014024160311107508000000d0801001c60481c1c0c0d5424956080b1400060105172140350701c0c0c00320b60840c0200c502089004c400c14000b1324003e6851011a00300000240746540e9403800a03100e1064113010001c0d694104c0c0a00740c6500d40c9142e0800890514082d00c0301071300a0b4401c80c8a4140e0306415100700d07008402070350b10544d10706280307081c1140005100340d0412074141c130460351610740050503407040006075070381980c2000007104824941d00c054034800d00443c81081080700071240f40d0b56624500c501840c1880c2e48120b003d01051400e800c07a0405481c82c84004140304201c2c2e0304c00d00e0001100301c507850703513548003407481c40e00c1d0b86889003200c0c0b070000c005d585006440c851302030b544034104501400c09140f10752502e1b0f8071903002c0a00c40050001ea50740c03000403842c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 635153192 1250 635151942 635151949
    0x80a0207150e120f06070f0201271a06030a020603041b03050c0111030f0415120f02030a05010503030c0c10050c07080601051207080706050703110316061109031b1206040809 76
    0x680600101e0f40145150504007619660724440100104100078031340d0582505e0900c00c1d0006803041c2030000c030407039008220f103d0460003240c019070112100480e40d0000c1c4c60b14030300c01070064840c4100402034442201e560f002d0009030741c001003085460740c02d0170451100c5204155030b034602950060000307110200f0b0103c0090002d21035200340030707604d0380300303121241e00403800800711780541c0c0d1000e49450751445c07445400d41c3c40002999041c881c042c00d1102000546440b5409036105140001c02440643d03610001d064984c801e414010105422680c1844002e0500a0683d000d078401450101e142c82c2244004504000554210040e40d070007000c010001450100e0315004034000074005005070601e8110707c1a80c40e561885080248940440c4100601d0b00a4021104840340101503e694100301d070072035002003446981c1100d5107898045001031a404200a40c0c3d03800d00c003c0c00070008001c103240c055440e401811441035100107204548860b5440a0160900561144031156141c58101080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 635154442 1250 635153192 635153209
    0x206030a1404030c03080a090809040b03030c0f010509010510030209070f051b060f0a060b0307080403030f02040806062e0e1207080a170901050d180c0b070308011e03080a0207150e 79
    0x2000301f014103203c1030f48086003115045070400f04c801c030740000d4440b02e0080030904600a1616509850040c494803205100042d00060b00ca040200020401e82c0c1d12000681d03100d59042c00040d402115030400074803007600401601100301d109040c442c2c2030a0400c9200c2c0300504035a50050550707003245081c003220b4040308160580229003400d040c0403c40c1071050035002e5000007011042080304000100c1c0905000e907003c1d11015500b200151750340d1340c4505000c1c1d582c98007500c01c00d00032603d0810100003804101c6074039094050310035080145203001075040342c103415030192075a8030820845114214a00c00c102090080c10344801600303249041d41449031102980c010b40ba40b500b40104040c03201d0ba030b13000c8100c0782c441e0303110b8100040b10317040c40300e00e508030200d03900c401026a140024041501407900c0082c1c508a031081e600c4280c1d51703894400404c045224a41c1c0c01200d000390100500001d1300e1507000c1d0014418134412901c6081c0d4819440e203841070854542c2c2c001c40c2ca443c0d409607850500441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 635155692 1250 635154442 635154451
    0x1805070327170702100c08070818010e0d0308061513060201060f06020d090320040f02031506040f060c02030a0c0f030c0b1207201f05060d050601030206030a1404030c0308 75
    0x89040c01c3c0142074012031074040b00c004c60081001207801d040001c000c2e1036010755170810340150566403228116131802124440f541009400715900e82800242d0b450300c0581098119859580e414060301c40009028454060701800801e8120901585c01e040c001400d05030001d002c642c1c0042191480d1241e0481040301a41040045400800c00d244803580c0210fa51011250301108040340c607160040281c40f045540018581c4c010704065411076a40219000745008002e07403240828501d2401003044411b11892244071140c52401104100090240091003220386c000f03400d0303074001d8646994003600c0c00d0355600103100790306140e2002d01c10700c010802c080024150413160030345040c904050351341420703d0007010342d01002176000c0e40289000a450523090071401c0300701242d21041c042e03005813010502c0c810101c0e4840b8034102c0010ba2901c4c1008031050a81c1d0048007518090f4210303024000b10f54401001c000ca1340340c0751884141210310080601d4130440c0295580b40b01a8a07502d0b00500700300d000360 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 635156942 1250 635155692 635155733
    0x140c180708070c1a1026070f0305150403030209030706020604051c050912010e100f050915070f1b03110f1b0d020411311805070327 58
    0x1018000803484c500d403081d0040d041c4449003490740c42ca80d2400a040044e0003a400c00103800700890004459203140c40d030a1555101941c481c03a0f1900c0d004189030101c1c0c80083d0160323220120781c036800101a410540c00c035000345009890301c00e0741401b092500f0400c0d403040c40140e01c01010842441320500070300502c02280341c0c1441550400000042c1180100d10443d48244030b628400da0002d13000b540038107a8010700609032018418200c11550040a03170600200c421410207000651201001c40c64480d003480141104215841c0e614045502c602c80e10411030512105182c0d0141c3c181400b46030504c518032941d40d031098482001c00e0181005450400007034568407003d092240c0b500c1510104400100c10f8075080d80c104220300008000d81a070340c0b0760700480e01001409c000b6980c60390098503152001c16494058040c078038250401d07410518401c6404290030071101210b009031301d410403038004a06240c0801c070f0398002c2808003402c6541e03940c0c01200c290914031003420014610141d0700f0115225 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 635158192 1250 635156942 635156957
    0x3010b06070c03060b03030f09010f11102007081c020d0203010306020306180f0712021b01060f0e0c0423040e030a030b0406141009170706030506030307020d140c18070807 75
    0x988e80c00042c0140c844060502215080006500c0d1041906140c401000c00403691011900415000241001c0050401d007002481c80c801d940c0e42800d04403194580e00c03502c024a001015001c2e19441c117500582100740311740801211504a50074000b40d07010714040c500059a90801c1800c001100c00c00d6100c500c4020545020003140803280188590301c490350303003404020740f5003c10045000b40b05d40615400714203540e150304400d5100550018040d1454008118481038440030454251201103401c00da0300d603000c01c4240300300f4244901101c10282c00c4480b0081d18050a000901611501e51903020f5651020440310002a4140210040c483c2c055804201c00d600300074a60602c50644c1140501035100c228450420341e22179501e0302e00602484400e01803005141d025a074445081e403254500007409c0001156003480c000c82290403542d4000c03c003c116040958580300746284880803c01d440c02803041110480d210340350100c400203002d45008009141c001000760021001410400411905 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 635159442 1250 635158192 635158207
    0x10f06081005090a020f040e0601171b070c03050a060b010e060702010816020f0f03130e061e031207030e03060c0c0a030c0c15020109030201060b09030a0f0203010b06070c03060b0303 80
    0x503081c000c0190340302561071089503a120314140020b481541c0c00000710040010b80001c6900545d0102c43c090035090b40c0d24411034111600031038038903409403070703035450001d4400300d642c10206c10343c3c010700c1114419111058229500e2b1109030604000700710079190300f41c40b07402c500750369a0700903c034180e000b100321007480c01c242150300002c1030550010429500c0c44c101440c00503965008022012a04088000b2034594074090b0601c1903ca40007400400e05001c3c0b4080c0103e003058102220354400c060252175000311a2840f2032806a82111000194041c0115200c5c00d00440c40640106045402500d0710312400028030280b600d045401040322421b003009104500c0b640c200403d1240e1556090302e0035403d80b50a60903c0c9402031541e610059402084413101400560190052401d850190b00204401c0d03545007900e00040c8201035110f80d0542000c815080010074001c0072042d06800a0000034144a004000c5441940050750a8444411a2008008000c810b000c0c520b40517106030003442c00c1c201c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 635160692 1250 635159442 635159461
    0x4050105060301053106020f04030c0e06011b03080a0e0f0d021905030a12020d0204030f050115140105180a03050c130204060503040b25053a0513060e06010f0608 71
    0x45c0880103590750500d5103030b15010300401c0e4064807000481034041c2540e44d581e03880c1c00540d60250b0301c90b00000240307001c0000c00d6503003d00d8900c1c003408580d54921100410540d000c80c1c035000c00601c9e0024155032540780c0c240040f02045214000349074880200100500d419002c0c4c0b80101200340809140d60041041780011004000e9422606031402d042e0404401900d05101900400300f038001e4081c400f107000030510080903100020b0700d001e080200b2030b49030f82e0640038819405c14003800e000300400703c95514887d4842e2006210610740000a13070480050301001030340d0360060b80d00946907a0301c0400d2249417403500d1540112855024071045140c9440c09201501a0000a002400b50340303191000455100401c0d103603410b0589481c500d200c00d240c407500301614a400c0488099654413011030303410042001000209000240d2210803c0d81180c42107000f4058a0001d201d00c82850484c3e030391000084d6103000b040c1d544244500604070300e60600d041c80544402c0c0fa0300902c2041000b0302807011104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 635161942 1250 635160692 635160751
    0xc030714010e070f210206040e04051e03031b0d09061d1c0e010c02040b03150a0c020c0306040803042604080c1e04050a1d0304030212010504120c0c0e0405010506030105 74
    0xd03029000302c00e041c030300e1b800056414051940950102104a0704100c02c102d404114028421200c078400c0c0382c1c980c0074054842c3d503400300719074603484c4a04000d152401d00c00d03110003510259140c1000400c0380d540954604060b00d030281000c00c1c0c000d04840900304060000d008810301c81d2481d80d01c04178002c04041c4000c20121035614002d05004a80848a0039525507070080134442201408849003d60903100d00c3e007032148100c401c04001498480102c004510100b500031409000800034041c2d622039840c2c401c080c0c2e2004e070044400000c4403030b0802c00c07061340314117078203035010103c1450340c4440c1341c146464102030010404500ca58002000042c5041f40e1070342c0b91070140030070b5400240319a10150007400900d050040c16614a0360034480c1841c1100000040c02900c1c42964198080300c500421142600d50540c0c005110003085019040326910404000381718a0107190110700b010f81d0307011000300e850001e4070203503040c4c0d444c0c8040040d03c0c00c09004694010000300140e40d140c1c0c0c0541030034050030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 635163192 1250 635161942 635161979
    0x180102040e0f060103090f0b04030519080a06060302031b0c0c1f030b030c0904150b1e011d0f060708221d0105060a0e22020304050706050f030c0c030714010e070f 71
    0x39254980070270240b6210382e080d640040c4039640721088015070300d1005030890b00121200f4142901340a40403545070b12030f00a5038001e0042603114200c504d0030344080411900302000711074507840b903206290f80b00d540c0d40100320310b0b543c214020b030040c80c00322500080659880c242000d010b9801420760b000035031902000958055000aa488209035900d00c00001074801005025844110407003a8840b11000c0c81c82600700034000d80303ca0b00124081c02041d00c3c00e10811414550028002d44003102c2c6040c00360090081a22403c4031074a4500001013080314a600e618150030000b0110400f4050150300c2c00700d500c00344500380149140c030341c500070008500780708560515080113548503549540307483d0054a281c204a61001160007002c0c8514070030001d410482e410744042c461583c0005d00e96000707200b01c5603030b9400d003c02d1525541c0d6141d2a56032039400a91940c0503032008000400228a040c1229805c1e0040c3c04000318035400956001b0346008843e4001048000c40b0780e20410109611b0141e10500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 635164442 1250 635163192 635163203
    0x309150624020c1e1e06031b0d050a050a1a0d02190b031602070f0f0e190515090c0c0304140a08030a02030301150302160b180102040e0f060103090f 65
    0x74021038042282060b0742190b655800420600721200c1c120103405042d441910700303030340c1c0061854030b920032050a41e50384d4000301c2d04200d0800100b0003200101c011410149110311016190024084002c800c0755001c85000e08000e94031010b12141c030f2283e02907001001e4100d180d211000c072010f00010380410300010002c0c8609907154100380303900606001c4000030701c0d201809507224035001c10340101e4201c0b00d40e02000140102507000c20955007410004081e18590210102c002d414507024489562000d8603840c1c26425940194014080c18019103124444440c00c0300312601c9038500340700703c0a00241403001e400105014082c81a00000300307950448181c002241140c401c05004a500c0c00240d0f0050210340c000011100c01d4150004000e41c101c40c078180f20643e85500c107110843c224016032907080c5100e0041c22005012407800301e003d9400c2080c1403035440121008200752401c99000f64404450b502c0c02c070040280e00c1e50400101c1c2d501c02000e09061000ca07007250f44e07030800c0181e8100300401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 635165692 1250 635164442 635164499
    0x2032d06040f0b03120c1c02070e22050a021002010b180a020403120c03020d0504181a031b09060a1a0c10020d0603050610031e0201180603091506 64
    0x5541038182c03c9055054006800c2e00d4800c1a800720b410b4066000c043c29414520491550320003038940303600104640b002a5028140780b80c200a00810546805450405d140072105104000c202c0300300307840451580320b01d0050030001f49030301c10b01c508550140e0019056924200103070300036403500700041e4582042103001d03804a59906c070111009001d01e40000d490a8a810049440c854011032111003450180d02100d00e80159030320101e406100c1d1b0b0141e03500102510a80701c100500c01e03044090690a4060039464800c40100070a1800902c2203002802015241c1040f1700340c20049042600018141c90741c407451400d001c2c81035843e001c2d11510409050000407947c100704824070050801d412641e40955403080007900680181c245404159600d0103840041080208182e8942007120742c0306948104210300301d44400e591a29408082e414041c80c045041000018034400e20040e200c1c03500c0018006281d820880700714a1410b6500d0300e45450501e00b802581080300200b0000501c08000c1030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 635166942 1250 635165692 635165711
    0xa0e18010602061e270106060c02130b0f04090317091b0105070503120c0d0203040507030b010e0f180708070801200a0212090a0e07021f06120b0601021f02032d0604 72
    0x25002000b250300700e8546d46442e40c0072500300e0f840521070391a0350080740c110007081241200340c0c0866810101e031690041d60381004548030b060682050080c2802814562000d00e0740780401d10f4004001c0321190060f8110020300d60314a100c40422001c840000c0c6480c5080082c140e032179a540f8031441c4860313034001c0700141c00104951151011030720f61405107441552282400d182036540c552181c08201d844036040030012a2000ba081d4140741700e03160442d078141464a0390f0090307107014036401000603010b0207004408220384004101c840010800580005043d401c040800e82e404202e508011a040f4005c100c403c03d2160300240170b444000040a6480d9101c1c40800000c0c840c10b150f60007840640844401c02064035008034010303400040a000d0501d540a00180803001c03914079020341014a01280440c001281045c00010380c00301040c0101e0344000e20320b401035a08900c2403a0340411240c1c000080100020000381850f80c0350400602d400c000c01d030b8040c0c8500102d00000c0000e80200d030b03100c6114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635168192 1250 635166942 635166991
    0x9020705030f070c030302010b09250203091c0210020606130509100903030e06012403050603341e0506030912270a06020607050a0e18010602061e 64
    0x482e1902d0107415071960f10031031032a0501c81c440c01444260050751a00a541d07189040c0884d500d4850019114500c00102da050743c20324030003c2c0f000c10a400c5100501595465403100e40b0100c80610b100c00c0d28500340035180c070403c841e44603004446400c54000c03000f40502c0c0d031a003201d141001e170510070b00450740d0303966034450700e10b040c08a5854400303080c18107541c00b042c1601540b1032204800500c0c21786240b80e8807008008961214200c0018640c845291491520303882584895088480102564001648409a000800c2000022203400c440000380200558034110fa40d9004101c01220b12a810f00c4080d280703090030f40c0621400340191400070001d420380005018001d40c0c4004402e24540310011220312030061445240070900c41d900b60345d8103007294178014180d601258000e9009122076903071240202c5543d008007a8041c00e01010450454880d5507803407042c010000207507034a10840d1300d804c800030301d002009044585445040440f072a02185102c1116030f01a481c07000322042403003c24541d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 635169442 1250 635168192 635168197
    0x5070b0403020f1f0b04060b04061206180c11120703083312011107120c150219110a02060915030c0403050106060206010617181c03150608010902070503 67
    0x100b0405002d404202d0b4241c040c000c83c800d5002c1300580080000010b200c061000b10394090281d100161818002080303114492003581d12490703c0500089951a61000000310480c644010801e03903e8466031402d0846901ca454000f0001500c0014002d00b146540c88003003602c00c07220041d0402034100c00140c4c1c4544850f011003240014407801c0d4509006140e903501042881c003108071702c00c098004c100c0c140d80c60140034901d110840c0046c401d03e080007640e2000b07800d4464042c0b400a000e80c810f40700c4041a41031813071280c070000c03a00015035101c410418480d619111004084180104050216030080e4005240700d11a075043e2800e6a80c5c4003000c002030164801d030019800e0810002040200300c8003140d0180003207031302c600024040543c851106a846850034042c2c140048d00b1540c4004600e50150241a0051a08054600d05081d210089400c1020000c100003803580c05c4a0049070007a4188580d602580700000303150002805c0010041c20355106110344500c854004c50b0440074003030180704 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 635170692 1250 635169442 635169463
    0x6020a031b0206010602010501060e0303040b180a0603020a0201110705060402131e1b02031c0c0e0904034a1201050108070e070e0108071815031d030a05070b040302 72
    0x1200c0800d400302210082d83c2e00c2007402824019400c11000203a1140150200e07503102c100100a9402c00c1e05010b03541142d500040c0400008408005144c141d5440d280700f400c001d4000c070364008d070341c6040c030308000781c251680f8444030507001100f0030000c0d01080c4041841d58200f035045aa4405401d14102e031040035041c00c0c40380b80200b0160a0365401c8994a65000c1c8001e03c1a070041003825501d60708082ea128052542c51103051000340c2c2c00340348800e400c3c0c1d2002c0d902d00c80500701084080311510100f0641034044404401149a40642c00717011207440d9861110404080300c0f82032604801e01e01101c0f220443d0602d01c0031340c26564180d0640355a0301c82000c480c03504070300003003160350b0b9100a12030b900e4030544284080c504481000c40c1c074461090b113900d96542d0041c0c4501d040d940310b40c0c1049500f0f0002404190000049031000304401c42114940030035070080b907030301040729003010074030f02080300113100341c42140c0d84204021550182c1000690341c0540d0003070034540c4c07035964500342a418880c0541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 635171942 1250 635170692 635170721
    0xa0609030201081b0d06051512070f020a1a071b031407031b0503030609090102130302060306030102070c090605040c051918090204060507140c03150c040504050c0405030c0603040c0306020a03 84
    0x100000850781c00d41c002001c03100300b29102d1144154236aa011900c3c481c455001c10700d6203410001807031981c020b000c1080245114811169503101c02c1c1c942260710040010030741c082c0c0c3c04400510881c0c40d80211080b5032002600c1c1000c15125055801030070b51564405980108080418200103160140520400c03850240c03001e81c262600c03600c0e00c0341e10b86c0e100711a090301ca400c902e404039a00100501c01d45500500c2d40140103112415a002c00403640c00c0106400d078150340800080c00041e1190303039904d00800080d41d0215400b03040a04000039240348800312410007070144583c4075103440000f03101ca5001c400703043c0300e40c1a900c4003021001c801190303081009120300021b40007c416901c41c000304141c031b000304403c1e03030700039400c080040d1110360324a11654580d110404e02c403400e80520001c00d800c102404a024601584c070340108043d608129241c40c040400071408010600701480000d103840e204582a500d0340c40c2941c0c4078924100bc0d80009814154041050070f22035010b1b6010070340c0b078610782c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 635173192 1250 635171942 635171947
    0x3030f0e01021c0c080f07120815130f15030c081f0903051605070905061c0b151002060a0c022b03060b04030f0512030106140304170a080a0b0a0609030201081b 70
    0x6c1c6803007540c0d907015410485219085000f0180014442d40042e0301540072484030801444200b802c100050132055041c00c00309603101034090200400c1d2080c203202440d81c0f0212482d4030714604151000038050f904c05401904403a9500200050080d4170a2444482e8200090603960070304040f21140901d01c01040002c0206040100307104000a0410464a00d103506014658850052000380c0d03502603201040d8400c4000c00900050b0401c004590020440588414040c0c51400141c41c02400b0700c2c810380940c10203010303c0300c41a0a40900200300d0090300080c1503940d03200303024800c0d41c043d0340e94071501504045021803c0c0343c480e401280082148981c142d4503291031b070500b81468044040c040720b8500c6040038404840e44200140e9040700d089460307079075000391303460240e51040d400140210f03611420691000114029000901401c03031050396090600e29200c1c404000f1940b1904001c0e1003140c9038001084240d44c440845c00c262a820302e010701c41074544100060f48401d1242c201080345102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 635174442 1250 635173192 635173207
    0xc0f062d150a031a0a0209010503010b220f08120a1b050a050129010216120204060b0307031b0c050c01030f1401080c0109052d060c01020706050103030f0e01021c0c08 73
    0x130f4080318a00b1072a0560840c464648a003440102c0c8580c2c3d8205c0e0101c3c03410b200400060860b017000e00f000450341c1c14104141003031002d5040c1c0c1400701da0440000d681f000003080c4030f2542c0403c0b80c151807209102c4207614140032075a020b44102d004081010800800341e541a04128050000d8100190720030300a0002070f000f04007998203c1c0c80402902011003805c0000c0091758400508950714810103208501d4403070a03c0d40c1e09038800c107416002d90b0003903110b100c001603100081d4000c500c0307000740348c1e80011340780c1c103a04500c3d09085280b00b0b80710402030044401d102185008c29100706440d024240080c5180f042c421540240c284422400348040340d035000003c1860022840c0d491030282649c1d289005500c4004204d800003000e4000840d054441c0d810038101000144180114400103006908080e480030140d82a41d0007517500f154181d4440004008060b0010a008002070690038040c868044d8480008d5549030104440800d1241c04400c0303c6109000722040020550083e00c4c0940c0c4103403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 635175692 1250 635174442 635174453
    0x32412081b16031703040b0c0a0302131e0e01030c0b090d020d03080601020111181c0b13050606041820100503090f03040315150b0c0f062d150a03 64
    0x2c500c002d0380d0400039450008a00e5402e101201c1c03145074040c0b001c1c1c8640d1942e143c0c1c2e00c1250000d519a4040c59420809130f6061201072640750001c0c034104400e0380c40c03800380b40005a9a12072551180441c0794000c4018400103e52a42090030b035030170401841e0311580b2340000248003c01e84400039401107180c0f280d030000c4c158040c0005105406c00c1e0001d0040940c006035004c3c1501c56119080305400000c2050611442c00400c6140c0c00003000600202e01071064440c48d610300380c1075400c1c8510030030f06601042017200900c601c50b4408411641007200420314605610a44003401c00100500c40b4003c0c880005584c0700c42d001c240b46000b07451510a007042000107015640240c030350892610400c074200c40001400803c64003603d5100011503000040354901c04050300054240c03006001405030086582c0f203480000c2d100d0545080f00504410078030f200d0440c14000040c0025100c45200c0044419000500342c48040c0458000c052150350303501d2051410341000191141644403580b4003000080c0070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 635176942 1250 635175692 635175733
    0x90302040216111e060c100203010e100618030320060c18040b0a05010f170406060915051c0c120b3c06060702030a03032412081b 57
    0x144a5400902c121001c181002040c240355044d00c07010140384100300c1e02905100024042c5540c42400b10f5035420301d4008100166002600101c3c4044030780401c200002c144c43e040710006107002d090192050201080e1513030034a066000107002c0c410103c0400d01c0365018003102e81c1d01038448000f81d6245081c030250045159001d041000c2b040d45040350400b185280522480c3c0348240000e205995042c035000c010b50301c01380c0254101081c0814410807400000200e441648030b82d1090703000003000d03410300704d64800303c80d2011800c2c654095048824051900d46454102d54400100d51058010140303161176000049203401c60705142140592a40c100500b02e0600b078011509812085640d542c1c202c3c070b0b424404041c2d4180028000d060b01c0c6051011403d0f103076103401c0840940001d14000c0150082440c6c12000d0b002100082e80d181c802c102c3c0d0f6120003900d0003a26101c6903e08410342c0c50201c0c8294040110740b005441d00c0c0000588074035464000021041207041d10b0140c90300000112000c0701c200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 635178192 1250 635176942 635176987
    0x2b05090127030602131d01060e0a03050d0c0b01060516020616050102041706090a03050a0521090f01050907050a0e1f030f1110020d0807020f07080c0f060f070f02010903020402 77
    0x918210808156494513039200c6e01a100e400460813403503840c0080c105c0d4480300745181260031048071071000c00480c2081c41005410320703280d1911031000e9500d24003406554816072010381000814802a1420380d2100310289105030102e403010707110321208480d05054060108010403940c80003c0004201c10008491001c006200c4280e4109030307200302c0b110703403194080d40c0d000340018010084030b103803640520040c1400306d010449280700c0d41004040300031190410b94200c034003544071600f0045100424000d030382d4068088000341c0070359031801e4003241c6208481c0c06a09180c1c42c0d4440014180040b0f0940c0c1c51106801144441d4415600e0501c10b260700040c1000360b90780401101c02c00d4003824404841c3d0003180f600d600500205000090899030000007070090740840c0503041a006400104010500191600d030000e00004903c4000b0424144035000703c40d801440c040c080e19029a280d0303829905031982050700780c02020300300d1004858140c8107800c02076100b440414505900d40001074102d422 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 635179442 1250 635178192 635178217
    0xa2102120601031e0c0906031109251409060310081b1503181605190e16051603051903110306130207142b05090127030602 54
    0xc2452110164951609000240413540320070000982c0c41104d101c458001ca0185c010300c5103054440e0200020b07602c403a80b0649428602c00d0b44032607649084115150804d00e00c141b81c1100e41100003498004e40d00b40c000400502a0203800c81c1d18074a04241110f41924006007031b26a03134600b0f080b000c3d0b0a840240211000c51103407800d13000042d441c602d041038171094000d0100800f1860400001c2003035000525a2030b00e01030120308071422800800c00641e001c616040c20a59140c100014000c80c40043c0a101c001055058801c005030811040142c0c0c0142002d0b08500002005e643d00382c03a144a801070207039825040445003000e05a015010307001d2501801e5401e103145400020071402d555001200d0000f001080002c6889450510300c0c04079200700740788000d800d003030490b16030fa550004450340802c2d072074201d0602d000b0242c50820085020540300c1c0d50502c0c10202096004003940580110281400041a504e21409500c00124450402240c2d40c1540705130702c920341071020b5000b0074102d804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635180692 1250 635179442 635179459
    0x30c030215091c050d0906021b010b1302091206070305010e06120c040f140f090c1c120c0210030b01230711040b0603070201050411010516110a2102 65
    0xd114189090032402030807148014403002aa01c5003c541c2d40700c203c441482403080030840501411258014002224085c0c54016200e0450314020302c00303808500348003052a40341c0000c001040e582c1c01000d00395000301160040e158103104010a940b007024003000d030b495210310b9041004995040c0c10141c1030b40c0c612000403603503449080500003202a05001104140c01c039003641c451034106603010120515040e4030100f40854601c00024600c40300340c400c50b5640d4201d500b00a0306c6c0000b04400000c0b94010303181c140d650b094000b046070024111000082a24442c80304400340588149200f01c01c03070380c0040002c401c42502c140086c0c010109a03060501144040c500300d0803201c402401e07003911100002d540f07458903083d81e96032a6910004902990300941c0c07140d05090f16281d510245200380015000062141007d0a04018044145841504200007009030407003020004071701040d0a039000b00900490100c000c001001d9070031a400c020711106000302403110b51030f154240d20b245180281c0d1100c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635181942 1250 635180692 635180713
    0x50d020c04060506030601120f0c032403020109031b03020402030901090c2103080a0f090305130906030f080711101812051c0311040e2401140d1404030c0302 69
    0x1601e070540f044aa020038203000141c2554040c0d000040b00d0380381641c0c0040c06031082d2800c08111464101401d001941d5001c0e0500355404001d1070720301c4941514080c1550300e25560001701121000e0000074010a0a8004131b856050ba8145400103168010029912071034407178078850003804a038805032500803030b513034001030104100084c61140c80041204c1300c2c210a0a510280c50188000c2e01034508a582c40011000204252096042d850f100b56101c0365204074070000c1100341e0500303421901b00c0c1072401000b000001e108006071089160b10a007003a88420880c03c020802480f4081056000b001c00540056070644c822078800c030004401c204900e400761901c06240c100070315250700030400d40c82500c443d019107021425140d40300ca1a40360200d201800d00e04203032410341060340051185a0510300b400301032954500c10807160000d00c0082045e03104641e00081407803003400080d070050100000da007421464250040304008209540703008060034140341c01001c0c4d2900c68410740c018021300c1c401c0c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635183192 1250 635181942 635181949
    0x40e15010c03021c0e09010b040806090321042a0617152b051e010b130203060a080a0b06040e0607090302060a0507150903021603150e0309090103050d020c 68
    0x31050303580c0641c0203213108800303d0790041090728002903240612400700c14002555550112050103003006200e9103895624241c0303c0c0d4507000e0081d082580c207400920036903c0d51007184190204004c00500030110b151214102010361403a4882441d00c038151200740482c14152204056044032015038481e58891141d04024bc540e2206032078220303984501c250800300d60300d002102c2c01c5040e4160090251a030f081004210b820702e031074070f0040704c298000254802101842020840d41c0e4031203000207100070b496003030008541501c03080620401c254003101041d626107030182140090304044049900306c40e101d0030090100c20302111218400c0d0304003030390301c024581c0100e1f481f40618000c0d200e014480d0300790b508110154014800c1e07001042424409100424282a84018210403030180090440c00d00d0900a04100f06d52403031800e8152120b000b000011803081c03005205020001002403821010f141c5181180f00c1c641d040d0380e0100c9004004024400003185240d8211501c2d000c8452207500f00092 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635184442 1250 635183192 635183207
    0x30207050316140907030b0306040b0702010c0c021305071101090b040c0501171902071a16090b0a0c02030c040908300105010c0203010608011a0103050c090904081e040e1501 76
    0x6041e800b01a04146600c03a0130448142030f00041c1c5820007213075038011100460305c0c001080383c0a90b600710008062041081d020320501c41515042d1030034800281c11034021034120a80c00704102d52140d036500020301e20a2040482d83cac0c055140c5030090041580d01d0428503039030346080c0c0702a07540801c043c100140c550b0040262003a10f4030b8034050f082043e9141042e03115a0100010001d0440d40c081050700c001841c400d15142503503031507800c0c0c1b2f400b50074804010041840700034080b0050103920542404100105020340da003001c8107251400190b20103201180c109040605e8150b0801c1c10b00220300708126140c2c025000a640c4014100b00c03291842c0c8580e407407075000002020071118040300502c41d65102e039114444042c0050000700c1c1e600d644810b80d03030845000401c185050b90308848141070303d42e1306025050300100f003528180d01f400300d0308000440400d40135000030009240001c1d140d22414024001c058200310841e40c00e9100e5560b1041c0c1c03101c06004440d10307440e0040c10315a00e45958024041d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635185692 1250 635184442 635184449
    0xd020d1b0c0e040602090910030b0610050405150f070302070e15150703031404030201050610050325120509030a030f23060a03140f0c0a031a0a020c0a030207050316 72
    0x1070060960b00e40400c480c1e91641c080c00a0b9009a000c0000400a4440709071483c003e8a089840103400b9245050040d42c4002c044c00b40f6116285403d842008598483d042d2825074038200c0706159030f01e4000030030030710a02c15800c012041d52004244a0185a000f160070412a0480340c0c102a9503a10250000301c1c2c40701c501401c07a801074403410b070040105145000b6000540c40781c14000303288802550801e034804421502200180c0d1542d00300491400d04040c50144e2001d141840d0f4114206040030f643e801e0405020001305034919075a518030907205030380e2010102c5410710100320504194010355280c0d4448620840401c0c103060840c05040b00600c0381203045143d4002e034880c01680085a200051409461282d01c800d83e40c2000c0702280c0700c0b5400c00511a5034000401140102606050800b80143e149520508981604001041c3c8040044100031242000384a8665032040b480740240541c9440744224401e48035200101a000200c02060365400c80841b03041c03801c1410101da16064600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635186942 1250 635185692 635185703
    0x30408120307050f07110f06070c030f1b1509060c03050d0b04150e2401020d0e040221040311031e0c0106051021090317060a03050d020d1b 61
    0x145000d042039003100510707044149881c00c0380c600303641040200d0003604612420b6540d400e608404422624201816003600d507030589109040045942b206900780d03642d440041c110303012156100f0108849441f001e5820540001680c2041d510f6852841170001c1a040080100380741c02c00110b295801b6800001ca5140e265803540d10f08130308941600e019099241c8060380041e141c11070703c0500072448800b500070703240014650902d0328082103036940762620480d80b0344410b4001c10b00015144d9002c20064090000c0c1e041c00c094a6002001080003803080b0426030040d00035014541c0440506046014000d07800317591021044261140c1107a201c0c800c1010030b121525048069814541c80c0c6405070960302e1110000081d03082c1d4641c040764400c04140102c40000304c22220541d4a042d800040409002d5400400c0040031141da5001c0c02c103120884070b1048940c60311000421070747d2035081e214040d42d44201920030380e11045401a542e011b02d07001c0c0c10045428602802f6503108519290b20709241c101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635188192 1250 635186942 635186953
    0x50603031213030c0206190306120507050613090207080703020c010305160e0301111602011206210501020d06170106090b06030105040905030f070302030d0609090209040b0711060411040e030408 85
    0x49102d8540012990201d00f40640e0110b4207002d6070b5450041e1420061580103104540c1070404d000b012901c0c03541010610449514440e4081400020a0320a8540a542d0360399285d208500040c01d10381240e00c10041240001040e4081165400c00b82c00340a10a400311032943c4d0b959801502916402c03200300d02c2c400c1d6600240004d042c402c2c507036000b4031000640006a82c8c8140b44031444150b1000e2468010300f08000650811540d01c0f21100401c03e02092003004007909000c481c0d003501d0924450b0064000000c0180401e100307003076045034403035008040104130326a6203a184d040c43e15100201c01c441e9501c3c0c10740010f0100018040e00c0c06001c00200124a103a0a0004003c024905207105960030f202c144190942c1503c407100a100321030294008544551102e00000160340700d5820003100710313007040c242000680360311100541041d4028084021a90340078000c403401c4a040c84c407070750030b80701e400180000d100400041c1040b260003070320140450310900060964a2180344134100299010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635189442 1250 635188192 635188201
    0x705150105090f06100c0204140610140306042c01051005030703050a02270c09131103040f020f04020a110613050a11031f05160e100e1c150506030312 66
    0x4801c441c04280d01c2403c6c203085019064022030201c424884019118101007001d2001c14903002e10b840b03818055500d40800d626a00e01d0f0b18030a24000644003e0103281c0302c00b01008403164000c0070703960809110781c601c0040c000500925010b041c041d0f0701080352000070309011032582004600102501e4004004084500c0d480d0300b4806240e96458800300e81d6103100c00d001d00c00ca14a01040c40c010300340d685559071654811010003003201081d002800700b9902e0705080b10310f4040d00d6004e6a6000341c2113411038065410600109150340c4a020b0701c25409440040c10111282d00701162440d8091441c0845015590310601c4541090356094007400e2980b02c250301c0300000d00a02050214140c01800303581c040309000b607105400002142e00d580d1010345900410044016860503024030300d95624080300032a60b03020100f00180214119a410000141100101c50701c0e4501c00c0a075509030b403040c6034403108540c01d0130701c0c506941e100103c04660038207021034a2441c00006580300340080d2124040c2c90340b00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635190692 1250 635189442 635189449
    0x17060301060b0a1809050412020c0108130803040201031407121803051e04050a1401080a09080904020c0106081b120c0a09091104150602071e03030305090a06020705150105090f06 78
    0x344d019401c18081c2104d000800c4407819401480c0c012841a0318a01101c1c10038100a8200564a070029041000c80c0d0100950018035140f50200b4a4010ba00309030b594480303000490140c8503240d50305004803409028004459844014442040218401080402505202c440800310004400b0b80092810701682c00304412009a03511040c90b05410329203801d0340e17400442c074110740b564440c0700d4080c0718884446d000d50f00494015486065420200031111060717461400c0c900a1800e128052607011850310100d81c825400007001d0001c29048400440100c1d112109241e800f0300024081d1a0760781d002d403907242000602d10040074005044a0806007030114001c01440f92040558001180d8001000903884611440403150044000210301c1402c2c0b010291500f5000da000d10000d481a240000200e803251150b1000d4079407525010030a41c8130305000c0c510b4185404006055144005650b1041020001e00d034142e031040c000c01c11a05070307601c0c0200480d01300100d502255001c0c5d9500055407900c1d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635191942 1250 635190692 635190707
    0xa0e1807080c060a021606050a11010e0a0b060a1d0106020d11030301050d0804230907050703080406020a020a02060408011a010c03020c011202041e08100e0a03032a17060301060b0a 79
    0x41d07013881186d08111103100701c1c540c82d05503680b010300031800001d400705000e82d000c1841d6024010081c02480296162414a030380d8110a01011b03140c1ca81034404148140c1d91900c040000703101d041ca0030980c0c1c04c0c443c201c03007540600a10422025105c0e094811084a0042046400410009020310305681c64401400051a0411011601c0c060b0400000c200c9070001d401003500c15070800c24544003100c0c404244010034074050240020f200c0c00b804000006903000c4000b80d80240d1200d030152300c0d003810120980c81e00c624114003e41c07004000c42e000c10003600560140c510302c0c403640460002415880015102480d0184e006001604200d0b14041154040c0342c9120070200c0c08540185000c0d66804500f00300c02016105034126605000100010b4108000401040d05040010800e003280e424600f0764603180044010181038480d0010b01d07166003941e00154070421400a289074420710984018028050180d004020510740400309580c0c0c00c05200d000184c8222552007031078400301140588096 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635193192 1250 635191942 635191957
    0x10c170a0207080406020604110102030f0d090f020312070b07090302010e06030910050118050c0f03160201020f03070e030d090807171f0b2407030807030b0a0e1807080c06 75
    0x6408210360000030f803055000b40000c2241368064142403c1c0352400750b00c1c0c150340032283c904650050200c103c04c02c003403030202d865207070201500007a03911051074090070500031410003035454000d0185441c1d1841043c402800514400c40650b54180d40d11380085c3d885804901000c1d000581c0035424200b181402c00046070040350110403540c90058012030102595026001a24114104d0780308503a43c3c29107000c9c144e000301482c2c0d01d5500f41003540150030003602005004451750b13003010381c00911880c000e50403078569028030700c040e603030303900c0c010a016103032002d1103110368080d11070700203d041164455440002550503000203080401d152010b400103201881405058a000c0c9124000041c4400303400800950444400440c074120300400b00006001c00351a8070314407801c0d4052540f000140d403001c46d42a40c0e85824042c0036900c0b40c00003117004204545c2d010743c12071189080400e404001e501802c0c410031515076030380c0c0101c4039032211548890aa11489902e80e2107040e54583c0d600d003042c09003519 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635194442 1250 635193192 635193211
    0x30418112a0105070504050103110408030d021303050a0c0e18060c09041404050105091216020904030c02040504110a080307030c20090106030b0103060b120a111603120e010c17 77
    0x804481e1142908466058510314049000001c0c20099540c160058140200c1c108515a0078280781a0300380c1c2c4c03607115804d0200e80d00e41d0700082c50504145000c04810107550480c04030752140c0603d25110311000703030034050389150900040001e11400c00702c02a032240750341d501000c0c0941340c03921221050140c0040003015071068580f00841401034400c482c01d1300c201e006400100d2503080611000341410081844882007076402c1044405c0c1940768070300c3c1d40e452a41610418119680da0808445400395190001e621506050901060262a400b01c0d1801a401c4440c12507807075685801d41d0307a911500030004d01042d840c80c28900030405010100840c0c004c00109242c0122690380001d400c0c2d2401d81059001c6aa03d501414480d45c6c54402ca10113815000d01c40b40c0b07014586a0b000c003407031600070000403a160b00d4200d02e010802042c1c0a85074440c281e008684e2032004145805080b20301d090b00c00c5000c083c544000c0c840710101c1405000642683d40d00d50001c2451140020220000001d205d0707481b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635195692 1250 635194442 635194507
    0x61005040c17180109060f06090b0120071a070309060801050d060504020a1509170d1707030603061a090a060e240901031113050103030806120f010c0203041811 70
    0x3c034890280160301c01184101c40003e03005584509410171a8516000303e62850324108a000050b6044408044c064440303001d0384515074400c010f010f1420516800050320445100c1e02641086003440207400c0d0507120351641440c940e2a12000c84565409108083d40003044090b004041806175000320b42140c009006403240640300d583c05040310301100c0281c4000f4111240412042d1050000440d40000402c05004842c0e06110020410052060b602c9034800f10280030808140c0654031800003194008000d0201082c000c3c2c0c5010700140100f841d50148841900103010840c89101e040c00f0740c7d00c000104c0003a41c44580001000058501d61700c01c410300c0d0030030070100f43c0e520900c0c580c0c0290700ca1045408010003890078000102c407280d007409055030814006100191304030f0141a44443e0503200000309004400b842450003000601c0c10b6455447d112502e20216408001082620040d4600790729004110701c44004407086000d589840c0c13981488101150005001c0e911000955280c1810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635196942 1250 635195692 635195731
    0x90a1109030105010e090f0723041e02040f060c08190507060501180b0108070c02010e030a060f050f070903080304060c14030901090b090d081b1209061005040c17 71
    0x3030846900384c00681d1615110010006c408208000180c0303584000400b800d5814a840c1594400342030b800506030524a0001e00100c05880301c0e84440b0748001410111071040880e600d82c80020350040c00744d450349010344400860901e01500c0954017982d800600b1038900700d103280b19480780840f181048002c000b0204110800b07e43c082c01407031b001e0318101d0300a0100807410885041140c441801c00c0d0f052040d964100300140c1c0e0040ca031f8900c0380d902824034500040c1002c00203801d000748030f08000d0a4618280201c0e0050711030758030461003400101c420058a45500381c040d2865195840020716100b02000040c0014400750089000c1d4911420540d000004800c405040703070f00101d43c8001180e40d01c1da84c081c00d05c900100b460307030055144006050000140000208080801021680c55218a600d0964030041200445a02c02c4c41da09290840d400d0100750309031122419100d86000036540a00810300385094410008402296110010011091150340d44541d4000b0660035042c0c0448105c5e5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635198192 1250 635196942 635196949
    0xf060209120708010b0d1104050405032727041511041403250b1b19030e012d02210d0501080102090a050105031503070e010e15090a1109 60
    0x1d1041d038001c003808446080c19501821100b241c450b0911800061150001280c2520302c0400803410650340030443e03a80d503051076071451044101200b280c10b21413803200d0300d9011119040b02640400ca07408010b000900c0c40328000058010b02c61055010510046030010300b4484001000400f018400308616100c1200d145143e00154025461641c0c3c0c3c150440040c5014408034005c1101038860f404031010f42403e080301c8540d94002c45a0700c0c0000074103813860780140c0130704501010b00c940803280d080403000021182120051800c40200f00300c144075a507036600481d04007070302444488002c21840c500e40c49503e903007400540b44c6401d40c0900780d1001080c000c555001d003040c480d581c0e04140d5611240340c0f100c04840050348001101e0348188100400c03580da4a0f8518100d500902e8141d841e921240100b200640102d4030165141c85982d0001940d0601003003441c1c1212240c00b581001c523580ea0341c80308040c2d0030030001c0b168002140030005081401c0303580910300585600740b0a0382842c0910010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635199442 1250 635198192 635198209
    0xb01060c1101081b0a050906370c120e04090803070207211b080601030605181b22141005100206060405040611120f0a0b06070f060209 59
    0x1840000c031040344650074840450380d0700400450070b20345080d441c0b80c966a030307010108845040110f0f100c000517401850b9480b4806541c0d5080000306203996070004490000f050074140b00f041c110081d2a2a040003420f0414004610b03820301d075440b4582e00c580d255840c100100c1010050b40284081464903070f070140c4035403240d482c00c240714140c4c0b11b6882c109080c5c0646070800580c4042803265116000c490a031000310f2005460300e6000400d0501e0b01004c40d150403443d94a500400000d202d6500008280116500618040c868210006090b0003480041c0b41c0c80d0140e400d1042c01140c1071410741c00141c14003580f07004101e100c1c0364803880709000d05484c600130b0300c11408103000c0c01c0403003200340002291000c01600040c24103c0c2c9840c45c03940020300c040d403206002040548559920000201805015082807a403868607050440e42c0d41c041ea600e12000c01d005840c42181395a001d000206140c00e507106800600400820f4113051008590342d80d5104000e000048500355024040480c00e520384003407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635200692 1250 635199442 635199449
    0x230304061404030903210c170f0c01020d0f0b0d030806030c040c020f0f0d0f050903030409050a051b03131106040f180c02030423042403020307053106030b01 69
    0x1104c448803843e42c2400070815540794201c07203041085990900e5025000b6000c484040c1e4042245d4907a1011401100c01d40c0c0a80c1254401d5a0400942c2103030704601036000705030808140108000c400c449070003c0045a203242e00c030307981100c0030300d8252000c80d0040e11013541c0080000d08580040e491f11010801791484000c1c1c00000d80d200c0380282e0b0b40990140b090360012040c000040240c109504001000019210030b40390a003c0c0005066443d51414003ca502400d0303443c405008509064800f0002003104640703000703007600102c8281c180c0307954075404c890040d402c80f90b070034084100c035849292084074450051076100d1400c020010780c0854080c40c0b54010165040082015492902c0c02401d0314603188820045400422080c862a003000409035501000700045401c5110325501003402041c841c050b00d16100d81c0000d01c1004211820304242c01c1d40c0c4213406848400c0d690390b0034080e40e4a91503130a0380001c0703949420a480e140d101e6070001800080752202041640e62a2111100250281c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635201942 1250 635200692 635200697
    0x50a181a07021f050403170408070b0a1808060601121b090e070519080402011709010f063528063c02090316090c23030406140403 57
    0x34058082d40341403141c000c0040042007204000c04203807200205039100303502000b021611160003481d17482d046001a40c01902c007100485072019100c03d400c65030b2790090300d1a40700048002100302040d1980550f05400c6640b800c000301910703160400107451000c450500292040d071350b44120024600c01000d000d1b0b011071180c07600e170501e90802e1420242428010140700c14050200201d0802d001c4007404807002c000301d4908100c564889100482d43c10303822840c240203411307030b0f0414401c051034190722980740e5103110300007049003a5486d40c020402030070528031070704202d1b0b100030560184100c3d00340b0070740800407040a981c0c88075400c1d0b03071003201c334140700740f0340314121301c10585403410000075125a0007400e1200c00040c1480d408c552110094620034209003122080707050f510b6640c503003240c0513a030060500400b603034039159007a10380b400a03050078847d0904032410074008020950003000b080017400c400590740c84501a00b0451488507038005801114901d6580040e22a000b14250b03015014900c2035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635203192 1250 635201942 635201947
    0x406020d15030c052e0e0d0501050a0e10060605181207060203250f200a060c05100507050403060b06120109020702120d1205040501060317030a110a050a181a 69
    0x1420f200c20000c06814805030070813001c1010817140c00703d54507907400f00254034206081c03403030090200d15002c84c903d000901543c204414001c960040d07411020607007045c0d00c1281c060012101c001415900d0500c036400c0410750400c1002540c4001d8286200158805402d00c0810224016898641070065005500507040468681150348081e000c4440b050302400d0070400c0045192121111580d1242004100107500c0c069200c072207903995800d905078407004181000007a0355078006010a10552822202ca000302c100c0242e0489044c4159400340459a0f07495042c541113640c0ca0b0014100e2004440d404401800040104020350303036003c0c042d0980c00703005038642803248144811445d40c1021912260012056000c003243d002210000320302200f500401c0907240c904001d401014031fa00050021004040802d0400507500011401a40c02100410031660034030740c1000940a540502c80028500b00000400301c0d1113108807200305014845039000c026070b0740d40d00d401e010110b881101d0820002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635204442 1250 635203192 635203199
    0x3050c04170c061c1b051c06080708100e0607020d121103010605071b051c020d200102071d070c14010e0d020c060313020d080415091502150406020d15030c 68
    0x300d0241035401c080138170303841550760100c6a0181c182c0c011080044c09403c078848840b0800010f50700000000c00d40c08003501c14203509c0e464110745a205030b14003460340c103003844045045034500150700d078851003755024001c9103d10740700841e032a040301781513000e40b90384a2080c040d800004100441c003e0040707880307a075501c4c0024a410504200380c40f500c0c100a02c5400001c100301c0c0c68610b0081020002d000004030f800c00d4510000320700e00403440300540240692041c10403441000740c078204c2035180980854103039a98420050900e40413000040d1064070341c10011403c4680208050300155125102464072403009001e010f00b1125180702e2003074560f10410a031014250180300701c801c120025564140345140c404507a01c030304040c5002c000d0003034140d84800700134030604400341e401800c150401c04001c400750340002800788205020310100988810b40303448406000007050b0041c13550002d40396021f988c45841e80402500040761a9203007603140c07440040c010100744801400b56108440601c4007506 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635205692 1250 635204442 635204497
    0xa020703030806030319080c0c070306140f040c140607061b0305150901030f05070803070606050906091905060a051309060f200309010207150c020d03050c04170c06 72
    0x14080c03d080d009030000c00c5400f4100c07038180d00148290b0464140010380c1c0e1901030509261f4469820060900d01901c0008010403000d600410341e00055a9003600c20345d00c2e82d682080d00f2180a0b20000c00d4009055000c000b0081c031010046440c0c00c00030441400c100e00c1e078881c002070318404805030030b0700007100d4034600617680c0600c00c0d030703030481d5411002c40444030602c40404e0f8016010300016280460121a003010018100072400c050040d0006982e01c2e0f80c050b2425202410580c047d991141c422000002e0a40c117016502a1040c0138104c0000103106400700110700520002e04800d4104110210105085c1c03659521070b8039400503802c000410b03100b1410008101c840302138450400904161000a030324049401079058a80901c40b00da0f543c0d1100710900d030081c400c2e03c60083c1041c201c804e61b0554001141d010b0140c01519400380d4070743c2c003408042103084910403907101d10030700c81c140000c0c010300d4484001c0070b152581e154119443c008104c400a000390300b004071010881003241c442d4455488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635206942 1250 635205692 635205707
    0x80a03230d021c2c0a14070303020f011107020112060924090908045108040c120c0302041d0d050406081506071505070f0507120c170a02070303 63
    0x500307044100b02c040d0036013540e140e00c00b0405489801034440c840c4450600c52051012a100d607920a044050b903440c200c00e10364036040c1910055015008440783c6120705841801031300e2100801854240c6001c00c0d680c01901d40c8003031611400c01c1c05030360f00b001061542c01d5106007580420b1002d010b500440c0e1403e41000b500400c1d4105640c82420450310800003014002500c044d0394810410184c1400d803400190000040807407100d00400004250300410764a5545e002c1791110124294030810340d00060581c3c4154040c1c0b4014004074525a0030094681030410110a0500c034100800003144e0341c4c0c000030107480c8030004048600980c2861f10700c00e540200704500349621142001410b0030705d0111701030314045004260501e42d11810340440003681e01e500450302c207950320001c03d03948031003200b6602008100031140031010403510752001d15968021019102d100e03134444c01c00d40e03400030154012503000074000c4044510142c0300724800602c90f641d002400c01c0c100382ea80200422441d60030014101d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635208192 1250 635206942 635206987
    0x150c1a011a0c030d0b190b03010e01061805040f0b0d060219110d0e0103090b100e0606130302040c0302130324090302100e0f0d02070509070306080a03230d02 69
    0x701c0d400c10a0b101110310100a644a4441018000500350740741e802040d0345a42544003040340104581c030101c2d0b00360034040558181e6103c40031040b240e030b0701c80d90152694850182c20540300c481c0260204032a15054200c0111802c203800c0c042030304000b2101080128180003001c503601a00440c40901c5d10050032403020781500c2c2881c014041484110720207480c3c0418481b20400c00251400580706a400b82d00180745040c0d03c0b0300c4c500b550386031035160910050f541b4041c4444650f101c4021824a103804c1e403e40e004400900384c00c5114a01c0c550821000b482020117050525400340840140d1000c3c5249102c021402948030f5180100088084803450000c40b0607181864644041c0d080800d030300141001103403060391000205a07541c3d241c198a8050745010008543c480e054501110503804130340081141e02c16130b0041001e8a42240540c2680c1712400341205640c400c51056002c00c1c8100c4007072400c20003010081c00030824800501c00781e68881c3c0604030b0241d400141c00d0304001100100e8081d403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635209442 1250 635208192 635208239
    0x61324020c1b130e030909070e0a090b2805031606030c09030803060418140f010506030604030206160320041d0c03070c03050d060303020a020a0e10150c1a01 69
    0x10301d1090342c001020b41408080040c00103a03a02e1014108603002c10482d403030050018000000c03840c01210003000c03401c6401c1102d018883d40000001e0015031406502c0490600518001111041010940040440300c03007004044004840028540d101849000c2503840c46000c518030300d07420840041c081d104016100010000c0d41141000403c0c603540940e50800000c403408146c0451441b68103400c01e000300e5000c0d05203000f4a00141e040e92000541c151110b81c040020b01160755141304242d2071710000c58010300940c01103800103030364141e1440c003070b510b858103818005500c404001d40426405521200254124000a03082c0031141a0000303aa50358081c2020854840c600724203800c14600020704000180581000d0752070030140201700b41c9915410b6441c08019607030307485c10003c0d96602c103894182d020f000c3d816004a10003414109003881000c5c01c80c100041280f50607040d400b40030f180d85a041c1000241440a00054442e4030814025441c1c404178101950401c0030351010a142c130b1440d44c82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635210692 1250 635209442 635209483
    0x7030b01080a1406010f380301140d0807032d0f1101150504050901330b0c2116030e1005120f060a050901060804030e040509061324020c 60
    0xb0203100301c3c219100752005200d41107e07040340d403415040d50102440c0301541e00c60341002101c00001d1000301940c102d40d00e60400c80e007041b43c03101c01c2c000702c40c10020740039100400c100405408039000f401c11000c802c5040304500c1034a808078114500407891618414005078910f512100c00d030b81d0000075128030b60f0301d00000f040101c00110204580000034803d51b80556129000508041c074294010840100010a100903101d402040d030f00300a05c48103160b800f043d03030702880440c280014100340c920406001c4000c04144034422a1942402440318450942d544104080400010032105214000d442603c8034209144110104854021001c041800700300040c00011078280d01944916008203015945030702c5911441c02040782c03030000350022600056884000207400d07074031412041c071a5001e955440f0700a0002c904100503140146c91999150740960045a102079a510303038a0011880f54540f5880d82c1d07040303020310520b030500c0c03070603d101141d0204545000301070a12134a001c80304a4100c402d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635211942 1250 635210692 635210699
    0x2304030210052d100b07030c1205090a120507050d0609051c05071103030d0c050d0b06130302040b030a02040609200a09060f050403060f02090f030f060112020307030b01080a140601 79
    0x10b0b05050f039141ea05100000d80c4012032100d016400d510340c041c190b454025a594241e60801804401d2441d00c120b4443c401c82c0e14100d009446503003514181480241120070302881c0800d030303220022400005680b24000d0240008003940c85103605100d0500c0352201142e000482d0074114240795040800b23480d07800d4403260103429036602c06d0444120301d505c1801c20200300021400300385036004041c002c036065460103101841c00c0d0f400c28090202c0b00c0750030740c0500040c00040f0034850503000301c0560405401002d5014801032902e600600240b900240840700510b00c50340010342076400c154040c030991075507030044415141a24042900d4208404081071070181c0300a00140000200c0c840c840401030079442125a20703108004036001550004014403030036500c00b20003c002d5009059452003140e407a50200094200414100300d40308504014001c00d03031800d140c0d07096140902e00100e83c90300030300c88003000142002c2a40b6010f00031240050030384603120301c0c00548009202e2403210007548045c0040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635213192 1250 635211942 635211991
    0x3140a09080d0914190507080c0f060f0d050c130501080906040605040c0b03100e06031c0e01050408100204140319020f1203161b0b0d230403021005 65
    0x2075610305418140003810000e07a06140c0844d40d5240e92000960144400301c032009801d01d4100020b0718003680507222050780d91449103640e004050452900580078420010700c900d07100340541002d94402c8641d500c1c2529181c4094125003003100c0110b003840000c01c0d00c0780f0304226500c0c80301c0070740001c0c241014941800b640b00c5a64030001400101015100c80000b0104140540c5050042041044681d164180b082042ca008041801081c050042e10f40004c2c005180c0050201c201d50106040203030102b1170345404032054900c203101d84c0e0504c64100b10010740300c0000c002d00002000d800200503100c60614000c0400b50401d20710052103580410300c0116400000c034080303981c49038125582154003000501003800e01d100d880d00000700707001c0414035402c001e10440c0034030703c1d1f14861456020b907660312912030768040703d5a0090202460080c07001c851040c805a01007a01240000d4100a2403a8000310340b0204520807541280141c11040302d06013101c086010301604842c080e60700d40c82e013440d061400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635214442 1250 635213192 635213197
    0x3141306090527040c05030f0109020102060c190e150c03030609071404090b01030f090b0403020f0d05040b03090a021009210308190b040e210a050901120e070603140a0908 75
    0xf0510116001000c5010401410760600c000c00014064580711000c480d2030600030701510201f0380c05805244005211108010200e90508a800149603030b2401102c4080717030540768a85e0605c2c0c01c10070002d00c5120350f60301000076001d840c080078000d65803450901d007407103040c00d000340c401c03002c1c00b100942007034007072002405a6040e01c0c1c1c01c450000d0f880c802a03004030007600406a45103205454a9650428080c400c42a01d2140d8013a13000c8440d00e0740c4184095039100c1c0c01c0d0034244009041800188811420352000b150402c22510444104912940010741d0300a840507000c0b01055200d60100300902c0107102e513040050b82c41d82051001030039030b00d000c2c2c0a00402440300b0b41a103a03d10b800c7d4406604c69000040c85003025100f00180d1303501c036480503610510203014400b0801d00004007a900c0c800042200c85156091ba941410315003103000540b0705ca0035041c03050003015219101c0c5204040f0401007140108020b542c0403c185094860904101e03101a184504072424143c5050110b00620304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635215692 1250 635214442 635214499
    0x801061a04060507060b06030408040806062e02070806070e012a020d031e050a02010b0a03050d231207090b091005030c07020d0605040b01081605010309031413060905 73
    0x2001130351030a90346040d00040c0b19103824079510200110500007441100806881030300d100300121000c035141e00007000802d036403401c0800142d5401d0001d807403810302407080007940c812241c01259000c1e5207030300b00c0038101001202c1520000d501c0c468082070541c0d04c6292081400307140485000200c000301c10161044100080190151844c161041e00701885061190300000f0400711b020000c40e10810020300d10340c400d01540005600b031840d000307030502e0210580001c0700e60240003008041d12401d819543c8400c1000c03400c0d14400191184154610440c00501140d03030007540d07442840c58200c0700a04017007840c2d0000c00f4428000e21803035569454200c41c5100351692810960707100d90354501002c0c034511070041c000b90000703004450a03003000900d0300035034003d078424802402c19070380b9012601d58503009040300d151804c040e82d0040049500070b84c0008840d40c081d1070250b9105819164201032070380a4081c0ca02880124002080466400800c80c400750808131017108542911010f4203201a4501c0d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635216942 1250 635215692 635215697
    0x9031c1b17130b0c0109030305070e1c02040902090403020601031502041412120a050909151e0102010212190c08070f05210112170910120e03030903040801061a0406 72
    0x106910464401d020080c014001011002c4c0c1d01c081c0034031014060400800110046400e10021510403401110004100c00c40909502c50320340b50190000a40d0313801c1c04050b40c0066480d483c600c0540c503031562281c840d5001ea002400700e54903515240c1b0b10840e40250b00c062f180d01c18042400f00405202da0300140300030031552061f50f141150360407418001d5008150094500004903c5050380c6c010f0054011000c0890b410880759032504040201c60081d0302d22141d100005001700d942044680300e841d82040010f100050401d5000c0e407484015440070342d840440c40d0811915807803091603034001c03915161407a192901003400c6c082c002502c044a03000d0070760140030000c10440452408a041d40b40c0d81200c1358010302035540c2d110460818118224401e55a81290024002c400c7c650442150100a0003416441c43c0d040e4103401215100b0f87e0398070710086107840310b56402030503404001039802012150081d55450b85040c1c4010308441039540309907000407101c25944039a00c0044203641c129600c50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635218192 1250 635216942 635216947
    0x711030307090620011a090108070605030c0a1b110f0f150c030706020301090b030d170705030c070501050c0a0e0409050a0210110a06020403060c0c11060f09031c1b17 73
    0x600c0c4c0030f802c554040160408640c81d180040406459116641d02c42003000d1310301c1c03106642c891034a9920343c03000c4d02078007000c9201000400c20804000000b0402c409951610cd61043c0e8070300c001c1c641d00b0220083c16502402c14440549140c9460030309650100c070200e682d110001145000304024904101c0100d400c2c420201d941440d00c1010310031607001c03582c080030441d0340c3d68644074850020031040300198000c0c4205818402d6850103600d011105402d84038064005954411046440e5400100095a085000c0c04600c0008d01c0901509010745149403400c1c0e252070010900804504810b041d5500c51814040480c000c25400300b141494560103503108044402c00d000299140d0310319000c074a0b800e00c04c1102c02c40034040341c0ea0140c800d0f07a02c1403a09102000f07402900300d452080c43c420160a03a0003180c0d4429180c07810b40003c0500c05030502103141400c0c01e94000074144030100008520802d07c00c090903201036070080000d0080010341c0100e0b03401119640714210308110200035401c148000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635219442 1250 635218192 635218217
    0x103060c031a0f0d080c0609070803120a050402010c0501020c07090e2d160e011503020a0f442203030b040605091906060503150402031e0f07110303070906 68
    0x40c600d110b940550040c0101c1d9540d000c241b0b000d540c84500b25088605400b03110b0004c078503014080101e8450b0a006a07221703c180c0c40e85c0054000401018108074103100c03845410310005102030018086004a50003e00303c80ba203023801090039155001c691140540101014082c0d4020301290001070441002090300c0d181c5180104a142c0020130710a00300b100750003e80001c00c201c02801c070034180c464004040c200c01e413140509509034012105242c0202c3c805800848034144211070306004948900d07004030042242a12010f00c039100020003800720a440c0c5580386200080ca41000e4005056611811440400400b8010b55060300c0c1c500900701501e030406501540c0d510303000071020f07210042030202181850407002c4020181180c4034042c0b142441030016256014005691260380112074074404142e6600802009520080041160002e5844194082c1e01c41e9a042031142d08801c105c0c04250900c03c4001d13128041001150105034420410421490b5203c40c0050844085041043c0c007201d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635220692 1250 635219442 635219449
    0x6030612061509050f1e01030f080c07090e101401141e030712020117010b090d0309260f03030403170402030c0d150605031501140d060e060103060c031a0f 68
    0x3501d912040c0d6080c100411700844068007601140100310030880c2541d40352008403290409182480051310b0040d14002c0400460800b00c010041030b000c20741a1340704180c5800e4902c0071503d1804461070302e64803d16050480001c14800c491452030500d890070380540c54032000dc030504d13141c0340c120790244030301c150550645c151107180604452030003010341300d000d51a42c0480c50807140d03408007a80022200c00d4038408003060058814180d6007039400c06c600d04020031301030040780480d04808604104c0c56940c001480b9400c2d10705408000186540c03640c860821841c100d00c2d050b1640070ba0161600300f0014400040c0c0c00416440e03403003010201c050429136850001900700360715045215003000c40e480140c070421040014004861448082c00c1110603110024181e50f43c0c0310040c0d2007102d207084001800b054840d00c440c40e01d0048002c0000919458990b1110b0a564400745841d00c5984400014410810030380a4440840114a000c20841072024440316403100c4032241d07c2d000e40420501c030b80700b40d00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635221942 1250 635220692 635220731
    0x40e070c0f05010e06150f1e0307050406080607090b0c0c010e0d0b15091e0402090406090c030302060f0a0e030d11130807031a091b010905090a05100603061206 70
    0xb81c0250007040b4403d03104415984030309084410f00e061480c02110108103107440030110303002c0c3d00040c05d00040b180500092628940d52a00748503072501c0f0300400010240d40f2805074901401d9094050b003031030b050505001d06074803c0c60300308110b001028400000354800c0020880c550800034039002c0301c581901c5003c076000b10722084000d804030002804200001d1901906541003d4041e10b40b120380c0e998581100d820082c0110081a043c40c000000c01c001d86001d44030281c21038001c0000141c0c680c056500c402c501c00c0154001c40240e0828000c0102401949a4a581c080f4140e841800441034140102d620303032181450000240356603000f01100541c00d141034031081c50480303049641d51a110018190340700c0045c0710840e24100c0c0716203078500148a241c2500e004200143c0242124880f507400204ca001c00b440031b260421215900005042c1c2d180300c400c1d80209683d020009031410207020180014080c7d4001d90705160905004214010390f00c10041181030304010001900c00c0030520245ca400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635223192 1250 635221942 635221973
    0x90b0c090d060f150902090d060f141915050d03050a02151e09030a1e020f0616110d120c1103220611030a03050a0b04050921040e070c 59
    0x110700d804420301e05540c3c03a50182100a035840e042020307941c0e0b24507100040e486001c0b019600007104075001c1000469640296804400010300441c0356030890205401c00e41003183c20030004440c10103030070101c0c05a8400d0040d02050980600300d03160404000c609075101300c001c02030800c00001500d0060510901042c622040c030b1055001850410b030038000091285102007003644108240440c02d040400011030b00d00c200d058684c403454a60030803a943d03030099412902003d60090404442c1d4000d42440400e124032003003140c00400442181004040541d0b603181e01c82030303a2104400c840310603000386459a00b211034481c0865518480d0310100c452610400c00c03c941e07844089140d082103030030000c0038461044009003000006658410880e0000d40700b000c40f10a0f60000c12100642501c40e4201c207900c00800100482c00340080404901160310450300341880380c1009485402c00766800085840c0c4051182c00b01d8242418074001040924001e0444001c3c0545000d411081040c5180c5c0031502 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635224442 1250 635223192 635223203
    0x60801290c0a0222151401050903150a1b0f0215130212010c0201051f03120c0212010c030605041e05130b0408030906010b04030503030a050c13030f06050901090b0c090d 74
    0x1c0200042026944038011080c03000950921001409810850305e0083c1254000301102c07a60110040065956601001d5001d0b01405038100c05801c800e002c103c801d00804003140001611a803203c1c00da0600203e00452104100350302c1c00c06a0080c0e400038140551001e50844009103484507400040c4841c0c1031100250005c3c204103c05060b440f0652201b4010101c54000f401507568004028010b07010512040085680700881440407807203d00c0350341c01400c1d142c11714040c1007030310340c00042c0b20210802c1038803000e030345802d2044030156142c0078030380c0140f4050318148145281051421118000345800481c81c40d81c440000d0003080741c448042000c1e80e04400000000c1c1054101178035181c1c411100600c20380b164800004096100100311811203410102550542d1135041c41130000e854054200141000f040c03100034440c85140040394002c61081c154070f10240602e00d040070949100501c5003184d640340400e2000810089001180c0c0180c5d855403440d43c41c010140051060700b20044027506 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635225692 1250 635224442 635224459
    0x50f070b2214061f030605040501020d02040b07021503060f1201180302070303080702070b070803091f02040521030708031e0a0501030209090f100b130c0306060801290c0a02 76
    0x9012480c1e0300891070002c050309940c425600d80320229442042c91040900c2280f91020400100300701d40d101d80e400030301c80c400251501d04d90444510690b0080d80200582110004824085150060340c00201c1c4000036101d500f9440c0c40e0000400c110400100303140244249610308040b168294070003404401c466400c000240000d003002503444d07000740811000708006c0c90110700e000340001a100100c45e80c030140c003031030160680da40100c107400c085c0100070b05101b8401e110100c103d00c1d404002c000402c0140068449160804025038401c4148000c0003002503c0002c0d0300d004c10110480d982c0b2504494010741da6219040358044104280203681e0201443c0014000101d0141e004071741224000c680e008059110500116242c60352051603130440c1d44028030850840146030480711704a00000c0925045008800c43c5406a41c4101034880c002682c0355030511940b0340086d0079a000d42045c5003c02d0066a80da4981c2d908070052412003080c01c0703c00700b400410494204034101c615503005d0003103203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635226942 1250 635225692 635225761
    0x301030b01150503161d150c0705040510030f02060417010f05180703110112020c0106080d171b040b12010e0601020a171308190210050f070b 62
    0x880d04a00780112040c0c1403100c1d400c4122644910152401a0245031020740101e414100a440d0a09000c5004145840c6070b498807140707540701d0380d00303585080a468840d035507002d4681040703007080c140d5000944194681000d01c105054030003154401c1e0f0b540b261584040190398000a070f0140030f02d40c402480c580c460103c80040400642018035a0000e110080c8095103c9810180b214152281440e15a51080704c0410114804100c503005c00c074418104000d140003d0000b490a90b0700902007050107a4442c0d908104502c02001002c0c6400d40a26150f2040241ba501c6071809410281454454010041500e4004401c000031603000b03001410301e15544c0c031394040c01621591000d2240b10100d0941d00c000400c03a5001041a400d10359002c9510402e080d60610050055084401440001e00308280f003c140042c0811106103212103c5040440f0009907104001c00050b41c031051200b000001c0c40341e1110742c1300180603a03401175409074002c1c0b00e50352203007010015886d0f1042404080089403030800d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635228192 1250 635226942 635226953
    0x18060406091104050705030a0911060a0801080c15030c1305040e010b0a090213030206070f0b07110706140f030618070f1403011a0c0a020d150c1707030b04020906030103 74
    0xc18982d00c41d0314100c42020240781088100c460444404c408110100001001c000c001c4c0d210b141010b2150f9036403a460b5101601050807500000c0f401d101007548a03005000c1c2110811030121052011030b03c88400d080032501c051458000680006050741c0041900c101418103098408083d002c0600100b01d02c81c202d0540b0b038080c2450281081c05036003d03100100b91000c0c14001c985c011501c407000c012146103140e090081d96405034a0a41e020300000e405200040c4210f0030a0303000d121640e50352687c00c00309004207030600c4c2290340000c00f80549004d403203040c2c014000a40745200038005041d0b459564000200340080c0f12031042403000e1480004010320140c102407440d018000c6a0343c0c100d4100e50003030014000d48000e000b4940780303400c1d2401011054a42c10001c18443c43e111090301e1150711203034007140090344060412991415882e1015000c40340d14410031802c580d003464280c00c80d58600002030000c0034050001d20030035456107040c40090b01c5580494a4489015041950700d694a0a02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635229442 1250 635228192 635228201
    0xf02030604080414090403020d0c080d050406020910020606130507110706050c0c0a0e0109020906070c0b0d0c0206070f0843090b0930010f0c020706050f0318060406 72
    0x240c0403070136030340b26181c031050815440396841994141c000700f800d281208000d0b60301e280c60040842e983e44080013a13054402940c02603a014078031908000da100c50078501004a280c0c00045400b0840d0b101c40f0410a4550340e03500144103803250701400050944031100122104191050b0810302e0f031040030800200194000000c1c00000680d4060300d011410702d40c20020303c01c0d03030ba2203140c00c900c28050041c000c09000340d008124521000345800e00e4035009a6801d000a2460f500075840d0900200c0d07030721841d942a02500141400c188040c0006180100d0007600d068a01455076040001c640d0000b03406048144c0c1d586540c60340f08540000c42a2990604944012005070201005258184820b0131030300454500007906c0700c1d442d80c103040140c92400d120054100302c14400102041e44004000d0295a500d42d0744d0091582001107000281c1c141c50200b522007500d40f03002198014a010030800b50310030160b40ca140303040c0c02c11650783e449100782c10b820841e960350011110f00462050000704903d0740e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635230692 1250 635229442 635229449
    0x1703040b07020f1f0c030612050c0f0607021c11060c01321605070b0412111c05030a0204030203070611100506011d03070f0603290d08070f020306040804 67
    0x8480500f004018455298071407580c1520001c1042c205003014500290001503d1420b0361400140c220f0341d40540381c0f044002500191000d4008031403400c0b05003000005c4c41a002c005a803c2450b00c0515070126400221050f0b004403003080c9100e00a0400c90004c04142c034000e00200f8850300d94030100e518034000c0140c1c0086035003803c440c003091003404901100c10342142e2840c080701896070b51403084400250459009a2040010070414030000403155a602400b49001e0114004da06001100140940120310120a80ca502442c1290000e003603580100c100d48150345030823a00c9490f4011101d0103801503030002035060150f03c80100c1e07017507840701c0700e0070703240f041c96088a10b29050f091030701c0101c0304103032081d90001d118132249a5209441d28400714104202a040f0f030038040d642c01031603807901c0041d041200025215031614400407178080410a251002c4110000384004600002c1d2003504d42c40780041c0740000200703d40c8144070200310001181ca4001c1c053303d800c2d02d010318240a26a00500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635231942 1250 635230692 635230697
    0x20402041e080c061e1207030605131104060e0a030803070c12052104020d050d0e040c0201060b07020d0212010903020114010e0403020a1b0b07080d0b060304030801121703040b07 78
    0x44000404000c0001d0310f0000032405006a46407298421624803150003240046510407410440307403008184140707005106000d681d80015015091101b0090400000025404010300705400c0011443c51902100c048500c2030a058100c2d03514100440c01108083d40050003119002c410007498a4110351490b2080b48203180d5030846031013012007030b5a14001c2c00e1015018900c179407503607503050b0009524203410600080c000020640c980d5030b0a0328017041c244010000810b00e500c0f8a900e414940642c072030b0901140028000c80d4101682400399001d00d8201901c02e240407000f5a0a54139041c06002c00032a000e80284071190361820084d0103004401312003582c00d600c40c000000e4a900500c001c07802980d15a0140281307402036240d0296101d205038a034200046480000560105c141c4020480f040c4660000c03902c840308480c6507011100d52001080c06807808004220009078015510b50564090507410a50000c003800c200706002035101900c0030062000040c00144142805018864280395 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635233192 1250 635231942 635231999
    0x290d09060b0612040213020702030a1b30030509030601080106050a0509192418060e0c070f061506050c0f0f0c0402161208070f020c010504180902040204 67
    0x700900509214041c043e08444040c1c1012500615081200d214034008044000d41400c40303a800003410005803030401c0314074101e01e441c501d030000305150100300103003041140c0041140f032400900a88814070201030510310081d00d070f6441003500601c1640c111003405000ca0304203684401445008060034000e091080b14940d000181d140386c002c012520407240c003004070300094002d83c00c050140c09a008522266400503078092a500119190318005081031415902e011346041c003008201c4001c0e400818080c401001002040c1014404403441c3c0b5034441d0a602c1000c0050a001004089080c40c9108500d40c0140c0040c90343d030b006014000d2411514113455440100300e104c43c1d9206022000b40980340c11a2054820500d03081c0d02070400031600490f00036480703d01d640e500c4914a03460902001203a0341c08140002e081c1d1048900c10001e5180c00101410f0700400c0020b4134600540c46102108181c4000381a2050441d400000ca01c60340a4029900d0f42d407548126550031820303031048101d86610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635234442 1250 635233192 635233211
    0x70e09010b2d0904091b180b1f030504060b091303031401030210180b0f09270106051305031903020d08040c05040c0e040c0e1c1a06060c030a0309060b030f0601290d0906 74
    0x700c00035809101271401190103014800e001f9000b80000800590305241d413880328036460b48a08031000c1c8a00001c000c60b4410740c403507182c0507080392100017a804401c10750364014401038035118040e49400d82142441540024207090b20740b8550352580014007400c0d404100c8081c1f001c1c02c10050600d200048907410b201c00707888844021034034054014204182d05240041202a01030401080c250308a1954034460079214030209140c04600ea00d840c0030544640e1400c8145075040c0a20a000f600900d403c0c026801d09444a00394441c45011303180c800c556601c0200700e100e001c0d640d000e010700c1c0050010302c03607060030040203090200d882583c00d000710204071088060301c200e4140800a41c3d8801c04005540c6c05000c010a4800c800612054115004000c11400608108064194004543d50100380ea00d07403454074900782c4203424015070295002c0d800030340503080702007409030654450184401400d000e0400c9a4440c84280302c0000f18640d0020b00358040c1078081d0802203001303008107024803a1100c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635235692 1250 635234442 635234449
    0xc0212010c0e0f0409080309030a030513030806150403060516020f010c1409060c10060503070f060c1419060509010e0706050f03070e09010b2d0904091b180b 69
    0x440d403444000612500b14041c064584112141440c141c041c2c00000c164020366110140e55000380e8922030260300100b000011543e2500800f80e1291400d43e003088818115034010340b104401406d07451092208003410304a50017a401680e00450b00f001003400b06040060321606500f15481046006000d03945404c1246141401460000a0150b48440702d007124110030800c41c3e00604103042d0f0048007081103641d208003c00422030200b4000340005a411b281c030b401c040c03030130100d644000031441d080320041000356001004c48801c1d81d00a45004500c0040c90401414261007211842c00462440404400d015660b0310040c440c030700c40402000407a25048409566101a124007000900108202103d44e203900000d140c0108003070410021410242340050f456043c01d03000705030310a4002c640c500300c22000800c40701280c9090034210440c448003001031411842003450142c020b80d1100c48000030440821201340902e05140591481591620b40e440300351903200c3c064200c45400c000c0807035854034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635236942 1250 635235692 635235701
    0x110402041508040203010e030a02100e01090f0305160819090812090123070303090b0708101710090606030b1005060d05070e191a07080a0e030a0c03030c021201 70
    0xc1c20034000c00320125082a0488044030000c0003241c065407030b03600b200c0010700204064821003140750040d003d250700c6120424119884100704003485d80c1401c1c5504085003966485182c01a054039045039600c44290b45007140082d003a800811040c000213041540305400d03c1210840c00d802d5a402c5403d41c0d46444569456a07c9480650409420400c10070b5940c01a44032803007204c608a4401d00022100b051070420b81c11180003680403903220f845010030050303038011440c2c0c454070600380305c909130509501102e50840b40b4001c111341c00c140095407448070141005654214680400c0038800041d00f480c024002d81310510080751078034084000324401d0380d0010b1074807090f280086e2003242048007413035843d4041e0102030000c600340060380590b1f0301c80b0b8480c1042080d2403170719440d008507040e01d81030154446407190600c1c150480820f01c4080c000803003c200301c0b000707550765140c046030302906440003a05142c45d220000708843c41c040307800410550080402c1c400300d402240c03910300560f0241c0d5900c1c00d85 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635238192 1250 635236942 635236949
    0x20310080a050705040b010903050604210f020c150c06011206060b03011a0a03060503061f060507050316061e140a020315150d2903121c090209010b0711040204 70
    0x15081070f0030502103401c03c2d03801007800250502d800b88103142c0d2a201d040c1065019a001c1d0361068081c1244140d2114024a605146905151490000700c2c5003500a40b50044030100314420b40b4040c0041455135600e800341d542401d125010b94041356035801480108409030350046844500340000010000140320580b81201d0131034088110010699400c19910f501101c4440300341665104081150f480400c0b030188100302242e00a01c9405000c0c920090551141d848842001010001d4800041010007500d40d1541500301800c105d00040c902203000d0001746884600320001120910400059904000883c1d80401c43d510001d03150542180d05030300c4225020810210a00701c4961281065801d240c440701443d0981c5042002c1040d081003940c0c40c00000c201c210300100120b000c0015482c5101080140482c010042500034403110342a9005504055490b030710140316030a40600190800150164001d000184543c0c6421154143d900403403c15104a0302c0122030150b2401c15100b100c058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635239442 1250 635238192 635238203
    0x30308010e09070e01151d15071104020712030c03060e010522050c07021c0f1b03050703081c0501050a050f03010b0d1a090105160828020310080a 64
    0x160308100c1c9488000101800280b120312802100050008026040d05c0c0070300351281d26007040d20750324040180203842036940c1e00c030040110003c034141c03955800204d07100c1150b10820f03151103c90b10b06050201c9112049400c3d040790002640307078100303c0a8809161402c600da1030400603100420401c0301102d049000d00400c01d54060300600040c0303001055258408032900740120071481e031001880988000352000d58031240c0102c1c045045181c0364400200024440c1030388824401e103900c0c1c2e000440300010014160700760114055250b10030b4010180007464000c81240c0886e982c0f440c200d200c41c2d000c1310f43d94020400707260b500450600c1c0f90045604842c0006c007152503c0742440c0070070414044041040c0c5d8990760f11030119040e91100e200d00382100c1c3c00364800c03000c0c030103010303046c20450b410041c2110110b03498181001801c80d202a00002c4406a6183c030b2100340c0c0c2c48503601800311021808401100441860002421300329400441c030407440060f40c1e81c1206c3d6540070040d0b0700c260781d0303000421 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635240692 1250 635239442 635239457
    0x3090e0c07020d0602070215090a05011b140f0303071e0804020a060f030f1508010c0212040306110c01020c210406020604020616020904030e18070f0c14100504051203010303 76
    0x240c609004428201802400010301c0c00140c0d43c00207440e900e945500b6000c0c1d14010404584510702b1000050080c88282446a407160903060b00301c400c0c59480308010058500c103180701011a82c10803280c0a0000c00380200d969a04003210090243c0201000c584502454411400c03c9684603c010b6401107a0140c0710680306400c0c00400d80b8220111341501d400c01d980d4440340ca900880302c2c01030b98a18010102e1401c0c8a600700000d150a44000203002c3d0250b50020494081d611207040841d41120340000000400745400032030071001d403280b10500900d660000c10380364080030300844c1050490842404000203003410254000103070060348107000c0960440c400080140c00d01400030901090010b00a17410480b0590001c1c0d07040e0801c1d40c06400181803080d0b1410903082102e20003550602021400e0070382c1c9401d00c401084441884020400c00045004000402c241c21100f8440201110f040c1e4403090036842100004003030407241907a03148202e10015852041260459041e81d825644404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635241942 1250 635240692 635240707
    0x70c03060e100c0e091f0902090406050102030a080f0a140405160501020601061715040c0f02210714010e060a1e050f0c0714030a030504110a05030c010c03050c01050f0403090e0c 78
    0x651450010701b024041c01440700302204000c6030800d104003034109208010788980c00e078014403040354060f400460665004024071aa4035804c041c0c410ba101030b03001036030009a40c6255522000d4040544040304200d040011b2104014000c240c0d41150f00300c0c0e60782c0241103640e4400482e660b441c01c1c031880010481c0b881d001500c02d1150301e0120f900107600c02000c00804e07a00c00200b41110b65542201d000a40d020a0b181106e507414051210004040c21420b060140e108000b4400c51144008c000c20034400503032126450882034010118090b06c0c0c00c20340e8110716140007080060078101c030041000d200d000000100b005400c1c030829000d0103005c0100f00907681c401003880c41c01d50200f0f82c01c0d1882d030348890403288455800c00052000741003a540101d10341c00c1c1854007c4810f0f048180191051000200c103020030744000030185c5e00003d00340303017161550089d81002d854511400d840c0207155400c3c0300400c00403004060245000741e2081c2c1e0790000c10740d034580440382034400554060301e4418003000700d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635243192 1250 635241942 635241949
    0x5010f050f06041508030714060a0615030216020a0e090d080f0a15030f081b0a0f12031806090506130c0b1c14061302040f0b0c03070c03060e100c0e 65
    0x1e880401d01340320740d0440c0c6525180040d28640012004460030352003881c6410035210144a0160002c0c1800f606002950070b001e003901d40750640c9100f01301010750201d866512609000e0507015000d8025105808082e150031010441c100119403c40b0140300e100305d40104d0030300c198000c0f4451a9604007500194640e1441400903121a00105098808040c80403000c05c2402032102406489110344070b580e50103035042c550f000031134201e40d400030b40c100840d1200800d038503d01200515034405200014080c006c0400c2d40181b000c007252802001d01101c103c010000980c1c040011130780510201d480696a858403114501b003034403c02861625000d200b040f040b903142c80606445e02c4010b80100d4600f280103103403022079050820024a034000401403080600308008a0391511041c00805d501d0982007984110560032075206407000b202c5d0004003242241ca041c41030b501c900e94021120003d01d41e03281001c0c0c02818149000b40c0246c000c40e82c1060340c4100a220f900b5410005072101d030086020241007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635244442 1250 635243192 635243201
    0x3030804020f010c1401050609060a1d0601110f010608010b19060c0305071a04121d0609130c1d090105150c150c0703091403061b0c150405010f050f0604 67
    0x1030b03505000608160f4800141d410b481c0e50003c2141400000302880c042c0100569440013070702c0b00c0d02480248500340400c8286141102100c0113000c10390701c05485505c0122054101c62503210243d0241d140154018401034003c4421100da101c001d01550926004000a0303240c0c6448140305607480300802c210741801900842441800b9060050522407240c40d030003201400701c1d00060310460800100001c000c4003c60504901d040b0703140c0f92510081e114003078100604000f10041c410000840d00c8103082d526403e040080d01080300c001d0002140717040c40078141d00d484181041c1d0181d4000d909003080d04000206604071030b40240100326601040c031032100700342d0013441540145d004200402d8203d20102c2d5845009020500c01150703110214140104a60740716003084003000e050222404c000d030303000a480754120b0390404444241050032040080584140c1c4840c03c0207000b0402c22407011880d843c0c4032849140600c0c005e0159081c1e490300003045990480304081103412020210700c850030503501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635245692 1250 635244442 635244469
    0x2a0606240c0303060b0d0203160f0509210d02031b011e1a0a060e1806101404030c080601050a09180b0a14090105310210030605060a02011d03040303080402 68
    0x1400a0130b5620340146190075400009007407186500003041c000f101c0d5403806402065101464000802040715030300400030300c916840980b056410714207a0011515180d1800c044041580c1210b202c0060501d002c0d40b41c0c1c0140c1031050754051500002402500103008280b03c00d100c030280c0c49144840400c1950080591464001281e07c400015581e1900e80315100006044103480d02c200d045040e904200c4881c0362116070010340000340e0141300c00d17901d80482180d0a92843d00b0b141000480154402c1040d0003140d201134540c0340007030400204500c010642d54181c1c1d90640d00c10b00060703292003100050710182c03202e50301182c0c1500520000305101d0300526410015018000c50320320070700d4101c00d5046c06c09503183c3c40c1c11f954400a100c18062200ba050300e19807280729030f602d52582c1c100b001c42e00305180f09402030300412440880c681e0462003079202d5005041c008200c103131110302154000740200301d8020f50301403c045545d95030588101c00003d440803640d05640d0010140c2e40e80e030034845468407030071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635246942 1250 635245692 635245697
    0x9090f0906020a1206120213090f0510150909121d120312090105190506040f091110030209060901051b060f04120c110f012a0606240c03 60
    0x5181500044642c002050b404003155200708400308540701800894804d507101c20103c41820003e00c0042e10780800940000044001c00a9010140d04000c40128000340004000c0d00550f0303000346107161240c0c0414180d082c00480c6a4640783c030b411102080300d000b010080c0c17109c10740f410741a8003a07210b1104c00016488400c100c1c2e106821a201140701c1c900e0324140030102d9040440e550100e6242c403802240d115803100024403203414103030006031754418099014503445489000081c0c1d0341d2540e400121803010400c0d4100a10002c0703060488906d000181c000307104801c200401490030341320b4001d4560740d00c0000c1250f4982451034006641507030124040602040c440c82100e801502c09108981c03040c07501410704581c0c0d2400340b4115038460140034001c1c007801565603880c4003050140c800113041800c00e80d4140310b111120001a5981101c0f154501c0200f094025400242c0381c0104813251040d03c01c1d441445043d45404c03020321452240d0720010060719950039000599031091481002d11402030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635248192 1250 635246942 635246951
    0x3150603191d16080f03090108040b2a18181603090501050a09120305070507082107030c0210050603100c050c0601120b160e060d0f0f060501020c090709090f 69
    0x200720504042000b0418502024003d504002082c000d00000043c07029070310207546410885000a480c001c0007600c0075200381d4100c0c0000f031146582014107042003481705002c00f8000c40a45000c4d100707600904100034151807985529005040c10038040d55025002c665200311903885240b000d030303c5090780003018101921400c484c0c010038000c1c400d2a002e04408400460f5100c098200343e40840304121446003014680010090020f6110741030f40c0a16030300c90100c40d500c07145019040359000e0923198803140c0750410003e201d407168240c0d00c250300034071898003528a405100d105280844500f112030981680082e900c54000780c1da9503200d000090020b051160030040003002143c58000241c024291508407400e40e039090250640c10a6845045a004003c24580d41d0100030400c0c2070301e04035070303005590204a140c0414110340080b0341030142c0c0c2c0400c00591040c82100c00142c1241c0c4146809170007140612607050802002c0c140c070844140d100d1070f9000b850494500c0040c26074440000025980d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635249442 1250 635248192 635248241
    0x1b07061b02092214070509070f1205040330110906041701140c0c0105010b040803090409140d0306050a05040902010807050d1814060a18021201110f0315060319 70
    0x82c071a51501402c1c65000030705e00740d401c090510994002c05000c2c0c5050010800c040000c0035880f440c1c4000ca030468800100c1c0c19142c6290685051240f02c0da98241e9503094070040e02403032400b080340440c9070070500050010211020100d91240716041c550383e00b040e000c100c14416400c1a014104002e0001c000029100851007904410010191031210a0707600000300408030362024010306001d4079940c14160700c0c092401c1c20a65984c0b00309a0b07858000c0781c8a400400602014821000c040010a4140c40c0f40b00030415009009005500450b4424040c001010905080c103204108026a040c0c680a08503110814140c81d55000a20030392111900c8960842e80d071052105d800701014400e44035555051000c10196080110050610b4405450200341000121000b10300e0018035070180c0b40294004941603102d405050850603810084000003101640c20f0004001584079404c20b5500c1070048072040100300740d42c402a54090a0031001c1706003c45190003580c01100d070f0416841c501c130f504144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635250692 1250 635249442 635249453
    0x304240c022e020a1d0906010903260a030902011403060609010804150906020904181e080904090809090702030708040e06220f150302241b07061b020922 67
    0x4200f03095400034145c034a40601a40b0322035118500704500300e9900384c803442c0190000300380f2002ea2001070100c51107511500030403203130340c0c40000c268003107102441c3c0d0750207416034040c0140c084034100300d0015800785003000005180c41d0503240903150040c0041d00d400180c030011903400c1070290003503030b81c1c011a1041114203065445203002c1c1c2441201d000d40c462880400b000101d6035003151082800420701c3d000400242c9111a18a013170f00c00c00c4800350300500303605080c901400ba00a5a58001d49461240b0b409d10480c00041e201903c000c440310b0541350b440c0c0ba800c90710380c000e21000510740c09050000348981041e1103402c031361000d0082c1a000240741010141040d101410407000b46050752151052840406402150001035044c3c60303078241c984c6103074041401c5000da030f021550100c20044000070284641012541d03601001e015040066401941990310707503265225030320108640c1b841401c0504102802904010340007820100c0c1940c40f6215401207601ca134406440b003080c4901c10700c00194 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635251798 1106 635250692 635250697
    0x31009060e151c0204050c04031209060509011d04090f0b0709230d0f03050c0d0912060e070f17070b030f160507080304240c022e02 58
    0x4407420389200f6030707000c1104001d5005041c0024007122420b032802070021b49001d07000c58080c0400301d12003600c41c1c8d03259120300400b21300240301c0104550702a0380615190101142003101700084040007d0480b4009081260108850740c8140103000c0d070704403c1d42c5e1040031030420460f0541070404101c84031000992424042d101807544201070b850f0401805035144c1d00820425490107180b401a0a82e040500440c50900c43e461001d9074180c407540c44c0d02c080301c030354040090a401e034649900c406000c80e181c5a183c540b00320b100008985000050800080412811807215900c60304012408c1c1402540700740c400840610a00106188182003603030080e00707030308280070144000441078030700f4062100d000d0800e00001c400c110a00865401c01000401204110030f0380c142c06481c01005c451040801c0401a403200110b031900030900c402c03640c1c1401079050150350a2031684000e4050303a = true := by decide +kernel

theorem cover : BRFrame.Cov 635071942 635251798 := by
  have h0 := BRFrame.cov_init 635071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635071942 ≤ n) (h2 : n < 635251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
