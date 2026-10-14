-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:29.412445+00:00
-- url     : https://prove2.me/submissions/343a0af5-6c3e-426a-acd6-da9e22ff21fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630755395 ≤ n < 630935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630756645 1250 630755395 630755399
    0x30302011d0606090708180601180507080403090b0307050903060a0b010e19151103040e060109120209061002010f020a0207031b0605030f06030106050607030e0916050d0b0607050115 80
    0x221075166103400800d00d400625151810f040011480d00c00600300030248400b8601180c4c41d010380100960380350443c0e000b1a6115603540e03030b8100400c0d0b4030021305094540b802e40880c0d4500d01c1003108030b010707035015a16101c1940c203110846400740d202601e603c0038004200000f0300308e0740701404114032800aa0000103900e0201c41d0016101250704042603205444112400c80030300c0216404400b81da414200400c00801d00c110309076500041d004024400384804a4002040c69403118500d10a5800b80c0c0c0302000c403030360ba444205595503038880003541712202030000b03112070030001101c503225a114400071541118000d101c004a82c8098850001600301381e500744180029601e895501400b1046200042032900400400900024202c0c00c0c281d40c40801203509a41c094110601900008001c0c9580700345915014010b210409001d03400b544010700000c28040c0d1695890314000402c4d280c0910b42007072210040b00400c10111030a41c040814003080d00800c01c02d102d41c640b07101c160800e0f5150b00e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630757895 1250 630756645 630756671
    0x31b1c0806090a051902090a0b070b0a0c0203070312020a120608070303020733050409020d020a08070c05062d010902120c03070c021201140901020a09081518030c03030103030201 78
    0x14001001d420f01e040c240383c144000c208103d140b800040f4074200b001600c038100c4000061480e00f180c0d020040c086000718500301071003c246942801100550b4040120020a180c2a40c0b00e010f140700140105504001c2c0c98400c00d51a0003c0c40083c103c0d1400038588aa4403108004941080c0c0000071a0307840842c0601c1010b0301002142c0103400d40e0181c800ea080f40281152000c03801400c0e120544e1510303c0500300d6201d000301c003500d010b080103400c25900c50020550210003500000c51391400258500003090409020342c500d10b41c05500f28000e0401540c0300114a10110844003034600c0d10710304a609a4981050f09406501801940c440507035501c066000b10064100c01401241383c2403002c000380321000d034210342201481c80d0705680901031b02c11600c2070781d8010200c14000e00c085e0341d60030702040001801907006000c6d00455850700c401d01030b200e00e02603590b000302000703441d1040381c0d500214000080c0012203616203601da20881e407808201540460031a08280d00031005030b912041920804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630759145 1250 630757895 630757909
    0x3151302040f060206040f020402070f06090503270a060503060a03020607050706030c1107090506010309120206040b0a0c0509060306040e0703081c0b01020a030c060213030b06030111040503031b1c0806 88
    0x600c044c0c07004280c5410140c035440c5444000300320080c440c950014845003048010040c3c6214260424402c000000342800d1407611307944444281a015503251048080c04c283e0361101084600e0007401010f191405c141003910694005001503074810504d280020050343d0343c03c01413409610900203801240d1401c0d002409480340755400f0002d002c5c4038105141060340009502084480f500e8010a15480f0140182d000b080140f401509000d808004c0f503111315000143c1c9401180304401240890703940152850803910082c0c1c6890003c0c00422561405103816406140c1002000f8070000b144d402103441c80c2d180001c241d10843d815000072170300a0701244003080d8403101c8140001d0074840d00c0f401340c0000303449030940b01d4010184204540c118060018650548440802040c0d101d100c071a200e0a10516240381203442a100350b081c20f4041c0644030004055404480020b001035040030301703e5403183c000114642480301c2d00e20404c040c9074440c1001400c01c0d40f8592a40d1601d4070030782400402c0c4000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630760395 1250 630759145 630759149
    0x403120c05030a0f0509061b07050906180c19021621031d0a120203060a0614090702120a0804140c030c041a04050702010c12090c050603151302040f 65
    0x34040840d40c0c020106002004440f040481d5281058030002c4138502a02d05020b1600700903000400450b840004480c1045004201e001c7d123002c65206517990707400c20110341400c0f5409904400d0100b07850400e0841e101040b500820103095550070b0141a81c41000c04c075650326803d6005a010170101c00c0100f4445d500b034005400c8510025034924068442c64042d4025101c004080052040003141400040320030041c010000a240452569558440420301c2c481e00105920900907040810411581032080380222400141d860040e205140c041011603400148210194080d174132903404802070341002013241032010b4980f49800c2c10a03003428020440341e41c943d10815032041462041503039001902508800c411a408910b40700c0b4142044c2c1101c545298441e045810941406a141e0b010740010f69100311943d2010354100800440c0420f5450500003d070001c0003806040c01035040c400c00a41d440781182c2190014410404081140105100c040258203540401c0c00d1001202103139038440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630761645 1250 630760395 630760397
    0x303061f0503040803190e1c030612080a111c20070e101a0d0b150702040218091509011401021b04060302190905060a0806150123040312 60
    0x10454403003180c05445444080c1014210079008000a200b52482a03008440b5002c5002c060005441128040307036500040c4458034030841c041071290486511030b104900031243e8104884202a040c1e4461180319400100e5000070802c041030072242c000801c0000208200c013032944540303400d031031003002000e115800386601c0c02005190807070002134030b0000317400c2c046da0f2107841e81e607195485001030340d0401e00296000b49a2915000000140c1d43c46a00160001e44d0354110140506c03030994040140d480c0c001e17054164003000c00e0101e5070150500394050000020460044012054031100064034107804441002c0700c4894112046400c1c18a098400e0051440304000c5004000000020303480d078810030218545401d81c400b1030f0301d00c2d139950303000310000710780148c00040348000c450003003c010b080c4e40c0a158038503810400800c0349401c10036010011500c040c0060900c6890b42c002c100c0e41795070211030b600d04101c0360fa00c0e51140301c100112072008001c201c0d0301c0c0e20760b502c0c80c40c03400351640c17004004864 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630762895 1250 630761645 630761689
    0x20912060a0b2e02070512030909010b1e131d09010e0607020c06130f0b041406040302150309120d02090306010e070f05032e21080d09050c0909030306 66
    0x1241001d00c401c40d040360780fa0328404641c0c100180010881c07030031031560312440e40305841482e40801e030301e0044014543c0013401e880081d2643e80b500c0100141d80320f140008403a0701848100f2000240000000c0e046880c03032030010303021b8540d41d0341015414240b844001c008001020382031040c501000d01c00e110702c00c100503016050a14240310041d46030310007410001d014030700c0019001c4141e11090310741400703031402d02130000c03682391111131103d1160045d014280d42030400b00344408103440d0540c203960480382c0c010070300041c40320202460b94580d000601038131150300c16480384076040d50011004d4080c150324690010f03220006802018030701001030307011080300220002440176450780588007e24801c0c02e8200295291254412410100c0b4800c1c08031840c40390fa080810f00707400b1583c48082c11a00c000001c074443e07810002600c0403140d80f002c4010510707042000f100440d02a1030700881c1c0c1c598081e10075a80c11800e101c01141155001315610305440d0400410440c0030315110b0070b0989401d0201e0900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630764145 1250 630762895 630762919
    0x203030d0c03150b1c0e030a03060608090a050309010e1f020102130e130b040507080601030b040209150d110d05012307050301062f0d180b0c0a0602030703020912060a0b 74
    0x500f44c00e1162512460070740c10114440c0c0d4401d03250703800c0700c3c040140c8002220b544940403e0010002c2c01d084c000d01c8009405030b808103e01e00000501c240200341c014003e1840c3c00100e100545203100c05e050708a8114070250300c1400f0b08400c0d2943d8049904543d0000350f43d03040400c03a1209080c1c55a045441d004019405105610009842d82032031280e000000e03103031649850404034035207500340c0d10000030303842410008010080c5c0251f0301400707144281c46518403074450840260700c60028048580e005845211007002141d8912540c41d4030a8014120589017035094550b00d081d00e0201011000d80d0752034031511a04804601200b030b40c071840518101d4215410a13500400c501010720058481031090028142c2d503100c8812542000b1b031119007119002000c0a80213844146460f50a00100e0009000001c20710203010440d513401d0b8100c0d024009190159480500940000d00000201907080c40048105c2e21610003041c40407000c40020051071400c143c0c1001503030301c10300000d8014821760740340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630765395 1250 630764145 630764159
    0x80d080a18031e050c0a120f031a0d0c080d020307020f010e18040602090a151e0909050a0e0106240e090411030c03030f0d0b0f010c1704030203030d0c0315 68
    0x800611000100d81030420b49030b10394102c682c4c5c001c03001601010b00410394200f0410800710306545544040b52030780c0d000445284401d4089032021654401c45044500e84070000389030038010816414440c9480c0b5000d2512501001e140c03401d01070f00c0d0340141e4400680c240c00d51600c41034a01c0141401d28240d89039900c4c150109a02e1600070030f00f512004003040105040245640580c0d0740140c0141c80407180c070740e0b40c80c095404a000c00c485440810f006c0840401e80260211445c540d154071511510115480d044850f4010500100741d1500c007943c424041d002d440c020b01030000200160700580c1d40d0001d20108102806003040001d10074044074484511254a4031140300342c0c4580c021000c040500c185a01107801d10642000c400da240c04000b03050003c43d078204024120390241100100030452032001400451145009040d010401852002000030400c0c140c0006035260352550b1810700781c1c3c07540441c0c036507042200100006512481c41e11b0310298188a0588450103c60704401c0f020703d0012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630766645 1250 630765395 630765407
    0x30b150406021e0a081c0e06071d060702030106060225080d0c031701170d0504030503160f080d05191a01030b0120010506100f080f040309080d080a1803 67
    0x30a0050015403d0110001c22005102c040c5085030050300240e5a40800b01503c0e0000c80038407a56a040707480d0075045000c00700c0011b1014881d40329603c0e0310072040041034070940c201040f24075455100b04100150320040c0c400b801083c004000d1600141252000f160100107505040d035038900c540106008100004100012100040b006ca4281250106480d0400700c60314004000801900003c1c00000580002c45094020751100c51409a40708607624520864a0384a00d01c00030300704d41c1c418001002c0600d201406052085d201d800c5003003080c0b08031341c2c4001c43c80d08001c583c40b120696410070010070501000b1442e10b40003040804001401f4034074045212030302c0d00342e0b080d41010795900c0801400d03400b60040a01010442202c40c50000109100c540a031504442e003074012074180c075180b810035006500c0507454610a44503100d03103071342c6d0305c20200310340c10000c1c0140c04001088a000035101c3c82848181e000940550360070100b850111220f9090303400d00050a19030440c081d900d6000300360700072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630767895 1250 630766645 630766663
    0x4060c020a110607080f121801060b0319020909250903123605040c08060d0b0915091e0303060a03060b0f040617121624020a030b15040602 61
    0x152a0340c2c1320000e50a1100343ca01420321041c007074240010302c4d0000046400b2903203101c1d0302c045445a50140036101c0d000e003038070001d205210300100f0038000304011450f03011102e80c00400e409801410309205500262020a09803030940c140c0d00110201d10b188401811860800d0045092201280340785230b0301e03440c0c00c1142d90203000030085c1000c0309607103036007146100824064040d480e18210742412083c80b000240b25100300340c400c910300b026086109004010051148000800c191001c2d60203031a1400b41c04001808840540265440400c3c50a81c0c40700c01400380147c40700800208401da0384240c01d031802c010100720954814030410465a441c1444c0c6410b99620031000324909072500003060f6013540c06050b040e8028102900843c400d084807000510100d03641c000c59281007030040c4c0940b694820794521480c00034400030750748046442e064804815010010030540075000d01240801240c0140c840c500000f03840748003000561910b0350929400d419036000f02c5190a240c0701010351307921120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630769145 1250 630767895 630767899
    0x12081005130510090606020f070e070e010c03110102030103060b12070509061309080403051f050118050601180311011205100e040c1e0509010b070f0602090409020301060b0304060c020a11 82
    0x224000f45214081c0b1090000410902c03406022154903910081e44034030400c1080c4565128580d4005078101c0242c0300e65016440d0703900c410070b40f02c0c00c40c40111080a440102a800d024003100c3c1403041040920085000b140220b00c0001c17420001c500b0403100c002c010180d00140e030b201803400e021655503010080c0c4c006800f11068a002c0900d00aaa4040c00100d03c3c09405000d0109000040c81000315030b0b100d030f0544600000642410082e03441040741c40078001c40031803241190b600c202c6041a5800302da000f1505040c582215050407181040380d20f1150000c48076050508a041c0003942c01140494503c003c64100340b00d0352405252160805215204841c0302c40e045074041418081d42600c09030140c07841c0107082c41140118901902e403001d00c1e114050141b00c1d44170001030810420401d89001a40c0480e40c222000d110303443d550040c1d0002d8034a0307507105076185d8900006a80904c85c10b4000c210803074001ea200c0c034003802c002040f11140c42c0c404c015504250b00910000f6000404409400c0003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630770395 1250 630769145 630769151
    0x10e040506120a060f141005060714060411150a140f0c0a08120610120b130e06091504050a0303091502030109050f100812090402161208100513 63
    0x1003400286842280302c0c842d24003402150504414008940c10051548808110a104c240903103100103081c40c10403611440040c40e100c500740841c1c5840c4d002003480d02d0185040340c01208620010a0405805480448101102d540b554403503041000606502e000910007681c1004451a006041c60a150080c0b20786450000b071510f181c111000191180c0c081c00c40c044032080b41c00341c82c0121180c0d12842400c92148240300c0002c20030710740050001c04070750565844901c90540c4a00382000b9026400b081580106441d8038401e160101d48202c1780310805150040c02d0754204407201d42d0034076658041050b4201d01c1002004041100090303184090b45c0d05240015881400c0d04040200280b0682c581c1103484c0000000684010160071003070048049202078161078482c000c01b860801000c0c45000d1464000960701c00700720348044050495100081d0015181101003040a44121442c4004807201d148079003003090301a40c4602c0403030748912109412000300b400c1000151996a030080c0c1222940c3e2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630771645 1250 630770395 630770401
    0x6020c010e0d0503040e150f0d080a0c05030a090e15061b03070b10060e0927120301030507261504030e0d0c2c0708061f1d040902010e0405 61
    0x11031050b01c014040c3c209082d00e44458503034100e140032a5054842e00c503902020002c1084502d010b40b0341e00e4035514001c00000e0b401009a40e02207132500004000e206010320254443d001c142d00740002d1503c4180c03070f519a2115820308010803040000a086200c140c0c08200140006403600d40840705441c4100d00e000c1e01d482c1c0c486c02d4452940c4600032006080400403030500c84414501064802522103d8607030118142c020010700a140e64212090790002c154100c0342142c00c40c816144440440c8045c0a4650194840300400510b0307000303074012142c0741c3c0041020001d00b46407106592142e03400300c400102d04035180f10503d0b544d8649141c100d040304542d80201d800c140c040c910b010002c0320058007401c02c0070307014201141c00c0030343c40c8242044071300000c0401c40c1c590740b07008805000014800014030340b5100c1100441e98000020b18040d0440071b0704030403031900d00b102802c46119581c55a103100341142100703144010050300e0303001103010b00e00b48610000180e0304031080100c064030a41c2c1c001126030f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630772895 1250 630771645 630771649
    0x307120c1a0d020a02150106083702070c0302040b06030c0a20100b0108070509030a0b1e04060519140f0426070204060f03021005030712051504050c0406020c010e 71
    0x1200b6107045401c031610006400103520740108a03107240d4000c10594035900d80c0d0f0347c60140e541140403501510b03140802116843d500424241c1e20200d08403103800c0c0701c0c112540441301400c030303800280d00f9120100605010021441c05c0d010b000450001500c619066052140104404d0702540940d14240101107002a800e90387e140031081c1440e0031030782101c0461486911007002451500e1115000401d00f1000800a50003401101c100c0100640200014419600c0788600d020001c1c2200c010316079081120080c0c2501100024011401954000f8840c03c00e0030002e10f0355125140d03070002203814900350341d0020003141170080d403184c94007400c2c03070840e41c03103251188141603980d80c5c012006d42d03c0300c000b12001002c04003030f105891090782c04010450700d40812030035944507403000a611186184244071010300c42c101464002d403407810300010f0032403180c00c02410703507404607142000c1c030100020480c4186428025103801901e601520351500b402c00708000d4072081c0a84100f8140061141816141c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630774145 1250 630772895 630772897
    0xd02092d0106030203040507080303010819110402031e01120c140117070f020c15032206020708091c030801050d020d0c4232090307120c1a 61
    0x1a80510030448229a11244082c00030342050703030705035024030034600702045025000003100e0503070743c46400600b4201c407081100a0788941001c1d0460303c4801c00140c4c2501c03900c407400a14000c0a000d00c900820585a1307140020140d4168070000a0300740041c507690200d00640c20020580c2c2036032003100c609100d80801664049041006c8100c4042c180013000061540728400344420307201d42c0e09a940b0b194003141007180120420800510744042000842c14403801c44010460400491504001c7d100e019103e400890b00902e03015030300007600040c06460ba162100070880c0c91310f448500051912415180104200014000e0700c4c020020b03e07411000390b648500d0600005640450450004c64480100c0754651440c1040302d840540640344c0c5040340b40c8030300c0a00c90300751b1512a010200313800841c000c495540320641e000d0b5009901c0f80800d000354940f541e100c8801d03034040c1d52156851200301c041c94a0314100d030744407141211380761107078400084040280408503201e0740303d6880081c1c8201041c0b511 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630775395 1250 630774145 630774211
    0x50423030c0a12021509030d0506150d140609091b030c1c0c0806071704020f0402070606030c091a090604060806010303090e1008060a0c0e060711030601050d0209 71
    0x26200720b44090042020309503c51466100c0ca40c00d544000c0080b85480f403131024140c03990703500758005100d009140841507008580c00030005200074043c2a00c20100f01081c0c5c001c014103d145515100314044052044980a070090b40940d1482040e10301031450703988170000d0800c0b40001c19030103003960031103035020030020407045001402d1140300007049078103805506020703004454545800b08009910100804c1c5640f1802c000e85034030f05400810740b01c8100200c401441242e020500c91800546600c03284040e105042c0f003000005905030440c01e29203021000d5901107040b081c1401081c1610790298803140d4850001603444501310b4440e100040e0140c02c41c9d0f044690103106800c0004141903004855804071950203098107203076101d1b40c2c6400e0703101a550181e0272995110301c002ca072811074075a11105400215151103500c01c9100c000046c0aa4807080302a10b0324201158107003101c0c41d06010090040104403490303120b40d440c0c1d0303001c9201908020301358188160a0003085524000110030944 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630776645 1250 630775395 630775417
    0x206060d1a0a060f0b0d0e03120a1806090515150f01030504060603050307050a120e090402010c020a031202072102102d260114060a0509040f021b0105042303 69
    0x43c0c0661146413408013071b008001000c108a041440340c60b40c2901c00300c100c80f8100c24070082042d60341d9900903080040c2207000c45901e40c40400068202c0850303803d1241e81c03280c030710400c094040250040c4000c400a18090005056010950090940c940d100702650321415401e00b00840c02c0e43c0d690628000500c2d80c1d60010300a4003001401d03104000300441c021200c18820706c0380e40300f00c0318444412074100044002d11500020000003185c0598050150f90310f1280c4014a40741c049074503541c58086042d0a0210000517078001c00c002d001001180b92100948001040004c41e0f00c60280c0008010314081000601440070507001c40c0100e0307c540340c1c14204014940c581c0c400038081a1340c0101440004060a0a000300320219200c010b0301780400c2c58125041189408a000c0000301001141d41c0306480c40c4091080401c03403011184c64a0280c1000c14954160040c2c4884a80c1c0e0000d007420409800c012640e4134220030000081c034031036916101103008804134042c0320000044541b440c800e44540702c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630777895 1250 630776645 630776669
    0x170601122414031009080301060311090d1b092007020a08120d0e0307020f092a030103030809070b030c0703090909061b02071428090204060206060d1a0a06 68
    0x41803440e0015400b401e030480035401ca03107140b02c80c1c1004000f102c680b5000181540740c104010000c2c241b080c1c12a2010300d1580211515100b85440094800701b1590005c8030f04007400d6030100c3c0740c118134040c580001d1250711010b22107006a0f00c00d02d00d00b014001c6903507008410101f05c51080d17403280c0e0080005012040b040342c0c4140c40c541541c6101b50054601c07540c4182c201070515100800100a80303d5071035000e04491b4080c50711904211b40c48600904003001c40c00e41d009405c000444855410710b554290180c6540e8a5045045c000c0070300c6001040b850542d4040da00410940c1189011030b50702c5039030010503940301d035072915003110449415445040302c2030609144c10148416135104c41030740095000b10818a440516050303071108a00d1051002c043c80f000a50b80640c10651000850310341281050300d00e0040d0351130f800b1280b2a658000daa40c580d070200b000d10810b50104040d54010f03d00f11076021180ca1195200c042000c2c0a48640480000200102f081640c0b290001400340c20240861 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630779145 1250 630777895 630777899
    0x31b0305060702010e1b03100906020d09080301080c04050106020a0305090301090b0a1b0306180b0a1706160c1e0309052805190308070822061706011224 67
    0xa0282c0b80c00205c928203802414810441b054200341911420140980903180d02c82070201c0c0d9000600591800780c40e003d40070002d01088401501c51071085500c650002610ba50500f0305182c503050440c4103850166251034014807003560002400d05c0e01c9541880c00030360b50400800800d000d48001c100080c0081c1000b002e00801c132784242c00c078041080320340c4d02074020071503800422415190399100e40700b5685141c910b04e2410908507084803241d400c0160101d18060380d1414100301540130b207441440182c11035814810b440803000d820120980c02403900e07528621407900ca078981e800d41014005410310803640c4010406005922420007080001d10b4144801c009580304022041c07007140c014201d0078004008550313440c204030230325103982d100c01c83e900703c0d41d06580c0c1d40c9085034003251080d86d5411061003600001092401b46400314114040c240340750310f28181e0003070500640346042010805c0034500700321003645c0c401010412014201c10100e8130b4151b03900500b412030808810951150842500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630780395 1250 630779145 630779147
    0x10030b04141c0e370509100614040b0f03090a060c1817060a0908040905010f031205030f070f0c080705150907060c1203060909120201050a0207080301031b03050607 72
    0x180381044031607450b4480e2424040c8208040f080007940505986800f0403100c4642c0240c1241c0c6035800b13459904034038030140d10b1714000f402c28002181c80b0780808980038000d2042d140d10200623032050016404c0117080c0341c01c01391548064000c5509450714100084009041303d141048440520340d0032500c00c000701034140c180200583d040700f80c2c0924003e1981c0c00010940142400f0050740301c9400c000d8a15a2150002075014141e43e40c0180c400350014000401e14a49034031403d03001344000c0150b0307100145545003100c4001080b01907076050281c14400c00000711201448a43d00488070b190100407900c47c04005c0e905000c1c5c80c10060000400440c0d460108080040c81020325034401c40c481c00da550f103400006503999100d0160000007021907105034005808085948240c103100e0902140c0152642002d07000c0b6541d5000070b84a070f00d450410844d9a13a028400e058106664880540c9840215202c2a44500c07042c0301c0180019030b8041e1410a4594844a03800a540e0240c140c88082c103052034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630781645 1250 630780395 630780433
    0x10504150908010b03161a070c06021f0203060d031107092306030703050706030e15090a0308060303090d0213090b0f07090b0306010807052d0403050c0910030b0414 72
    0x22002c59600c0d0860707000040c90006090003455820707802d070315503540c10030202d540741d601ca0031030304002c0c0c01d400c1c4803020001c4c215940309409000e07268020501c02020710340b414008400503041080c00c601c10000d015032600e0b400d0300c2c800c0f85500f60070010f480c588e91071100c0b4501801507205240c01442d0002c1003d00d401c21481c85200609000f005d0b818688540b02055251a2144401090350b4040752003044518042d801185504c0c0070041502c1e030741d912281510540a0b800c5442014a4202c0700c01d0760304040d0032280c50f90700314409030004c5003041c2070980070806451070044040d206224402455458a0507a040164482d9125500c50701508022506180d0f02ca410349600c0040740400d1008600c041804003560b10441c0305079a50306960310b400c04151010f501c0002241060f54420241e0450f804030501d05082007804510f105944514604103181006240c580b000c1c450482ca00c10305c081c1c0fa034402d594009494001105000d25241c038641032148445a4103160518000c03030f8002c1c2c1000f44004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630782895 1250 630781645 630781649
    0x6060e0702430e09030714070e2d1306200a03021605030f03010f080c130504050a1a071d0d110a0905010b0403060e0105070f03050c04030203030c030a1b0b04020f0105041509 76
    0x103c3e100c00d0501c809107005031222481e01625427854910303c0050a1031b03a400c0070180d0085070310180300303c8441e80c000c981540800200d4551814482a941c40000c12240d40b091103626600c80c02040107405e02000442d060b486408004010140c0104401d071288a1007102c0444680e8802c045a5036294801c4001c80d0741d070801d1003082c91190940000240480c000302d402c0c680321000403d24998200c458950b400205000350080e15644103201c440000505035007004e00b040e48102d11881450302d0503020041901e440d0801da034040d404510700018440d01c0d0020080305581e400184200c2020646d004540c40e1030381d40d4021107910303041200028850340e22600400c03e481c0111340c1480600c0ca103a000398203840c401d40b40c1c0340010f1042c041da05441846540450740100c1d8007010030b0f05d4181c2d00c0e00040d20319001002d40700c4127074200061150005400040c040c00b406400c81c08980c0c2c900d440c0d00c420445410040002e030003240061030b0b022182e849013085401030000c032288184030701601c21006250710024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630784145 1250 630782895 630782903
    0x50c1b040b0a120204090804030b09010b03010c032c03090901141306060804110105040b0d0203090706180b09010203040b0a1101050c03010b07020d020d06060e0702430e090307 77
    0x603861030719041101002050310840c260740c400202069003840700400780ca501c00d69183c80c0512000c40000c8400070081e000e26014400494904055810982150741c00c8594400349071501ca54040d1b4070104251214182803542c101400d241c110610881c103610030205201e500c001103d00225840c2c0c0c80102400e6440790544120300410801113031441200c07030300c0c00b600c804510354400040010301c3e440200c0c9810813043c541581000c0da1030011641641100c030300c074400d480e004001c001c000181000303500000c03d020310f480b4510621a0103c0340002441d0301a440322103c0028107445581d0082045030014603ca5500560f00c41d0325507801031610743e0204081195500344400b04290462001c1501d05880c003001003640b80000c2c9500b00550009821002c0783c0000c400300742003002c64041d02c942401401410b50b0082d0610386840028104104010402d4101c80d410942142c90b4500d00d4240145144a0701da400d02c89030519000030140215500100040c2c45c03000c01c210315001c0100103001721600c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630785395 1250 630784145 630784151
    0xc071b06030609021c1a210609122203050706170a1a010e0a05041401061e0507140c1003060602010e0a050a0b1e0c03060f06090f0907050c1b04 63
    0x241d50642040e84100e4103440c514403c0401756403519800c2d50300c10210b84480f42c1401079200801d0303001c40c02c400807594010080c1c030404001503c5d01c40d42840010340c000e050b600a00629182e40c00c3e27210700e030700409410704002e90940040090300d1010981a101a580000442e0641681c92100401c2d0880070b81007441c00c002c003140490a03840c0035008503400a480406a002d13031541d0700c401140c0d00440c5688007580500f10405c000b41c16241c40c071402c000312541c0c0b40c00c5000d0358145500a00100381d01c13180510b8084000c102d00701d040b0340c000c0665a0b4182e02243d151003c2d4290080f95291006824000760b001110003545262207070582e03c014119851078000744401c070303212015035451b9198014050119006100c0318400034821405980d4440e000d00110507481400c150954000c0f2022220380d103070b4200000503c00c40345003041100201d001c00715407040c40c2604d40000b2400c841d1120790454002c07600d0380041aa03280c044c0c41030701c0b0750729460f04c103c07442c211080c4890700d689021000003e004d245 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630786645 1250 630785395 630785399
    0x30c010c091203022524030c05070308040803180115050109050d0515070306030c0b04082b080c0d14040c09090308070c0201031401080a0b0105061804050c071b060306 73
    0x44114111030340d01d4154014004103103d0900305000c00c00303c06044017401c554000007148000303d541e460218600e0181c01e03a10080d54144000c0e044812103a685020b00509001c4400080ea1100c00d0301e600a60122080d81c0301c1d201c0d165092034200e20020ba18416500780341d1444280c100203950003045490076038941c040d40e940e45042c803041c01c48102c0c02401c0c5821901140700549051004c07142c0081461a0000b2800c2e540e445c0c0c62300045050300442c1d0340d10340014040210440401403000100300d03800f580c9500446081540c0b242e080348140f41c4c1d080c0f24500d03000880c1000a441a03c80f00b4090760000c1c0004e042e14007101c0501da404075011950320203100c4000c15010024450300814a906845e054281e490341c00c5c0075520503402420490406881300c0f004031248140010041c0241034000040203d08664684502c28200517004a4002e0405101c000c07003141401d0b0450305100d005507800200c2e5180c89d078a40c83c1500c00c2c0b1300041d203041c0c20b116000d801598003101520032110640d50400604c1c0e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630787895 1250 630786645 630786659
    0x501060c060b0a21050a1202060403080a0606050405010f020c0a121406070f110c040f0b10022a04020d020a0c1a04030c03050904140a0e070603141f08030c010c09 71
    0x4007140c007070840c131000b00c90340b1800b00c080d510034994092070040e0215003004c410340d40c0305044810365054010040e00b00ba8144001c050300905041e8100d41206014007190f400c190b4001d16502440c03189904001d0941880c4911500900020594040107808032441903182c03490b08071003110030308040b134003142404030440003030902162542c080c00540c0d030340e00c0c100030301d05100321400384a1200301807003802162086022a07032140b00380035014024400c04250100c100081052201d03401c03400300195009809a400310048208801084424441114040c500e40f0404038000740604815200001e100055100721550403a00031080c4520070300b0f1a2500c80a0711080070990202a038009000c02c03045165100064000c00207407081080240000509280c0c00c104400c1d0700030107548004c0c6031540c0703040b50703081203800344400d0019054504007070000d032032955005c1017a608000d0a04004d590a44a64840e018180e8a128001c1c07510200300ca456200f01840301e40201003c22418000c95440c5070001025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630789145 1250 630787895 630787909
    0x2180406051e03030c060a090b0603060610030c053601090b030708040f050a0c2402031903090503070c0617160f0302130b0306100503131103030d0501060c060b 70
    0x80c82010308508036401c071140868080c498030b81d4050768540801e01035400803850400c00d5a1240101d5800030a0b1948181020007000e013000d41500c1c044d070041070411200d0703150040c15143e84001494001031516141404441c50700900d60001b0011440001d0442c40041c00300c408030400c01d446100400c0d8407120001944c481c005403085044d25001400000c9400780620f140ba540103006407945420944142e4800742851010401201e14900c02a800e109400b00e43c041145403402e0b40d4444400160040e6010359240203040c524401c2c2032443c0c11068001e480382c1c000095581c0d005084071745030300c964035000b100c140e1940143c1c4001903581914565040521100034050050000c91000c00c11070a242101c2c5d490080c5880340a150b020032200b800700c50901a21801041c11022660b1607082041c10042c2024404220341c4c00c0003014400e10a8200c00880b03000a140c2c2e101d00302d01c00042600e000f0a00311b000d03c1c207440000c940b80c5800020f1540d004078203030700078a100312010400c085400d401c01c150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630790395 1250 630789145 630789149
    0x30512070804172b0507030e010b030a110d020a060f021204051f170108010f14010e0115110d120b0108070210110408010603050a02120106080a02061b01050a02180406 73
    0x850740346145252000ca24000141384544590700400e842110030300030741c031800b086a081801c1a41d90342c800c00030010307030600c5001c0001e5442c4000340055209040020740d02c0c3c012500c080d2407003500d40f00801c80c51751010440700d410356000e480c0b1140d2030355a01d00506854407030820040980100e0750701c81d1200d5480402c85090740d600501c0d00c020641440741c129401c00005111609002a80600315130301621f107050607000307000b40000820030004000740314040d50440402a03054a10740f0700180045000c02d0b1900d410f4424418101001180e01d090465402403141c40c0d08005014082c517101c0c05a500c250802c0c903007006010180807040c0c0840c011220070f0411608000145c1104c1d5000e141c0020300d0704160102a070750b018103803d0549404000e0700f120741c95401210640d2044441400710f060820f11583c0e10303215100200032444c0f80c440e8041e180c07580000c1c003d02c6200000b800744d00b2400b030031441c20111180d02000700316070b14004210000a50040001040b080c114094500080c41d190081e002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630791645 1250 630790395 630790403
    0x3021807230c1209041a0f010302031f0305071d0702070b160c08010c0311040b0913060306050f07110106381210060c1109040302120403030512070804 66
    0x100390428421403440003541188001c200e01041100541803030041002c1105920310146240d0307038850007400c100460b0703151004071490317808034a40d404030b40c0e5480d0741c0394440d10820f09015a503036440e60050303000c2c110003c80a0102c02d0210f040030091100005d8800c09407290018985d43e216815241140003440c11600c07040103034012282400541040000b42200390080729003100c440485990310300526109030400400e0f60365416550100e550305000b0288540b00c0340c0c1e480c40c50f00e03082002481581c1718a51400e8096542007491f0010504154040da00035a0440030030092401c11462107140080107030b4556000500601c3c10314030300301c010311585e01107400d0984540108030741290300c07201c0c0d800701844807211403100a1141a080556074000e120416084640217424608000044000602ca0b0020020041580441c40001d6814032524014a10440790740001e03548510f8100e2500e030000003607407107924000c14000201071b00700002d080b52110300550b42209a131026411110381000702d0b0050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630792895 1250 630791645 630791657
    0x10b180408160206040b0408011b03150e1003060216060b03030301081506120d020a03170609010314010b031e060a051302061c0606090603290402090102030d1503021807 74
    0x842410300b80402190014405002d140c2443e503034628160890304540e21041c00ea945624412107400524000700d441105541420000c004416640001d42e00641c0105000041c0342c802192800006044042c000c541c00041955201c20301840004a60f80b802c03400c0300d009040c000c6c02c542c070345400b1090302e051b41c0380040280182030f000d14080210010103080a50082185c1c450003600314801c1c0b158000d011502d07001001401c82d00e250042000d41505160b2403c0701340441400f05039601e02094a0440e038000118501126444040600410051180f65490312901e0700700300641c5000d03004d060101c45003a00b078808035500c01d14030a003516800c603101c103a0344201c0c001040051400202510517100d8008808082050030603940d82103842d02e80007003001c1103e80300108042a8180940c80240307489106200038014032940e050a03508030b201141d40710355000b1a0000c00b5900c20010303110104801c110603c0b05120a140c072500c07403001808181c2c060041812600c04210852503c0ca00440d40b80c0d4401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630794145 1250 630792895 630792907
    0x60605042c150f09070801180207120c1e0501050714032e210c210213022b1404082a0307050610080d120f1409010b180408 54
    0x60340751154202c20360755000c841c4100000d41e030340368207080c02d2291100385c552007000e50404092001e483c08003200c0d800700740e00400014000a070808606041e21105090a80d1140c9403440c2c0b00101c03200c0f0002540595980c0340801090110542008e8020b4100742c48000c0c01072081ca01090701c61000f1030701c5501103030460040e01107600d10115140180314841d84400302171034a60310b401d0403014540ea0101d03008001c42007682d091240d501000f00c01064025401c007000e04d21025081c90040310414068494040700c1750b141c484038600d80480301c540c640605808000f909014a0400e1890300d224540b00705450a2100d505080702140c510380625003109200b0b040015803c4107002c0c4a6882006110b00c2003440031181e03583c4002c1001d4000540b080d8050303c000d15141a0608041145a001e40100d501c100d044034000f03134005582d080702d013030020070110707070620006181d10141c0f64090603000070101502c10041e00c1b45040d80315240c1600111256600c920800ca070041b4001410390300940320050422403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630795395 1250 630794145 630794161
    0xa210c021c0905030a0f0201020d05091809211b300910020a0201031b050f131205032805031f031e020108091219020a06060605042c 58
    0x410091041c052401800c46503c41012a00b02512900c04407507030300d09055510215078060040300070307920b6640b0304182030003808000104041100020080741c40c5032000400d45030a0103003c043e041c1005102155009090400c40003600c5d40705a00d505000c00c1314480401e000364000c03170307044460964151203a40c45d81b52190812901201212401c0c90050100466416601c0c1d40307880300c00e200791503009040c0146007800090195101ca2185102445101d071003041d809030448152088103081b980c8160700d4600303d1a1480d140c40850304441ca980304240c03400020004000014011840d10700341c0111001c40c01c1c2d5424209a2080c401c1c500460303800d00010768401c0328025003140601c1c20058250416649844d144c0c14a1321705c000040c81040144801d0040d96080070505401c4003001c3d0051005104070580c06059000704010040488007000e0951403070b510802084a1003904004108000b59469502038150b41c4288510074414030740300d640515800d6140ca004604a00c520080d01650741c3d8142 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630796645 1250 630795395 630795433
    0x4021308100c390804050f0405010305070909050f01180317090a02010f1e05090a080a02030a230709060e01050916050307171815090703170f0a210c02 66
    0x71030740c02c0d2102a0107489500504041081010501544d0240c1d51142800709001e0100c405040841c09141000010000601e000a404044490880001a42045500e801402c182c07100500703454960800030b500300c03500306805040040506c00d4a5500d01140c1211060082440440d48410240c020f10110009075005810f071401a40041c0740078a040340350021490880c4100907181000504003154007a104d0400c03001d0003018002c200c00804202d00c40b80d0020b03942d040094401460030503040c5086d40807584071010803003200a0301c8141d41d841ea40b107a00070b0004004030b20607481842c45503000001c039410b00103551401054146c0514110401d104025035855002600410030000030000040d00700490305001d07402000d82d0000084805903414216280082004200c004410300d441030100e0b0f41000506d80003142c1d404401707021070040e4a00b50b401c0c603003e03030001c101d00c5e6a00050301120072070b44010201e400903040f40341b151114458001200490349034026050150740032142c1d0a6041c8000c01c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630797895 1250 630796645 630796697
    0x20d050f07110d2001180311011815022b05060108040f030305040309170304050415051f0207050405041515080312060402041a0c1510050607030e04021308100c 70
    0x108403d03104e5008001c1c518211507005080c0ba90000c03000b01c0c94003c00d0b900c039030b040b403005041c0700003402140c10000300b036811511001c10042600b0301c01c0d0001c2681d0300c9280c068860341c006d140c1f480d0306501c54402c0c09400080e00302c0300040000745410001350712036008a48940c05903410030014800340a480d641030b40184400781c0290240241c500c00001d15005200c41c00b017030503402d240a5030315107181109003c140c810341000d60b056442c4c160000c0c0141e40f2100001984a6074040400c81010b5880780c081e070920500360001504242800c0421041c84540d05c140001082400800c000c0905441c034400c0012026010341c075040e420070481c00100040366003440d80c2000b00100b0040c68140d0321307100c101c100b000ca68018400841c0101d00d034240d259051040842d40003c4102d68122807808007520b01d003426050183d5485410046140717020300d84141505a0098409002107640360951034102040008610844129105038100a41c080065004210b0071400382d0310b82284d500c180422a4130110521 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630799145 1250 630797895 630797927
    0x100804060f060e190e06060607020d150203070503011d190c0e060705011e090f0311211308150402040e030c010f02030a2d110706020d050f07110d 64
    0xa010040b802041c2021007500401801d0054149420081c002c130050301c00710f00d003d030020f030880c0c1c04124184d20f540046a00d0280c0c102c42d600d048050324900030315049940d213140c6465a10220400800035000b400460503604035020307446100d07220120203010341000303c0d41c065070300d02c000050b250300c0049900702c802188414200400c40c044083c0118000da00b10040c103803181c0c0e4445c0b070075130340b40e00d10303c000d040c0940d28070101400296050707114a100141400d0009040005882c08002013260a0000f18042d00a4403000002024404a4038130390380c01c030102d24104201c3d41c250010384840c0001d6554590203440b50075100c26580d540802c0001c22a00c021003038030780002c000c0c29601c0312003845210126042254010f8072414154104812a2032410012500704014210030071008034810500f45c511080c0c0300041448040501c0d0740740103001e944030040600c0e0004c078080e030440340300713800480c420030700001040b031a40c0c0c890201f21504009610102801d41001000e00981c510032030a84480c002c4c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630800395 1250 630799145 630799151
    0x22a07090e210a18030519230a06050c070f0807020604150503011d010b1e040b070308010510141204031b030309051e070e0603070302060c060f06100804060f 69
    0x1581c488a40c0d007440c0610b02c040981c0740010340104064006010700700d11008116651042811561419914039540da2a40e000604000f03076101009600b0540500c44882c041c4201d4540080e0071141d96a02c4000e0b500322800c90401000070341c0c910350071064a1100b60400090320526035583c0302d149007036114140c26a0042800c00020618100c4108054015040ca0380d0b4a980ca40c9413687c80d183c0c1a20080604244078100c1c80100f0441c401d500907a440007048030181c1e48201052800c074909407095034003420100001260103c01c0c103070001e960300d0403100183c850b040302c0400d00c241141c107080c40b0758100c00d00e88418003a0920a0540b032a845034041c3c880d040034217950101c4440101c10500d0000c04400080c0c60307c6099082080510600d101c105552a01d0340c000c0c078240031150744401180c040c10240c10445000035120340c0d01044800001e540107002c6030341c1c442d40815802d40324030301250104440d0b0112004140b05080100d05003100d24a0751380d440750507444039a1181c0240448020300c0c1010b5072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630801645 1250 630800395 630800413
    0xe0c0a031b0f120b01061409010807032a120c020316080f0f0705010c390b07020312101406030a09020901081e15060f1210022a07090e 59
    0x80c10030350010781800520201c2c0d0f1030301481c01038100101604460204151031071040b48021014099a10414090074500c54513030b01c03100c08070000c0c01c9101c650043c6820b40c1d4040c01d440340c8801c0ca2a407082e8220750341d003046410510010307019101600c84050044e8020006640d504400e1415400304612460040e8502205254240c0854200038003a001c0e00b1800101401040001d20540317811440c2802c000c84240300311401100c40c1c5210301c0c01c0d00c043c50044200301e5091242c7e03007100901c03258048058121030900e0240255203410110380600c0c00410080424841e0b602031400004072401c02103814807449005040c0007594001418101405e0303101d060303480050392075102c0710380609554002801310040507100c84502101104200816401140d520b0071446040400c00354095816140300c808141418082034001c0f60800006506005103400524203c03d135070001d00d44141d141003002503101c03101725800b824080100c52605168010350040083c0c04240d00801c030364000c0c4009aa14101e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630802895 1250 630801645 630801659
    0x909030a0302071b06031506031808030901090b0c0405090112330c1107050d0b0c03060f0a08060f16170a0e1f050c0703090303030902031c050d0e0c0a031b 68
    0xf0150001d10209484809615000587c0c0790088020501403805001070b107020720780307140030310802d000c040d120300b40001c0010300c01c600c01d411600e272140c0e005102c500d0328a00080c5441e103d070840d0103028403514600c800000d01c0c17402d0ba805020034035040350040e54603c000148540d481002c0c0c20f1014048410074505c2441c40d80203104c0e0340d48400c071544032440507201f5030f000f1a003080f4282d00090701c03400e12066110040340204511903408090642d41540e00e440e40c100003108481c50030541584400300c1d03080855540f0300450514051205047d001840d501c8142d0292450a070040b0094001f030140d00d03100c1140e2091a02203038001c4511040098034400f202d5005080041c1d04801810342c403001001214420018487c03d40d01207804946641480d00c0c84d5002002d9406074030001e02015202c4201c002075650a00c21203140c40c01040d800c05c40d000030910042c00b180c11520074428118502030900c0680030300414107100c2c0d903d00426400c1c010341955141c9e0130080f440101040c0300030758000045a10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630804145 1250 630802895 630802943
    0xc090f060203030702100e070603050c0d05010f36050712061d010b0f070213111308010b03010603020a18090b0a2007050307080c0102090301050718050909030a030207 73
    0x50403a6901a59403840d00e01d001a24213900b03000880111440c2a0400c0802580403c2c040107442e440d02d0b0100d07590b100d40c00c03001818011400f113407041d1407030710000040f94907031703000400200c44012003d003040203900700482c01c00d0174003807140d10390702c0030b40c8030306640c1c0d40d1002d500080c3d03c04030900305107048545102444040314031a8124000045070000c4808540c49007110780c500404628400c64540116928440402c2c064180c2c000e00640d84105844c0102002c0d030451010030058045040c0c44090480c83c160f035030002445250f006528040c00c14010342010b003d0081a43d40180000e00070340d2030101e44202e243d01c0302019108543d55110340c28001042d00b0440b50240280710300c0410196000b103101114040341c222520490f88042182c41d0002d44040140da158681014186499204541d18540640710b003221a0382d1551900c410080a5500400c40c80000c2481e200c42c409000d89902c1030081075003055039440c4141c0c1c024400348401501c640c005044451066084511800001d0140d90311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630805395 1250 630804145 630804149
    0x70312150f1a07123e070510080622020403060f0e120d1401030506390306041b081f0e01030206070f050a11090709061d030f0a030e12120d0c090f 64
    0x40410600341c81444440d0682d405c0540190402c042c0645a00d041c0c000f82c000f0030802000001d1100b0080003d8056481071049000100e03611112030140e04106950340c000d603c2070108440084c030b040009000314020741f04200c81c00c0c0801c4000d00080c03058810501039500107030060111161190942c0c007501c0c0448a020740203500c03d200400307640c03c0c44d51b0420841c40341243c8003e100509006440c070b01e540703e0711000342c5019119083c19030b65103907440884d028000f9884412400c020600c0e48850407a40706891601c1441c2d03001d21044280b40e0320311584c2c0501074522036920024450301c01400580780c008002c0c40147e12441c503503042ca10895480e0740c101800c1c40b506440e03941030076110301010b05080380002d900000a01d4426405070522901424bc1e5040d0703520003941100b03a881c0c605542c1c800300145951044600220f60f821402840c0040c843e2454000003401400b4100060000880001d01d80340d006003080e02c51810321809503080c000820151203440b0070040b10f002e001841000210f20440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630806645 1250 630805395 630805457
    0x603070b13090507031803031107080301062d020705090a0b0a0e0f0604020703140c3c03071208151008060f0a03080f070312150f1a0712 60
    0x71440749004107603822108020f00c02028581803c0074032124090b682e0f00d42d00c1c01d03a8941000900103c1c1b1404129045c00303250360061031017200000105140e60010b445503028281e512a0b00010f00e103080e07011140d46021006100507a000b44c07001e001340d00c0c202d021281d0010002d0380c00503103140d00d0350000f40900d200da48045103030000d900c14003010940b021251a8020710641e82945800c14983c0c2c000e03c41304141d205021121400704041130751343c5052022044030804401158410b0440124086003980801c2076500410802030980e0040c406c04002d5416843e04006900008442140140d40e0010002c01d0388200154008010240780d07600509031180e103402d41d48280080c030b071940511090030004d051052140c062180d0030400a9001c9040f501c280c08101d1800340c503211540740664000c0300d101800300c070460074070a0aa0366800c0340c1942400b100c4100c1d503c00038a0766143c00d282814045280402c0c00440100048804562020041c4110034214540004410415200341400d81c01c081c10b880 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630807895 1250 630806645 630806677
    0xe13080322080a0e18060609060a030f090c0501091a040506030403050706021204060b1210180204051e070f02030a0e27010306060f050102101a060a0507061a180603070b 74
    0x507135030804e194401d40804450022080500f0004002080d40c00350403c9548210400164038945d103200b074001c0c10042040035828400f8001030b20301800c6140c030701d00a007030009161180c0003030340748540701c03450ba080c40090011902d81402e0006000260340010405c0c4d043c0700c0c0c100304040000e0307020702c01855400c11203000c40009060600d0120250b03041c110000e0f00c030312800441051182c50101c8c513160000010100012000030001c4046035000d0324440c003950103440e010411220500a84500c034440c0f02001b242c2000da0380d1b208041e5485031501610380010380c0140440409035008485000503903038000d040c0381c0502c694071251000a41c0042c01c2da51080c4400c001042009154050031307026044803820050014240b0000035603844290480020240d22642a280e0004812441054004000e07002d180e45540c20b20003d400b66020903c2214400d2400356012940d0025401407407419030020300d520794542d1250140700301c2050103482c0c158180a030901c000381c43c4452000506220b10118858 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630809145 1250 630807895 630807917
    0x1209081204090605010c050606010c02011b05010f0b0103090b04030503040606150c1407050d032303071106060d0201050406120b060c0a0c0b1204020d030c0b040c0e13080322080a 78
    0x8509a44082d808203042c40885012280014402315046034414000e203881800710145000485a2015a95200541d03801c030051070303000c3c01019007001c1043ca00007203041c0f082080c00e800442c210703120200d024007040498000b090000c0e22407001540c0003402032502203203041e04c41541254555485803d40003003801d883c1d105003000303038220107e45900800805010100d04d0a00840d044c940011001030070030020a0341c0c082c4070300340d50303107595a40710100303c1c40c1e500c81ca403904000d04070b00c24900d02e002c803520510000404038030340081608581c5a040e598182002d18140c400da84c00d40039649180e0b41c054135100c0c41801511070310040d00701d2250400080c60036069609205440c601e03d500210000d010070000411440740c119402500140e06403014421900c2c00e08040b03400422540c00104104080c200b80f0090142805010303040d1100050200303c81d0b1220359440c0038011511030005e100400c144009140c00451500c80e000d0020780c001d0b11b4400044540c2c0c0c9000c01d500c100c02c2040420782c0c2e0480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630810395 1250 630809145 630809159
    0x70314010230070809061602030d02041401090b0a12020304080747070c030903060603030909050c09030d05090f120106093204020d0b1e09030f03041209081204 70
    0x28a43c110b207090038950031900f482840d0b19240c2000603d070400c85440c19100c0002c5910030030490700d1107110140d085480c5e503114052556004070f070415203400250250303c0401d2040300e9404452110a02c0e44592898180d0107800348069000103000b40c400300030900c42840880d8520303c0c0a00f0703820402400103080980c03010610010000c14004501d0750381040f481e41d01c0e06c00b51607800d80e0084114201600c0142c010714003290018600d400c028a040d0070140004201500020440162100d1400c14481c5903540802d11340d076401003810082d450303405002e400803800d000d60b004206030000500a14014019000460401001c40c244580c0310382d03503500c0401941c0c00703502c20888401c03540b46400041121624001018a00720000c0011004480d030109003156200007204001d29440380b000740d5285041d1403c0c9510a12907504a004000640c0c0091984a004011a4400020801c01c942503440325203c40000810080300364090000b001400b007812981042085031040220a03410758403800c041c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630811645 1250 630810395 630810487
    0x2060609071805131e02030412080c0702090613061410030b090c2d18030c220b04020c0601030314030106050406050c0109080c0a0b060d050703140102 66
    0x101c81003280040e640210040c0441e481011141e085078400c05a0780c4880d00300000344034052000001d8659141940e00e00310164010718801d0740110928a0300100c1d07100305a503600c0046405e4040e000d0204040001880c00034203140d008180603040c510305800c801c101d00d040b01c000c1e400c4110b0704e00c5518000f5045181174802e603900082146014041190908041a007118014110042d100e101040190444c802c1000414141048000c03808200380e00508052003076015016642c1d220034903070013440e024140020400b0300f546020701184030301e40e6514410349241d18100c5160301016213039a00841c032a43c42e40060081c0ca40300d140501019450342c54003a02c0404440081c3c0881001440100282c5402909a5003240c0041c104203a03540c5000d0f8900e4010904801e00401c0d0290200d4846460700d00010142103140c801c0c502903107151201d5081207881104204004d00396406144240009098100303290f000103400c40025041c60409041143d0300b1810040d107c2c0005001c02d04800b00289000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630812895 1250 630811645 630811651
    0x3060c1201050a0e0c220609030302060a050f010504090c0f091b0e0904020f03011506020601150302040f06051e0c011512050c0108100314250605030610090306020a02060609 76
    0x4520000b03d84c0f03411008164500014419911202c011419031700300080f00c2d10b8031188a00d1200d482000549408014000d001e01b40410380052280c200041d50840192048501810a50030211003580c031b0705040002a0030070700c800700c5280d42a408000b2b440c003440c3c80c1c1d850150074101000300d68491304146000401d5910107a110400c9194a5980100c0d00d50403105074202c3d4050f55801000040c1d040400e024101781104200c070600c1619000071065408940c0740d0680d101d0042280008118900c1202a400365004105545c0002c0b01c0400c41240940000c0c04c008811110f040c00c9a000311711107002a401008180d00f43c2d9465910841c0c1440c221031410016020550b1b12880c100380648500755901c4030110885d05103d094400b0460010f840604a8025a840a00038002400303000c07030a911018000e80742c2c034100440000e15050030400a4034801500c2481d569030381150303501e030108509108030f107003c0310034082d0014021020842c0c0d40020107000c2c809400600c550708091050040b0ba034001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630814145 1250 630812895 630812899
    0xf060e1609140405100815060109050f06190912030c02011202040b19110f01090204050c191d042a08220203150405060103141c030905010b03060c120105 67
    0xd04007400005200000014009420f80b0001900e0390741c3c0707010288400f0190403043c1e0511400c29001060141a4440307031040b80203913a80500682d807041407140a500c0c42400e40d607c14400e000d10321101d0014040c4c0762001d5030500e4040d06a80d62840d510001c42000b181c1900010803990855007556080100e0300700306024203604600d45403811340800303501e020b004401c07156403600164904416119183c8207603907607180c0054442e01500c00b91030310f000f04145030041703000d10304004c0012115404201618195090612001080d00041604881c0d410103541515580741600c03030150090703200c2d48980000f546488500030301c85401030026214400d8580703104801c002c469020042c1e01010003030140e580301895140c200c16841c172440024200000108840d00d00220b1400700401d102000030524102c80c040c60205081a6848030b1941d20b6115240d90124080320350102004800e110354403240701f850080d000000d03032083d5040080d050003400d54004400c858085140d50100a186800380d00500003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630815395 1250 630814145 630814157
    0x708060105090f01030f020d0e100c080609040c030b0a0f05060a06020714041e0204050a08150609190e0c0f0d050c0d03090306060e04060f1a12010f060e16 68
    0x2210000a0140c4102c40145018a0f030141050101d130340207070018540100e200006649407203c2c80041b000030102001c42140d64030036400500480c070201d204805601134242d40e468032540d00ea405100c1c4807800508101d44010700341e14004082010b5864640c081c01d128130b000f0500e8101c00080000b600d50107000745124020960003048000e4000844404492a10801045801c2c02000182c010000304543e240d280220389003001ca030700d01175801007040d1901114403070001d588428019984440c820302c3c01560030240f90124845d0b1804104207070340010162500b4200e41640032519043d210f03002e0212000d5402100c2400503840e20341d0051000e100251024007081e81d060b2200b039510b00c5035401c41802280d94004032400e0520400c0940080c58001009002907581d810400801e2403041310306071742c1c1601d407000108140406004107194a25107500403211002440200300030081c0c8100d160880d59a80c0c003044074640e48a01500c1d00921003014104403501c1d0401906000b41a410480002c01071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630816645 1250 630815395 630815401
    0xf01050306060d1403090306040606030c150806090a240510110715020a02120309030c01030e0c0108091c020601080c0a08100203060103090f0803101505160501020717120708 76
    0x40e0800c1c050050303508060804d00c00121405958114030404502d587c15005160030801848415082102100c1c460000c0c0064140e40300a19920079040340c03213000c00910300b407022401130f151071681c03c0e0304038201d01400100980300302c00200d0040c1100070b42803d80200b08408000b24074190254100c500742e203041811303200c4007521456407030745441c1c00340c00c0c008103002911420b414802c21440c00e080d507016003004803410144049030f50740d07005504680d1185c850070401d00300b03a5120b405220f0341002283c0c02840c0c0c1843c0c081c010344d81300100178072142c402e100d07100b40c898143c81c804110100c0034081d07402502165060444450401d0080c80c03405014004007401000300820000e0601e03403107205d07010010b03101d454240040303000e8203060388050300f41c10500d840e14050204e110000d5000b468405000b0b00c101e55140c0401c03030600e60251b06200803801c28008545c100400122100403d4403500c001480c00d4180e58411240650b06950403a5120001c5a0b02029403000e00b1a1038020200b070800e141030345 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630817895 1250 630816645 630816649
    0x1e0606020708100e0703080a050c16121103010b1e0f06281202040321020c150d020f1201050913020312161a0601020d03020f0919080106030b0f0105030606 68
    0x5a43c0034000e6155902295802c403402841140080c6034040940d580d41c9038540f0000b40660031080302c13150b01d4014081e001c850394825411607812608d40302c0121001e10f004d034840d03d416aa6001589406540300c0c041000d03140d9519a00c14040c40505100c071191103050024011f00010012285025030070420900c90b1060402034609114100000d4901e205004440c0c00c595001d04401c641c000107001240c04801c000001116804480c6003c000000c2040c0c116412a560300b07042c5841e6070048600f00304007810f00b508030003d204102880c0400740c0390035024050323040580c2c0401851094480034a0040c0810724102041c0c40d0402451040044181350b40d800094686610744a5500552800209040181c807503c00b00710341c50b900012600f643d1440c0818001d1510005c441250042c042c0b045240d16040c081e00c243c5543c1d800f01050306051100d0030b8240540815106c044500c0410100c00c0080e141c03400740a9040518410242060942421807580c41002c5040c3c001034842c0c2c0040041011079 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630819145 1250 630817895 630817903
    0x1a03010515091012030201020717131401050c030705031306080f13020411031806060d05070e1012081e040503251a031e06031b0103020d1e0606020708 66
    0x4041c21201074000f07488440b1040751046150380300000300c0a41303030650300078544c043d4060700c0418061740c20414122050710304280f0520980d1080c03004100a41001e2003800c07191313008180c40201c181000740c03501308400f0519155412020084640d54000107405002c00c5241001d600105900d052007100390401001004008200405041c0c4080340a1090025540e85d42c0080481641d825200c603500e08100101c245031030020308003002c0030b00c140400300e0014141404810800754210f40a051443d0824201c40c48126002c1d0004000c1480c890f000304800d202001c070010164412070140e56902d061010009020820490044218038103000c01c00c4a506e0225064940c4408404220b19044a440c506a800b0116030070451034000589175151840490070000e601503414000c098082031141c402004036060100c8546415401180660311640071848040b25100014100542458102950002200c224143c840c0d900d4000e80401c060700d4929202c1d400c00b401491015204482c280079003aa66 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 630820395 1250 630819145 630819181
    0x61b020d0c0303020f030c1e03090d031a0a06091701090206040308090a0801020d0b010e0301050915040c091b11010e030406050706020d020a050c16080706121503061a030105 76
    0xa1141c1c030030303034801094425811601c66100588996449080120303190190703411030070a15210368000c5803000d0031104250252031080c604040280038030303072440504a002e400b084d0719002600400e1080f004030f9548910001c0d001d0666595080403042c90b010210900c0c10308170708054844d0b45007800071800360b02c1c0e82085800f52034111200343da40b6200c41c0c0105460750b44a40c003005c0746520126007012140342a03001102510401d82e2030f903e410544008060032214183c40d4080c0350b61101184460720000309410a5100b4003910b01500410703500c031091415665081d800c07402d040e0802d1020001e00381c0100002001100100003040340d848144000707542c034411409244203205000c5074810800c55680c045546041145000b99100c0d0620040a0015049081d0441c800e014642c8401c042c2c40c0300c06424402c84810100070b054444c540384054540c0f21090a80701c00080e203035144495841c118602840007580305800000e581e6075419440310ba010380c011041c501c644d04000602c804031884981d0200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 630821645 1250 630820395 630820397
    0x301180b060c0f0c010905010e0a0311061b0618030a0914060702030f0705042a1214090a0203070602072603070219290d090c05060412061b020d 63
    0x55140d10040c00242140100007614a0358030a0841c01d4510303030000b084600c00008207032140c40c10240c40c0c000545aa000c800705544e04417041da8070400108028641840004401400d0a0f14103800c42e01070440400e44181030395101c2d4001c109004400b06070745209050308001601942c14441442c100030007611152203540812540c21403055015034502c02194449a4020211203030900008000da48524035486210b1149160002100d4101c00112807a0001c40e884a003600721070b58508030a5031072404a6860b010f000c0d40c1e4141c0c2e0342070005c0c00813000c0d00030300569004081013001031042526001c2207401100442d0443c14003005184a500421105c41d01c000544070b52035180c554020b891402520f1010790300c00c070502d200402c2c024291102c1030948845e03000d0064092120a24041246440c0920100701001080032604061855004907241071160307180178180d40da45d6002518540190b0001c1507400d15242c1c05208010451041181c0802d400010b00441c009041c4040c0d140c0450401c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 630822895 1250 630821645 630821651
    0x10c0201030518010e07050f1f030c0c17030a0c0504060e010804020301021e0c01060b040b16050a02131410030308010e100503062401090e24030a0503130b030118 71
    0x100403d88a18681401c14605002042090300c041503055445107544039150048440107800100c5003440064045480c841c0040c40c00030703096010040707000301000c421100c01c000c10040c0f03000001e0654284500c3d8914100c2103142c0380e0130b01d05410001c03103002a50300c0d001d10408001c00c22160b07070080c2c00030341203070030034242078403503680320b00100b40648118084c0d0710030f04000490707407102e84c1d00d460080d02030190840000c004180d2a111444410f00c500d02070019698020702000700304460307010f09080d03618410019114000c00e01d5011407290141c1c00780c400016912601c0c1000c0b030001148031140e00106000c451700c0780c0d5107103440180034408180a040c0e481081c0a000602c802c448103600e10007800007604540c0907241110100149a02605003001858825905111190312610f5060f06840009a4403212a1100119900c0aa6240d000d0000b518000d4400b044c00b030f5024000030b001c0d030b4003580186031303696000012002003c1564019188940003440180403202102d411040c015400201c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 630824145 1250 630822895 630822901
    0x120309021827062a0a08010e07052505010e060702010b01110a0b06010e010c0f241a01050c19080d0e120a20060a061701020403110603100b0d2009010c02010305 70
    0x313942c060201c82130101000200040b03000c012035208034618104d4400c1c804140c51034480c60b0007151a8401c520414250071402000702400102c2c1c100120b440b54401c40000075900f00d146081402d01504072900300260359541d1791104a541c0150740500041181ca002d010306140d00c0d03803131041055000d800d050400c4051901c0ca001e51340104003030190300360084950500304a003450709150a0400020100601d4125003650340c8082540c00350b15040e01c007901251710100205001118581c001023190140c42c460380c00c083c02c0c050401c40290446c0b83c003800e1026943c2ca04a076054040d00d0701c01c070008074281d101d42040900800e0307241c01d80e00007000700e241034508a00e400301800b0300700300e42c807064001d24041d41d002d00c40d140f42a80e00010413256000c20303800304030400ca8401400c038000c51101a203801e064040030a07052030038200840c0d2204038000102c22164440b021001300341c02020240094032384e15030f04e050a42103002c005c084c0d881000c4100d203103000c080000081009905d0710f0028145a141c1703001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 630825395 1250 630824145 630824191
    0x91a0904050736051e040b01150801030201230d11030406060506070804091a1005030709080d05160606080307050a0b010806280f1a04110307020a12030902182706 71
    0x403500c41c01600d0f108245e0b103040908140c001c2400a2184000044000c000c0442c114011003129048a030143c44450400c0404030029030140301c0307940710a00390442004080070203c4184100c0080c207405e918160b46900d8035140080888800350801d520504040c80b4103400901c140c02100d0a4070b807113100c0070891843c03034540c405000c6850300c05541d011000840901d44607622402541c410300c025502c542c0f02584d128807150b02c1c1c880c00d06405000400411640034080346030b101038100c2c0c600c1110000b4030b0302d50b680c00c090f040d1303001381d036049440b230308032024400c140034251600d1400f6140007005440582095407101200318541e04e205508c2d01251941c04072500f103030b5030140909190000c0b0078409030b032045081c400700e00700d90b400d02c1c1d100b54a0310b14607034000304045056034030401c03280d00200801001900d4400100c04401c0c045020141c885001c0c90050f1a13000b48089280c0c00322001044a00f0500c8242104407840182800225140410030b040f2810003d4417542102105810a5190441d065 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 630826645 1250 630825395 630825421
    0x1206060715020a0c0b06191401050c010510060909050601080a0902060c1006080d03020c1534080703020a0c0305090a050604080307020108130309091a090405073605 72
    0x1e040744920300c040303803d90b403071034120780a25031640c400e4070042d260380d40382010000c010050381c04403a8444203010051000700381510410303441d200f0505046091911503a241401d442007204c1d08603030003024100c10003465130001410341c05801140818007a1f8030348040004c14012008244400c1191100669029901c8020403118009251010380b032120b5102044200503203a20300c95800c0500c5681c101c41d54052003442541c0114544902510301804140e0981c0c0840d1800b40c081e40c020703119203d5000d5001851824103800144504821000030010740d0701a0011328020004030606004121031800c85500c007000444040d454100702d504d90000f0004210080c44a4200b59001030300010045500080000940a0b451007607071a078403590b4030f108000c105006141c9000b400700f44c18002c140840001c54100f0001c90030005601c1d2500c0440c1030000f07080c004240d400707540f950001101030100d610321840400c00489004050443d0134480f1031485480740c0301c110305c204040e0342c0d900411000c11000e5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 630827895 1250 630826645 630826673
    0x10c140408210f030a05010f3c180b01200309010c080910050d1104061d0f06120703150b0403031202070c0b03010e010e0f0a05040f060516020c0612060607 68
    0xfa08651a80b6119010100424080c0070b06003110301c8407030000907000c0c103099142c09190711564042804d0040c010298078a1076070030200d101c0c20b9000090100709441e52603038401c3e04450b10301000c00ea1001000001d46041c400030b0b0440b01c015210800c00030840390000464401c0e90702840c02000c1950309041007a400d008042c0b81039031002a000204840c298020040c0c07460842e91f150820001c4109075a244951040d40701e003502040981030043e00c40c0c11005000c072040c800181c00c00300400350789000104540e02502d030000c082c1c0140000e06c81040d901d4400d034040346490480215909007030013000c2c106800340f80320042c10018050078100c05142280c05952030998040340c0350003060740320100e00846400074014040141c06510001a900e440b044200703009001d1315803203242e1034503000f0000015003401041a5102c0a035401580d00140c0311388205889030044201c940c090b40403554000b800c0890f40d00070140700344400c1c009c004100e42c0c400603598110200301e8810741c4d2202686070000b00c40d4240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 630829145 1250 630827895 630827917
    0x6040f060803130b0a020c10110703031707080408030c07050106030803041a090304060e040902220c0306060203190f020a0b09030a0f0201021912060f08010c14040821 73
    0x900141880c00007028040040c500407a440300d444d200c940110842c01242000d00c0168014414503020307040504180c00c107003240f440c0032050652030703249091400f40f0780d41c4101c00103406030010884403c1c40d071803416002082072801c042c0310704017074881e408140006028075200d0200010040c082040940c03207040110b51084409407a0700d000c1c03d002c461400c0d103600d00f4104044860020343e96010200c01c0b1029114603441e501c409003070006c28000141440030040f0780206a0001fa06810440029801001600801d02045100c1072150050590300d1907400308095500500c4041340021980035102a00341c1c8a150a9050030110301040303150443c180000360610010f0824041540c401000811001c0500d4982880d01c0003c02422401c0340704001003c0c0180c0c909001c0245954814290181042c1c2040c00200e911501d855000c0030550312f59008010907035641d50480c1d507d44d082100344611a12040f41107060501d4219401d4580440350710840760180d41083c400400040c007829200c3ea2000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 630830395 1250 630829145 630829151
    0x70c03030e03130e04061d060c030c1b010c0f0f1706010c0f1b06080702030a140d020409020702330a1b0b060306010801150b130503010504033203040b06040f 69
    0x500e103c0943c2c40141a00d080c0c4400d820300f9881047d00c00c0c0500e0118803a1240c50061000d5600c01040c2075440d04081c0c5100d000440402481010852044081294440c40070000400e480c0d0481d02801100d000c038001d00900c85003c90299020f90401c02e100a088020341c0000300c1d6640714401214680e42543c0010140b00c01c4411079814021803160341ca080301c89080d050341c005030f1909001e032199002140c00d000164001c02c042c4400600c40c94601c005013103071a041505083d65440e07600b09a8015400c420511603020444200b9072401041d0100c000c40043c1d03011100009144000c003020080e81c6403002031200006803d4821485054100f4455000002c83c851451640c40d01c0141c9071015201c2074824450321001107016901172150f20013035107154052720900da181c40b03503402854100c8c090000140000030350028480c0c600f0301070148190700c03c2d0758000e404194941c0c010b41c44401031410286c51510384090500002640c02160f0b08a030300404080c2c2181c5c1c030040010054032a021045040f142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 630831645 1250 630830395 630830399
    0x51309020406110607080c03071214070c170f0403021e040f0e010e06100909110a08030301081905070302132307030e0615240c07030303060905070c03030e0313 70
    0x540003c00c005005046820b0b50b105440f80d080440e1200b5041e180219000000c2003c95000f60080c0f415203e04140024049208400c1d100c1620358000c040b9090030208030340980010801007100c014202000b82c1014850920341a20542c03121801a4000240a054000b5010084000c0c081c80790165880c010014040070081314031080c007414680c1158401d0750b080158044121102007032040c032035032404114180c01441c00e401c1354003a1045030025141c10811960700b8200ba140c2440782805400148002d694a5140075a124a4442800300c180d09500c0c400981900041c0003140c49400c0380d4040b90181c0c4203182c142c24100080840c0d03071440003281c42101c600032045000002080c81500700e92002c1180448807895962115401c880040756081c1038022031070949000c2107000d5030f4030344078084070a00c26200c1c24480d200703600035900b2180c0c41d400240100201941405844003078018003406015500709100b002c0c0c41040c3e0280300905040d100c1c000c0c62480c140c100150b400140e40305000d00f501d55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 630832895 1250 630831645 630831647
    0x610111c1704110a080303041a060109050607050303060a08031908180d1706040204080316050c06070f152703110706051809100e0907090e0609010c090b0703051309020406 75
    0x4080f2210b1107024602214000848071004001d13644200d40204d08008001d110350030884031540018480340c10704c404030402142e60b803900409407604522410065584c0d061400c20004107000380d510803c10340d0300820040d162103111101035510001c0c00d080c40b0086885120035582450b038402400f018521072038580d003180507403120440007018000e5481402c0740d01e810302400243c0c8901e0040ea6400d510401c8a856100c0f078038110310380b1841c041c6040d1020b0302d40200024265a022202c25580c031640e0000076801e10034081a04e01c906591301c00100100103503107405560585101c00340c4500c2028184c685018140180003014148111000b500c102071f031600c401410ba80c000c070701a413200040b0000c00c06000d0a003020040d010303200d414202840c003494142c087c0c08000c03008181c030a090040140003e103c9101d030048440d420f83c03110140a8620b003c00c40d450850354041c3c0081c0801070381000400078003424070210362003130f40c0501d42159612408200382c0110700540c0c0c000c02000c0d00c0050001051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 630834145 1250 630832895 630832913
    0x6060d0e24070906030608191e0b0702010e01020a08070c15050106050a03060b18061c1104180c0f0c240b1003090308010b030402040b0a030501050610111c1704 70
    0x20b44215100d402031562110812021121940580b060719070003110b4940b5911406801e110a031407050542c05420301401721503141030a511441220801d07424070a0020043d0203001d00d160032202d8900031401d181340c2010042840070007426010620000118120611009121032a00180c1c03004040c09196510000284207911010250000a14207840071a901e02154121041d0f40000240c0d0085440f400c1c0402104c1e80c00040e1720000250b8158030080488198060030342130240903503001e03840c0c03881c040e8980038006600c41c0c50082585402002000950844a2090062441e02d440c1100f06085e14006213644800b20645e0050149120848041c182d1504840c07448131003641e145040001c0306a0a038151020403d005000c41d50a10040c0704035020355000e55401750008001040500c40c40010034450205030b04266206e944401c1008a075090041e02c1d0800c0711a0351412030080c00110b00640d4882c03e100f020103281510501d4070b005064816100c0040764840c02c442e59100d4240b520f000c804d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 630835395 1250 630834145 630834151
    0x10e060108070501090503150601020703200103050c03090a120e030a0606080d08040b060409060603060c0e1f0203090f0307051c02090f0609041101021002071a0c0306060d0e24 77
    0x503101d000d00215403540319203044806c0f41e0010b4000d00110007050031060007010000c2c0300a0443c401c000002000ca030381d120447c5010100b40385004091a0b04200042c252040204147c048600030018010086800100d06140c150030850700d400c0203400701011102004030460b9a0307810312071040080c09105032030740190200c03002e8108403a80000102030540322294112005040a01560001100e906103500040c0d11188a101c0015540f030b140d03907560046822000003000001e03000004480c05040604d09601d4040700f0345954910012825002542c0e4410101014040e0460a00d000c00b1510f0805c0309201078600188007031490302c0c0c507240d060b45400d07001c0c0303090b03205505c180c010071540c100c84400d0f40e0044402a05c00f10b030a41d96500e501b08003004080d039a5045206100c100c41c2050264030107004000d21031402020041e01a0560300c120301809841c85030a510f0400c240400c41d0b5410b012101003955030324012032080e1120206a051650b203441010071108000302c2001810702556105d0305c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 630836645 1250 630835395 630835409
    0x70201060b0c060f0f060102070e090c04020f0a080901023f010b0d14011d0718080a1b120b040c0302060409021b070e1f170a0c0e070905150c010e0601 66
    0x515a4070490950305c640002e481c414056000b0010a2040c81c07e055800340e0b01035052011038031452a81804981203074000359841400310004150301218031362003400b0740c0d00240410020f50515010020404102d20341030307450800e4007907810481107034030681605243c182d2044030007042c0541e9142c1034086240d00044903101c11920b41605002c140e2001108181a21045500c0d0b1900c03118043c3d40c89500d81d00a0900014480580041c001d10352003000c214018201d48009424a80c102d858803000c10104881d0646030495450800c0c8901680910085211900420903003c10f4a4604091440c4002c0e0f8001079000308001401140400058008010052080115100301066070070000d03219045402400c040441810201d119010203030316400e241840c90441c83e0006580d41c0341e0707070344140c5001140843c0f9007044211f4401d000b0a90034130001085903480c0c0b6021881d041000030144046030240380d1061a2540350301c5291804641644d50141c0d800b0002c02c03480b001c0f905a1940c0783c100748946e030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 630837895 1250 630836645 630836671
    0x1e030e160303021228021e0708160803160201050c0a03021b09101404060e0114010807020304180c050d02070b01170d12020703020a050a03030f0609061805070201060b0c06 75
    0x100034680ca04d046400d5403010740c40c20801010702000342c1d6205000d6250400440c4204903080e8001c0c10040080180e045143c80100a240d14242d4001e0605c001c1e01000694101029001c00003203002008654880101100c9410340300301d43d200680d56406030a00315401c0d4031408001e1000c2540009400301084612038040d01049940300401280c601c1c00c4034420b444035110481001080c000c0c3c41c03854207101006202041c01d07900c0301c21890007001c1c03d901c98000001606407495481d6080303000a07400222070b1010703518160809442002402c28002c404c800c15648a1210424910840695201180c050025583c0343c4141c10180d078240d0003070284054a044090104100701000501c0c0d00f0b60030340c140c8a0366069090341c002e1000a400c80c3d4415429402140440030001d80280400e440700c0b0300c01d40340042d4206c9103030900e4044a0032a00452002c40c507040c024030556580b110f1002e00d80328a490040b500d41c0d0b0740c1d2002c0b405840194041c410103400420417190181000c14054820a01c0107910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 630839145 1250 630837895 630837913
    0x3020f3702010509101e051008030d050a1505030a03050906070b0c18101202030a06030503071203050604050c0d1e050c0d1a060708030702192f011e030e16030302 71
    0xd40110b0300351045801b9521007003039888120140e41d40101da807202c03020b02020300050b030700d002050956000f90754104800b0f0340c0e0b20810040e1804d5100300090542820880340c1e03c94185808203969136015800982405070110702d5060170341c0d40104680c0066405022480c140c10070b00010000c58000b41c03080c0000030705111441c820b6007091103030300e10584001e40d19004080b00c0300c0e013040025800504850042c5840e0342c808000305100b04024040f00b0311810000501c1d810800c00102101c9015100c240303d503091406214814606405842054250400c0028416007200c00c00c0e03030b51000803060001d11400c04003080301c2090500c0c098410746440710001d0103903e82c402141c54204240c00741250744500b0a1003880b0116210308043d6600581c0d40c01210f120394503181800c00f040e000907500311869105011154840612000417502e90f800500c901080f904440c000078050717034a64900c28114401180c00500c00910981240b2500c4a41c0740a40300340c28501103082141c510f00780016005440340c2c800b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 630840395 1250 630839145 630839173
    0x612231e0d140a0c03021e03120108030316053604061406070f0305070b2503090b060415030b040b16050307021c140c06060f0103020f3702010509 64
    0x1102800d2000c002c2207107080207a40301074450f0803026209800318401c00104800e0346078518104000502c0350360042d51503048c41c003da000b492078145c00580c56030300144140708000758500110042c04802d8141640c41e0f41d00106211085507130020740000801c51034049095411071006a41d0744d6110035503080c0031140d141d0850952802c441d00140b9000341c0c3c1001200c0108028030208c5110754400c0c5456440c0c4240c0b0384540c50202001c0c0c4240c0280c50441050411542c0e070100c5441c00c5041a0406002000d240c4d04d0700480303404002d0106024030340f90070281780c64050300301c8150040c4d5031043d03c0b4240b40c20542405940190201c5980d21600c8146040064441c02101920301c226110350003003480c08106d040341c010b468103030740b00e480c02d1010003120340d1100c40f25540540740d851405801082d00c1d2a003030081100e840311103d42c4605052040000598020f844012034040300d05000329118040c2c2c1380038809200d803403401d0104040d405a4407190301c00d1035042d0402405070361200c0c1295116441c20761 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 630841645 1250 630840395 630840407
    0xa060c1e020a1101021606090906090c0807030b040e0a0609150908031305210a18300b0708090c01090e1620010213090612231e0d 57
    0xc040003580c0300512400c0000c14995104500c24018416240c9504600c034041c59811120303008400881c08090301486854030510030b92005007110300061060108024019202c4600981040101500c0e0309040c200c07519680c1204200082150444440c0010307410031200134030384200105c0e20762603400051900b1281600415483d40d0300410a01e140d900c500c00c100c0007807040d030799044a00340609500400b5104190b000c140c6c0303143ca140d90140c0d4914440c08000c0000f0a15091107440180c8160306204442d41c800c0b8031910404080400359020305114950701d00c400602600601803000002041052640940817601171000312040741c81302c60311440103542465440c000e2000c01c00e00a80010b000a16058060805403018100b80005009803440f9008020980142e1516070790001150070110b00811101c100400709644104807060030250018001d04815401030f2840d204e0221381628840c00c1501c0074152044030b8221000581d0221400d1060445910b00e611240208100c031001180900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 630842895 1250 630841645 630841697
    0xb1906090b09010906050703020f01050c071214030106120b090c04031a0f07081e010b181507080903030f19110c0a090c0c0501020f0408070816150e030a060c 69
    0x103104c0f80e40003805d0402c21229070700600c00c2034046220b440c1282010030000c1c81000d0090708030070100740d40c4a0705420803140c3c00284105813002c010701d400c2105080d0403900300f0769041d03481c2c0e8600040c10200000c8141c028001d040f0a050b8080800c07420700c1040030006000b0000c981c404e030f46c080400c03908030022030303022142250000c040c3c0400d0000a80e461340f081410715440b02d6490a8820fa02e01c041c0b250615400098200741c0002d24006031001200e060490080c41c10503085420000a004244190400307001d0010002c180c440d0200b02c0c030582d942c050007a10a00181a412180c41c0c0285500703480c400c0c241c14220101052000f030808442071404610800d641201030030310040c0d07520b410b00c23000041c0300d0744604c0c01c100490700800c000011003c0c001401d03d0f01d45030f15901d44036410800c3d000d0074482d080d0302030552030740489990910022000c180c0d8086400c481d000c01d1160a0102c800c2d10342883c00b00c5c1d071f540e05000b0903d44004001080c0e1024401081a81d211131041c0007030300800f101c81c2104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 630844145 1250 630842895 630842897
    0x307030e12030409110c0303090c0910050a0302090c040b130f0f03020105032a07061a0102030c06041716140705040b18090a050106080d0f020303070806130b1906090b0901 75
    0x200f00601104645401032110464903031104c1e0b1400500141140c2950400c2e649004a50030001510b8010b1808445181d000080d44560070400c0f89041c00084e0201a1840024060a600c40000e8145002c150580e00201300803400b4070303a60307502480c0c04007001c0100c3c001e1210a1600c0365002c03a01d607030007501c10410350354181c55051a43d190034941c43c842c00d20080c094408000c0340c503600c0f209100384002804a00303204650110301214565640d0401c400c240301598115441444400095040043c074903410941055602d81e03440c001c101151b0f1140b1404d020304400100706505c0000300092650020f86021034a8103584440ba02c81e010081a50000d408080d4030800302205440150500080c417900800d03200103c903401c000c03e941d40b60075180350b41c0c0700c0f26068118298010210ba000504034603050f080c1d1015524610304035102038030002000c3c0029000c2c200684040540d00e40a81c4540803e200c001c4c0301c1000170901c694100c0c616803203401410000303182e810000505032104810380303001880c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 630845395 1250 630844145 630844147
    0x8060a06050d0b0604060e03071403060f15030303042d1502160218090d0315090b21032203080a0c0804150905040b011718030c030301080307030e1203 66
    0x3500034212080c1e00003001c110708281d66000f9001d00c41d0354a800910060803a500d40e0048030541c4000c044c1490026032000d10700d001d0a201020780b9030b50104000780d00806ea440c03040784603201e50607000d054403001c03d020754162200100348002e0003501482c1c546e0b80343c0c1c00b441211003104000c00042c074220303105c900240801c8214140300030040254010740129002ca00b140104d54260f50001703034442c82007440c0f007022540c0200621821000034001ea42205005060901c8080032441f2610960714503407141c1640199220448401c0750340d590440310b00703400d40010f0a022030070780207425602c0340d104800d4070b00d03242100301d40d40c600f40c08580c44220489402c00142402c00c00084000d5940c0107c00204850080b006c00c80410344c1c3c04941c44000b1a041075690f40d40c0c110f4200014403044420402c0f0803814800e072442030803011400001c0040d23020b1850310350b0007503203501ea81ea503c3c603500070703a0101125800080004207000200001070410709000356038501038002111709201b889042c0503842c04c01500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630846645 1250 630845395 630845399
    0x715080a0b100e310605010e0a0b04030f020a091d06150901141f020d02060c03040506070e010e03010906140c0c1c14070f150c2c0904030804030201050708060a 70
    0x1d81800a0465608020340b111141e100c080545031311442c1912060b1030075a40c0d900305000d2541e02c0400130f4241d200a50b00c00d20700c1c03400d0041000f85400f951100400c903605000d080011900c5101c404001480452002d110180b5034103e100d010b21105002c0c4036080c411000060045004480580410a000b03401556540d0801d000d060301c1201d910403c6401c604841d40030350080c0101900c0110070619503024007116074503464000c1c10014007505202c1c1040303051017800003003a008111250080a54100311038200001d00060f95604044244154154030300210b05d000c0c0136460304204003041144841d09a642e459103004402030003400300c2904140d00c65505800c0101103a20040c40b00502400c0013455494402d030300b404541c0c800f807000c585040f500300c403040c100000d905041e055068a440c3c24011032602d48030052611202400044080f0135988102c000d91607540c00d0803806c2c01e00030303183c000249410709000d048881c1c1a14101c00661900340040c092502c1050424021030700203082d100118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 630847895 1250 630846645 630846649
    0x2090901020f0a0e0a0e2e060f030507210b03010b060f070b070e032407090506220801060806071b1e03170703200309060609090715080a0b100e 63
    0x25190510560015215880401c4000c55025281c0c42847c020003841c40c0d008400618541c0d00302da00f80c0f01160000604c400740480780c0c2242100904101c03921380022103607030303e80301141c11800310240003410300d0203455074143d400ca01c1d4218040d5220305034004c1c05004e0070780d010f000c09849041b009034510310090100c600010301e9600455080074079460a001d1046001d4002402c0c428407011041c81c0407005007180c0d5981d40403c0d02268400454100444214945400300f10140b14045c00c5425070b05c45223104807000094002c004015050260003000002d440d040d4550343c0300d2068590314046002c41410a0208018a071580c1146611607000084085868070040b20103201000840600101e490103800340301007100a180b103123091396804100340b10142802c0c00c1201907554a04080d5404004020f11210300050854000d803042c0c8014038140d6451040c9410620640c02446202850b0b000301a01c0d6940b2500302030003500e000d1806c20200c045102004901c007411400d46010071042c040e21540742c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 630849145 1250 630847895 630847907
    0x612150d0c08070e06060906210c03010608280e031605060402040b060711010e1810030c0b071112070f1d0f040b06040509250312020312010306180f060902090901020f0a 74
    0x3088016a407915000e000f42d27204200b6801218200345480011004204490b44080e0594020885000c0743d062020b50301c0680160205551070f410015803560341c0503842820070400c03540f03801882c4407080700700c200e00d241c015160705003554180c0c8940c0c12701110032040d113850000c8400082d401035404401540d5580151020440d5208190307110090340181e01034100e402c0001d80c450364104140c0a0464110700c0d1400d001c008581140104840078446080010030450f0366090070201103d00c100f260540d0a06031b0301c3d240a9400070f00385843c240c40001824080030402400f825001400104140d8480141008400d000c6802400c50281d240104c1c0341030916900060300541000242c1c1c44240580305013510070007941207120b0084404003410828000d1042c001c1e0400c014910195140c2500814095003d00043c04042c004a55900f00f040703040386010004d00410f0b910040c0e0108500c03103810a00c004010699003a0b01849403680003400340d550610854126420410025051a0441c0713030072038203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 630850395 1250 630849145 630849157
    0x1505010f120f140f0a0e1906091403040308181e100e030105010f030b060904030801060810240e0909060a02070804051f09060e0612150d0c08070e06060906 68
    0x109039603540c0c4092600c0d00300452603200c1c1107900004c0d440c50411110b107034110381220700884001e4008291200526003105100c507111754000340003241e02d611600300890050500c082c0c1e5800d80c80700040c00410080340c48050413408218640c402d02918940003030045001d56294448842d245c0c00e080643c20789401502c80b1030002851404890040f00c2d0804282141c20030703040105007000024040080000c0741daa965072144c01a101c50449003002c4ea80904200707810b00900c02885500070000300c41441c0d2027408030080c1090001c5040400100344032019005940461800003180c040e0241050f08028001d5030240c001a4001c0865030744003030400d030094021003c01c40e50b480c03080100003596540c1040c1407104194a490740308540345050000341c24045c599000006202c50301d202c64050340e03100010741d04101c000c4d010b091043d40e180000040445000e240315648910b80074400c4003480501700b000d80980d10040102c515050f19000080016101205c0c1198040c0041007403021a041c07200281c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 630851645 1250 630850395 630850421
    0x302060403030e0c04060609141905010e150d092a0b0309010609090606090b0d1110030f1e110f070f02010207051c1101050a020c040506011407061505010f12 69
    0xc440481c8030300180075031b03600c1e51010380060300d40041030107003803007003007040642c80c0c0102d8054203480b4995204080aa40c40c0c401c0c0350512000d103501081c0c3e520340200c030003100703007648020325038a4050240010050803e40c3c400e4a0a0b4455141e820400080101113101e048400c09991340a5140c022182d805520080040d4495521500006042609801500358051241e840460a5400c1c8000d1804a90b42184210f1183d048410044040380e070708100f440003c0c20941d854080d08542410685c042c01d1581184640a450001c0c0807440103440b14201000f00e05032201404501c140f400c0903003080c0030392920201d40034410040c030340004541244081c110341c4180141e5040a9542340040c00e03011500b940061140300d00341100c41007004010280a540c0d0090a180e410710100c0c1034000d43d6151107910150080d5619804a03440da8055101c02004038040e010243c0c1d9210186043c0000c2c001e034201045250300300202c007040c3ca41c0108485082c0160903034400c000f0006111b035610142c407101d07403c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 630852895 1250 630851645 630851653
    0x15010207051002010b03061536070c020f0907200f010c0c050c0901060e010c1104020406030f150b03040b0a0e0a03170f101401021c080916030302060403030e 69
    0x10381da84070699400e000311100d4000280c0f110591080c07504000004102107881c20303046030802410f80d80c1009050600440300240f60041da42d10f46502083c0d075488a90342d0101911500300401c01d54030601080c01d00703102f078520401054142c01804400d03441a90410007284910005845040c40c41100c80e05c020360700c4003100d54034003185940070708403000c04802c500003a400c160504203010040101080e8180c0a0b60344111542c0740a40040c02100c41007146410042c0d0750034514184600c044610703203400c200600841d036840d0394110140c0146084815100d03118145501e03610451082d240450450b04418980f07407869a075903480120301c01005060140c50b580d90013a840c5001420807414051a10a80740c125410b000c0074004605102e0041041480407500300070494a19040c1e50035208540350955030034100000180143c0c10540c0c040c00d60800ca014204004441170391002c070450094031800d050302c144450300800b1044c001110300000c5c000d82c0c0310034040b0300000d100303910030b17a44e82813000251 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 630854145 1250 630852895 630852899
    0x31c0c1d040b0d0c060f020d090e07050a0e150901120b0d1704081c03050f0601020c060c0705031002070c06050c1902040902030f0604120509150d0b0909101d0615010207 74
    0x341c415050690859400900c1d032903001044544c040111101c10810b600700b43d5102440e004180c00c02b01c0c001046802005008107005080c1d9019880009000d88020305001a503242c0c0c0240403160341200743c2d40d5000400e800108600c81d2100d100300c00b40c0c10310107049000080181d445200305800540d0400051700000c00000134902030a000c4040c0114210081d0075000170141801820768101401c5420140461824401c0c281c0c2c00066401750654142c0f0420f440e02540c036402401c01e03115a00058160040c01100088030380d4907801007000750320685202c1201d5443d00012100750141c400030030f00c0341c4c3c8499504610111446840c80704940300a00c04504e40c1d02d1a40400c1c280010510842115840001880100078000c04884004081032500e98241110100051701c180d2046010b4001c203c0c00250301030182d401d030341215486580c0903141c0140c50a01a00450341c4414400b102d2403003034600300740351891904101155030061800001017006d074844500c02c1003503088400106055109950380 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 630855395 1250 630854145 630854153
    0xf0a08061605070507080102120c0a020d1112131e031a13060c0203070b2518050402031801140f0f060d05010c0905010306120308040b0a060305031c0c1d040b0d 70
    0x40317401030080303c40096103a100704024002d10002c050b09030f001c5200d083c0640000c4179400210b82510100b10714105040030740c0d44030002c8c1450340141202202c1c6a00142903c0082d0760601c9a408440d550004041c10740d1040b0903020580045010003414a01d250303030140b040b9a2202c21050f0020042d01d407140e0034100310380c0d40004407a11480d00c40090707000070502c20244107400d017246500c000c1c0101070008499038084c1c003140801c80c01d00c4041c1800b000901c82c0760744000080e0400081c00d0046c1c021541c03070501400c0080d402011301492400e940c02e1164a100b5400d4520b041d43c080c1d515190400f8071074442c07070034100c0300c030710700800b0300e40c00c6902c1710411408242c09001d052540805526114040390404c00014243c0b2242d404c41180300700c0c0040c1100010303500c100080e9000c0d4020201d8456501d5000401010749110341c40540b0030301c03000c1101407045a1007440c81440d400700d80c1c1c4c20086032220718825a44c01641918ad0034802011140040150070320b07420804100500501c1d0005180440c1d0b6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 630856645 1250 630855395 630855403
    0xf13080105101412120708041203092c130201050c0a080910020f0a0326090304060f0c050718021209240f060d230105060f0a080616050705 61
    0x40c1e91a100b0350940820401907080c18110b41c6034410544001d459150025402c66941807042d2078110a04070000d445002c0c8646a0191000b80c0710304082c0080e0030005080090a11500d4004c81410140c8001228400241c0602c0f074051101405107150465840440407014400116000d07030500c41c0810407180c48800038481c1c0c80d1918403031700606844414600070700081c04480290350f401c7d9030001013207250a074000542010f00e0360b41450403681d9862141d8486801c1e09070131900d20250403800c824064211008800b070070607104103a5030004922180481215a42c0760584041d109401821092203658035072000e41c0c541c00008a00585800c0e5403841880000100b2507410103150008400d0008030540101000480b01c00f1103401e800034106040741e00403425001c7c108500c41d100d610012002c024541c241b848035200a64070b1400015002d0381542d0182004a402501c5041c950000305030354500aa00342058480340c1000380f007680d50b201003410018400c8000c91052190038005800001c030204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 630857895 1250 630856645 630856651
    0x506010e0402042a0e040b030a0b040f08030108010509010b040b060a0f180308091503190906060506032a0a02120c16170d090321030f05070c0201090b0f0f13080105 72
    0x14000c0000001c0d04d850082049030054a100d00c15410b014844d040340d41c001500c80921900024034803419211491306d091500d0f02038000604071000400000b50b002c2042d4030040c41800200000e0041c900700b0020032040b1140181203a038880002d01011a91078440d140d0082310822906140c045441c1d00040842e100359a40c0c812a24030307500080c01d8505060214103605113002844045065003040e41c0b800c0a4403aa9900800906a0310b00c00c0d041840b055070804c000800c4041d02d45a642d051089001d40a5481d00108500900403d40070000076140c40e802c49248800990190419114220740014694802e8007804a140b040c0801c030440380e414010104002c04800030404038104086503220b003008039034600301c0c1c2481084071007000031480d50f140140088810503a60300f0010500c0809500600cec9400c4c80540c1d02c3d1604003000820354020740910b030454003d88481031055038400c02c0d0103d500c034401c0c401803038040500030b4000112400002c1e21070501da0942c0c101005854407115804c580f411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 630859145 1250 630857895 630857951
    0xa0210201b031507140a0e0411031609180b1809030726300c03070912120f050705010203040305031510140306040e120409050705070506010e040204 65
    0x80000500740d441c1c2000401c050002560b002c0900e4500404054031800c03010003455000c000000d0480c0845119166408041703034024410805403202c6541e25030280c00445640b9002c0c510812210b840c140030380380b407004541060142140c0c880203000c2000103031511200d50b9800041e40805030703d004501e03040507807051600704011611407401d414412039800042d40e043d1b101194000c1140003d428500444450501c580c1d110a0340251031b080c00e840c0030340400b00645190a26030300348551030109100450003008603541c4c49031010745803143d800c00218080f1005125286074058410b40c503014005808403c8110b04100f4142035040c1c59650036640202c504030000780002007002944c00d041c41200c2c1e10b40c44196000389400c11200c03000b5120486481a06ea1a84004400984603580e642c001155554080050324070300c4003a425081c070b00b41c11a0007020b0b071081c102800100c40903c81c20a03912540d8000c80103241030307481c05002c0c0e8083d2401410990700242c9500311100400c414450000480500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 630860395 1250 630859145 630859183
    0x7030f0501020a030506011701051e1c03110c010903120302120405060a06063006050303041d0a0e030a111606020a030212180f0f0a030b15030a021020 66
    0x203c4001011920000c0c8080c0c140310982d0711110303c07943e21101e50780c1503910540c0c10000b542c9030408403040b150b01c8103009503480309160000c0078080000c149000038442c072079150140302516840c1c4580e00e5a111072901400a01c0100e000c101142e40d0440e4503d8400540c280145400b1140c0c0340700b80f00c040304407800d0340e803588140c06005a0310118460400140041d2a2013002c00103061800c1c143c2c1c02c8202500c90415a030008040c003c440d8540c4580001c14005007120740d1565900039400b115600d4800660061140600062410b007460041c0c480b00ca071007902444c905001c01c0d0050701c900c020320000c10228411142c080c41072070003542c190750162600e6002851a004285002413074000c091072092681581071120151144011206a52208046030244200201500400c690449001e80716074441e13000c1100000303002007131050030b014803071080c142c026015402c400c0c540e5a42460200075040780144c1c1444000700c0c410503040801d03001c1603060b0030b140116483c41d10310305880d900c0746902c0181 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 630861645 1250 630860395 630860407
    0x11181302030f010e0a0204140f0103060503030a0f03060b090d12030b0d0f021e03071512050f0f07090501020309090415090b150103060e0c130306020f04030c06032c07030f050102 78
    0x1c3c21044c080d40f000d903e103000e503d4030313013001c2a40300c60701500f0758030500076450561070031010385c001c0d0008005440c0241c1201d84507506000010100740500300c10801080c0f624402240c01d40082c41105c080203009401960703001c0b030542e40c5802e96416420000c00f0199540d5103050030340d8440300c0b803d440314018050507032808050b00400101c4641c081e141d400c2c10070210850100f42c0c4002c200041200d000c0ca070a48403241c41c20800769803150035008109019480c042c00c00621203009506e02d4080c19100c8040007840c3c1d114103095032001000d0080c275016920600c840740311480e000c40d01c1c5074080c1c41210613507610882d41e0b0001c1c065a000c61411038201c0e0041e4200310000188040ca080304450910b010b01681e40303010901d40120001400c0905800400200d02e0f4080b9205a103100055500031403c40d46e400b482b5021041581040c0401c888012604d2400595140b00e40201c20081000e40280c0282103009691208030380c0900484021a005000703000010032040c1c400001510700501c00941e40341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 630862895 1250 630861645 630861659
    0x5061b0303070906030e0c0a0524130602240f060a09090506090622020402250b091618200c070512010606020601030803070207031e02040c0311181302030f01 69
    0xb81306c11014005a03030114062000c25550400e6840c01c42d0030542d05102c0b107255003058903284220b0030300c200040e10000602d1041180c1d982c41801c046030b200d42c1c03c1d41e50951031440e490401c0101029424540303125080840c0080300c002110581210005040c4810745548803914000d5490104007a1456040381c010800509020320152703034010b80e00700c4040d15002c4407402110400348042d1019008030b07404640c103800c051100785600815404405110b84920a03403415116440c01110088054000c0c10459944c0014055100342981e075200c2002d0211900c0c4009100100034040c0b04178628089a4550961211801c1c020041030114102400c0510300789418001401100201c3c044543c0c5010307801c00400d0703408a1a1307410740e41d000413042d5494640d0741c0120701d82405a0005099505000c0610503000380c7e00c0c15440e6403a10980e01440030340c4520030240c00b02c84124004204208080050001c070040c603420b031212107c4001c00501284030108070309000c13600110b501e1040c0c4600c0b440140025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 630864145 1250 630862895 630862901
    0x1e17180405011203080408090909031903090f0b06030705060a03150510051e0702090a0603050607032c030705120c070f0812031504360c05061b030307090603 69
    0x609000c0d03805210a514203450441e19000c4030101031308000358080030800308041c800880e50300c5c00e001882008907080180c0c0301501d82e0700000c010500c04098850080400d4000c0c054104103541282d04814548803d8807100f02c9000020400d035454084c0f2480410103580300006800384820759a800503402d10655000c0100180700e8110f40e106020b10400b0b004110345c841c3c2100c198540d000c491804401d03001561030b01c80d004400000394170082c140104400102254001411031b4090340032506151100d460070380880d0003002907810102500440801000c05202c00b41c0e5100c17080c081102d01e0034885071619814002010491049501c000a449910740020070005000e80030701070800059500e4003805541d11090100c1d446603001c00400000e0030902000c4a1240c51030b0003901c02d0103000c0c40401c04c102982e00ca4040032615503182c031242e640d12a151550a60000c0c0e1150311100d078142003900300320b15134208500d119034540003405101c6001500b48041c0d8000d004945a901d03441d0304003003019040e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 630865395 1250 630864145 630864187
    0x412031e05190c050d0e060d020a02060a0f02030906270304290a02030418020c1b01031803050d0905160f0f1403031c02090a120c1d041e17 61
    0xc01c030f90a410300b00460b001086641d40c0040a0505000801c00c2a002c10317018000c1c0c4141840844c03010811081d115004520302e44174044c4003c041000300307240d050403002c90101340c400341619031050000914942c846d90713400b9000c4641084800f505c0c5070b8164484e203035a1042d006400c0f090110020210440644010800d0048405a0a5007080200c003002941ca0007944070300c141344069840141718034000360f81255040c0f0841b6003510417001d0012510821002d42d0001c3e5800070b442e107503d81c03108030a080c01072615aa407640e607482c13401e40030b49404c0d00a0100000d00f0b40d11401000c0e20000401c40c0c18002000416000704070160a600c0c0100c8030705000307441c4e0302034480e05401003111500c658020048854041080802d04000c01c20312541030002c0c001c40d030160380c00c00400940484e00d4001400c140140d68840d50614290303d448005002c594a01c245055071020542c00124000501503907902800101c550b0b5002d040c500706d6291400900b0710840301e218803880004908002c06401203203442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 630866645 1250 630865395 630865397
    0x4090c050f03151518070509130b06070b1008010606021c050a08010512070315020405190302030c0112140112020111120a031d0a03030c020f06010b0412031e0519 71
    0x50f51022035501c44102180207012200c00c05402c1e0302403000341d6131001000b50011401202d2101c0c0e1622107005001584008600e92089401d0401c07100c60110390300072100300c01d0014005a081c04026903401c000d00e00b000d00103800c040581003010840762000d22442c8024a820341c014030100c0c86480c540358a4140d96000002080001c012900c0788640124074203045850a440c928518490a402d45090011070340004282010f06150061510746d2900500182d8500312640581402c84484c50880c01c1b041e444002d4068010004054842d80182c89503144d0f104402404100703108810f003042c3c2110001d030041e41c000009503240d5425960312004e00303100c4900240c02441c4945008a280119009002e5035804064440d140c141c2d402c00807200440d074032005881140c030b401c07815160240203410b00085010041c41007501500c0150000114103040743c940112540c1f43c00d0500a10b008051719044007a403d02c03020340c0ba10030718440810241480450aa0307645911080795401e12025030b111100848 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 630867895 1250 630866645 630866653
    0x207140312010e060607020f03010207020405070f0e090f0708070516050d030b0303070c2d0803120f1009020d02040302180103060507030c050d020a0c0c0303110d050708070311030904090c050f03 85
    0xb06007511005d08072510150100c40f08c1c01480c07010000240a48503204000b034005040c0b20900134526080515030980c0b0209031192107000e46041309001c0d442d182224030fa0028400c1d0808100c1c1140190055500f09600c1e00e0118604031400503107043c034400041c01100c0603070240d21000b80072603140c0701d1070303032980c070100c01961034580180c4814103608081c2c0070340300481540880c03079418240c000010003007814840d1442525559143c100a40340c4e000780150236800c110302c46c0016090840c89806502c82e00c100205c40c400141442503a500070b401500500a40e16402c110100250380d99804000341603207010b115044542c1903190040603240c02811000c10325007040c0100115540102c25941d001003000b00c01a111540380b002111030b491903c102420988164002005043e804103044040c09000c4c1e046518105454104840c107124020024040590034000c40700007078840c14103044100e412204076420000b440e400541198100740080340e0003c01a0400c02071410903102c01c482e1000210064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 630869145 1250 630867895 630867901
    0x80a0b0907080a06050d05010b0f0406050102250906091e02030709181d061518040602031005060a020706020c06070c050d03020f01180218011a0c010207140312010e 72
    0x30500d2050301605000610070320b40d00240710544a940302e90010034004210202c115481e0602034000c00c0190051130240b240d04070351076064100360040d00215201030340240100000d15032050031044400000c2d410002100d01c0000d1010348500900014040ca001300040d8030608056044100310040110039039140103004209030a90090b13a208221560014540b4001c500784151b8001054642e140120410000100401404002541a208110101a0011451051381002901c9401c04002540c4003c26800180000d500390060754100b0300695101c00e406840f4000940207800400070400142d103d480200301d09941013180408042c0e0543d8114074041a9449040b0400300a01415000d5002440503008051080240c1102141c00000070482e480e0444040d0381000410038040c0d100e00c151403c6602040340f494460380c1240c138019010500700d04c1c1c001030351195800c1880700103a25542030140b403004c40c0c00c108484d010111407902031a9585440794250000ca00181c001c44d4800440c3d00070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 630870395 1250 630869145 630869149
    0x60911031603150b03030d090b010608090304030f0210030e1f0f0b0d02060912330702151003020d060603031413060309081b07080c1203040306050c1612080a0b 70
    0x101c8080041d0075002c84c181c0c0d6150003103131452081c00042c0744040d240061010070301070060029810b80d40310350b440400603103c031903000f941e901840c003010f0185517900018500515008042c1141c1c042d860402060600c0b59099850a00b07800000c50b2441c8822104035075100000e9224400c064110703c0c40803c020b0740f280e00420941060994000d0203400000345158140d07840c80c06254000c02d01d0300455140c1c0343c038a441c50103154584400380201d010580c2d4160700c0c00e01034407a0140f01d40c2c016802810603110301510420b0050340500f01c180540400c0d1004005a122503a481c031407031340180d20110f071751495450000d0917414400c07401f0140c660b00341710192080c8102110181200d01d5860041707450042c5003442d010074410001240d8520061202c403089203000454440700b203a00b00429924032042100c14041f072030755801e03075105041c0c00070041400020820791240340c12440181203103003080320924480f207441c208000d05640000003900e0041c20103074003890362948251124424000c184200c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 630871645 1250 630870395 630870413
    0xe070501020d020a170702030a080c01020405010311030906041b21112e0e21060a0b0a030209090c030109051005010506040b03040803090a05102315100c060911031603 73
    0x5d101c2111700c0c400204002955010001202c0c0503400082c913070366482e503c060b058001e601c140b1805021030b0808814480f0344203ca01624416000071002c4c03d129520751341d90f200360a00c940c0d11002c545051440c04501d5607034550908011581c0841c400090309403a00300340000401a002880c030450001e1112903414491241c08000d003581d51160450303000c069503080e90b070f2a504085603500907800d4140c46548020184200400c24848010740340c0c43e4482d000c405c1c092b21287c05840d030304880e071000204014103245c584103900101035026203030000500c00011703003940e030151b0066171140e004c1c03414640d403044c1c03a114083c01460200d8040e85058501601c0c030600303010041c0b014000c400c010001401d60071007071242040d501d41c041c0a80701c01c20080c180f40001024108800c20015074003800c408130300032103448010300400c2c200c0c40c80300020080e00c00b081400c03d00142c4c0e1400304006142c21000040d614000d80006601c5400411000039a000506142c542d001c0c0d401045011007081c200042501f80d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 630872895 1250 630871645 630871673
    0x4060318051c0302270108070206011a0c0f0601060c0213020306031509011e1b020c0f0d02031e010207020117071211040b1c060f03050601270e070501020d020a 70
    0x550202c02002e00c04200303500901850f031495010300c19090b800b100c40010b071551161619400d03241c3d68420f44803900c040783e541200b402140854158040c1c0d607054203082c1d5014000504c020001c40e019080c420f0503003401d00e0000e0340800c01042150350902c085103000849142004503040c0c00714218580000003a40d80c12142d0000030000b011035010410303808081d0040c0d5080c1d1a40c4020a1140322140c0008000386142e1148080f202c081d50741100c3c0162002c10540640706c001031a4260005201d8100840842105400c03649132090f80e29400390170081c40c408a005450240005844444c2c6000145c48002c440c0f102d001214660380c104200d444e0012014400d0200c01000001d825600a0f2941e4840c0b0841c0c2220412001c0403c041d0102400240101078480a0800c2800340b142d441050941c1060b0b0f42c00001c1c2203400000050ac80700d02c10180920044240d01994080348c00d1408255040f2009914602c0e1a500200418000c95804029000c2e840819200810600d08180c8a00c11180440e13 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 630874145 1250 630872895 630872923
    0x1206060501110a30080a06082113050307030609050c10081302011101140402030c030c0d06020903030409060b181909090807020414010303081608181e030406031805 72
    0x719000d400440c80c1d542010813488490418042e090001001400c2014111440c8200b00d0a221010804100101b90303d0034940601841d12152038540b031920043da04507101101084c03184140c0003031346950401816009600031180000c1c0c141203410500c2c109040d0510260050741103e883c441055804203c040d8401c1c1081003481000300288012212400d68140d030501c95800c080301445903990b542001e6000d50f1080f411200c44000f030200b032544403480c4415441d849004500310402140c1160000c2c00796607801010389180503119110b510840b950b40d0400342c0105808203568041121044602080c80000c44034003100391400d0048040c5030455005914401e5201e541050420507a00113075100181d000304103005002d5130b014003505810007480b0a40019200401007070103807807035034407203a5036680d1030b6210704099030703400103280c2610001d88841354644a5920400c3c80b04400c000c0c4048100007181c0510b81d6a031a04000a040d1500c01d12040101402301c5c80c0100066000110203046c4995 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 630875395 1250 630874145 630874163
    0x50406121512060e0105190f060815070c0c090c03050702011514030a081603090b07080405090402011b14010b030c030c0f180a2009220e071206060501110a 68
    0x86183c000060140842e83c0c0f4855070809041c481d0040340c4001a20510700e010208010080e1002e100d28251a03042c890745509400001ca03421145101d0b029059000c109401e10344000002e43d5107100500010758440300e41107035241e409100c400d0707050140c1c680141d1584004d004071241006e0303400c0604502c0c410700c040c0c1c0d00203036001d51f6a6241400f0382901150048842030b160045031031050081c8240e240103c001904440d070100d051040e580940e02c44e540c124020b40e09290410b02405202d02c80500f040c2d0501c038142c0804d50b40c00c142c03460b994a1a510900c980d031100000f0402060a5501c0d0006480c800d0b08041140100394800041124031142d084418407078003441c4e6408070b0580c00c4904145040012504200b01c090802500000070910151540c0e004024000403103450600030368803401d9005038002d80344441141c203445120300c0c40b640401c000032603003688840743c4d01e0905554422120008100c8a62007440b10070f01c5920b000700003e082a82034040c0b041480e50312902d5281c0018000c0d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 630876645 1250 630875395 630875429
    0x30f0b0d11041e0e0304030c080d230c16080706090503061b0c030a020c130b0d020103050403051606061d010312050c100e010b0910050310020d090609030504061215 72
    0x5610860781d10030702070707000302084032190400f1304c41c0e1241e0090005442000c405500041c0c0c2050024850358207240950301c5000d07490b007126070142061181404814121130511084c01d8102c0180500b40e183d154008465041c149803071001401e040c1e09901841c00c0c40b148841c10230050b00c0114903558002942005203202d50810010115103005550509a0520000c40c048020680000321300c0400441211f0300302540c0b400d9481042541c00e4051700079041010b0b070200000550082d00500e800c075109003000350a010340e000e4071622034400d048060721801d849810070050002401d00c0c003124240410400c01c4158155110b918a51100310120802c000300068404441c990500200c0100b8591510134000c2803100d40a03103020f0101034404030b1092a125001c00d4840c1241075030318084602c090064448054400940030003500b10f459003402036901c5e018088006001440741c410041c0c429220f0035191030400e04010b10541c1042040c008061502c00b03011002d455900700141211068020304500b03407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 630877895 1250 630876645 630876671
    0x11120f2202031c0c0b060d020d030c02010905130234030f020c040510170f0c22020c03120a05040b360304140a150c08070c06030f0b0d1104 61
    0x200d01c00c10f0221000304071108940500d134091500c03156640039810b43c0c01180c031030004201079003881c540000e40c032000500c65540080d009100c41c0301001e005040c640781d0f00d03966a001c1040c80300c880903c2171031580d0004000903150303881e8a600e00d00031402c8544401021111071a0382400c81c5044015061041907001d40510510800c0400404040030b0014001820007141400b0403a10a020b8880040700360f500c05030380c800f40080c601c540c40c207a82c0c0040000c48900000e00803020a403140b100488003049500400241c0715000620012004000843d03989482c806903d2041340040c2c41c008505080c80e081c080461543d42d2820307001612106240d031045918800f440c110140083d00341000300420380001d810b00c1000c000f0f0300440b100c0c5c10b0f0a0f60450080420859040001c0c000cdc0d03240b4040c849656181580300e00e4941c05501d22500f01c5515180c81a01d452511034069881640040d40365208490340e00d040c0e000c0d14026580039074074014014220b0350b4130f401844104040900960b51400908214 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 630879145 1250 630877895 630877903
    0x10c0810090513060c200303270321010303080c0304050c0405070e030a1214040f121410020a12020304020603040f020303040909050303040512040f0909080d11120f220203 75
    0xd5070092040107101103000003d0035040151340102100b0b86e50021900010001008a82c800d41d040040034140088003200c0442e000a902402d44540c4024006003030000c5213800c02848a004840ca0a04250300d98a0028002d00008149070b014a006106210001d0b070000380c0b80d0300407181241d0200703882c1da17241c6084443e0b42e984070071f05505100300c40222050240350795404400070015a02d04203c070004040881c0244603a1048540391000007134104079407244c3e0480e05410600c1002103495402d100d0040314584035501112880b0b4a40c002000030b03110703400c00c4c0c080d0f01d120201c200030b504524042d00000c0150000a00191507400000009001c554062080b82c001d04400b4004216100030360400a5491304215021500e620864901c260080c0542c0c0641d001c0f2602104a01400c42c180304584010b0450b02c1b10440300507005119040f1042c1c00d50082e161f822141c60318103038079138070b0040e906141290090309a42d52310869000744203d240d501081c4440514926140481d40c0b4924800b00b458 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 630880395 1250 630879145 630879181
    0xd050a14070503131d0703050606091509090910060504110d050a11040603021c0926040b040e04020f010e0102120f040b040303260915091507020f010c08100905 70
    0xf0340d56020340c010407045c900c00c50556808103c0201130340e840c1d0b40c40b00141c08507102503503466400341050103007900d42d2409140203ca500c11030f400740c0b42406c209402040301507034240d07a1003130a500090a84200805a4480e840c01424100c0301804940c00d0031807045042e1042c0a40f02603169150380004060310800e40144610b5410015695611a1b99490042c020340001108000c068000c032902c55040c809806990b102c00e8014044000c4504480c00d0b90400811131040f080e042a8284000543c0d004004080c00082c40903021800702880d284c810018010509485641030101c0c1c0c280c6075a6590b80062402d031085420b222081d41c402c45c0034036800240c010f0f64815003840000140220402d54414103100b14801515155104d141f485801e840003c50304480308166540304104a244402490700c045800842c00826254a07002c61144200c11138400c82c1e00c0c00259002d5000c09100c040c0174031815584902500d852100d0381442c078001c4450407081d10035900380e16158004034008000090100384 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 630881645 1250 630880395 630880417
    0x503090c0a03060e070512061303110d080f1303080601031a03190b0c03240f040510030b01170c0d031701060305040c0e06090a05092d0d050a14070503 66
    0x1c1125034a14061000d401c00b0102505035018800d8001041e06140d01c0e04a1044a0100500340d075940e90046d5800001a02c541a8104114645007201704442402042e1900000e980d0b400e004d890400001c1144a02c0900210f2102d1102e01c005404241e20103009508000246004558807031020038410981d0116031990f50f05009613000c0000d00d4000c002c001517001d10651207203a581d0783e1a49200000d00048940c0b2041056280702d00207980d40d92000c3d100b15200003010600480c8541002c14122070085a0908185c0d1600d0000d0041c088607980c03942c014010880d458030107851b0580d00a8507182e072298414011010b0488138002c150103500f41286400c01d5814100c600e6a4070000103005c1d2406035030a403201c001070380703004c40c446070803e52680c80740b1409003803070903141c881c0b0020b8002000000d08240d004e0041082a5503180c0f0380c02001c00e100d0b210b541d5080c40c03018245c1c54440c00d00192900035804e202d02080351400c266001554600b1410002c011a5110705c1e140c02c0407821841038211100d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 630882895 1250 630881645 630881659
    0xa2f01060801140702070f090903030f1418030306220e06160318080304020904062007110a030201020705060d240602010b0406061e0302040515090306070207030c060503090c 76
    0x45040d207815400300b680ca0750a14210b0380706403500c0074240d0310760340ca90144070300282c01030100740140503940e040000300c01d00c6440c0020b0755401d030b01c0c01d00c411030384001603604826001d4402e01a601c5a04500c0b02030240c01080510b1460805d5000141e20144243c055081e12001881c000122041c943c002e02610000038191012031501c05002c6920044c2c8141c04000f00c0c0c60001d00c003012801c0034002e602e2107940300c00040c0c91a1a02d80070072000000003802142c0b41901c072000e0501000c440c40da0082d04608030603d03292202500e103407240003050341c0e0310502d000e812080b00800260b07a001072208121107051302c180f640e403c402c1e4030b4940a0020028413400442c081c4080304a0310b400003040c03804070745546d4003c22090f8084003c100a0703440511440d000600180d0300c000000001d2840d0340820b0020341801413a155851010030541c290880d00301208132404a070001c02c904003800303115401a054805060101e0443e07403811240c545a000741c8040110200008188520820955110904c02444c0e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 630884145 1250 630882895 630882899
    0x15040e0a060603021014040605030c090a060302091c020616021813023c0d0614060a0f1d040201030b2101110a050414061201090b03060c0a2f0106 64
    0x1c00080c240512049002d085990b0851000d6849a0740c0b0314544507601740c1703440c641443d00d101200c03150000350040c1d00604c4200050f8155641e00919000200315544000d40c540040504002207440d0710103c2811a513903208840d001a5a074004441200d411490071105281190003c2000840080d02d0340180003c42c030300340803210742e900c2e0102d0740c11403084504010881a88004820408540c44028540340c5000d6070b8080d02680e0401c1c030410b00201400404100b4040d0b10f408080d80c5407012030303008212081c4103102c03880c1002e8035050f000c0e2a110003480303145440c0601403200c08190301100341031800c00da030200302160312a8101800b130f010000c04c1d80c929040b143c001c400340001c1c042541d666130f41c0b0349001c056600c0c8150050b40c00c0004075880e6242810700c0c00300e2645a0703a44c00d44c58150300c010200300f0707110000a40c11f034860103003440728400030300b40031908181468820050100d41e10700600b4421541c080340c0c400e6114103220f0fc86429007621404007602d503628004c03000c0140405500301480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 630885395 1250 630884145 630884153
    0x319080412080c0607050903150406240f090b030d1101142401031e0f020d091203060515090d0507090e0a1707170c0c04090c05040f1415040e0a 63
    0x586440b0f015482134541ea502d54100a803a01c2c8201000c1c00c1d05500b0622256050008140400b648580603050116111018200d4880070100c0300c60000310180016500b844000f01100e1020040c0c1005070041008060b008002a40ca542d4000c04008221801c03411768524007081d00301558241040c0001070582c10200900304290026600c4e1852000140d01c0d8041a903100740110220442c0300150035035400181c508180c09401003007c2136182907000c1000f40000c403058402d8500c264090031200c25003808110005003540c400780d1082e0320500720015000300040303a010890f100103070106c2d001001c0c00c8503890850308144c07465110b0405280703170481c5840d4942c0c0206640b031049201e10f64a881800d17018250045a00445d0307005419490b00424000146800d20001c0c1005103400c002c4501c480704500c0004c00f91015510112800302ea442410486030400d802034411280c400c1500740001c0022100e203c50703402c0010040c5c245492120022000c540743e550200f4619900103041d10040708072424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 630886645 1250 630885395 630885397
    0x29183f040f09061d070f12090b04050c030d08100b091207180c080f06060c07080f07060905040203040201020d030c350c03090303010312120e07061805031908041208 72
    0x1300340e192088501d00c58900c1d200039012854860185030701c4488406014520440f044c6040e100f80c030754110f998841990100785282882441a4402ca000304001d0340521300341824045500003860600040406001e0350001003051082998846c5803030b240c0762081070380014070100c0b40c8031001006001d0420042002d400440a020390106401420702c60a4013210044400c1102103441020105032403011030040d15200c001801000f0400c1c0482c0c001d541c0700d2000c541400e41d000b142450580c450101013242c560084ca20768003c1504417011403c500e400c0c0c0000c0e41303401304040401d04245d910504240351074050361416009188031003c010000d12031100c139885d614201781000c0c20042c80000001c5208501500702e038865525013019604503480d40d503903800c0201010041500f40074200c20700d0300c00144d00d403154210010140c0010a1032a00d40000a092810700b040710b03000c1e00b48210014000f41d1000681c0348811644010301a10b070055a042000107405541c001003a081c05040d27003036040c031900c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 630887895 1250 630886645 630886649
    0xc07081c1518050901110a0f08070801031101080c041a070516120b1b070308040611040617130f0c060f0305100329183f040f0906 57
    0x3034401c00542a410060604404541c0b00c1c038141007405002008140c01181c00a036008103004001280e0392608100407605500003402d01c01c00100c40c9401420f0840c3e1009465421030344a0500b4543c0b0b50440c0c454201c2900c2c102d2005041c400e0f4100072035100f240b0002124001e151640b0041036030700a004591003503910946050fa22845400740e208002e00e042400542103601d1202c56040400156490301c449150040c802c10340c10151a6510300c2c0120000f004101c0b0760300c2580c60341a1841d161070584102c6070001400070040406010910500e600000c0400c0f1404010030b03e40e1496441c04040c88600c10385500040c40800c190051030100881c0f82d588105846003506c0b0894000350515080701200d00845110345480c500304000c1002c5800c0a40c000400c6210040142150710815510002071505556940040d48005000303618804180318030380000d00c0d02600340d180c119005101c00384da03903010049054058150007401d900714903260200c80c0102454100d80b031a503039980c07440b40000e103054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 630889145 1250 630887895 630887947
    0x105010b13080d08010314030c0109060b040507031b03020d09050f1f02160f02010e09040b060109090b0603010608180a1506050609010f14130311190e0103020105030c0708 75
    0x80725010940d290085141c1d00d40710340c40d0b134030202d10741c0c82c44d2160780c15045906444251800104501390754a6401c2c050082084c0c014031000c944206046c0a210480c1e100070211810140790400074000798012030f000380c0900040f0302e0096141d220070300c41c5100409050760000d02900c83d41030040c207505404680b070801e50f800c4c0c180c04004c0c14602c94081302a48600301070403800c21800b40c801000900c0a102c02e400040c018580303081d0381040c00001c2100d2a00a4405072004241d4908000c110741c2e006480102902101a00303201000e49140890801d02042c0500014032511200190007103441400450500c00344008980490100307061a500810680c00b141741040e042200100316810034004407000030b1410b039a607942c5100700c4031080700c0006440c0d17030203801440100410b501d05140c4030181005140500540c072501010a410400032040a5109038482c034a16501045980c41401c1c64a04481d020f00b0844d60702e55a644052809108150307008001e15004a01d5244803504210706040d41025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 630890395 1250 630889145 630889177
    0x90a020a0f180510080105090c040f06050904020603060409230106060507200a120305030a06051f08070203090a062106080c0402090a0b03011e0b030f01260105010b 72
    0x16207106071a100020302454075070000104111002014690002d41d000900407282d07880e040d1a40d082034203541c021b64004482d0340c400c5d50340e002c0c0c03845d0078032804c203580d800c1d910304001103860040442c03103c0314000e101a102e21404400603072903440301c1c2c004100fa10340c0b10a110282140300f84c00240e40810343c160309540c0f5860131070041b6965011f1400c0300c140340d13080001d845403280340d03404070301c00ca8002c42a02c540044410100042e0100b19510601c5858869220302da100d142c084580e40c12128130754440391040155100b8200201c4e011441d8042510036440e00515950310207800381e1440c4600041603070404a650800900035901c0003280c81e040001c0029200c010701400700040a0f00c40c18041d04007942c0141010481a140ca54010314032400050701401c14180d8444455840b600b090b8840301d19000300035200001082035600110140c85050303801d0b8294200300040d007245103c14014586a26000c03021000c500d0006140000d503c403c4600074011036865007900451508201d40380c0e0181c1131 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 630891645 1250 630890395 630890399
    0xc04030c0501021504140a02060309101808040e04240608060f3102030a05060106020d09030308040308041109070518010c050a02220e1f0b0a030311010605040203090a020a 75
    0x710110307130100251440702c101c54598039036486140c108030b905400910b5500c5502840d20040e01c030040a1449154080058400915420180403e80300495444d84185101840e0b42c400210b10205035010303a0900400c05005a0721890049000702c1c0d540c5210a142c00c203000180d161480d550066001c1e540c01c0010303144651a01c00f9800418002950301281040d004440090130750a0f07619a160300c080d103185442d12442c40c60300441d0400d480007106880341e400580050140b26010084000704000c58540620f00c1451518000c00744880508020100030004002c1010321203180b070030f0805404010800302c840d08012102900940c45100703030701043c0c0cc4012540e0b80e190f001d61084001650098003900c000c1e0190b07401c1108003000f940e0620103c0100e50310320741041d42d030340c821b2450403c0040c2c0280a2080c90310344d00c4060b000500c84020715103043c046800306c80d407102a1040112541802c1403030802241081c8140501015000150058408010040203410018040ba9814021340300711414503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 630892895 1250 630891645 630891647
    0x80709091202160510020a17030a0b10090306050a06090f0603021e090c070501020f0304060603030e04020f0d0f110d0f060b0901140310030c0608090f010509070501031a0402030c04030c0501 83
    0x286221040c1031603d40f03201082140741840d400c402504190792059034050b501d19900c10312900244d0a102803802408001c000451081d0300c2107240038001111000200850800d0080021441e4000100380d941c540002c2501480785802070030107002151010b00c098442c0341040001090300b0700c0309900c240e0f00310104030070740081050400503d0b035002c0e0a202c99030392514a990025803040e04200c80c159403c0245140c0b0352648405035008520404d070100f65203241d828010314210100300d216104610400000314207a40e040d00f1914400e01a040105d64500403000b00c0008140380c9040c28000800000d070f4002203145a401110101d035150800c11055880b58000e4103903001c0e0380480c2d03000c10410142d10030390b000f20030301656211108201c03501070f154a81d51a1607049510380d00480c04200144140150707032070144444103070069048020841450200000707aa81c550350b124441c1415500d0f601200c071800350142d0030a0800024105541c0d03810001d0800c03084e031b481407006542d980820400865a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 630894145 1250 630892895 630892903
    0x30325120c1112030906130902210106050909060418080d0b010810050a031b090f0c0206090a0b01050d0606080304080606120c0105041a070506010e071803021f020304080709091202 79
    0x800d03c200c00540c00c2001d00018000a070b807102c05180003943c02e00c41d0018125031503000901441c0d0540340b80000c8a20b00c400c021840c1201a00004203014060001600325154841c5440e03209030115008119040c810340255000e07060f03400f0103880e840d000910013101a500e6044a03000c4103080c1d0f16a5059503031000044203108440c090160322100200040000c18212000e80c40394043c62050300c0000c4da600c41d520000c9a003800c48210324241c641c441841001c0e01400016403140325003018140c0840d1f140e07035500e40010140074480c46804040450b174107000c03042c0d2011024045a40480f56140e48482100d55074140840320548104c00301a2030b0301c4404000301c0c100480210607160355042a042c0b20280c2200071003203280c02d60401081c400c1d540030030001c2154038000d20081c4d1400c00303d820310364402480d0300301c45584180048030310081000140c45036150312005607200304603003403007550b0700f40101e0075407195038004c10052140e4a0045545295640000c5c1280d205486c01c079a407103103040040e83c0b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 630895395 1250 630894145 630894169
    0x30a0227101b080a1b06062d0303080a0b04060f080606150306041d03160c0803040807030b0c0910050306010f17042004090b041b0302030325120c11 65
    0x1079802d0311031800000810310360250040e035031107050501a405808850f4610900e502d0340554440b038403218100078039214111418003403100c418210000c824504c2803070780654003902c001000c00c4071340ca000604840342c90b84100080d0900030002d1000e186c2d15061840d02c1780860160326a01d020702c0d00403507054500451940442c1c1d03209040310f030856441c80d0070440145500c10302581e00608000804207807a200380000c1030003a840703144801203d0300e1410240c00010301c6404c1080158010003082c00944400200c803000c03a64000583c40340c91782c0741c20420803d40135584c2e125402c0b507441002d0441b21034011000e90300c40e001c2a42e42c488241000300c01203a40d00981d641c21451108820041070200307102050200340901e10081c030030360629204e00407408070303240c403841a10b1184252007880200440d030703002d48448000040c0d0701040c55095400103030700ca21500080f10b00c810b025040c2e5108a44864072490300c0b0302c0d0088080700c0780110311030000e0842a120b82007101d0011040491b50f0070391401c001c01c0340c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 630896645 1250 630895395 630895427
    0x1303050c0925080601170108150106211e0606020d021b0a060f030e030c101406030304051c0209130302150c04090e01020408030c010b0a0623030a022710 67
    0x5000c104051094039200c0011340311070304002c0024900f00100018440306802403807490010324842d2240000d00c4410701c4180c1040013004a15207002200541a82003620707480001c005c00140d44898400c051000d20710300d080008200e007010400a2040d802040c42c200d07500c0d5580955035034060748608031442c041d9236100c440d84540c1e1481c0502c046c0344a80031450441e405800c000646445001300507103150013141c1c1811a9034040d80203a880c1303c40fa8002d517070151109070350000150510200094907030045001d0180039141c004200803a020403031004845d243c1e000b8100103c00c1c140011110900218281e060300036118420741e86942000e003011071403052034200003090400f400d00c2790183c090108421041c0c0c1c159028003010a0110701400184528901c0e48000a0101030000c00d111546280c3d60040081c441601034450041031148001a08012507071a480e03075a5440d002c44000a028003003d10400700321918806560050a00b040d80e02c038842110080302c0351121101c01c50b171124681007250303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 630897895 1250 630896645 630896701
    0x209060723062823042003011e020702030a0804080303010e01121127010803030708221b030803040312060b0f3c0d0b010c12141303050c09 61
    0xd5241209a48500c2c0301d4080128900c813005080304d04845a407801755004e5580b10340c0c42c0000d00480014204401d0003810130f40c000c0c85200c180340720030001d109008840300501c0d0b400240520031940c080c001072403e40d502c00740c3d25171165259140d040c3d4ae50024060801847c8550700081b5405065004071004603604c20150200b118054040c00004401000320310354886c01490f10140480c804210980644619802580c03a03150116006010f0080640080c10014a00b000414098048030f6011901c82d000300d100145415035042119001c4002d90000d800c0c4071010051000309035000e0500418950603840500150392590b06107280ca1040380201c0d130503600c0c108498001110744042d141d020b0064030000c44904c0c010202000c60b43c2e524000c101012440014910400043c00d04c61201740032002e10300700105130000d03074444020000051a050034441f030020718601d040034040848900034405852003601540d60704e00a980c850034040b20394820104500000c1c0890884600e0b220f02410900c2c3d48 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 630899145 1250 630897895 630897961
    0x105130915110c0a0b06130501080a030507150c032405011d0d02060c0a1b14010804111002010b131103010b03100812040e0708010305030d020906072306 67
    0x40510462840d000342e400d10401c0c0300f6a500b48403000300f09001d4600c1c00d010307180950800c0380140c41100a07400c3c42e80f9007001070181400009000311102c0e414117225944401e2400c04001e05c0f4052401c1c1c10b401410200512601d070b52540004014040441c01c84521200902060500a004d8000c40d40003136440d01000c4085110b60744d502c842428050300591010900e5008248194030a0300340b240340341c1c82181004104a0b084c075803140700400714019030072a00d0030b10b581e810007182c2140c400e604101c0c240d000f01d01881241c240203003245400404040e850126054007a01909101d24400d101d40302e8600480c15181d424010404d44d1450b4030480361070b680c20b00d071341100160006801ca80d40399218110200c0c00100030811048510480302109071107078078100c00c0101c001c0b0300401000c100102600108000361000054890801c02c194015840b0001d00c2c011422500030480068032117612240852201d039100f01c08018402107000581d007040c0d460b241c0108003141f01181b80d41c020725001c464 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630900395 1250 630899145 630899183
    0xb041d0c01030e030d1a0910030c08070b072d050705040c1407020607051507030f0f18030e01020c1f090602120d0f06090203090f0f0d0801031202070e040b01051309 72
    0x6144001c02c0c0d0381881b0142c00401e003c2004d5003400c07151500080c01b81c14080c0b00307200c111505080180303a014010084242000301c8804180103103c002020304121003040c00d02d20040402c101c40e0015030681c0d4080500301401c1c403136515045841180d000358603000c1c014015a220b414005046080034440e40e241c280d0715428000954455241600d85004600e15414038000d034900e06800b40f245580c000c54000103840d41d200445144181d00d0350400d14016407004079500242200320a1038040c00c3c645180c5030030b08010b134104011003d441d50700858a400481d840120091401081038040d690600013540710034003aa500c021030f0050700c11140060248901e108090b40140801d0169074101040195031041010181c2c0c001342c0e00034207243c0280e0a0702085c14400c0002902d645c0e514801002d040d06c07030380d80140820006020140c4900241c510700c2d800c107402001791340001c00b000c0d202c907022803030a41044d0200355000c4c001d4034803072400403002010300300041c09290300040e0000c102094500710030300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630901645 1250 630900395 630900401
    0x1218050a1b0308120603100204030f150f06030818010807020a1b15030209090a020406090b07061404080417071d092d10110f0703030b041d0c01030e030d 67
    0x70007204a8400d420044000346440015040140d0034145850507814044101418520340b0000d07000c1e0300d80305100400c00b21701d4130000000c01c43d4004408000300c034110b2034403901600030302400c0c80e4400e040210006c02c000213803008080c610b16251904420016440046903480340503140d000c01a030221903601c010540a143d0010303044102c1603142203499a480b022222034500e240a880829030100c0c441b81203003042d441d6140d014441e004110302d00360070460007602d6940503008815072104007066110401515502284541e0440901c42c541480c1c0751070f06194a41c010700842c009540d651642d1641003900103040c41c00d46a000e0840204103014110b004070a18004202030000c0c450b030940c01c000301c102c107c0c00e14040a6403804040e040c58a010341e4920304446141101038003803900d0080783c0940c8001066a00300710a104d100366445000b400c0880180c00d0003002154007900d81884005040710102d07000b05c1414005d403c3d07880c5a51403000540c1190019200401c850700104200703090800da030782c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630902895 1250 630901645 630901673
    0x60e090906012402010b0a0e0103120e060a14090a030c1d01050102030a050a02011407030c09061b0807020d060213090509060708160207230103051303020c09060f030a031218050a 78
    0x31000141c1ba00c5003000180d0194041e03071103c4a6404500010700078414480c514600c00b020500f0320f0321080018001003a240d00c40d02150130104052070001885188000088503a0b2160003400f45481c40c0d260b00340702040000500ca0540f800ca04408100c02c0c009120000604950058010b5803c003400c003441910142c0c815081701e41195620403c01141007280c41d000f500032011603400150345d050450024002081542044040c051100c6c00d0507010300c14030323101c00c80440d4000600c5484845a1011031030f1000344c0440204518000f00da20310070400c1c601110f40840c0c96140c414042915407424441e1108415121000000c1004002800c1011544142c0d4200d0b5541e10441d0502540c031001c617000354682c03140d000e04143c03480700306004940e818060ba680000881d481c0c684511220b0b035000e5500c5060b103c0046c0500c40550006800e80d031b07070340344c245603242020b402c0d500e5054003481c00400817200059201c8546150074024451003c2001044038001d5200d4001c0c80070070815120050342c0c0c2605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630904145 1250 630902895 630902897
    0xb150609040c03050a0b010309050c100e030604080a030c05040e041b170705040615020303150a1d070f052703010e0a0c0e060d111e0901060e0909060124 67
    0x400032103156496a1180080c040d510f07030750026041c00c00107001001d0301caa16488504140c01c0070040404070344042102d1041020443d00130b10740c0003a040d02901c200310300038840381e4180102810003082c000304070001d2084038066a07080082910012069030580994059411000e1107400001d0009281c25071200c0e046625524510300070769075181e1964580d11100b600503090f000f85c8400c01c000c0c14140030704009006c240e9000e811003080403500030355034000105440392400700c0c0c030499070442d03c94807281d101a001c5070f07401344a101210300004420030002d841d82c100040390058600c00d031601c80d1003916807140550101101c0031100d140762003079001807441002c3c3d0555031802140c0700d0110401c80000c0d100d204809084501b46402d54402e04038100401540c0221601c0e0302240014502002000195038112074103515020300c070042c0c0001c130310b145014a41020040300045019038014680a48031001114506c140c0d50717542c41210740700c1c036080c8211703610145249189003541551144100c010141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630905395 1250 630904145 630904147
    0x106091404061e0c03061805090c2e0503042003030a030b03070f170f1b010305070210050a0b03010b010311040303030b0d15061a130b1e03190605010206040b1506 71
    0xc80c46401c02c1350007507000301020075500e80c400c116041121820b46020040350030204151b140c400600c0f5214030010a00b58480c0a0100b40c09108008003d0008a8100107010080d0550340142010740603620540d0103890160080d14541194030b2054800c000050020b0b020b0b609111007003a064001d803098085a60b80740c002d03448007003200c4107165a21001020903503110a001c8049400c1c45080c40099810000d03e60048248210111241441b940c0b014100307182c0043e43eaa18108124201240202915040740c20942440880301c13841d040701c08000c00c102c00801080040b8001901120400400101582003d020810110b402a03000c4001c29502415005600700b00d90f8072010760074603004c1d0894507039540d02018031040761074003100f155040e6402401403070140bd9621080d1035500501c20329946c1400040c0404ca00c52580380b01c1115022402111a140e0904140b055181031540368404401c510705840020150300c00a60b10380981c1d004801d803001a02c4400400d03502101d821481504100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630906645 1250 630905395 630905441
    0x120315030109050c01091a27030618070b12010e0901230702010f06030206070f030302160311060702060403080a0c0e0a1e050f1018080a0b09010609140406 68
    0x40c00e0103071041403803080000d08040010000058401030141d0019100d4504111100740802c940400301c800700c208440021456070010317030311000046402000c042c2c01d07000e41d8082c0009115071907a0002d00580400513a2400390b107803001c6084a00800d10300c42e042007801c2c001001620b00340c411090700b001140001092140102821104104800d440c10041400c90307000c0220259081c03044029444030314105000702491900010700314054464043e040b41c00d45049202014041c2e0304444d10790201c50200c3d01c803030b0071504002e44607010041c101c000702e011342c0002420703080c03010920307500c65a070503220504031381c03541da010304018880c0703c1aa109200302180341e1241130b030394118124020002c014540311500c42d1104400c0c0b160002d80d00a17809140d145c2000c13403c035074075030102000d2044140742007480040c007042e502c0352400b2703603601255590213014901414801e07424121f521440366031009105441c0e82c0d041c040119000084805120700c6960040740004905170040301c1c07856001303400e100002d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630907895 1250 630906645 630906649
    0x403260306151b07030506040614040809041a090c09120a0203151b040b04051c080a1202040e011410020a12140c0106060801060e04020f03220f08130503060405120315 73
    0x842c0070b17041903915902072020003040194a008405020703400c200c800c1c00c1828140d4800095000e400f100f00e02c902d4841c00b00c030418544041030032115100003010314082e801d01600c20700c195400160341c14041c984ae2150480e107280001050050315501500034a404500107000d00300c0403002030590181e0020507100d50b03c0c40e400e00c202600103003e100f80415034503454002040340d0062450031a44c444160101400d02249a1206032250321086003860a8001d080c03007080402445960000e42c0000b4100b000424245130034181218522030640d5240a1103042500990f6030b0b000c10000240840f0310007881400e114030411590021110036401c490a025051213050b0941d00c10350070450025000800400c06268804607161a83d4404d82d411480c2500202c84040240301c0100458812104103c0b01a121559004021526030304054070444020305481c01130401e900102c510001400300701c0000ca054039000c42c03c140a0782d4454000c0c9444241104800540c1d00010030071400745104103500d820355 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630909145 1250 630907895 630907903
    0xf09070c080d05010905070f0f030515030118020316030c0504180605090a020901091103010b0906120a0501030218060d03081801090311060a1e200403260306151b 71
    0x3600d540c00110f1a581041454011100700408200420203111540c805032a08583c0407070241402c0e150114039a0398110b0070350016000d0005180d0103620304448800c0d8041e0b42800320700854400c4050f00c041880000080582003424040580360740307041e44003080249042e500c58605104140049100b01b0250344825044400482d0051041d805c644101030451401072041d602612079000c0401001200c621184803901050282c00400c40c0001240849aa141c90a840130390640a807980c0752032a060064001030502880201e000d84180f203007810358040540d102a10440002d40300542c04441d40d10211400e20001d40028800f40c150356046600940130f00922988901a48540504481c0311b0308071032800c50018030040c04186008102498110700c0c400500c0e50180760316000c40e640d070075170740407242c2d840780e03d0980c0c01401c000041c004104501881da0461400715003101212420882129003800e110840342154810080a00e8003800403e04019000380711083d9541d5400c0c4403a810030350b04d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630910395 1250 630909145 630909157
    0x100b03240a0b1803060105190918061b090603020a1416051c020f0d0206010b0c0f03031302030d090602030f1e0c0303240901030639110307020f09070c08 67
    0x1d0f00403007607940c1d450342010000140141410b071a100a4075a075070240c1200d03020180a2007600c00d031950703824401c0d12188a2481c0b1415006007003001001e02010240e480480c445000780e0101e01c0c034039000190a4003c1c4240c0c0c0031024203803501180305034800b84100180e80141d000c1440020320740c08200104404000546410b0417007130061044c040c451002031f10b00b498801c411030f07a40d0b129804945109501248140c1151141d1101946401080940c64101480040074507047c3c0f1003c001c0003403481c400c201e09000e20f4002d4017070b10962900040c0403903001e4054000c21001d039204000600d24020b04000500c1e41c0c50f815035500840c007040080324040b503403010000300c80561000c402d00c000c2446040030884d94084410001103e40d4032a808600020380501c80984000c2c3d49182c0140d518074105d0407810301500711041a030a004104844e4480064101c040c50005400c4800b000c0c0d0900c0008100c0d9a03940c0c0081200b455134400d007007040440b0342e00804031010440020304c1c1c03000080b504005815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630911645 1250 630910395 630910417
    0x70c080105010603140103050d05030618040f020a1205120d0e0307050703060e070f09020f0c0d020d0f11100f02040e0c04210b04020d0606080d08100b03240a0b 70
    0x2036654502400181952805c10720200060041401000004c40001c0d1583c260f0b1a2420a80c0c0c903956a640018002d000811600520085800420040080503401740825902c2180c000d00416218940800e9030a407a0800a029602c2104e60503080d015481c00f0f000c001d80030280101711541c0f40d841036803c42d0001b80044441e50b202c0c0c0d03001d104000031801004510300000000305039851070255407030500704032442045021680090041c82c01943c100440308106c681c03104592640c0c001150003955441c0e50580320000075031603194007540500c200d05800c54283c040700244182c181880c0400028400c01c4503420215608201c00a021100400d030903208004511000b61183d140480c20340d078555440c940705070b14601d071018420000e2060b024142d00142c050320070020540c10b0b494004018400303a0803c00300703480b8141c204100710785d00500300c0f03210740420940742c1c000550307503c1045000e00050354150182c100303000d0408060451206002414600104108000e5a444441c041c10750702001d2150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630912895 1250 630911645 630911651
    0xf091b130f02250305040e060607060c11010e07060f0810031208090d02010203041e051e010c02101401030308222102060712200f1314130b030102070c0801 68
    0x40e40d8070648000043c4680e480c400820510030f05030780c01040c61155025120450002c000410340c29222030040e00c81140d442681042038644444000d444000168075040359903083c090031010440000c0740590842e8000e4031a00a05c0c103221000303843c51003008000d02c000c40c00904d400000b19900d440d0b07070403000e035a0381c8541e0010f08104102d0750a1100002d0050706580c010020300002400380c19415907084007070410380c0c901c6000ca15001d8100901182020a01031032411840f407480012f52041107980702540031a00011407066840701641e000710800d56464803000010000b10b400745c0e0155511552a0110b0840c580000c000ca00101c55002e0f000e44403000710107840c882404006001209810444c0010892480c0400000300741c80001d200400c0f003a40c44a084288420a48007810741e03c981d0044400c0e00c4060f9103041700b41542042c00310420b00110210001001c03c66000d00840701d05010b0210f480159041c038251019242e1090742a406660030040200400c8520f0844406406440008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630914145 1250 630912895 630912907
    0x7030f23010e011d012106110301050a09140703090c0f14121609180b01300b060618030d030e06090d05070b0402012304030302060f091b130f02 63
    0x41c021000305804c1107950741d5102448400d02143d000310141100c03103c90f185050131014415100c0d000100380c0008003610f041c1228001d10201c40c0010b54181c07101551b40000341c2d60341c0c900b80b0007940c45028070250302e1003820300440d0541c0e00c01e80041c1d4a541c0200240c040155480f1204180030140b9400703c9059124041d00ca42c1c189400302c10341282d89000360082003c2c0c000001107044d0350306a8843e04501550358480350344072405041e036169102d0340004a40308550394070b5210440e000c1581c032500b006900b4400581c036a2850407200c9501e06908234803801210707070ba54010b0052035480a002201d00a100b5000701449503030810030b141d245402d40e80d0100c1c0040225101d18988980540b4100282d00aa0515845503078001c0a4507074090b00300d000c4d2512903e40380010b840401c0442e00740c0d42500b0551490340300e06ca203064010f10850b4402da00719440d55445e8258141111802c1d19080342d2078201e004a0013800902034840241c1520090481003d411420514002c5860202c5181c0b1099004545 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630915395 1250 630914145 630914159
    0x603050d05030403020613020301060b040f15080709030b0604060905011202010806040501060e0915030f0a050d0503060916030b040203150f06090120010b0d2001030605030607030f2301 81
    0x10320329600005090041c2141010303a030181d11141d000b0659031020280541c090155038094000c20024100b00c08003030380c4c40f500ca84100c0c2c113041c4540035002c034220005c0d10401840d407158042d036100ba207181d600c10503542d040d0340d210204841c0140006a00580310013020901c4481e070f201d0310b402084c0811150104d620b0034800505151002860a8440c40c6080010021541c01c1004c401c40104200d6802e10300759038081404030089545a04c036601803003900c428000310000000c80070111030103401111180040c00b00c04640c0e0703101c21241c40d07400540440100380e09503240c0711030350b070b441400b03040c00700b100300d1030784082000ca0300102c40c415040d031a56a40f181c25820700024803142603000b03030340080c5000360030760001c1c10168140035070010b503002800b00c1400b40d00c029400700500740c40c010007012080080c0d08005a246803c00170034400508a9079083c081507010344116800ca9030090080e05c000d03500c3c1b0509400078042103919010080d00c1d0305806d0b1f51380c034014618048014250f02d1500c0c8a50600310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630916645 1250 630915395 630915403
    0x302130b0d0e0c091302030a0b090a14030301290d0f061401080906040f030c1202030307030b030307020a1e03080f0d0501050d1109060111010f0e1009030507021c0c0801060305 77
    0x8400708107a0040c18a22050b0380f03911340c82c3d5030300001c070803940d03074445990b031001c42e02d4a00c6405000d05041d81390014440c1c0c00c2c402140468216010f0707100004a000e001c1c1250347c407888217105040824031420030341400c084149900e81c82c201100d603c00b50a08015646003002c0c1c803105404000d05503900c081c10f100c0d0380007140d081c0391280002e2034103100354502200c050b0f40d14900940701405120507102c00604061290103128121540f0080c051003820f01d20324042d60701e40042c6d0306080424200602d0740304a0400009543d40c40f80c00a24416070b907031030710354090100701d034000a1001050a190021001c1200780004002c4241001c5045a450000741c4400c1c00b0ac800603044a0301c1501011001808511301015103094610102d0710300da00fa494481c0165100290f241d9504142e500300944400146850340c44a2801224001940d4002c200e100d11141100e0004034000c2c0894030500100740581004600d050507a04548607a000303443d025112a82c0c0c0c0401a8000c528680d1114801d03c10010244 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630917895 1250 630916645 630916661
    0x714160801060509040602070c08030f030412030b061e0c0316020406050d0c0314150901020c0606030609100f06030c030c1503050c0415210603030e120d08070302130b0d 74
    0x2040350b036040600041c0280d0010f00060000c0d0f40128403041841210218000208640070460350303504030303100e10b590654008036010b5a0024400001000d80c82c0240600401071100030a401c1c54640d400101021141c800081b80011190a00c050040c00354100f00800403c40b030032860b0742c844000c500c1040151840c54006034000c000340c100701c20028155444000030b90b030b0b01c81c0030140302449400c58540f41110107e48443c9654062060007140c2c101135000b4030000703001405039030242e6284001e00d542c0c2c500a54005c07006c0d034441840c5580c03041c00c940c03140c00079504405012035101c0d52a2180f03004004284c00543d0720b220010020045074803240d44070b0407c12200e0405118507c4c1c100403400d52400b5902c034070400c50b003403141c40404180c8284005c4d444514445002e9440103041441a0002c04160000300e001c070310340c4484850503140450303160850340c1500004060700e4840200c00c03580510040e16400a046c0c0a0041c10750f41c030711110401001e003e08502c0c1d540c0320708080f0f10308000d0310084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630919145 1250 630917895 630917909
    0x31e18060a0612031202130e0105040b040c14090f060304050609160807052b0506060f01030209030c0f400b0f04020a05160f03020105090303010608040f08071416 71
    0x700c602000203c3d030400442240b282c050400303490a0b110854030b80040c0c4509401c0703007020000014040b0b441c0c03101d01c0049060769400d0314204114100002030000325400422180b001c1201e07510b1950300140300c000140b011910103020554118040f81c08603180b60002c0d1000c0754150400c10402014510412000004c901760240d0160b40500e452030880e1512124028240078590030651021158456101c8002049940c5034107400e606850516030b40380d80096400794800d4440304c0410f00740703620034026100f03031103801406403001403c4c020410005544014a2503000321446010f07146003101c0150310008500c03602031504240c00d410240100080c4400b01c0703035560618043c90304686803a6a154510f40002c1903400581c1c2d08112a41601c0340d004403200100c00d8040b0340244000c100301001a008564440d4009014a48035050700d039407240024098080019060710009010400603c0e10304645801480624a450100d41312a0240701d80c149014a4680c01441401c1e00d2204801c0071500030044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630920395 1250 630919145 630919151
    0x14090d090f030813210c0803070209310615051f080702120409091707050604080a0c020a091d01061802031518071b03050301030305031e18060a 63
    0x40202407210140395020241c082e240101e05141919006421100941000c80324503581c1040440c100c0700468040d81c0c1101e401301003850020380003c1c00004c0d2480290700809a0500784e07200b8001c20030001d14610b00f00c1401460f00100043d52528807000648240103035004181020300461300f03526564103600250041c0409281ca29a001d00385810300c0c03c0e801c040c98022210303100c0c110101e2034000708107400f10880c40000b4001031043c0d155485007200360b1003800d180311070b00c00d40400c0a6481c0030703019024186820150010380050101401001c00f509141804c030943d00c120740110f683e03144541c03c5030303074215074070726040c0a81010f89400502c1c00707103444000d0241c0b5080c404490002d4088a000d03030202a0040086451800703289a1417a1408010300810030540d2441300100d0f8109068070707280040b5840d19a0300f580003107503142014855405448013440e50b484d5541c2121503500040c40031413480d00032007051642000140d21140144480030604043c29401e500160408001a200da00c00e149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630921645 1250 630920395 630920399
    0x608060f07030b010c080c1e010204030305160305041a0d1a030705010f0c06020a23040b0301030b0a090c090c0210020c0706050702120607030c0311070c0e100302030114090d09 77
    0x400c803080e056101c4460314000c10081080c500595482c840c0240090603c1000300383c2260801d80080c201c035010300744200308010744003040e07141c0707080340302d280000b07000200100000c204003c0300f6041e803122207100c0d2130600d144c0303a968580000149030510407400c00c008005201c038a641458004c410392703030a07803408040c102111880085d035125400c4c86041d050000e90702d0402880c5028040c1a58440c1d0810300665540c0700581e070081c500184016074500042d801d090000f0003080690541d420795000c407044a19503429070701c840d40001801850b41c40b88940350340301000001c3d42d080410005003074414001c22032154400c00a41030030002000c00c0318191040c401c058a07000c000881c1e0301222802d040065442d50326002160301a0048210024988122001d02982540c140e11000c208003840d58100310400707040c0c03814411071051110151000b07d410381305000451200d018240c012002860f40e040b240d941c0d901203030030748101120140e483c540550070481512410700c40c104c0842c480e03140443c0081c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630922895 1250 630921645 630921661
    0x3090e070e0901050f042316080907060e0607240f270302010b030f060601081b192006040c092d0f0608210a0e040f0b1012060806 57
    0x81014444d051017460130800070704150712540d00200c41c015a01b051604815010281400c01c10340698981120a012021404100307200e1074030180290880313409428110700e0300c1000c550360054000c07803d600c04001c003c2c1c140010590284c505028807010301031005d1194000ea07200844501030150b41c601400d04494110340c400b000b41c00004d01185003529001c20b049410120300601090356242c0d014460003640148050f00020520300c83c1308241da444003195030b40c003554106040c10f003124002c074007002d1064080c0250840030002c0e4803000b070300c4d000400502c00032403042000b814040d4021182c00032424403052041d030810940241000c210240403c0da030340202e003001c0c5840d190015000b105581421106c64400740c01040210700c049105104050300d50000c944c9840314040001e268100c01742e4144e0036118030409446000906450b83c07046a8186030510000e4082641c02d0103a2554a503641c00d010390f24400300359585c06c000d41c2c400a904200e0004001100c0c980c0e080400598810300400801c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630924145 1250 630922895 630922909
    0x12050111090d170d0203132a03030f1103030106030c030630080c030f040914150d06061502060403020f010e06040f080702040c02010f0f051303032703090e070e 70
    0x950100c40c200c003150f043c00b54202c080c00340b0384015080c10300000a0142001c01c115403482c24a0042c0180190850341c1310030448001410000d190726503124041c10000300e400b640d24044848207a04205107440c854a0199003107178804d03086040404d03940d240302c0003511786c540304280203010b00181d10605100e5015401800103100c1c855210304000325260b0b0000c00c5071042c140e6200025010840303407030301070004449134a07070854083d100c10036240451700c002510400381e2072030050740007003000f408181c00030003485040c02c1c010509031251134440200050003000701241e50ba81309188c1e4082e1009050a140003802c05888000c0ba0201c3d0381410340031100303030f00c0200e800c41c0c200d0340c4504e012000e010725180003082070246003c0030b94010718040c450109142c0640140c103012508050810106e01071586030001c4810548030003a07154800807000001030301a5216880000c0c0c04064080510f0001d5503500325400c502d4000c800240d52000d0030408102c5010016070051018100b900400c0c1a250100f030301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630925395 1250 630924145 630924169
    0x1d06010513110c0304060e0f0d120806010e0303180a0611100b04060e0906070e1206012c04030c0611030c07020f150f130504020f0d051509011205011109 67
    0x15141e5240042c0c000d007100b100c00c4030708100011007520b4032180d4801020380f400c0060303032259000b4614070031900114a8091911502c06920010003410700381c90500444004000400345410302040001d02440c0d690300f00094418041d030b0f15032416000c102102445075234215a88180c05202000c410303003003403210105038032040402c4000005500b0031148001005000e195000081d031601620620008140100d203962091301703580c0702c80340e45642c240180003141d20405030000480d042800103004003001d042201303031022a50400c07074507030404515441640d50340aa908070b0100b403000d08d4050030402d03140200290b503030345180c0c001c2c1185000c4004039124454104028482c080ca4450400241d072650440312103501061256500d404140d41c00700311580c46a208c3c5012200b00460000b00d03031800740200e80d20301084609007400c02002541400261901900d00740c21004078030201c0005880d080b100900920b907140c207403015004d05007042800c42c0c51007a01486400c1081040d0780356601c0344002400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630926645 1250 630925395 630925429
    0x150e0a06030b130c05030a0c090b04030602090d050d08011d01060e10120501060504030c050d050c120102070206120613050105010f1d060d0e1203040f1e0203101d060105 74
    0x24007444602d00080a108100c42148900761801c41028595135105002e5031103101c50b45010808030300000c40a540c3c0088501c203044c03903103504110500000c0d1564000d4900454080c080d1004d00c00c076582c0701410f0554a0b242c1c140040c43c0c80c401002050313212520001101303881e1801d60529414080c0080044400100c958020704008202e04070740b5203c0c01c0b9130780c0c3c0240c244504200558441600510341d600620003560406808000400d4920708849140c4005038010002d03c2e68aa000c0305125000344050004100345d54240015000f60300c5050003011010410101501c4514050003009550b500d140c40c207818a610f440c0051000d66001040303002c0080303084c1020b41d0340400c07598a500ea84074081c1d000075048a0007003040031307000426030080e11905ca40e41d02031311442c00e100900307085107000440c0c000e041c000480f9100e40c0031410074018a010030b0003c182918694286c0d4002c203151188805d41c5030080380d502c0c2c04d840d0030081e031411080f4406802030301920442d490200019860419000009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630927895 1250 630926645 630926651
    0x1030207081801091706072f011b05033112030c11240a0605040e06040203060c0c0d200312040b090703020d1103010612060c0f031b0f050d0603080301150e0a0603 71
    0x294041800d007040c0304401070f9407121a4240c090b00c45480d400b134075101402c007403481020070ac0004c04034043e0054922a000700b10052000310090710b011413600d0752529000502051804044000c11003d640520071815242c80105141100c0350307000b0718074022a800e100f10740e0054001d030340c420801c1d581519902c3d49034181142054407001e041100415880e402181c0c040d00c3c008085a120074041400d81c0304600031002c0c4c0c0c1e5207641d4010414254880e05080320316940203080c0c1062602c0c050807031041c041d25400d8021500b2444c90482d5440c541c02211400a072880b0707101040108902c0540481d485805000030b4900c2074a140c0c0483c658540740540200107141f405846120f940302540300741c00804141120341440141740c14441d0003445441e03400780010300c0ea011a0701c4424083e015050165030180146880108007210440750894441d0b0407004100c1c04201c20503860402c1d00403a400345000b07040581e540d503d00300070442581007001040c420301a070184c421080742d4035400c0c20b5013103c800341004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630929145 1250 630927895 630927917
    0x19050a0e041e0903110f06160f090e0c0d0605030f0c0112150b030f060f0a230a08010204061d0d02120708060c040501030506030705031b0103020708180109170607 71
    0x102c03072180c0000b10074094a62400d1050401d061780300802410103202c0e08143c3c3c01e9a907031407243c1525440c2c1200c102c0b82d444001c80d049540a4818101880c90b11083e14006c0f0f00e1a803130300440c40907100d059507016122600802d03e0142c05d072480c4111001410120020112148044004d83d1948150801e40c1d05103d00c501600c0381c40803103500402c0300c2000e0200e94121003501c8400c103400030340056a44c00d81794004071303000540e0341c10512070741030500a00511400e00689481aa102d10710301114000c0e150103115490807001e511910504009030001e40000741e151401c100c0001c1c40781c90003050b00e0000078000003a91b40640c0760b00104141312034058402c0302d103c20980503510728008450b4480c001501c20b00c1c0404c441c1c000c19102500a40e01c00b42d03400d0085450380310030156540c94500410743c0c0342c3c0104442c1032000e19001000b5812003018140035043c10540c0d124005541c120107106009148050b0031214a0741e400001c03000030b000c6580400032048000c0484039610b00005103004103016018040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630930395 1250 630929145 630929171
    0x1e01030c11010f020304170a0801030602070f0b161418060c070803040e010e06090402150903191401141909151b081b03061011030f19050a0e04 63
    0x48410410520300280a2040c00b0b001403c0207520465090f034038119209000c9002084100803100d00c40c85950f1140110790854032000c00a40c41300900303c400325040071500e00040c0c64800014801c05100c11804200c0c0c603000f401400e04e1685d4640d81c14210703010801068020500d42c40704081d05e5055030501d860b03c600700c0d01c45d8540001500301090610012500044280c0340368492410b85619010000c20f6803510000c0c0005c160080c1e034000d6000e8000d01028600c0b80c0c4034805002d410360300038100c6043c03410070341a03600348a491400a403a10f1881d0030008100b103000b40185607005002d0711680142e0f1400c12116481d000c8003e0381041e10f03503210f030409001d2003050201c03000844591541008400710b08004805920f10080315040406d0780100040c800040c00341d90703100800360104425145a8641042244000038140c0007070905c8405403410030540020000b41c104071541f001c0c8030341d072401d480c09190800c10300c4c03040150404c8400c11140c1b128592000403420141d0094501041d00074950712 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630931645 1250 630930395 630930407
    0x30605010e0f361503010b09010602031617040303020c0405090607050a0804060b0a1806091104140418050d021203010513020306030109021201060e0f0421030b100309111e01030c 78
    0x103100d02a0005030f2081c0500085841c00c028003440044008011545d40001800070f40740e004d110360400b58106118010403144100030502d101c6104548100c0200d1300015552b5403900980c20980040e440030400c007180b4149442055044a20398000742707100c5c904031000800f1482022400b10400043c000410100075007608103c4489400821040d080c0d41c81d00901d00421003501d03400d91201e8241003002803062010b02c10783c400541001c022526007820b08541603840c1944a0f5905e40080c0d071528050b880032008001340ea195072044d000b0780801040068000d00c2c0103c4502da05400300d40c03c1004010b0380c4e40c1d44020b0410140030b00c0c000368490742d03004006401824041406500281d00b8001c44d03011355410342c00482610000c40c100e04090300c0c1c41142c0818240101c0c2e00500341d400007090602d00645042041c6440b100a14011592502c80001b00d00b144510018840c003094a60041900700900d40c02452001c00f0192500700c02c100d01c503295026003203603c6103464141503980c100c44040f51b00c145 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630932895 1250 630931645 630931729
    0x7030c060b03070311041a090a020f0705010911100503013b0403020d0f0203210907030602160b0a050f01032004020c0618190209071b03030605010e0f 66
    0x1c060f42c803156582d040c4a45c035101e0840490380b085141c25955600d0841c00d0714819901034006d0300f07080184e581c038444400298030050070010100814091140050000d0003141c02052040410440295400d42072100118000b0b0300d00f010b0080902c018000c51007441c02c919840f2a00d03003100710501c0b0f0000512420283c500c8113a0220b031044000b0002450340000d00e42e9550b8045a541d54260780d0b40040483e100d01034000482c8400a5002000c0b03101c85c5070030145a0099500425900541c1d13480d0f5806003241c1c400f0b01012020f0b5002607220b030030b00054503051980301d5644c200900035450007002a090050301400000c155150b19034039040000d00041c0c030b090261b0f00180c000c40d03942c64040d4020740d40701c000b142c50112101000a190707002d40004500d402c03a0f000d0340742c40440011455400c1140f00c450040c44102001603007a4007458120160010911060080d02e0020304241400700042004000001150060312085800c4000384c4078044200c05100000703480c50208121802000403400500d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630934145 1250 630932895 630932899
    0x402040608010903080f010504060617040c1221050702010804140321040b090307210c08070b04050601140607110f06030f150103090c050d0c03050105010902120f0c07030c060b 77
    0x2c003030f2104140c0c001c80154000d040b0302c0849602070785d85408110546415000c2c120026005034100c0d0040203001103503c0c0c2191043e03003c604e07113030b440c0d82072501c0200710306a09403914841c651080c83c0c8220800381070603d018207881e00e41d00c2d20503640c001814900000d04014142c800400440141d41000d000741c8190304d0340411101c5440c65a0005981c0f442d4003078506440060f017060205082001c000104d84085900c201040c0303000014028016210001d105a1414814030f111764900040d0010000c03d41c1c1407040c80050032a00b0b080c18068504001600030300c80903043e010087c2e45903940d01d001e0301c40781c40e48202090751841610000c0303612034184190840d080308010091004003813501d060305200c0d80510101031610b1140d070b801102600c0c0180d00c0540768201c020414002d42c10182c60440c4840d010718005400c80303699075145801c5070030990040691315408610840c2900a099126401040c0444051038034241000c100f0500d1044100c0107090200c49a12001000440e030010b0b4000840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630935251 1106 630934145 630934151
    0x50114041a0901110a0c050115050a09151d0f0a0b01080112020d020901060503011509030203070e07090b0301030b270c1c060f0204050103270209040204060801 70
    0x800b90104005540b41d909940a01840b0340013440002850750303c03904440024144076003150120103000b10901541d0b9010881ca55540d242d0380152003021070000f0308200e02c900350f44409001c0e64001d06d40313010a900762095011801c4086486003803102010407881e501c1c00311100c12280c1d1060b6aa0114a108d00144100f0f80482143c2c04d2540c030241400c02501020340000300b00d49400d034014400644004010701a408101d84080102941d41c00c1c0031020345e04580c00280c89024500400d1051003066001a245c54414009907005010300d0201a589507100d00300700f445804115086140c01000c89160040f100050511200031249030010340403a90700902000700704801400c41c0d02c81e8014149000011862501c115454100003000040e13545203008009001e845256517400071040781005030400c415189120003081035411542c0080c6503440d88006070052803150001441986 = true := by decide +kernel

theorem cover : BRFrame.Cov 630755395 630935251 := by
  have h0 := BRFrame.cov_init 630755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630755395 ≤ n) (h2 : n < 630935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
