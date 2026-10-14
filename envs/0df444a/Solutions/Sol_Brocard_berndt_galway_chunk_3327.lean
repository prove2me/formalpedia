-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:50.955163+00:00
-- url     : https://prove2.me/submissions/85202e9f-249f-43f7-9ac9-044e5e0d97da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598201438 ≤ n < 598381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598202688 1250 598201438 598201463
    0xd0c020129041407080f040302010b130903110703030219020604030c08010c020f060c030411011215090f060308030c0f070c14010305060102010e0706050a020703080d0504020f01020f1f0603 83
    0x107a015200d1078603214048904003d80110b22010703910075403048030010040382d40d1001161003912034800a55201d4441e10020032500400000300c0d80100e102c504039a00161030351a10001c00d60040044080004a2401403851910310b84001b59a180889443e01c0e0007200040c60b541507442d8441198007543d000300d80f032001e203651540414028514002c9a400502070309150003141c0030702044030b500501d0b2011a040c2141c840391140b5442280d5807114a050014400605841e81494000e4418044440032000b01292a2015082c00d0b01c04005007107c940b4a48602800029141000d4039001303032002c00300c10b4132048042c3c3e8a4010b07219010f0007504042c800007001500201c90410f50701d00d00f00a03602444942c84170801a4241e852005440720a90007040f400d0002d94811009030015550306c1c0704940b000c607600e40311104c2c1a0302854048486940350b00801055003813400d8241003540082c4000c0c5066101d13415210b4a030071403600318624003403003040c1c407400e4079031140c0116003c2c5410012881c0320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598203938 1250 598202688 598202741
    0x100333052e020a030804060c270e090c1503060102070f0308030a0b0f0607200402070c051206041a0718060f08010806133c05010f020405060d0c0201 65
    0x648090750300c0d81d6401d1440007000203940d00c0402e0742520641e16464400042c2c41d640d458002501038580c01e602001030300c12015402c400a03c426102020407403141d140c1607402d04c8202d0603c02c8000300300108030307442007400480548624400460b11041c00c8900c5440c0e440e840f004070701b0080141c1c000200110681c2000c418001c40f08010b5010340c850b11004c200d60031688060025400405469540c0135009000b6036012440c000c02a00b103d824402040180c41c900d000050100e0b0080c1000344c4262004000074040ca0070010324a462000d0781800038682c070b15265a0f03c65091a20180c1001403000100110352454041d44540503681910910b0a411507103482006010f15600040e40c00045c145100003e881ea0001c00e01034003d507200802c00242c001552201e00d51700c81c004c05482c446414000324522040c5e04450202d0f401c4011001031203135190142055400d580205038402c1789103204000402c01c41e40d80c0402c1310b1601540d8140451042030600d016130040010248003d081741c002a203a200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598205188 1250 598203938 598203979
    0x1080d080901060506071a060103050c0403020f010207051c110f0f0d050708100c081302091302120a0b0402150301120b0603010e100204060f0306080c060304020d05120910033305 78
    0x850004440e40e81f049075519001101078800070b44a1082c2e140e8204814800760400d07180c075402d400d05c18011101d40a90710030219200010001c02000d000a81c220302c01c04120303944058180d44041180c041b00031200e0f000001d144805440455031250100d00c3e0f0324800c024041c001c52000300301c200c042d40c8038150034078109400340071400c041c3c0c0e0016004000144584801c1201030443e1900a0410f1540759181500d60200320b81001050340d010010000b1041c3c1c0b2802000305010151003501c0544860619206212444461084448031002d05000610940d1815030400c90201d4216100c41601c1c4c543c400480e0050048011003c02d40c0038074048124820016001802121178980c0c40002d15140c0030811000c442860081c81000d80105620100c1850028082c1d41c100d030006080480d03802856403420b28044e40b04c0501c00d6001c0700440c0b41d4405207810b0b000c4a002a005023001e0041d040c00c586c03071301044020b0008101002180442c0c81d1201c1c01303002c1075031f0003800c0d0103044008200c441658008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598206438 1250 598205188 598205213
    0x6090a03120810050d121d1f020105010b040b0d0b120a050703030f0918090614010f06170105060306210d1e0912030507030c06020d0e0601090501080d08090106050607 73
    0x954500c60302d40c001210b00746007540c0c0805603040709030590514408003080343e64207055040c100c7c030001c200703401011945d10722030f81e540c1c1040361458581d80c000d405580031382540c0051780300c0c410304101400704001c07580d210012034807040614040000c010040100050b204462441700082c144548010007040280000d109401d41c0d010b40c803050710140304020119046252030107807008480e00954110810364207608110f03071003885440c000c00c0e480c1d080c2d4901c0b90b015109921404003e81a40340402c10305030000781701d40080343c0c400b071000c01942c140f4001c544c03607100180c40c440c0035000000c1000d095810010400b09003406040986032100e1070904010030b520002681c850301c00680c640c00d40b181da8040c58046048400c801d80e41400000c05d51026181500161020b40901c0b01180944001415620040c0301c103240300c000001d44088000c0c4094a407030b034140c114540d0075141500601c0b032142e0000720600c2400641c9402c0400e943c0310f000030360150681d9803025420000124405042244418044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598207688 1250 598206438 598206451
    0x10020708071502030402150a05160507150f080109090b01290307021b0d020a05190801050109020409150f1205152518060c060b0d06020d110405090606090a031208 71
    0x1051f9510900e0054a00c40e2514110100e0800c02148109030000d44900320480e0180050707a68466950842c084c02c1c0c44c5042e00100001c0792003526000c1d640c3c11100d05400b4114041c0c04105101c2690350740d00300e096060144c1c001307512042982c0c904810001140c04181050040104e440741803840000c0e41d11103003004403250001d14400d41c18142c0c100440e44140268006101d9040310740b800c814820101981c01d000c000100d11306401040f8180240283c81c001e01b043d440059640703103001c1c81d140458110140120020035906000c0180b07842c0e42c48144140e454000c59500142014900306240425400c03000002c00514020030059000b1404551200a1483c01d40302c0881d000c01c800321000300d50f1030000c818410301d80d1401e0112034820028000302074464100021106015000500d516031680d400b150400d8001a003010105183c0c02212111040c40c8501c0d414981050005000d018004100e58040e61010504400d030382c1e43c15030518000d50f0050906010310b0050315009014102c1142e84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598208938 1250 598207688 598207699
    0xb1612120b01050c1005090f2d0a0506010608090304050301061202122802040e0f10060b04050319080f040b0d06050a0521011104080105010f090e10020708071502030402 74
    0x1411002d5029208540d4195054009064030340700c904100002004003602c1d40320180f142c0f101c80d810540c0104903a000b2055010861124480020104000d80540184104081d088486c45600107200010071038103440c0d5909058942d82e842c04103041c614016507200591540c2400e60002d040c5440b01c400403500350007595102c40c0c0204402c00d55503155030101c0003155542c085018041c005643c80c0348000d1040c401070010440c01c2c14200d84918108281c090007846410031500c80114050301d00c82c040003815a161410704141c40c20000030b403a80101a0100501044130380080c0c2007009410407039880c500b40355403240c1c0356501d40c1444603183d002910760712411842c1020200e2949010280300007200c100170010044104224244200650300c2400d9440d55906c3e550401c6202e60300c03001400150602c1c000000301580340c03440002042000340d002951301c80c5040c8a612520320013248540e80900b2266016990b5800c0749086410b0780b0580744082d00b0309021682c00403548125800560107540201c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598210188 1250 598208938 598208951
    0x2d1003140709080304090c030f05070e10230304080c0f030301080f010902060a120b0301020d1e0605011b26041502070b090f03030d0504060504021206010503070b161212 74
    0x107003a6900300c910b018801d11588140020442c8190315000340a03680070916000c03c0e41000500c281d0191101078800c000850700002c0c0384070301030818800c4001094118036007220110801c4100e54a090300826006200c80c400000040602103a07008659211350780d4403c8074880007506003070719101d400038021000d0078054070403000c0d0b08941c140581e192468006003041d191210300502924481442ca040344c04007525160304541c183c1d07081c406818807a100c00380116449100642c910021b0b4607803c03107001444c0c0340a000784680d07680450341d2988003c2d0341150312800c3c3d8160401509041000128684100c3d420b00d408240c9503034240600100c604920103424096000241a40c98032800d000d01c0354490000d01c20b254a0b840c1820041040d010302800360b038034014006005009440c0104c2c0c0075030340d8944410502045061542400f82d4881d03801c0068003465040000203901e030441445281c4581101145150b110300d40035900f01526517024095002c00d898818001d041204c03100c402031545880c040303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598211438 1250 598210188 598210201
    0x1210206040920040e070c020112050c09040b0910060806060d060f03140f1b0d080301090501080c010c0b070507030e030d0804050601050103200d090b180613022d100314 74
    0x1040d18180c803001171101c00165034802084890019441041c5d04005140c00760680610603482101c0c028811400f88682e9402e46405000076104021440c80c0142200c108001d07035440014201401e0b1002d91915010307a0302c50700c0014945000b03081c0850355040c41d203d0000b80d040c2c8103005d05400c0324455894202d103000340980c0c803a282c6078217001ca000e1540100e4820121259801400d031594580100b21151601a540311403a00e0b8000360805034519503900c005028a41d820441d5414909091a0503030075098a40c0c0d40141c02d08000c0e000c6410b0241c0480c10404050059151070503020004c2c2c21500d00d49504071004190300d20a607025942800f4000021603154860301440c00c949180c0d02040d481d18143c0c49031101c1c190720000311504401c0c1d0b00c0c8040c0380000d20443d0401c0c05480000354042c03e03000c01480f602e0401703002514101080d640010302000584401d1030184800071401442d55041d403c01005000750f882206149038006505019030b415543c250b48005421010304905418a54516 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598212688 1250 598211438 598211501
    0x230a0501270b0903040b0a0207050f090105011b020307050d0605250e01051b030406050d06090513060e07080f030a080c070b041202030f192303012102060409 69
    0x220100c441441c0684610081500809015005000e280403649403640e984090603c41c1c02900c50070740160031588080200b0328283e001000c3c2c1c400c0c202c0b0160419498a000a007100391504142550310118802ea281590b40a0110b280148405000381034400b0741803130100c005100841c0c5080142c000070540d074031800440c140429078800103440384846030710b2030b1006407002c1d0009541003d01c04284403c01d0210202400600020b1009803601c503114403241017440c0541c2c01e19002880142c0c640360400010ba200d46070345010b001e810800006554078070194680c10034025030400c580314440c000200442040000080c02001d200d80d8400d0a203844011541401d4072601d0405441141c0380c2d008500481c00c44104d1a0b45d000c41401160b181203c0502d40e90341941182d82c1c07040403c0c03040c0c43d0312070b5280e4001398907031103000501182c0e4200249802d81a00d907404180070382c40300165600d1010740c4204408100b1000303203400038049a2682d507205440d90180c250100e44803e01040508030f0031002501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598213938 1250 598212688 598212731
    0x506040320070503071e12050a1a1005060a030905061815040b070810030c03050610051c0305030603120c06060f030f0325080309010e0f0309030712230a0501 69
    0x1c001d0200039141001b80400318410314040c1416444291000804040200102c40d403984203c01410600902d41401c81b05010154090807201d0700180411258540e03007820381040c0e40d02120701a07120b16420400310300410314000024001d10611003032002e03114030b260680d0600c2800e00c2c01c841c2d005400380214070401130f058800a00c10b401640216001c00c0c052085240e100044c085142c103220741c1c0780c464401d10380c00c0780d000750b9498000c14244a010030614440d107001c0c12090303a1410f0841d0703280000300d40c551050500907080000c007202080481c0e6041c40180540950001c40d542c0b541c840d504520346481e020741d4150b02c20301c5690812805414045882051080e02801441c185051004071200980c2110340d41d0101c11240003061002030007000195015013414030001406000d0128454900070038005911441d07441805841c0089d0380008500341554980406111010440d150007903001d0300c1608144140090302229103404c64000407c180050300403c028030114810718440c0a04504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598215188 1250 598213938 598213949
    0xf0504210806060f1e091c151a0301060b18040c05030109110714160609051e190312021603021503090a290105040c0203090d030507050604032007 64
    0x10280000b00e441c0340040203000558100c07421540340080308462a24100140341c400180c2480210717082203242818010481802c260f1601e2002420103070700c40840310341c0300c0d03900100c01544407640035000300001030040c14240800b4000740030090319015404100d41103010048410711120103d146035103406e00410302c04207940c0d142c01d407640c0d082404450103411700c4031103803849074001c205040c00200004110380450b803a40c000380a07004c240c1c03100034020030035131341c050801c00020710000c2c06a0b40c1c3e42500700300401e1020400d078030b0201c8000041022822051150305811b621000c00100344582948450000f901603801e5809001c01c4009036915040c039404080d41100385800c44401840740900119041840d420407100058955900c1b8882036020713003030900c4401e020a042c0c0c2807c6800065060250070f040300c1c2071001d864484002550380c040e0001d82403080c0341844145082c54028000c032104070303401c01c0c00c1d03420910b41402c0280144060301c800c024541c40d94021480440301c0854090140c50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598216438 1250 598215188 598215197
    0x4081612031b020904030c02100806030c010c030216060f0f02010e070b0a2106080f0105040f03030b060408070b12070302280908030327070602061314010f050421 71
    0x40380741c60441d004000310300360030010a0150241000750341ca991300c051280e44030f0341e2500740140e50362040c810490440c45194092202000c10b018103903401151480204400386842d4010600c1c41c14101d1134010b01c00004418140d011402255071603000052520354406500d46c44540e00300d4500403401c8441c1c0c86e4001006400000061203400c0320350f001403459040c103150a180c1d911100100304448050410100c0b141640c680b41041001018001c01100716a804000c100516260f1146280d0b40ea40d42c400034100b41c0da55017444910b42d280c2e401d4901030181d14040302e840c95103c10800d51164080700d1003011740f20f030b030302c00040743c60b07201e8001c4443c0001d840340329480c5c0702c0d1881c001e099403114003c2c801c000d0082c40d12000c07600c018100b010703610891400d0315107009200168070003400f121003900e40c8061a000400c0600c5451340000f5a150400346030f003451401c9007000e00301880600140d8400e0340c0d4030750802c60001070380c03030151308524001c07401160b11400e002000700b001c450780e03400d4007051000704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598217688 1250 598216438 598216469
    0xf02010c140303180106060c110d02180901020903010b0d031e03020915131205120d14090f0c09071202030a020904050f0a050105090c040302060c010e0105070203040816 74
    0x6510400340a04400d1081c940560501c803032442540c11500110f5065500d60082c3e0484910a8402d02484004000c1410304140c28410b036101c20640b00d4440c0005406800441400c0c41103407180b410300300500c01048460036040c10b010b50058080d42c0142c0303060f807096080108035025441c1a0110502003940760301d8908200d540c503078801a05445800d14241410343c00e01001c00284c43e41391201045008610405a40340e008403016044c1d960f640c0c02c0281500001c40010000590001d2111020b440c034110141e110031100c0b415401070403e120b10518541b050a0034062610300000b01d0180c01800001629110051407052008942d01214400d00080b1400d0b407448403444e00358000c40e00043c2000f00545044122000305003600c10540c1e603080304680302c0c0c042240b118010300c909405413030120784a0344030341005103501c1100d00580c007000c0e22410000811992039903003540105e032102c24400090140e440c3c90440652690414448c1d6020340c000c0420480c10040b60001500959500c6200c04002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598218938 1250 598217688 598217693
    0x6070b010305060f28150b040306060807150c0804030f0809040b041116110312030727030213090609052a090f090f060a0b0a0603150918081206100c0f 66
    0x44500d00c040381d070143e50b11501d01642400d4804031401900d9000200ba5235140b45203009005c6a00ca86e1061519030000102441021070445c2d81c1c1c84210340601c0d119401c2280342c10f01030b605204560000f400200184007480402002401601e0003001c1160100b0903028100240025902d52a04089290908100c1802808038011280e84070340d000c0d03640404003540c48404640b90001245d04d04031880c1c000b208010f0010f5010b4484400c000315001240b51401e6020404064000e56020080c030416400c548900050120350150344026004041800242d1550405584880907040944d0510040110b19402001010221100081d02511740b44541c1d0b01d1100c1100d08400103040c0c88030700c1c01800e10700300f0026410802940034640c507102c002800b0345181d042180c0810303140d1000090500b010043e00c00b0b03010381d40200c0d040b50082038022400d1b1100845d501d0001c03034010b1000340802d00116180208407561208280705490a40b065001208030304000da40500c600c4400800c190441c4502c03800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598220188 1250 598218938 598218991
    0x90b01060815100504380406050d0507120c08091006030507090c0c02060a0315090507021e0f03040e1e06060d0209060412030806040f0213140f06070b010305060f 71
    0xb0b08204514106040545400483d081c1800342c62100c2d0200d411841c2004c964049901c0b50707840004103206882c6803501c0c023080030700903020b060000324001e90382e480000c2040f4002c1036140d5980d2001c070303820000d42800c0b000150000005540c240403911a590103400070406920448007039a4010f0000c1064a1030041c01c0c0f0042e01b0402114000c012010b415480103031641000b03400907881c10703280030a00c4070a48940c038074032010355072100c8101414034062100e403d402040388050304460041c5107200000242030145400304424602101d440000307000030b0b445c40704020960059810405100300301651119a541201c2c0650b9038a5200000300801d9010b024280e0080c154402c014181a0070940d95581d4450010322580c41035021880e28400c00440307207858818421410002001103060000749036014000c0fa07901d010f488401c0d0003004c400c1c401075462240c20491030000516040e503404403490001c9080d0700c2032000f00c031a44140e6003c602d101241c20403491045010408001000740780d44035160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598221438 1250 598220188 598220209
    0x603090102040308030414010c05130e0405160b0903120f04061206030b010e16030509060c07020d0804121407061202030c090a030b0907050a15050c1f090b01060815 72
    0x1951503500700400070010702500003861103036000c1c00c0641818031030021420300b0f40740505002e0781000010002c800d00944445814002c0d12807495194180c1d507200d140c000e180c0071044546501a81d020342c0b00240c820174800050115040c198140c43d09040c50203107a1400c0d00032030400c6036507000c0520060080c0d911807030480001070121040403580310740e6900d41702c56901082e04250740c101501410003260f03440400c400421130301945803c02251804c0e040075070300d40d400a1310500303580000185900a5540d041c0001d0012904030a07140d607215a9000020054040c81d4001c41c3d6684249601c1c05e0060b401040d1740040314503580701c0d100203210441820f00254802030400c03920010030700c0000820b848540c10000507521920350340c040d905084c0205480e102a41e03004501c100b054100902002251441149200c0c0703d50620548908500400c28140b200360342000700f60340c1804220843c0101607410180c4480d000c0c06283c1c40c01e903210441214404000c440744503040c046101e6001180c1000324004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598222688 1250 598221438 598221451
    0x8011d150c042106050708040c0b0a0302090306090109020f030a030909050a06080f01060608010f0f0e06010e0d050619141b04051003060509070309151503080d0c0215070e0603 77
    0x740703001c0d20340d650681c0e0b030008042540308403203083c034002c01003250910030030b0340006550a200015280c46d0b9525201020381d4092160712800108000f03141c140a60165490351400905a0300103180c44072459008000d2020141d02c83c400c180d03e05c000b6424045080741d00c0d00c0d0140d894010880c103281144c0040d000140042c41d9003591030500107003124080c081c00120700309050001c5403492034200000d0420b80306800a40200c1e0031108204000c031442c4c043d0f84110b800360085107480340d58080050f60b48803014a81507401040600c0100c04225020508511610203400050600704001d1015000c0341e503001c0319110544d24050118901c518420303083c4c1405c20402000d18030342034a40703021a10000440c1d0811011940300d410034011494040b554681c04a0107140c1002050042e03112101d28810749005241542e50320100380c6030710341500070050301454104190030340d205840c039200c0c03008050f910080401805000c2101c1181c203030352406035000c2d05130b07517480c00c004800070001c01060b5070001d40344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598223938 1250 598222688 598222711
    0x7080f06030307170a0f0504210f061407020d020102040e0f0907150905030c0f030606130e01020f09010305070e01020303190e070801060515120c0d0e1608011d15 71
    0x4003800a03241d01e201003600c01c80c0c907913000d44600703102c6009800c002240000744144002840700b13000340c41c0320011740800008800360241034001903090490500650100c094081814049038842c5400b80e4610940943c0250342121020401108201d00300c0c0205e0040e03e240030b41c00c4005c13445460500104580201100042e01d1801b541c07a42d001005d01007000b2a080801c602c034008001071319040c024914070b2501a12041011001d0800290311000001d04043c410500f0100c0e402c14034009611030141d811244008540e290100004425250840d202480c00681804c0c0090000d42c4911540b541c00c0006030011800c60725904042100d00d05030240503130740d942d40c48410022200c07040020740c0003090044000035210381410305008441c220001949079151040103450f00074155103001c1903105645006c050349581603c880314000d85603200190354075104d80341101244102060020b021141c1d424020800103640f42e0350381c54400600200c88505d034011102c0d001e407000308000c40c154014601c181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598225188 1250 598223938 598223947
    0x190803190212040b060f09100501140d020301030302010f0b04091212152c0c030705090109050409061b02010c02030f0d180620030c0910020106210c0e07080f060303 72
    0x10402c10741e41c022107090303c130a00324100344540f5060030940000c85640c00c0c0c61042c2ca9180072000000c40d0355040c89060b04010384d800384e408680c80c81205550f007841d103500b4195620359407820000d000e02a03251906501c00d18000f81d450044c84c00788154000d9552010242c40089030404055600140355869841c20585440381c0601403c0f980d600e00014002802c5000d00701c0c10110340b404020070810041001d0000c501c0c0c1480f0801d240f01c03007600d91141e4a0318140340d5034008440100d50710240ca61080d5041802c040d103400401c03070141c022141d2100f015100d0680c42c85000b40c124240c3d510700f0041c0d000b40c3c204114941003003440500a14041186404c0031030316100c520f2030004014040c00c01901e40c80d41c1d6482c01a80500e06011111424009142480c00c504080700420418440d4002440c46412070103900e0034128000e404c40c1005200d0141f029000602882e05403e1400d90000112402403000340c010411760308190355540a15842d070b46d850103580e40c016411920384409448140d26100501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598226438 1250 598225188 598225207
    0x40b0111010f0e06060420070219090b0f010207120b0a0b03030406050d050a06050a060c0c08070f050118030804050d0515070c0b0f0702030a031a0612091908031902 72
    0x702c0201c003100003400555007a0000703829040240c01761119109600344503a085100c0000024101c002104680b0a580e0302030501c000b41e0001226509000580ea140000084034801e561100107a01025901c03041451052401245c907140203004640114061808000108140701002680440058000500702580c00000f901d9600168010000a200080d0015080c611401195040786100000f400464103182c0092003400b224080c00c001c100c6125a0384040c86208128400240482c00540d8074103a105c0c51180b02d445614000c19000c00c10300c044c05200c03210f01c2c050120171a5080059981010b05000801c40d02c201010b800340c43c141305250b4032514102020140901601c820384580040c86850300d40090001d00041c003607c0c50600f80c5041042c15030300882241c0c5850918913000641804460803001c41d4040881c5c5140c11150106500c9a180d010400c420301803040d180071a90300c4a1030303101d03403259102c011000510391441400850640c04c1d4030310340c09031480c80016016081000d4003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598227688 1250 598226438 598226441
    0x27120c0506070b011a03040506070503070e1f031a090402010f05041505032215180503071208010b030114011202070f1a181c020a05070e09010501051806040b011101 72
    0x384043c1d51810360003004100710242c0600089038841311000040c2180342940310180c40314001800b070028000e0000018203e03034801c402c01c00c12410014900301d1920600903803c8841c8800e1920800800c2c90184845018a441e403600e10105c10001c0028019541315070045642d2640c0c00300e0700e010710009201c00706655062004d59401840641c2c0e8a50b200d10b820404d00030549042c542419407040000e000101140a9003495102c1244001c804105051501e1a2049013458604007a107580008a540400c101c0d031270341c201440417140c2da2440916621424540c40d0344c8028400c4100884c0900caa080e15035004910301200104030b40001820281580c0303400e14140c071034020840d41d0a441920904440703240b1440290461024003080340c00858140815940e0100410302c003607000c00d0781502c00700c0144200b01c00f2460307540c002e041d00c0c2c54a9844001d11420281035030b54441550916001081508002d00d041c08510800c503051441038640d0014000285414445c107810400c1c1851800643d803001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598228938 1250 598227688 598227697
    0x50d081e0a080a0b010306060c03031d0d0c05060f06030304090c050f030406241a2a0708060f0c030c1303060204060509130203011d131a01050127120c0506 68
    0x5403502d40e543c1c0750084000f012a0389800d159814145000780038003029034082c1690912a6043c2000a40f031046100711401402034801080390a00c070303030301072203000a50000c40011031910820407105035407034035140340200840840e03c2ea50158000d0108103d0081c090300081840b03546070501c0d030b00d8911103080424083d0300407a070503544991103005a81d02c8882640309560b00d401500541c14006044c024000d171b051318213412803845203102040c107054584882030301821f198017003034081c900f00301c440460644600062003100c0040c0a0a130001302e1002c01c024142d445041254892455aa1554030800c00c075001486c4000e0300302581c00c00400016800d10040c0050300d03183d01d03255112040300301002085251319030a102078a005000401c0600452030f100c034010300c0d00c081662500e944c2c1c0256502c0022504201801c001c200303688080ca41c0901e8040075042c0c640c04e030b8034205c4040e059040810385003181803080b400614000350401241e540204c12030081d42c41070502c2d005440c0d0360300016903190032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598230188 1250 598228938 598228957
    0x1503070f08060f15120f0106062307020f04020c0c0a0806011e05030a020405060114030f060f09060108060f01051b030309010c0903030207030b041e03030603110a050d081e 75
    0x85100007408409810000305a000c0180b02e0085a140740195003810901c00f8043d005014000035201140745141c00d1000000e01e11100008001c4142d64000041544060f1070001c034800d801b0191210074102901d08558500c3d0700036181002c10f0018409000013588010b007c403001d030007842d408000c16620548882d00425600004048550404100c0c00d0b0b102038141943c1c200c2d02c04204104010b440114000ca016901280c000070507644035001a201e29003410442803d00c88000100144c03000301d41d0380c0600030b01080e0b9850780c1c8202228140050490140c035418085040380d400590b992401d5034402d2011003062400f00d0070180c1c02c1c0458054100a84a00e8101d500301204111484100b41b0450140d02d6552904c80005032858801a40f40e8201c0d000140c240b441c000300207020300103040d554040c008000381828400e0001820014000d002900084599041f2851280c045280451402c025200d00030034801270000c4075901d0340f02d00d0b8088084010b1120102028070080b107001c1c40540304050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598231438 1250 598230188 598230209
    0x170405090708190c021c27030309050915040903030605041802040e0610031101030603020619030f0e0d0c050c03150f011a0a050306030a060c02031201050406120308150307 75
    0x1d0030804031100701110a4900d00140c6480c40044645900007100c0c240511071000c071a8440e40c0f04001114a1f0940185281d460041e0551440c40d00d01100d4a0000f01c070f000341e48204c0c6480d1181d00f045600c0380280c4845401c4a2240d600744000e240c16445034a1a0740309050009030242e6130350118081d00c803900c04628040048020031425400d050081007030301c0385400058911441c1c01801c1c1410750002c0d000c05030501400f000d600c00b0036402036100e03002a580041c80130b62030300400c0452038402c038000218000068241401c008821811b17005d0352905003000f00c040c00b102e00c031040d421500008034050a444c1442945185a03e60f203003880005002c41c1d10072400603803032900403555800d240040e885010084040c0d4800b6410f0000181555503140c41860440d9803a04da200001c1d03d031801411002d0445032900160038100b640000003007603952007250307180c1c6580e0f80e140200b000300e82c101d114803200d482010b809140024410b00441790710644040d400011103000e10042032501d41c08d900080c0c8800d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598232688 1250 598231438 598231441
    0xe10090824101a300103060b0f031f06090e0309011d060711030f0f0601140f06040306020a090305030415031404020f060d0603380112170405090708 65
    0x101c44810066a002d5522594a242e2a280c58201142d4043e40c203000c941c20740c80820008100a0310480d440d150f00024040700c40e50008104a2440148080c40101d540c4c07031030100502c81605029100e034103a408014041c2105c4000051080c82845501800040480ea180c602155a12140c8101c80000001100454a5040c035800150a4000c10500250301c603100e10250601940c0d010100d6000d03507800000304032040382c140e0100c0c0c5400d0f580a07006120b40500070075510680c82c001005812140016003059450f42001c00b40300705a00400c0003160032220401c0203001140c56500103000c40011440c048440c20b589445143c01c40d04150888404010f02004146071560715000b131507440644040300500c541450703400955a40c58400825000b040085140c2c41c204000d54080401140c01410310881b1031040220514401c1c0070725640d01945029840d4241003000781050b00f4140d070000002100f80c0122038640000144540b80e00e0103e082c020400420340e034039150280d81c0681c0c0151a0122039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598233938 1250 598232688 598232743
    0x1308010204064503020306040b09011a06180109031505041b1d06130212041205070c0605630f040e0f0f01050702010c0e100908 56
    0x340c4900b422004a10f81201c0e403541650000080c1841c6505402e07100380c08403801d1070325407507040500d07a00203581406044100003e20040b60380c43d510400e007040080010190121460400008110035036130081010b00004810100a00410ba403202c414101450a0760b501d54079a0101d0306041c0c500b04440f600c1d2400d0000300314070103180051302141040c01c0319909003884405407490b55080e0131000b582c07010001296990300c1d040190000f10724514402d5640307100e01c900c076400d0f60005403401c480184010030980302c614407900c2521055036200d03e9000740e00c0c0c50010300300c1da0f980180000c0e030702e40f4a459228000101ca20042d42541200f14501904040d00601c1d0b0420713401204a241d130403058811400d42d089185041a0081c4c000d4103c0324100700b002c044012800a045080c0c211003e48100b00941e40d10000004141c09180c801350000d11541e070355000101d0907943c400c40e2040c042007003014881076500e4030000000301d00e003ca242841115554a120b140b810313030403e030000d08120380080700030311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598235188 1250 598233938 598233947
    0x7020d030c020a170706060306060b090a0e0f060d140615031006060f0f030b1c0b10030b040809011101060902040f0501030e030d091707061a180106030e03130801020406 74
    0x1076400242c009490404816295024035900c5015a0075200100140358010069250700640203160048020012592590003090060f4845420144035104240c0300250351049a04c0301442213400110904240d1100024040c0341d400140c4200e0311986542007017402400108a664407031810810300000f5180440c040c5801d00c90b0406000121604000d814440c0507041032040f909820b2a1904200030741c8641e408a000b0300c5407000041c1d019251441d03050040b00c8621480320700a004800c641b61688803880112060486440010032502141001034042810200031b0b05040e03406040121060ba00300048908490385a007041d2442c2368082002d11050648040c020702a203428201000b54407017800b03d0641c0c074000d070710300d62002d6600e4200c0002042044420f100c043e800903900103854075113034074006020701306113401480240d100c211403000070326102580203c1078000d0a101c24481e420200124058a01c14200c00070a100170004034102095004500009040140c001610369080840090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598236438 1250 598235188 598235201
    0x60f1209030f0a2f0a1101020705042a050c0604020d02060d0c080121080306211c170f06040b01090f14040510150c0201120207060209030601080105010b071401110307020d03 76
    0xc1ea18580d452040130280006000c0c071606030005103c0404450200040f441d1500780d030400c41d0441d003081c44801e0608062480d240c200400120400c0c1c1d01c044080b401c690602440c50341000755407000c40440c0142c24000b040c1c1d5a000e0001d0100d81c9003840142041040c0e4040455850008040fa03004008815400d050000004154000c00c6107419554641020501020340321a2003030200ca0006c07458254138807100d14a002609040da52604154100c2d000780f03024421001e00030681008a10300034105c00c41c1403c0c8924510b0106503c252250300170300c40100602c42c4d910f8144881c0e1003010405034402d422850040428191840d107140c1c680c014082500c0006d000301d05903c010400a000411203041400080000b03480e0800c546039030740c001298150000180344402da40300144003024414943c0060240c1c0c84207500f22912a669101240d00300c2e9030910405940c000706114960000d440341c511680c034003940d440003184030b070442032901845d83d20940b09600564009406c14054542600411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598237688 1250 598236438 598236497
    0x60c030a09061b030305090c0a1d01060207150f030914070311090702061306140f090c010c050d0513051215070903030207150201140a0606020705060f1209030f0a 71
    0xc42d00161940803c50100100d080040a1503290303000110008070400c06d100c2c2c0c42400400311512a503032101c2c2a00101c200118005402c025113001007000b60001404400711840c4461124502c4030506040300d5654044156101701921981c04902081c031265070080484103c0010700000392a40c64074044a010720072405000d080f6140400c803285402040c0f0300c1c0d1088034001c2010544030075203050001000e0040041075210501c5040c0000c3e400d01c00e042c103100311007020440380d445880d640113490000d01c6410090041d0700018a5000081c810005410490681249206030340d0300d41e000034907c200c421143c16295845a44a800713800345403003401303070080c02c0c605100d0070040c10b5442c000d483c0d01190180203c1043e4400f0301800592003507201c4000c0690a01007104281040c803020009041c051240304010b00c81d014000c142c3d4034290301200c2d1005040403c140c5480100d130304a4400900090100c507250006214070b8034a00c503400020b04c5485c0c41c40e03507411a6895110201180390b154039010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598238938 1250 598237688 598237697
    0x10f03060e0c07170705010504140102280c02041107330507050d090c0302010f0e06030402120705030328091809170a0804060b09060a030f0302030405060c030a0906 72
    0x400c070440d0074444041d045040d9107103240e0f444965040071030b0070000807881a14050000100c4000f03100d0198002307800741d07200c0c03c0c1d54110320750000c601600341e01807840003080030000c0c403e10f040c1071400322265542440050910044820180d000107084442d40a00d40c7c0c00b180700051443c1c00c00441c0390034811408103c9402010100718000c48009000628501500c1d50383e441c000b20320428080c0381940c0107030100700380030311a182c0c0f585080644100e40c1d1008034003180c0d81c5080080707282d0003a0f04410110001a05046c02c42d44e86408000500810300c141031524000c1c40004220f03070301c05100500007003c1c000d0107041d0004006030340c0c2e4210780c91008000c04102c110b030300a000840740d80c42c10380d1100105904c0484c0f00f61050404181401143c1240e4a90050008444619541141e2020320617405000200414460305046c001d20000841381d05500400242081c40000c012414110b800340c001e01c11203003003540f10b01c046038540d4011190803016500208540e940c0e9940308440102406d030500c2d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598240188 1250 598238938 598238951
    0x10f06060906050d0f06080c0f010306081203060604150207151b060911060316030b0f01140310120804030b06031b120309030a1407060807140d020d0614010f03 70
    0x1004200741018001e0408001000400e03028844a507002002c10480000c02000401c0e525140343d03983e4620041524020030604031030b505030398000d10510007101c804001502190001e0308103a442da500c02011540d00101c24000401e4101041c031090704842280d400802c000340c05c00c00c18104070418040c907001003042c10303c50400d030840003441440d80107510030400b140006c540d260080c50f0521030030442d508484044204690043d15503a00100002640c0701042000641014403030101140d40421b40420030f9040108a028044e000465221448001047c4543c0d12501c440c40891950a02561008000706040c41804000924540c100d8401c42c001c0c521040704002d54101c05616101c0f40303103d038241003021402450180f00f1140407110003400d4406a0016207850605c295010658101611a041c404520b281c003a0380c0b100d005500903240c3d02c61705000d66245d8040c65001d0503154034000e4080c8050301c0660a82e0160f000540004043d1000711200d0400050400d01d441c1c000ea07007010705014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598241438 1250 598240188 598240199
    0x503130f240305040f02130501050a0f150c0f050d0207260d050a03140f010e2d04030314040f051c1d0105091203130b0a0e0f13020c0f010f06 62
    0x1200726100021504012401d0303500c5060410741482c4800c0d020707406c84054040c58021218680c0020706031541100c41d101401d8a403120900c2205042c0a420075511140054210050044d007801801c14400d61540d0802401035a8080c208035a0905000c05a400f05109000401c00000d02100500080c410403284502681c00d459503030085100c40c00c140500006d158142a20907004540119900c0681625074240708542801c2da050034030848074a064050003144001d545080ca81c20201d04440c05004201d41e00788c0c61541418002c0c10840600d940d55a240d400f01c0101d00645d407140e03010f140c0015105180c1d0600e5030406c400b0021030306000501c250182151500b014991a201c07012103000560b01d8851130059031148203101c2e03400e0703108282145800c00c255001008003801c03280c48001a2405030740f504424641d00801c039810b008100c0e52280d01c0c075541400d60303d0191800009250440261030b002d120403c9900c4a0600720003600107401200b8000408d010300c990741046001e00304555031604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598242688 1250 598241438 598241489
    0x1b05031c060b070501020403150b014e060f062c1807020705030705030304091505041107030e01020615040c020a0204021c05010f06080f0a020f0f030103031b0206041206090503130f 79
    0x16284280060704800e0318060106400c2c1c10801d0091001c040003400160802c2d01403030ce40192400604400d040210204580c2d01202d502c6080b287c50792a010100c1c198004100d4a11610801e0142d00c581040c1e030a030201d50328080b0750140402504040202401c2542d030080c10008941c000038020360005808000a4500100302c500f202c40041001881d4845030107010681c03020303640f16950007802d0010f1011820002c200400c0c00e1403181c6c580094901c2007100590319020121642c8a60070f01c10f94810381e09041c641c00c03202e0320a2580c41079036426107040d40042c0403600b242030400d030303085041c115a40e200305803441707030707a01504440d21101c490a1621100a02d200da00400051101c4034075400329400c07800c81d8060310b0400b1051010300380c0f1031035500c9030166075410074030040c1c0000700011760900700d0301c002d9032640b44540d40282a041c41e2504210740c000016840d100100e5280740e0300c000d49804200d0034400351039060100f1104402c02842c1c030410407a800e0f10b5400c01c000d200c640108550220150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598243938 1250 598242688 598242707
    0x4032001020c0f3609060106120e24061809100e0f0601120b06040c0e1203130f060e010f0f031104090c0905011b05031c060b070501020403150b01 64
    0xf03c41c0721104110760b40200e40094041c0c581c020b0807444000490124400000840500406000c00c0c50301d1951040c45056440c2e8081c4240d401084507400a51340c1c0060740d070404626080c0110413038403600c0c42c0c1001d403148400041c03944426000c4640a1101c985407400041c0c2c1c02041203007543d0000c0c10900880c9440d612056495042c02d0303034402c40102142414880d4205000404054440d107603920301c035440156000340c0003111038021040001d15a440c00b403240700d0b5070801981d43d5000c80e0007170f1001c1c07100700025940c0114051005203c1d4007648404203050f18050800b07803101011103884e09001910a1001a030941c0c103200015060300c2e0406d6000f018480b9252081c5004038600e244103141c07045601c91500849002d40c103043d00690056000092001202e0007a030b200762007081e403100c8010601d41c20000050058004000104a601000690315100309090000040a55540c200d4040ea58041c2004844694020804105000001c0130448a000b00884140700103002c1c03800017800c4040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598245188 1250 598243938 598243963
    0x302180d0203150a050a0606110c010f05090409140c09010e041209030b160f08060a030b06041d07060e1504050420180f0406080309010f030f0903050403200102 70
    0x90420380c08055590800842c1c00d0f0300f808030540c6209003865600c84000c2e10084402c2c04c0402d0510000081c0b0078460107120a045030302c100a808900c2c803800044441c0c1007119907641c2002803e0221101c0b50303540b480b8451440340b1554481c00382c50081181706040420038030126101c0c941c0d1304010000ca02c841d425684c0e00590100100b415104865429900c194264101600ba940803400708544014120809a8140c94a49550010840401040b100b900003141c0c004d1b0803180c0d900c001c10001c0d03444a080f6420030300082c0013081441c0c4580c0003151030094065190300640c849202045459000811050504803d655155140c0b4945404030711901c01c62003001d0246c0d03514003000c0a04869140035015200010a949a032404a8040c075400201c529848602c00c488215400e0ba040c40e091042c00e0071100c40030f002d9424220900c4c015102d0070202e03d014810305450390b4101c04080094030950b0842440303511020744403401d40c102341e42c12206140c900300050035141803c071566a00003919085184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598246438 1250 598245188 598245199
    0x70203070806432105010510050912030a03140709080a0209060315090607260103121b12030c020a02031203070302040504021206010206070c0f0f0305070803090c0f01030218 76
    0x80340c0301c40316192643c02c0a003106500c0c0c980c925442992022410304402d8400d5405010813601d1003540040b16820321039140d2040150b007501500038041e50103020011001005190607100b58443d4a0031a40400260720000381d0381d07074a00041d8a242291150018003e142c9000d2441c1404502959402c42800192080c2400310000c3c80c0e80d80c00300030402710180304003102d01d25800d0004186a5694003074900381d001c00e1440003442942d010403040180030388400384d010381003640703103480c0d4000407034520394000104042890b001404050071801c0d0329840380308203c00c02c03021030f400000804440020084408542003602083c0240e58001208030080d00103000c400d60703e0305c46074000d400910840d0300c01030b04540041400591200b807010084d11409003a02521402d90303429804840d203641750100108415904404200030030180406410100d10a0410030302d0003900f034552116540040720559000d61102203520070034103101c42c28000081e33080c202503041c200050302c07480349075000c3c405183c0a50f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598247688 1250 598246438 598246501
    0x90a0e1f080c1e0613050405060f0d080a020a08070c050901120f031d0a14100503100b0306061201170f010e15040614010b04060e06040f090e0106030c0b070203070806 73
    0xf0b1800d0b115010011000a081ca50b1700d00b640704d4903a41820081c407526100314079101c0040c1d0329040c08042d040c0710440c000e02c03880103c00f0542da00304094201008034000c521030707010240001125540280041030007808400105d0386028200103038501d050b0440c82d15145100740c03440004500a03820034507198181441c8100010810041a901c1500504180d011008034070028840c26410303044440c4001c1595030f8240500c8415040d505480103031070b800b00f508070b50b010030000e5407610070103550060070040c40b0a1404000c108800c0c0865801c1c8c00c807440b01286a00141120501040061a841c68910090100203844113999444440d9411901103640070040080c0401030907910003501000c480c6001515540c43e404141d081c3c0d00315010f41d0740820911803030610300d882e148090310101c400a010040c14141440c86801c040d0513040002d043c2d035920b811000c000203071980120005804a404800e0322440391740101860100c80d9445039140750010024005005400c4003000d03001c410074102040c59 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598248938 1250 598247688 598247719
    0x60f14091302030610091d07171002040b04060338010e03010e0102090102160b0a0f1704080c0d03180f29070f02062406090a0e1f080c 59
    0x50000310070003507143c05200104040b000302c4008042c01d54034580b0040000440c003520400d0305142e840514600e0358007041741000314160040d10f0304800f920500a5600c0040034852640607a0040d40240f100305501250030f00c002a814403400360380c20a90104902c9a00c0c2200c00d01c02d003021400c0b40018804a000c528040e2640a00c001103903034000a8000c010a400e05c8420034000d400c050310450060048107049140c451180b0059800da50f4102c103001d01e442003881043e82d80a600089040a03c00880030751821052900c140ea40300b5402254002da5640b00504203074185004442000c050500e0000c66030b03150108907031203d803010782c0515491046621400d000340908907150300050f808411072400e00c4c01808503c04240140301c1512098643d40c94440281d0b1126000c941140c2c250350003e131140c01c0c00502513000d014412000d040f442c5052006400b2404010042c1c00005c000344002d42030020743c85044010445003a11924200011030070a80501d031101c803042040342c82914481070a04030f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598250188 1250 598248938 598248961
    0xe010e040e011d01090519030f030506040e03070302060f010609260c060310080601060503041a07030b1203071e1e020609040903020606030d02210f0708030c0c01060f1409 75
    0x103842d2019012034044142c0b500c503c9000c3c001c0824200c03418000c4844c1000114072074084078481d41c4d45901e404212001e044001c03801040d0080009034850303202d070f6917004031500a1000384221400307031780684560314000400c0304040748103900c441c00b0001002030800c200310031f650600c0050f01c0303880c0180300c40d6141c1c407029503c0d02d410a032146a202c000081440114070303600e01a42c045984400aa0b5016a6140313030940f40380c0411100900610114132a880c50000b1110b0641e9214519080c0000c2d0002c501c3c0c0441c072002e0303000030841061b43c4002032503003c3c49200a02d0664a101c1d00c0110881c4208036900d0540026525800c641e80505441c3d0750001c558030319064039030554001e03108000c0340c042800e00a56480d815075926000b0700a61001c25042440403454004401030300d1081e2400305d0780da0503140000d51052055440c01c0d401402881c00040071140294000c400c00c0c002d442c1c0383e110f19400d060840e41e01d607001d000b2414041c00c08001e13262011811114004049401a60707584e6050916076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598251438 1250 598250188 598250201
    0x1504150e031c0305130b1f0e0408090f011707030c020106051c0201080403050d020304150e06070e01110709060906031e2027070e0f060301030f0512190f0e010e040e01 73
    0x8005a8402041080b0f413903c09412025810254411401082c0c1d50b203000441000d0927240030340941c404200c001014184160f4081444106240001103040256401003034601d060340c400d0000703603d40d00042c4046509000d031402914040b607500e0a005124842d2445240b103c0b400207042c44840000a07003454010001d5418401003080255a82e1900f4a4402100e040c070682c66450203281c048030362119007000a850784103180030b443e1410401000001034440d640f0308504040705208000c0d01146000050080d80000c001481010818500314a080302248009441146503058042c0a10340852851500c214442681d82c00c0700d40b42040034808610383c14140001c40081c0344e5035400b25401708002e9181d09d4410305803075442c40c09040c3d801d410001800c038140c0321603900680134001880400d8000818240e142e215078115181d82840c030322004003036006011103030801c8507802c84148c40c8a1f0803c15080180d0405e01c1e252001d541203c0001e8103a085601035035000d81d640300b600c02035500c000d40c03280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598252688 1250 598251438 598251443
    0x61107031a010e01120b040602160606080c0120071e0803121014010e040b010215100602160b07150f060f0915120f021504150e031c030513 61
    0x1906400410103818029001c28030908040a111000003d03048407918030401d4660344c4102d1000c132903140d82c0c0355800a50042e40e81d01001007a10540c90000449522880f030041c103446003e892103916060014104920300d006010401140c803000e000c0162001c90b010003680c49944541000c40c5440c010404484415000b61405100c0020550203490822180c035105440c804503551440e40c0343c0b042e20100518100c6070a0100303c0e002003039085072506401040d4400e4040c41115030904120541050401083e1a41000e0212550060000c140e0511641d00c0241c202680c0c0155145000d4500c0c0396407003111006417011f441a4100412545140c011190004800900303104481d02c5e07203440c40d40b1041070b10901130480c0c034146006600c4442c048181c1c08035010247c0300e6050740050348a507072510004c3e0b0412a403021860075034071a0318000401900181c10004034a400012244d04d0107811441458601c034880e50014584142c03850014001158044083c0f81c003080503210203034243e0f0300421041c0c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598253938 1250 598252688 598252703
    0x406030305030a0605010203090604261509061f0b07050f120d0b3c0603010311040c0903080306060a09080d05070c0906141e0306040302010e12040f06110703 69
    0x515500c8000345014880c410b20410400d65903800592356441181c0a00e40c01c00c0c0c003030004006411801404003001403001c1541898514580b903840e00709a050288519981e0b80034044c003401010170020300d0350000505000e6210400b10f40c5035118480351a01c582c1d4040000082c00e83d0802ca000d0020016aaa100d011101200001d001e41559a00140180901a071070003d407411149043c0c2d004e50602a2140348011400d541060100d850b071060442624645a0045075442242c6500004500075030141800141003450386040106444000d2424020849020424800310b18120708036074010004070740301039403180030342800d4850300c100340c0c08000e16000b040308100110750000e0040858030b1041d4569020a900c0b4034038503040364103500807001c0f609600c00c01a030356410300128000808100440001c0301081a8001900d804001c41d4100d0060b512000040408007007000f584018102610513982094140100248000050b21400041003e40710b0040c0b2007020074840103010315041500d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598255188 1250 598253938 598253951
    0x603061314060f01062c040c0c0803010303050a030515130c11010504120305090318100e030a1b0b0a17061c030807170103032c0406030f051002090a12080904 69
    0x108884050034885c01010400c01c010046000f044c1910008001822040d110b183c08500340504c0024a180c045000c14080208101404a800d4001a40c000c40c480d544003a5510300c0b2070401000d039a006081441b443d80340541d8049031381c0e10100d24002881a0390303800180f81c6921030044924110140c00544036510b004140014402e003080f481d2121030b01a1000c0c40700d52140043c0326520320440e0f0020b60f03141c030300100c1c0e00102d184c1459122034403000d82c40d00000e90303080036002905000741da480864280b0000c02d0002203a192020668004103494400c26040494402c1d029044c00c11045040e540d502d094000a0481ea4885210b1041a003025800c038090305d00e40d20703015000d0749080d02e1840c040340d18040810380700c182c1040c9240c182e95041c0d8528400c0c1141d440140c2c01012440188000a03602c00c1d102c100703988940c07240f10f00450080c0c0c409041d90000c5d06001e41400010081619a076004002c5100544c4031201e0500c12900090620020030509040000070b138003858800c4d540c01414181c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598256438 1250 598255188 598255201
    0xb0609041823071215050c03090c10020a030c02040617030d050901090807150e010c0203120903090a0509040c0305010c0306210228050d050708070b03060306131406 72
    0x540859115114100e440c01c6a803072401441c0b0b44a00c01c040c040703595400000140905007118010010403480b84500501c0d8011020120050b14000c451003480b010000c8204415800208100c2168600a4511100e100d100e000c00035100c5000d40b1018082c408940100c1c2d08648456110100414414100c02e40c090000300100c1d440750303c880d09039190380c1d0900010802c207900612440a09903840072020f460b1154a995080c01c3e80c8030b000403004000d650b0789030130511040a0084004403055507000d55a100c000c020400d90714040a082d00d0841e0b4814403c101146e112804414241c4208448120880e90303a854424030184580e003000303140b9403c0802210300c032601500710700281d030103040c0030b159105040c002e42901c0440010001c5d42c00510901c0342404041c1c3c480d1b031001c0c084144002d48a02c16240c00100310b5011361102c0840c1c01c2e1744115401c114800e4140420723800f416480c1059899418800c0000391784000252a41114007000d0828004011300001c5c0c00144140c002c007503130442c0c0f4220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598257688 1250 598256438 598256471
    0x1a19050f0c210408120f061804050a2004200d0b150a17061e0123040b0301140904050a11012c041b0206040b040201090e0c0d0b0114030a0b060904 64
    0x420302c29254039514080768503946d4407141c02d441107101030079181c2400c40c6072142442d0f84030302a005032007034051110f0890109c1d446004c0000c01800801c40840641c030b8120901c811242102c040c540070014405980e0b480300450b0702140d99071483c111001c5007040c1c48200142c0944044514900166400078508000e0740d0040030310100d100c150401d00d140d65840d1014010320302c0b5100e00f5426100a40c0344461420340c014043c2030700031210115090b0040d0540041e050550348950010b000422012004000b40450688007011403141641c107500c45042607540d05660b00f00c1700754010088281627060001c2a485840e8804000320510002e03807525414807405e80c1603e10507026203000342e05222500450340e400d01e007462600d10050340200049d40d03480d02c9000d100310018000b241003102c48940014000c803800206401040c088000c186d80382004200e8208940440314114184000f46845859011804043c1c0744d01010450011030305214240018186104419116510030b14110011081e20b03500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598258938 1250 598257688 598257697
    0x50906180a0902100306080d030509160321020a020117310308090105010b27040509033a0203190e0106031514060d0305071a19050f0c210408 62
    0x3e0b120340c8904d0440307030000c0342605e0840c010212140d005511409249110b540420360014184c42590ba8520204200c3d03542c0c044c0b01c0e0300035030b410b005600f01b4003400f0441c1d5218041003001703400100214030269002810709881d00048220741005040001d9002c1c00f0023550040c120141c0040001609110380300d403040103440c0005800080e0307810002510000144034071410386004c00796050600d03036503850f03c9007690040702c2040700040104400c60855181c0f8040c150059030f98402840c0c803141d008203d6070f412112061b9a86001d410124420300e01210440d40e4100d403d406880541e513560b4000420840d4401c226102c00700030700c0c00b060301081603410741c05032065030b03c18603810300b1038600b10048800b41c2c0c120894010030840120b0206613545040c4c10300a0089204c0e00b0840d0405c07120761602008150b18140c1003045400400070404802c48a80fa08004400e0400040041d0304140c5108032410714003c009640c050340c0003c550a2100e240000303802c2010050b1350418091800f07107480c1c11203420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598260188 1250 598258938 598258943
    0x1416030c0e010e0d21051b0705010806090a0e120c1204050310021606060e010312080f0106140403080c03040e090f0a11040605090a0504050f0307020a050906180a09 72
    0x2910032030380041841010340c2011410141c0d65800d29460780402c0200d4603074a90783c200e5002d0726400e010820096481559440000d660f11816100d0356100d80c03503201c401c003192130590703a0f40008100740b0003a81c00200311a04110306907500b801c585d6422480380c00620303034250100e180344201d10259940580900c010400a1116030a840c4440c272801c6200304640901d00031640c1c940c0000c01c50061841207540940040351429020541c400710075213400341115030a1704208109003440c0014418800c4060b0749408908440c90400050715158a2a0301103040600400040243d40c00500c0148043e172002c0c1d50246400c124110b030384a50a07c0859a40d40c030921a43e84070020300d000050600401154510700a08464080c1402c10b40c1d42d5103c1c0c3c60000ca02d400150700c25900ca00101d5552607622070359200c2d000300640000c8a05090804d94901460080c640480798001c210030710040c4c5500101c17108640c8240c449140c9500c031800014078014013440c00c0d039900b0110404221014205400c603051150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598261438 1250 598260188 598260191
    0x171606120f1a03072c0702070510050901030510140904020636010908070e060607120305070e150d0203060f040212250905010e040905010203150a080d090e04030201141603 75
    0xe507941c0c80c5110300741c02c0880741c1507038110b00000120421703500ca007403130360001b02481642c80c0c080d1100d001600e2a4250a01c500028a01150088032941c042c80b81030740000b101c1c5689042c0500e441000c4015501c141450341c01500c003075010070115154581520b9120f450b1141320403c0851603143c01c400281d08034050100c5944062840c4891b5000c2e00c103903c2600c82c47c402400b055070030032410b0300d070100001e054140c002104108820208075901d04002e0304a450356004142410329041c01080042510303005882041e10303440c60300043e0000d030112240c451900b180940c40e581c3c1c420000d03800c1301c2d28210640c1c000b070001441241032544013482a00c1054001c41c0000d002e9240d0b001c140d100401c2a4254010a0b4030039020301441d0301440003401c03020001040800c184100390365450998106541c0f00032880d035085241d00052070007450480c0a015503d0003000ca001846400800000741d0384540b04090707803148041401d040c0700b0340003c0b000e5071107065090000d040c1180078550700c1c2641a00b280002e0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598262688 1250 598261438 598261453
    0x14012d0501090b03060705220b0c0c01081009150b0d0b011209030503010e06031603060605040b04020906040e0c0f030702060403030507050a0905120f16171606120f1a03 74
    0x100e825114696080c3c4002d0001c06807507450080558455100c0221200311a403188014000d500c6054006c101170300b006140c0c3d030b071200603003a605480c1c014130807201c1c0e051202000801001d5840509004115442c030980400c2c60b42042035210403100c0c5a400c0903924000c0051342c2c04000010340c007c2515172100fa61002240c6c181c15141c1800c55200030750040000f8000c20040107841d12004407540c00c524003e040d100901070304000141c09180719401101c50a4807041c00b00518a02849000c4500b4401d950651038001220000f4a007480795024103070010000002180c43c401c4020142c58940303003030300c0a995582c00c240340040d40d591811181100007a080c8000194414420010744440310282d0716161704050624041115242008240d2817081c81000c1d13407a010304008108800142140c4200c140300c1070700b0441c4000c0200c070003070703a0f601c0300398042c8501c0c2c2c0e02d9040104551080316800d1508402c460807001d400c1e4050800e01c80c029442500708071140f407003159a601001d8036000200c00b00d8a20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598263938 1250 598262688 598262699
    0xb0f281401080c0f03010e040611072109030f15090f0b09011802100c1103010903230705060c070204140108060609010510050409091514040309061b14012d0501 70
    0x30f034460001400c034041028001013000101100d040d6421a01c910300c0824040304610a0a809400401040c3c41115510414001c0c8248481140c0402000da24145030060709644442d4100168034000a0a148280c81071809403101a03020180c4568804004091501141031140c000002524403030465480c3c0851061001c8820512959807903004d0300710112961031580c240c0e80108019810760b20040411103c40f8030381e40038801c0460841c842c4d01ca20300e5040c0c8027203202d040d40700840d40301807001008000c0c04011a90000b4020b9005110f140304a540f441d0034408138010740150041c1c4068000ca00c000400e08190100740c091042c0000e95540d03119a981d03c08101040c403800c852139000c00e03020041030000059581011091a0140c1c0c20000e046111901d01d000300c5103030038054481482000140810140d20100f420001c002030b11b001e117107a1302465000204c280044000400b5010b004403603220340c000a4001d2052030800d01c0c44000c4c8494200c440c40f0030a0b02c089400c98005161100102d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598265188 1250 598263938 598263961
    0x70210050901020301360f020705060901053102040507080105030c01021507030b19030804060810030c0e06030a060c030c091a160f0501020a210b0f28140108 69
    0x1200e59001442030158030302e0306050201d0340c84900f03c400b03400c0c02c6c03220f6003103a081501a000807028a4140160344401c282011414941d0180940d0300b141d040c54284081c50f0500242003009100c003110995812030a0300320f80f4070410807504000d4000e82040108030616401851440c12a4070a030162841b0581580049803105141000c42107580fa403c0081810350317100340c1c0a0700103280041c1050605286030045d121029140783e20450b1110000213091003640e51000009070459003040410360300c01c1c10f41e65040801841070203190841c0e43c07440002001c036601040841002500541c0410005101060040203802c643d880c0c00c01080080b480007414041c0080241841e00c58005c1d240c2c140141d0300b040b100800c1c030a100a407840344541d2220408501c0a10040107044541c0e221002c1c001c407403440701109071a030100401400c5142c919032240300d03102c4001f020b80ca00e0f401c03a07441901104070031503103100f030350600c4600786103140120307011905901000032072070b42290076240e8800a50310740585c000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598266438 1250 598265188 598265191
    0x50d0201091a04030903060e010b03120a09061b0206090414040c03020a0501020f07120f02280b1216090f030f0b100510120204091103060a0e15270702100509010203 72
    0x10001761841504002040d10b035449001448a070704008a0441490f5000a240c0a214400d280c5009000101c80b00c03025042224400280101e08040481805580340c0c140d08000c0103601074091b40b800185000141d4942d0302107044460f45610070300180c105410300105d10307901c80c00102d01540100314045155030000138003200da0441500280303841802d0041c8440c0d5592200411924580f03030042420050751203a01707109a1a1038040414880030030204115121502a030181c40c02407810003101e5a10400b1000899211922410342ea0540c100018202c2d540d182e2540301c80350031595140d01200300301032050030000e0280201725000d1152900c90140113507508500c109036112240c50550010a8025517070901c45c1091880d0041c10309130750715100c10a070342d00c000d46040034920010401030a450b0620014014140021008126282c10f114130780015034030406080c818040c2c46074200c44848030b002142019000700a22019a0500341c0c00a580caa08007901c0300a42c071300381800940200e105100b40e030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598267688 1250 598266438 598266443
    0x10c03020c0703060e0c0301021207090b16030c030e04022b050121081c0524030607051e072409020603160302090d0c050103150b190c050d0201091a04 66
    0x801d07050f40786035a00070040901e010f82d0a110700500421920940c0c0c28400b40c400041b010b55007842620300414020103180c825002601052024403041101c1c1d228031000a260740c0e4107041880c400c44080c2802e4900b02d221000581c1d015000081c807001e5004a01320343d501c0560a0641d0400610039040d82c40240d901c02d010395001c000c1d60204c481400c1d000c05030040140fa000b100d001d443e000700c914a840c2e280341c0c6c4114140e01c4580743c9040c440902000305e601c0c0c0342c0901c024000c9134003066240000e515203101820640c108080410007201210602404030408103005074000d17a40c8c0c1451034152807448a0500c07041030400d040050b030309198070a015012590398004c051a28654488135810506617844290408059007032100c3c4102d40c480030701d01503155002e540c120444500e000001426108540c250a801c1c81d05058200141c400704001e5540c458120510742034001080c0c40c0c00c40d44135400c0a00503040b4031810740c1e60380455030107502501c140c40c028805082d0170013984031034500b040c8099500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598268938 1250 598267688 598267693
    0xa0305210603100b060d05070804022814280e06060c190804050414091c1b050c191806050102031c1b200705060d020c0a02130e010c03020c 61
    0x11096081c561000c2513036040240414142800024180d0442d081210508041a0004c05010542c54824009880547c200560003032411000c1c5000d000e40c40184900700201542c18100c0d1415039441d01e950a44850001c09032144030b050301c4113040c9180740c5206400c042049880481d0650804004075405e44042200402405036060620308400c0750f280020b0303401a000340000704542c0e445000d0041c2080004141441900b81010058101080c529250525002c0400307002001908403105490310742c020040c4007008402410101d06007403801c02d07003903030140d120f4042e1404100d0b02200c800550b9440421510b41558883d544402c9070014050f49000d80d1050000022004104580000070884880c0104201091590070b580c8211090944000300701c00c444100c0034032548101c140855410a80205036041c50040842e01900c56070805009450300010102030500081207143c48060b0301500140a00342c426080d08010301d811700703601c070040d400c0612842034103104c2d009803144950607901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598270188 1250 598268938 598268953
    0x11e08120702040906022805190c080d0c0f0306080a0b0c22060507022707080a0e10090302010f0b01140702040b100c0302070807030c060518030a0305210603 69
    0x89810385034012080c2260b00548601e030f03803400988240040c20045111413a40d09016a0100600e03000801d80c1c800341080090602813010211204035000002c6d51041c1410350551009091003991131003001c84184c01c41e82401090b84050340e01038861000306040c1e5908216041c3c480b12100c1c0c6131110180c003c1c0948600b80040780b0900304410040050740308486201440c0d941021022100c025103078050030200b10301042000075030800c0b0fa01103280184012014400c5175895801d800305010260519003003109000005a94100c0c81d0300c8001520310b108200c1b0b404000f0b40ca1040082c01401004400650170700c858803440940500400003d900e05031500f08800898404000c200d130000c0760142e034425222080d2201a86034400c1d4010b01072251703030343e80701944010b01300a03140c10510350081d00c540e0300000040010640a001b40c00c1034030028a0315665989904901a48920642083c103601d4064104203204142d041001800313020020148813001c1081c2503006442150225a9181c03d5049040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598271438 1250 598270188 598270213
    0x150f0302090d0b0106030b0a09090803010605070203030d05040503090a060e030d0e0a09061715040308040f02040902090a0e1b0a0e04030239040b180405070b0c0105011e08 75
    0x4025005800d4042c0851408500c0760712a440802e5003030707000c103000c680d41d81000388036410401080d40c0a403800c00418420f59001e580c6201581c0320502c80e100810801090050465030144229003d40c2001241030003d4105030808540b640e01c8010001e101b90004000010343e5802459000541070008014146aa84440043c1c03000c86080c1aa00c1d80300d800c0400101e288440d82c0300714000340842c0c5500b4003061210258035498458603400b40d258203610102004002a4499800365100343d1000d0102c808a046d0700c045005040c100c88005c0d40020700008009006c00b241d80b042401007030002c1102c05d0007090080140403044810802c6170030a91242062218005410a46402c103210b4411240e1010700b4241c1410307610311181e0f0f400f415010703a4107000e410041002d00c48200f03007002c4030200410040c40c0e0000b000c0c034050002a07441d800d145000542440410b00c003000007400c40020282d500e00344030000c1d9002702000d0260200e0700d21820108a09458800c1801003130f03c00000041100a5161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598272688 1250 598271438 598271441
    0x12020d0204020408010606030501080c0307050a0b07061409030d1a18090c1009060207050604060813020325030b0c03010302181b18010f0c050606060a110d0804020a150f03 75
    0x144141d8110703400308400103c403031342485002d00802036a40c0c0001c455040c5072106050201c00c1440c1840703035022a40c14006c80d40c50051038030441c3d00c1ca54039140d030b51041c1e1806e074021b00342034866212907001f68410012002c00200c0102035207202e0790380400c0000c01c092005200c00d50700482464200c4070180c40b0400c1c1e80301c04882ca03600401b80c4401c07030300e140703039050b00040a0f0302101506000054406408103c07175a010040300d4060401200c580d41010704181d80240381c0c403002010362135010782d0b8506400039500d092040c4080c101c0702640c00049503900c5070201c1e001e0242444111003442007400012501c00c0402c0c1540d0691740c0c010403610b04815031050342400540c0280c10900c101c007140d00c2c0e080982403404002c1040c940c01400301403005000342c0014240007100380001c0c01b0302c0248003015002500118072254488411030321541c070b824218070102c96200341a03e284440c0d01c100b00303c403000241c21000b02442588201d401080280c0c1f5600e000d02c4614038a00354030085100c2c01110300015019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598273938 1250 598272688 598272709
    0x9091404031b02010c0b1501090b03190c05070c1716050306070c02120f060106080a0e120c0106030206030405070924030b060d1a060a0503010216021e030604060b0103151202 76
    0x140340c01c9482d102a61143e032640f04080c2e41f241d205400c10150b0341c1c141d5810200583c020308402c8d0100b030a5203402d480f0707a282e9207034a00304000d4007507642c04800e80f0207010300300303031004a84c1200700c45100355100c200704031034a4441d0f03902d071200d44a0360342850080007c00c41c0784020b940b006005010b09444154003503800c0e000300c1c00d040b40d01001d4000580301c2c41c40100700000d0308158040003082c3c2c035490610b000d010540058802d28080e420055440d400c05000901d1040c42540d40a4007955115040040307030040096400007075106400000740020b000c400203140050308e0f40384408011034103c10300405c0800c00e05d100001401c1c2c0b0744008c10804500c1c2d03111140e5001802030145401960f2a6480ca8213905c80400b071481c100e070124052103c1d6041501c61800584410740c02140390014282d100020a018088024030034001041500701003201405030180001c8080c003240d580703040034680700001d450303080c624900007840c110f1120603047e04c1c0e1003081c0c225542c1d58002c0012a20750303003e0140000701c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598275188 1250 598273938 598273943
    0xd200901051b03040e1302181302190b04030c0305100213151b140105070e031216061b0e15090f01170901060518040b190b04060609091404031b 63
    0x40c1300001360000240341c0310784540000c55021550110a1041001c1c3d0030190b00b8014443c2070600400602480c00e521090300f20750100d60306180c0f104200e04031001040d8a40146c070141001150000801c66010140c50660348604240c07050207011018000403400b4030039840d1403160459500b040b840300724000e02410411180788c0000e5105c5070240244d0450319101e400c862a1028210a46c8111000c0c070071940c210300c41d481d00e2905210b00d000060303516a5081041942c01c000000c12242c804003405c1c40f286401c3c2e003302c003031040c1c5010940c6142c80303140303c0002c2c0300031500e00e9016910342d180a402c010310425154800d1424000c110051100c01616620640e05000c00050300034100c0022503891441010031000100e1070609000030f00c0788007210a4821040d189540040c0000114500761140d0720030849507c11141901500340d11f40500b060070b1805070401e10b07140c0089038459001e02c040040da1000d10060103402420b060ba002c88510498028001951581107492480707942c1104030201030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598276438 1250 598275188 598275193
    0x307030507030302040b0310050f01140901030f0e0a05010501031b030f081c0e030405010e0402070f0f030c080d152c130501110901020f0a030215100b0d200901051b 72
    0x16203803000f0a5169000b588c69494001e81b546040009151038400e208100c0c0b420b28099440111240580321a8090f01b80d4142c180340d105d00d6140172004040d0702410784c0c03050440840701c03040c401d41402802000c00380820740e00c4801205010040701041100302080720340c0f050703400003c00419158141d50380c2140ea064400e28089001c5002068003a02860507000700120156075110b240074009800d00b0450503006005500602c82140440c05107540100c1da9038201071b120016000500e412900300901002c024026000400c2162584800d5031020103032101343c000081071591905001c2c1d00c060034022411411801d4401c200a8555180e42829000303002d85103141d00f82c081c5a81c801e800d403803503c43d110724191f0307010840100943c0e040041d901600c07103003009400710307005a860007074030b540c401a10901d0820ba190040380c0300382043c0d14420020301100d8507140c0c507044203031a22405040300c0c080540411108460813440102c1d0141141d800c80416112540b425465410680d119060064145101d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598277688 1250 598276438 598276447
    0x15070c080906030711060a09170903010209130c0f09080d0e040b040e0a15111204050a1a040c0e15010311090405131a01061202030604060f151106090307030507030302 73
    0x2d449440145025803090b484040d115090300100074900140204040c0380d41d820420b00c000400d1200e8000070041364501211130351852500b002c240648105605540c0040e4a00c6450205080350743c050144400150340c0c50110080d1444100d488031002c5c0110000ca82082408024032401040d0301400346d2130252000c9420140000050100c4000c40f0001034a0b4000c01d4682c0d0400120056020610034414030800100e40700e10347c3c03203110340100d074280000c900308400401c003072140030400084540c0e03102c2852800380319007102d00f141141050350111640100c00c03001191200f00710280600c11181080076584178100c0b600110007034230034103180e058004000c115505090f00c4500846105060507820b4095013034036440c010b144001031840000c15a203a40e0014040250f202c440c5426650301c00f680982c0ba038880c0300026004003100e41c01650000a46000060b10807112000303449184d11586404404000c1000c01e10f489a5088901c40090b8004000890010703028402500700c0c60b009140c0181007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598278938 1250 598277688 598277707
    0x4140703020304061d0d080109090807031b0c090c08090c010516080d060905190c05040e0403030b041d1204261216150c021b150708090406060215070c08 67
    0x580341005145c0e0625006000640e010030b0300003460030f004052444040007003074550f80f13034030041c0e018800008003040b041074602d048400c0040d420108007a00308002e2000e090b500c03c182c40003052461485000320703026030300007001840045112640d0b2035044e100c2a20b4161000e2242c0705c100c080d0202101c2c000703000c0c001c6c0340e041c00c8a4032420340030f040b0ac80f03c00105030400c8070ba00d0071100503219040902e0ba00f03002040000075403203030641d01143c40915610300d40341c60703a18083d0301421410054175005407a040a5580400401c0d0002c000031958000f80e8040302c0700308180055a22450059100b40c944280400c10310b1082c401142104184290a80301d01201d0051010601c0d4042c0c0500d01400354002034890900402c1d40701c04101c08585041048680318058010792510481c4202c11001d450f001400d0000d40c035001e030300008500e9200c0e1000e90340d007450711304210076410444626000b60302c0d000e0085111400068219210356110124211941c3d521400319a82144803508841411007070046886 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598280188 1250 598278938 598278971
    0x306150c0f011805212206090506090a0b070302010b06071101080106080103050c010309170708031906030f080c0c0d080c12041229010e04110414070302030406 70
    0x29501480009003444041c14144203080d6031070821242540d112040070140090800500c694403100380c1004041040b0a40c022100680225101244000803103081c0803c0741004108070405d030740450300c845500c1e545510610502d809003c05550f04540e490100740010072904000c1d28010b403280c070000c1000c2c600000821038075002914121280c103d48514420f00f903800c1203803d4003400300d5203030400c00766246403512603a6640faa400c942c1803581c0c40003060280030300b03281111030f034030111040541e40f0400c5182141042c1d00c1211240e209540c40d00c8541d04c44103070343c09800c0899400442c04800c5405944400b0380580c01440040c90f9840f804c0603001d034640311300d4034608000f800340f5110b84d100c1000c2c3d2641c609100761102c488801010401060001581983c0500b54403a04020b084c046a0700209517001c0203030340c0c81340001c02c44200100010300201020803840c440d074410b8074041c081d80b58610030700042e24079615050b03a40d40605000100a03d20076405142c0c0140071320000310f590100c60a0842 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 598281438 1250 598280188 598280197
    0x60806010320060904180206030c1333030e0601031505070216140d0b1006020d05070f11030a1a1806040515071106160e0f0a030602030615 61
    0x11054108500400038020300d00100b000c044400d416501c80010244001402446030000c458802c6a9850501c07854118010f20f202c2c00b1a805004280c0e00d0038000c044801507081301100300111000e0709004140d008920350001c240940c1c0001c130101d80c0c0d403c100c0c05402c000991448004242c0c1d107589103260340d4404c0091030f0086000364860a10042d043c03d0890999900911004c04d540c00750310618040c00014041c00704559982d1590009201c403c400654030000345280503110f4051501400104010703d901001111215003c83d01c101000400a40e514003c030729003d40110040250380b404240c80c40e2100150709801020f0ba490201c603580c9004540c13084107010000902c242d000c10500213692030030040040c50301d5000300480d141036610300b5504c6103107100e40c111079104200441d04841c0a0300c4503d000303c600d80b0903170f40d0754941040c0d14140c1c3c082180078400000d900d6851200c5900b0005450054000080c1c0004103627401c54852201070340c4050903036600541d00042c08003c03010f2080152 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 598282688 1250 598281438 598281449
    0x30f0d0b030f1c030b06120106080a0b04050a05150a06080601050306040f0903020a02210606060c0102072003010515030a030c05160315050a020a08190914011e06051804020f0406 78
    0x290000f888440000e00316281541c1103400380d20200070411f50142c082021504407116480c2420f0035a503002c01260160140074102604581081d00384840603c19400444c45500c80c0c10402214417004001c00c1240c65207413040d40c01186004000c52030139486000115408040030b44041401000c104664040340e440000950060300072000c02411480d107041c8100c01802440c08408480071480000c0341c64010150840d4403078070b4009800c1e03070402c01c00e406840c82039030002c901190110010080281844040290a11a501c0c1c0800100b43c060711030301c895400c0e1800350003801908481c1c1e505a56606080e01e05654a00c5090911610700001c44400000340d840386c2e01600c41361220450f08801d846024180310403840c01400008109035001c040694000030071070003020b40604020204000b4504280003810104802a1080300058150051101c0e0008000000c0d4004482880c00d01190740364020350354400507269001440e0314001c5062a0400d000502d1105004c08020004040b2401c95109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 598283938 1250 598282688 598282723
    0x411041401091208090a0f0506160c03020d05060114031c050307030f050a02040f080c0102300307032307080a1e180201020f060c0f0a0e040923030f0d0b030f 69
    0x403075140d406d05c100810020683d1b01c1c4441d0281c1d0130080042c03a2070040c042d41a01d01080e510104c4148440e450401001303680191101c40640070078103000d80c603800240a41c0440c4600e44910007018200002d8000361011134001a50038002400422240b81d400a0030f100c0400d912400c146662000fa442007500a0030301d072800503592071800b0103c00c07032103510358090090b50300043c900800c0c50b600819200b130524241d200c02c0100d2070620504c5034503140c150a0303002d1000e0001c001c110007140c040e806030601b115907006400c00301044811900f4401d100300c0e611b400050b00c003008142e1959064014042500f5414043c00c404080d075904d00c021107a110052894000d54001e02409550b0103000b5005112850390240196180101514a00303101f801040e006144c4009500e400c0760b8490200144100c600400c02c0c0101d0040d420009000c13040341403891600e04a4006620001c040001114281005c0491503818550703000802d800500440400729014003c1403020407210205200c0c880c240d07400794a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 598285188 1250 598283938 598283947
    0xf061e050108090303060607020109090504030207091109010f03050a0227190608070f03140f0115050703081302040608030c0115091e09020a1e0e060411041401091208 73
    0x91200002050368819070500641d14184842100040120381e031026060706d0b102c0c4d445a103480108c031100440d9103d810420328007401c0c0404c0580c08a803440442d0261541032203109202d6003414a144151804540851a428201568107029401480c1d1040d2100f2005050480c10340d12610342621061030442c10110b803445542e410300c0e001190050680c400e075286011a400d003000a0256600580341e0f20600c80c002d000d00c91000d220740c02c5034004d11100c0d4200d0034581049400141125421700030500b15010324000400c0f248d108034150b0b525280c26030749500003502c03100050b040e154882c46040c0d0300651102000315001000b040102095143c1400001e404200148042000101500031080d001d0902c2200d60302420705081a1028034186440010200c0c8180b0024062400540c0100c542e45007079010079104a030075100040846211041c141e8650b03440c00100800c0f2080c21030b03c1048903000340010b04c9100c4100607c940e943e60181000361925031116400481e03524050790803900c2410001d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 598286438 1250 598285188 598285229
    0x22103070e061c14070804030f08092d0c04050610180324050a18240c0203070c120b0c0c0a080f0c0d0806060f0a031e1b08130201120f06 60
    0x90700c50b0340c040c2d11443d2540040c00d1070b0388d0061854008021180402c10101c0106003848014007a01c10030038200c145404504280b4442043d03c88002c103101c510a008030010268103007040e0103401d12400006058551104003548140c03104119080d046031629440e02c0d000c000100401040f00d41c01c03409000680708100701c61520002d03108018000e030802410902c04421114403e44980306c0c4c0c9602864030204440e000c803000041000b900b904d0032080781414485840290044010031295000301c0383c0010791074858460240340310310300c60f00070309006010000035810407048014040306884034007551240031154403403212503004141907100311180010020195142001000b441d0041030174070031014500b4100055083c01004592985070314001400400d0034840d5102440710081005e6a902d03030103031445c01000030300e10000010390310025401461200c43c0034003001413040305025154038250304a81e00443e1040701007442040b10544420440089612030300072440030b800e81c02401d45010385d0f40c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 598287688 1250 598286438 598286471
    0x705010c02061b04080a030503070c0f0809030d1b060b0a0810050609011202031b03120301030b0a06171209060d0f0506010f1d0909210a022103070e061c 67
    0x1183c038180303228108000c01c003220004c00c00c074810039014244551665180f040c1030309c0030100003400612040da00303541e20007008070090241030703001c01c01d50844030b86046e010010740c2c041000890f800c4485540c2e40e41140000e07861303041040c02c0800501101c42d102c1d542c00e9001d160510400c10303051282e460380108291400c0000c0003a004120b4001c3d80d291603071315900401c0e100c2c50b83d205102c800300190507200714551010081e107001c00d4004000c01c0c0d0b40c0d41c0c0d03d0601100c00035007a20b0150321a03080600014103009820000b448040d00d002c081c080000c0c3c0050301d100a50720542c5599000340040c44401d40f459003507c200c2070044514503000c10540b03060341c001400d5121450082d014800714039805482e00051007002d841011051b505c40855482d1a500d9a2921404d110400003081944100780c3c0b9001481e4060f00803003040d5021518240c1d0901c409030602207400c0d003c1079050106100107051f40384074444a003101000a00003038030f4030702040d8400100d050207428031101c00d40c85030b03140061012034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 598288938 1250 598287688 598287721
    0xa0801090f09021008100b181c030225051c050c01080c042c070c11030303010b120a061a1e0310060c0303020c16030b0901051512030705010c0206 64
    0xa12004001c002d25550005100c403164003885000c200c840c07000036418000d030b00c11045c003411035010031075194100c00220b90704140d11040d0700d038080c0701144501a0b440702150007104600d07600d600a448003046242e2184040280f036452110a01640080002e83e070315030341c017243d80741c100d503040c500440101b50401030300d44000408044d04001e062000c0001000610003a20281c13000443c007402d1811420300c070b07000b03203082910744500e41c51880c07410f002010380c200145180761f500c01c640d882c51801c100c80400d03480340024407602c59100420014112821000203080c0d60002d40030000184654071107024084546984111119280c40007483c9240300b40400030036500d55424900d481c5c91803030001c5000000280078407550061110a0800c0d60403d402074041d0f6454084500c11552000f50341c0411214251051109403401d54030040824004401805203900c242c00c80b09500c9050800c510910041d64889007060715140424848031001803c02e0040044000003030b0300800845c00d104180010302182c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 598290188 1250 598288938 598288961
    0x1908040e090d080c0c0f07090b09090f03030601030b010c1703011e12032609010213060201090b04170705030c070f050a03030c110105220810060f0b0306040207080a080109 75
    0x241d40b50807002ea006203a41c1c1d01980d00b02c04d0588940400c030700c1c2c0d40343c4a4081404a414001d0f0130020a00125552180c50303481402c9a850384d11b0703194605010f485101c4007592504030342007040010f6007075000b07800400783c0003010714001c1e10004691719201d5400405400303481240344000700420100340300100f42c0c0c0c4000c003d0711412096524041184294800400c402000c1c4800d0800c00f040543c0003000c1c0140303000a82940c0e2806d8a050000e841c000c0d4008030294032020308954010030000d2051054420f00c0e584650340d0031180d15036464004040140e00b1072440d0411007004540001001840580380c108030704001060010305043e41001e00041e9504458011807000b0010400720740e20800d922100b6070230a8501c0690a0000c004075000e2043c0d0f006803e901030741241d44100721484074482d0048854150a9031380392120806c481040e40d020307200b22403000c0b4a1910610800d40480700464010400810040ca0484aa943c11a00e50040603001d8045411440100641f000703501602c0e50100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 598291438 1250 598290188 598290193
    0xd020106060207031b0e041202060a05040b24100e030d11030d0f110403031806140906161e12210903090513020702040e06040f0807051908040e09 64
    0x60404000941c3c40959200c0034002c842d0100c1040800290801d0b2a8058502142c50701090b00d00350918409810504411b040144208000038421007950b03c00c140c001c0c0e070700180241c45500c41e2910400d0081d8010002e03c0d1045c082c4058460956810240c0811524580c8924011042c40001c03d810301240c2c5200100703114840c1c8a29001d050080111260100d00316000034034101c0509081001741a418840c00c1c000c4030000c0d020040c143c002e861014608400c4051002040c0c0740c010031120f07a030784440116041c00c1c0038010000d45180c040060600ca00700c01c858402c2d803019988511154141510201c10300280c1c0d25a010288845601640c41840346810481000c0e1410a000840080270805411241d030f500c08084003014440c1d0215402030000a044035a003010031010b4000942c005003040340304624103580312268560201e490343c81345800806a01c0c07403242c50b445c0d02406030b1091100300c8035405a80a48254070000c5800171140d030b80210421600c0c1c600700110300108450181000f040da5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 598292688 1250 598291438 598291451
    0x40b040e03031f05060d050a150303140903150f040c080c03100c210606020c0d020a0603020f0403050304081014150f03102405010503090607031505091303020d0201 72
    0x250000412290000c03142503402d070440340c0310506044410010313048294420800501c0d561628a01c0c0c0105008086010003088044604034180c10141e08921005000c1401c44110705081090700c0098204400003405480704a183d0a0910b24000c0040b15090450041c41040c041404401410b2201a0040f0310050210f1a80d00000a56070b040203040c0410260300c906e9015501c0e84a520381464081c160b800c1e0b50340b081800302c0c5040190a0a02444006101c0e29540044915100c0301000a10b41c01074a40d17901c0320b041c03d100b10007a5012902e4503804103000c100010000e042000180010008500600b0041c00d503100020203480c1c11820502c95003800c0c0d0309100071080340c192018041d02c0111041601540700c007000c20b081c100c409061000c0c0324a80404502903240400340c0701c0360b180c403000352001c11540f03400c015034541c0004d0340d45da043c9612880010b54018042e5005101002d400d45503104050f90b00c0001070300740c1c0000c41d1141007108145000c80c1c00c25404000c291040b55407030000340b01d013 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 598293938 1250 598292688 598292711
    0x15030314071109070c020409050a20090412030207020a120317270f010c0c0203100603051f020403151a10020a08030a02040f080f10051006030236040b04 67
    0xc94001c0c0e00d01034031900e52031004c141d40d94040c12814a400d940a0070900102e201800d05a4807808050300981d900f01e1a41030300070b00e800c518070f01c00c080070f0001801000c0c1a02d40c0e4030382c0710200c0c9441a02c0814103508019640141c0d450162000040400400001d4400c4052800504d04443c06020325900c02001c0c09000b81f40310184c03041c3c241c2c144076401118094648261103485c0640d22103c4502d0355203030245e000c3c501ca61280d28481c40c83d000b0350485500c804d20b500210f080741d00317602c0040d0164100c0c1d010410a0041d12580c0c0440401e5010b026080c9a22a1107443c1d2102401900d20b480c2e41d070703559410805811801030324024000c1243c040900040300c407406526191000300c000e05840d0008001954641a40e041d00c01074410541013841407034585920740e6854529200001d4944116114490502414002c2034441d084a01c07032015418905282640030350040a031003503500203203e14107010310b20070020340a406000c5601329000b0207903200a0200f260740d80d031304040c019030410141014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 598295188 1250 598293938 598293953
    0x601060e04020a0e0a181407020a120e0301050c0306030d020f1c030e010e011d07150f031d060a0605092e0f030305090f03060610050315041503031407 66
    0x1214002a100980d607607126900403544540392507003084d8017020000340420b1090140c204140c200804000800480d003c0e9446015030081c01c8030881c0c0180d1001075200000703080c4403021222001a800c2c02c206203030580380000d007502c00c1180d0008182d0f40200c00c1001c2840c0030010401444910700140c41c00c05900c1d01015101c04072200201100310740c145154001600ca61700c00d080420b5000c0080000c0d41d020700406018014a102e440400503040703003410098940031400340b0413070b01d040c1003881513030642002c29102c42e5901c4284105140c2d0703810003148109070312480303982000780e01e001500d841d24000f03500030304860241d0001d5000d040080d080150000052450000707511444c050200c950808008a40741c03e42c50f03802c0044841000d040020070550480080c0500c0340c821a564020481c4e2441815070b5070308100c800640c0b20924140c0d05007498080c100030751f040320b040e001d00580d481c124030205003651a0000d010034031034290702c410400d0560043e211415826254074580c41c2c01200d0b2115031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 598296438 1250 598295188 598295207
    0x30c0e120a060c0509120102040f0e190b040b04020703180f1a0d090f0b0f0115021009080d0e0708070f15210515030c0105092b0b09030406030b03060106 67
    0xc0c4050f6951081d01c424500030816600b0700381d40241400c62008040410a020350824404d210f030503011035002069000080003514881c003009841c400203082e414404030003800e80b205000d50042e689446101240e1a980028000e01d802a240c0440c0c0114185a80002e00003541c0440d035081810041407000c038405c0c0c449004125017181540b510341800d23040c44801420381c0000103040300d0300da80d1388000304000309031210700c03416503101011041c0c3e0b070383c0c20541ca418400350400401a08950400741c034801450303108101c064065a80c85041c2940708200100300c07140d5404100e016032043d0010000d011007000500c003d040113103090086140741407031455044003500400030074402c00011003081c4161702400b4503181101d420041c425406c0c00e90150119010174807004c1e000340580142a00d80e5406001142d800f5000508107912480d0704003580c6110a86da04041c64003040e00356100c0010070080c4920030300079540d02c0c0c05140e03528034000020f01110070b40d00a50b8000e070098030042007195089403409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 598297688 1250 598296438 598296443
    0x150c0203040611160608010f1e03080a11030f1216080601050f130605090310060303022d060405010b13060b0f030c131404150e0606210403030c0e120a 66
    0x190511405400001d05281d1302d10715004a03c48040400554550b2003500b240c12500817000003e0760a84800c020301003004246512401520110820000583e4003401000c0a21441c58030440000340810707124110390103c00038000b00e14010620101c0c0440c549055a00150103c3c81d030002d00c081c00703401030310116004080d58180580403641a400d84030341000c41340d00c035418012043c090b9441d4400549281c0090700e0060003072185c484200d2181c0214820700741665091340040c940740c104d4001c00d0300d2440c980701c1c02c405d09810010080004c501d0810189004522620021a03404141018410641940e0300d40107480b5090807004c100002c00c02d800c50f6032049074405510364994030310543c66424850071180b10003800c8804000581c443c42d1032580301c15090f048506010b101b44082080382c1000e080c0c00785054070400300b00880c4c43c41c85c043c0020040760340e240d401540d40c0c0281a070080c2c1d4009003240d00b0790209403034150403004d07241d2040c81042501c00445030702c000900250300881c0d45d0100c00000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 598298938 1250 598297688 598297697
    0x50316110c0108130602221e090e03040f150e0d0804060309080909090a030206091209040b0d0c03030c0c050603070507140c0a03051005090309030a2913150c02030406 73
    0x1c00c1c014800f211084000326044281903547d40701d1050300c3e46080000c13401d241c00411812501064211001b812210900c0360b90480081250500d1809002030503004405000303448200b00005048130303c42c2c410300044c0703030404160421809910010f00602000c4407a0b510403001c5003406400681740805907002d1303d05500d0000340544040c580003040d84140300b5001d034011304520070884c103e400014a900b58500c694259130346a2074641d40030341e13105181076a103051a54180702e011039a00b4258044007030144c00600550b00b010698950002160841d0820f0b00000c800840382000c1c01481c08000c0700801c0c09583c0c42d491490081c0000700980a41d8800034030031002c140c0d41c0101c1040412141443e148014118203003203559180c030f03070b507501340c00030380c043c1041e00300700c001891401c010007503880e070131005005040605803903070350713544543c50190b0307403411091800c4101005c0c0308000c50300900c00c203601b41c03056000000e03500b000c0e440003502e0b80c88824030350305080c00488200d50220640f01110910b080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 598300188 1250 598298938 598298941
    0xe270a061d0a020d090b0a05041b120b09030d0204380f0309010b1f03150e0c0309072705060301111e041a04030201180503120a030e070303050316110c0108 68
    0x4c030100941030844000d0402c070110b406000305d00c441540040d01440c0b0510802480500740ca036252041040307403043c2d8507000911014500811360181e6080e500400780340503070745006070480c40701080740c005c0d4000c9090440c405815140141050b0548540b00040b84601d84000100c0c003c0d040107481402807980b80f154020011a1260009412401801c40000c0c01118189011a15100c0c801c0c20111044c00081c1031031010b202c4c01c0320188c0020292102c0040c618007507591200220b40551000e40381c02510700c01d000000810001da0316820f040c02d44002030701140d03410400c460009075100035190754826450034800c0b4103640900d04c101ca00d80141101e104018041580c03890801e40140c0e84013400480e84148022003070501d6100500959200340c03902130840011a003c82c3e481142c50068a40561101c40d1102c00644200058102c8201c58034000c910b041d064040d4500708202ca60045000c075601109009204c4100080c3e42e042d01650325004001c1006100916951440492090b060100303500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 598301438 1250 598300188 598300207
    0xa17090609090705130e0603120702190e1b12150d020405011403062401080a0902060703110c0418020913140f0c0607080a0e270a061d0a02 61
    0xa89007110310003042c103821407600b84005082644030001c1c0d1500080e540e2000308149002d02c4d0650b000301005001070040e0403580015a030300f5408450243da00001d02140c156615980e45080b0000d014800c0e2074010908042010014400c02d1618451100e401400005014003450407502d5006d201e08481c06010f131115000b00f43c03a65035610b0007a4000782007900103e01804200001c12402c1001e0741110100d580710034000782c0602c10701e404018400c05404030300b00598840c034a110f8010b41c0200f03000504000c240e00007203040d805641c04901040e22210417030322030b0f0000e02100e1030408082d030781403010842401111042d03928011000b44580086004240090801e90141d03081d968000503000d03908480110844c0d4a0803005804005032045c40040401424414280d40c2e40c10344c00f00d2803d05003035601c107080e110002d104c950140c000c58454510400004250802d900e10b511003000c0001500b4882e03003040a0311081d0f007000741c0310202d8255070b126000084600b103a02c400180b0b0010703103465011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 598302688 1250 598301438 598301449
    0x8010e13031808060910020a05030a0e07120f03080901050709180605030607020a170403030503150315070c110604030c150c0c090b01030c140a0c03020109080301060c02010f020a1709 80
    0x4890901a401d81c040480c11800000e141c0d4081d02614003190310900d4042c020030282c8c895401d900c40061000d0010807041d882c103400c0100c0100301002587d062980300c0307402d40e403800a03000d002e031001110b0710709603401d05401010303041c5c1164448000f8002480c1846020b0400380c060300c58583c240079002c41958070641c003903000314094031000f02514014240103000941d22401c1c0801941c180705000c1089040d02c001e00f003290204c80d49038980f54119075441c1040045501c3d03a14045805000c2d42c01c41c004080d1101d145248245079584481084210a060010b01c260045020700d0091404000034400300d81252410300031100480341d4ac40025903402c03403c03510951b103800000d00e070f0300341c10348040b0f404001c07600710210801c002e0364104030b1a40030902c200d514400196441410000030048a081544580b0052a00d00e0080c0004140340e9502d0361403d845500980c0841c0001c0c46100c00c5008560f4000100c0070401100d10003010781c0303c2a52136080c030001c1440040580041c0c0010132120f02e4440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 598303938 1250 598302688 598302707
    0x30c060e0301021306050a080a0b01230706060e01150e03120c0f0a0609060c030519050601170a020c010e0f0304060c03140c0c1c080313020a0f030f1208010e1303 71
    0xb0740f1004c100c010b95030440503205030006681303403010445c1e0074005200900076110b04006040f05075a0024402204500d0034441c894100d2090079a00041001c0c0001c44c40134001d1000400341c0d250036105943c908a0580207100c4184820401c0013403114400b01c25580004101c1c1c204018002c03035682e2034000791903041ca0000e0110305042903004400b2400140086d691008048501802d01400b10440d18001201125401c80d4204484955609507400c3c402c02544196800745060504045030000100810003524049070340c03420064000480403004c1d42e0a0190303103601c50190004000ca054000404d5407203001c2c82c040c9000b00031141c1d1644046c18404c61805800320012042d46986407100700c0d045803a40034ac180e900340036800300041c0824691610040103851500f2000da20706507200c88003114440a84804260381c4a089448040703500c040034074030348000314400e0050401c841103c6c54101030603000c0314211740600c01288010003903010fa03d60740c16800384220520020f075070003915007540d44405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 598305188 1250 598303938 598303957
    0x80f030f0c0307150c030c0309030f0804060f1113090603240209090a0b041401060f030e1e0303011d04021806040f02040602010c0e0301021e0a0c0515150a030c060e030102 75
    0x112580b40f8648050545c40244100203554080c8182c0b040c40d4001d070300340d81d2030f400c1c01030000340b100c4840940c3c20f2007080c200f900188180070202d80c48841617154425112080510400b002c4002107a80311240c07029001001094006420f1002610b0340d01d03010032800708070b0b166210340c40c40b013601140da0624550444202d1038004058440c54180301d032401000300741c50401c00f8002c1c2d161511001c5060841d552044c100d810720317074411020901c0300c50228040c060310b184554203485410140140d06045501042440d00c010b0011910303580b41c605540c007045141c4140b40782c459042d8050101580b6803541c0140804031305895170146032200c2000c203009206074030011420500c04070b0045081a41034000b40d15040d0305903540082d04000704105401c038030598080120448003072010b86000d0400750040d004040c2c640c103080c402c10380c0d180c480c542010a04003c6a0400007080200031600e4025013075000800015101c085c51a401c590720340107542054041c0c41c060102104801c0783c5540c09404a0300d1049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 598306438 1250 598305188 598305203
    0x325050406121208011410020c1008090d030b010f0e0f040603110f06090d060c05070b16031d0604031d030a0609020102010b01230d0f15030c080f030f0c0307 69
    0x90356202c1c1045094415042120580401003800b01c00c140324465280c16a42008a46c0820650b884104051504201d409100350700400c3c0c2c8014043d9500744007140e240402d601c130a015440c06080c4a810410100c4112050500e000040300d00d07030f644080c543e00001e40609001007042840000185107641640b60940c0c4141402004420801042007080e407003a02520354210300d150080c01c000307245c0620300d4502e4025100f5070814000ca11940c0101ea0300c07040509240e480c6ca02a0b8840000c1d40030304450004c45100407440900030140d240c071589684805807d00881d103080841801a101c0c040503001608201c42401020704950070384000c0300f8008801003c4070110307491407600c04003400720030302c007a03000d03510301814011594001c0210702d052560903510a2024988020600c0d907640080394811001c0355103003050130010100d1700c40e481030040111741c0066020301d1480c10030050342444c1c00801e81500840000c0e0003402c030000503a900d101000002c2038036400d4103103e83d891405000005000207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 598307688 1250 598306438 598306451
    0xc040c110a03090503010f0627060e130302070f0510030506271906030507121a0114090c1305090a090812010609080114040b0405010f0501080d091403250504 69
    0x50b4200c01090102e42d0117400030300c90400c5403580e64040b00d1545c4103105100f000b6400507584003401c000d040c03110042a00c00002d0042d00d4104010120070115030072900c91595190341c4040c980c04024102c000c20545000c0140c0b42c1c10000484ca60042c000190024140c5903001b003078250f0341d00020f00c0040303d0f49424500c3d000c2d00342103200e100030b00c05454500c0e1060070072202d40441135032801841c05503900000145010392030301c0e69280440228110590b1090030390b0724400c130030603034018001f0b00a004544000198405000800c44814006403030450700303107410844880f030361800d0a02441115811079141a0541c3d4020703154000e0451000010103003400041c00c2a001c4060b060100e042e615a540e8080d082030f01c40c150942200c6100b2200d8980c0b039801000240090a080e008541c06446440080744c4500c8040c00d50741502d00c2a004034030640c00102c202001c940c0c4c42018540101b9030051202064290800425103075213444c112401c23496400043d80040c4460a0070040080c0406001007266 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 598308938 1250 598307688 598307693
    0x4150f0c1b1a03010b22121118070e010e1207150801120302030f0304110a0902031602031305010c02030f100915050403092d0e04050607080403020c040c110a 69
    0x10030307494002c440d01803814041d01a44100000c0a40781603401198840741303420a450046048410f507200500c0c00940100404030ba040c0034800c21a0009219000102c111305002082100d100b400007039070b1051080483c204803a055002080010304c000c00c0c2044800b1103180300c0450641003100009000c41d02ca0500300240c031211486100e440d80100781e030764130090b07602d5131104980c02c0d07481c0b100500141c2c41803021380f00d0310455000540e0003d2050214008002901c80402e030b503c80d495000d4002164084104440074000508854403240710348051490003506800c86000301c607190007918100801da164500854030104103030425203000c00c08442d50080e901c00c03402e005e4036146d00101c132010344100302041440007501078503000b0f580c15260f58888a00f0000401e01e03d1034916400100f50700002c108a844520000402010304281040c0c031065180504101e407400c1b6019040740e04110301e620400011030780c04540603420345002c9502092401030403008545050700701012030a05d0003106514000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 598310188 1250 598308938 598308983
    0x308130e130201020706090e1918030e01021014130602070203032805030f0a05070e0d0b010302040b030309090a02090604051c12110a02120106120308040c050604150f0c 74
    0x60034801d900f105c0605846a4049414041d144030f40c1c10032050082c0440c0801d13000709800c0140d040350120004211800740c01c40385980e1000e140603400f0420200442455580c14000e07001c14582100b41440214041071342034100f004010621301e403080c030b03041074401046002e404070355500b82c005088949400d440d903003820034000810b4600135102c08804000070424041c100741c07032040c103034150650020b9a400d5413003800382600500d2441041041d041d802260384c0c6041c1540d52a6005580301c00070345d81188140400c5a21200d8414426441840a0040703980c41c2e502e4503a119440c440f0150f214601e107004540c1c40c0c09281c105a5020030035400c0c1300e59001c510410504024022501403100018040060f00c00b031010800d142d4070f0703030001c004030382c00341c10514001001a0b044100003e0344a60b5030903011707010700c4100c0c030480000d42d450041c0700600075010b10000c007803c82198041c0ca420300d4903100385542078140c101d49050090030112001d002e4010507268100700d804c2010200140c54030f024020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 598311438 1250 598310188 598310221
    0x304120c080c03120a0f02070302040c0306090b0303090a270615020c0d050601140a03140c18010806060103110d050c130f0b03010b030c0d06091b02160308130e 70
    0x4041c0c0701c0c000c80141c50780f600251185040341c0c64014680b4101040100f1100100205048401e502c1030344030000060300d580c071038040700c01503556000a40b2030030442c1030310a484002e4906882030f4410300c032a100702e40d140c1c200b59045a40701090550040328480b4000400400c401c200448a440d01100060300800c090f010305e03600040741d081d02c5180041108002c10342e40c440c940600b07590310950041c01001402030940c000c0200042c00c803014180c0c1c81e80c0b206c510704c054881090306a004504440031030708000d0940001c1c0f0303e003c04003041030f60601c581c0070394032500104014100760311110548181c8038500100d40c94900c18120038030140c40d2014011700542e00c000d199006021f08040001600d08040c0c0b1841c00f03984c0714119017817845e440e1041000c1203420150440030805810000d0018040c000d01c039110080c813401d100450080108810554015001413450b01550820381e501e0340c8411140300c43c40d0999070f000102c2900d810020400030401c46450704080500c1c0c03c0d09060001d03445601000c036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 598312688 1250 598311438 598311449
    0x1819090506070f110705060a03090602030a060602060f0c030f0c040b070c140f060910030e060f0708183a0507050705010c3504090e01050609010f14030304120c 70
    0x1003d401c83c00f100200d441c022545000001c80e00190024040e9103421002440843d502d880c0c040b803a4038007602c03100102d0344241c0d03007003107020f036261810007106030140502980204015601407a0381780c24840c4038001c0c400100a0704049400710006881030740810f06a0300900141c0da01c2c60746981c042e20b000114100d2600580400b0441000d1101c1d0070b180690030241649006400a801c000400082c49407601d00c071180700040c0340e03d9419074001301508100c400e2299441145901d2107080699001d4402035000c1c0412800d40c014100010403034200003003150176030085403080c2c10b01d400c03441b220750790a4040c040410720502d030782d0a01c0824030360320070b0207458514004c0094850345a55040103455450410030003c040b807400301c14a03c02c00501c0e0007031600465092005c10290b46209107841800e40c860703001103003843d644084441d03086109200e8143c0c44802624122102c0d410400c012025103081c0c410240001785121442c07110307480600603240100104080c003c41d60400e484d0070f000ca8042401003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 598313938 1250 598312688 598312697
    0x60b1209030c070e04110d030f080c03010614030718090903090807030b01180603020616030315061407080f0304060b010f03181e0b190e0606181909050607 68
    0x1140311440040121522411030034001c212062419580a018100050003940c81c0c1c4981841c4805c1e50300d41224005801d446035440103420340000700d001d420307007201038101c0b03000c40c500b4070041c003009400109441340242400700e000e8a17645c5a1b07a00300d54000d621850070380b20084016000400045641184d0405403094585481d10f80c0c1740c0000a42d91009448050202c1a00c0001003010445120900c005000341803408181a501e94022038881d90100521038030509210722060301349581403080c1c142d20b0492401a40d06180707080700090140c1c0d0034018440c0800b60000c0d41c07108108a40089458140c0702e04422038882c40e10f410300d00014140f1021240c0481c400750601d001143c407900c076081480404041402100300c441d100d01a920030010384040300c1e03903541900e4102140251103854403c4480344100701e0b0348001d0f00706102c2035981d041c04180ca654005800d010150b078a4141b040803400000c00c41841d90f5945c500030714403030140794481380d460340c4c0b404001c0c80034480701150803440b03000c80f5240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 598315188 1250 598313938 598313941
    0x10e180a050c0a2907050717032107080402010e0a172508070603090c05041d1b030c0402090301090c0905070e0d0f02040902010320040e0f041a04080409060b12 70
    0x429020440404c1404040307500e03240364101c003010340300000e4035055008000311400e03203490741c20b1012441969038000c01c0c640e1001c1510142d40d01000c10410020715007401d0340c403035418884400752401e100503000905100340c5040b00051500c400c0e8100f0010305031020720700030001c5046440794a900120350aa40c1e00d00760b070982142c55004011404040310b41180c010144603243c0704046005014810080f12900c1c0700701d07000511540c45000f40240c009505140c000060240b1035081d01d00b204618900602106141301044143e902181c140140e0f003040e1405a656031404000a005000b000e01c028010510940c020070440e1103540f080c0c1c8907a500b62507031808011887d0801121030300020000303000000d4540101e005060903040103001c50b01c1818081440e00307075882d141410390081021110003140c04242001340d6501418a5500314600c802d802030142401e0b11070300c16510319281070b40c003514440d030b010804003c44081240e00a0a0351801040081e841d8920711841e82c1c03110f01a14817609101c0d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 598316438 1250 598315188 598315199
    0x28060f15051617040b1206030d2c030a08030702100b1804030c0c0e2d130b07020c15040e090d02101119050301030b10050306010e180a050c0a 62
    0x80071141100c20a080d2420b603601d80741d0318000055041020000e44940c01e010004041c4105c40c064507000001118000042c501503041c1403030304003e0040032041029504482516a807110303180148120141ca080707801c15440e002007450b0216001c4014001d13040007003001102c13a8081500259a202e24000b0f00c58049020100038030441d0000301e50010b40c107000c01080010780502c10340340301c4038454401100565503800600301100307021070744205c4090008126149151910044840407078802d012340f4010b0404a04040e000c0000c508010098400c8001145965000308030f00e100528005188244071030074410506420f80091288280010440000c03031418103000c601d4117038180e000c4d030040c0040c001410801000e08a0b03100e80302c030600d4040200050819450158204c000141e80701d0541d00d500d0340c50040201803004151355055078441c04240071658000c680036044822211082c1403940b01c00340007488241440c0746110042c03161001079010000302241c401101501140c5108895951381c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 598317688 1250 598316438 598316447
    0x14010515300f090304090c0201150f1a0f030628060e040f0e0c24040f06020d022404060b090f1b0f220b040305060609100b0328060f15 59
    0x580303c0a105401c10310041c445086c0c164005030441038070744004124130780c1162444d00703035030b4070350f085031a884032448814403c20344440812030b000c51071850314614114104070703664628000504094420701c0b040322071800c8090080742d00e40103040b450326005503039580e5010241c00000b1100b10240103505282e1104641d02c8180f00700790080c400c6602038054841c44404000d060200d42802c207020401210b500890f100b05030300030300054130301440c549144d2414181c0c040d00e0142d00c50b8095086500484e5800300c40d40410202c103074110301650076054980c69030300d031150140c400101080c0d00140020108080c4c4a0003040483c080d03810314001c0d250400400143c961140704902e130042c2060002c0110b91482c540500020100980c1d110650010940f540d45484141c0e0103648161003590155050245520f410301c802a08071300710a0071a43d00707910701140d0000c50b00004143c071032613407501c44140303110300c00c021054041020298002c0207130a4035492813101e00469130003001141c030000000807031024000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 598318938 1250 598317688 598317691
    0x30c14091e06310b1821070e041505060a0308070302010605061c320c0c0d020d0f020307030f0e0a0312030e10020405060f0f120109140a14010515300f 66
    0xe08001c41703134520384a030a2014600d41914505506800e201750385182002c244240c0c00039210712403514209085c541407100c0045c4035420010981c501c1c0100313125140d40c1d44120344c0b04690b44010116110840317420141d0040000d6841a0b81003240040c190304050303215032032100041c410303290820406060454003d0a000880443c040f40c451124030326122003001c800140d8085a001f2945103042c4603101401c0c1440c5031040c003600941d1007000c5604009410080001d01c07000e15100841c207005090724024024100c050205081c05070b40080e210003038603004210405950800d880749591200c02100a0007801070008200c1103016526a1082c421154001c41d01200c100a19141c01e0103d04010944181e01012100c04d82240811952422061484c0d069001708010000040c00301400074007500c000b40c004100300030446ca81a651100d00c806c6000c407d05640c002d0741c2032200181204118415032061031150403114032280b803000c0440700c0d100341c1007400c5132403002e044800d40c507400d181c42c0341d4090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 598320188 1250 598318938 598318957
    0x912010b030114161d0607060902100302040e011202060d050915040302100c1d04050601021e031b011401151107090b0f030a08040605030601050910030c14091e06310b 73
    0x286400c0116246c41e030098514240251000102250b20b540052103210445410101194000c0703400c21141c4002ca1002d03004144070000c42029440c04c0e400218180320341e000304100c40303036202e0100c2c08401c0200a10285692200c5014032303e8101820060340da0103260240780422418822030b500283c0c4500711900f9a900b0000c94030702c440034410100805071400a01c0603046100e003c00310f003400003403003480c1c3c0d03048003008018664403030540308502007101844c600b60b805607044c6604804103e2a110995046403c40101c00703424000110046580d540700c4103444100e0310500c01d02040c28036042d400640c2d007250456a004002481500b07041d200d2981440103404920305000801010380142c0013550f0248051601d140342c0040b140001e645004280b2900300040d66481042c0d9129030440d200601e5071620002180c1420902c0000844619960014000b0840b903007654114a40b598020f4035804c1444400c0ca1021440940821010724003101c4901d802031183ca400040180c1c80c0000c940c1e1445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 598321438 1250 598320188 598320227
    0x909080403020d03030b06030106171b070f1509060608071a07110a0b0d050a0b04060f031104090507060206041a0c030c03070909060816050609060912010b03011416 72
    0x500c1e40c0c0070032246034181c0310198241900d4040c0d4841c16590400298040c000a445000c01c580d10001682d00caa03000500749400000380b03045000213034102e0b4054800e02c46c2c0c08000403041004505c1c00440312840e00550804960609402104010706600081c0a940c1080100c0b01d505036215890455120188048242c5030703020894580030130001c102e4408802000303001d0240076980c0d02e00c04003541d800014000340c42a030b20000c5c0310a026140c020342e008010100c2c1c0511016007084c0000109602d40d100041204246140118441d1500d030001900c19400a06958003155159000ba4803444101d9080301c064000c2d00f0310312480c4c0401d80c0f945019035071558150f030075541d80d01240403c5900151206003803001d40d81d00001c0e82e501d42e00518024208000c0a80180c1c550a170078203415480d180c0017548526000d12098880e501d0341c43c00e5991004089500c550b21903002e0b03503524018801d10f00f8440d01075080034003070000a600c6000360341c0190914003489c8400c0c802040110303401d80c1074000881022 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 598322688 1250 598321438 598321447
    0x91103030a0306081624030605030613031b050c010c061409030306152503020f07140109051206060f21011b020a0302060f0c0f0301080106140102030403050a0b13080a08040507090908 80
    0x81d0b001d086d01c1c0d004603c10304001890541f6100028540740341203d04090491001c2064400c040d0b000003004942b403003050046081078901d071f44007501e07008a1603441d4100841b003103852040c0b1800f0303040003071070407050b014600550500200d80b0303450360300488030b140c06840881400f01a2107110b40c00c540e0703000c07401a05960000c5905650500c2d0000340b810903000c41c424007011b03000071041030106100130f05e4004d03500803074140202d0003d00350790301c0c50740114402c100700b030803e01d502d640102c0d407503611003400c841c1c030210780d1242c00001e0380910302c07000354184840340c0c4d41c00309296030300542c0070000300c0303000800044513a06a0401283d480901210080c010382081002c5145003000c1d604840c0c00c003c85940b110704201500d0032010300c0b60002d92044c005617440b40000c0100194400398210031507401c1c03000d1403800c1e0a503103985942c3d002000000300004200300008192120901a140049030b2000f4003554030488480e0041c401e0505850595450045610000d0b00c0001407040c260200d91203030005c0e040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 598323938 1250 598322688 598322729
    0x606050708031b2b180203030304081303080d0203100504020301080a060903020102160b0f07090f1703040e010303120e0c0a060e180106090312030b0112091103030a03060816 76
    0x500c01100e0314441d110100344401d0360b02c50003600114030f03007002c1d04d9491211645044104000d544c50030005030718006803040a000943c60210459911075000750203a0b40c0c030b1800c40181480310409a002a11888021420000710006600150b0103050030300c0580c006141c540d410441284030038480e84042d9849048008005800c039048003c980d8000d000050900c140084000200c0f0314082c0c00700d80b43d0403100100100310100096040d0001840c1c039115102c14144481c1080420140c0602418002c0d0014810001441041140d0103050801c1c0300071090350356464058025404441c00100d910300b005003c4030a038000084078078440b00014000f00303013070b0716040080d00d00e00940b40c00f86400040302d580040145455501c0c15000380a02d9807104406461420a030440124040714241054100359190202e60b902900b080c146504180d40050a00c016107821000380c2a01c40b103542d01070001255030304096800d0f41c070071821542a241030b12141402c0c050a421102414010b4000d0840e281c00442c90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 598325188 1250 598323938 598323961
    0x703030509280c080a11011409030a0c0e250f0309020d0302070e0c0415320a110708190804090603300f080901060509130303060605070803 61
    0x2080141c041c19039468082d101c41c01c1d94548481c5144000e40d04810389103000b0070400b100080c000f040c000015060301c1a40d541c8407030a16601c111501d04105614072180c44c1201807004544c1003c4000b01111b508042c2440c101030358144521400325802c5001000940a451f80751040200010042c0d5116142d440103206650385100042100101652060200d0040e110f410300560883d019030024040700d80f0345039001200d100d0090166421110602c810444c0c0120340d04002c410f20020f0500541d41c0400200031110144040707248074200c550580b40c602441c280100034079000c0b010f5940c900d4000c42c2c41c1500b50355107601e03100d41412680140307080d902c18007404035052002441884041c0c42c00c2d40c0c076000c903001e803040c0c4e4000744c924010f2003a800b9800312040001e030940c000b541c4043c40003981050360141c0b0740d21a850884d41440f00f41000954401403e6102d840035090044c141c918500b040400010b08905101c01100032074513241020903058080c10903691034991011001c0c0c50f56490a100c0ba9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 598326438 1250 598325188 598325191
    0xb010b0a020307060603080705011811040b01030e0327010f0e0411070803090c04060911071401020c0a2411030705070321020913020316080925062307030305 69
    0xc11400140050b4001440380d0003048001d500803032030356031034200904000e42100d0740380c1c240c0f00c11411f0b0929050001411145481d40040d4122000a0841058001680580310100f210781c0280000104c10402a00b0020419030400e402003401803440a0040155030459060340040c0100e0803544002c0198905a0030481403030024a440c103091800c682d036509000d40003540d4403441c80e0002920342c049070a061180400810310130034103200300141c4c81b000310414840c5210103802000c00031a010101003094040f101c1840c10081202c0a1f100e08e420320040c4080c0741d40078081d10f00c00c2e800d061180c6006a001d84180300050b1844180380d5103545000391403030b0740002c0d0100e090000c0c0302000e440c1e001070800c0340c0d80c07200840d500c0540d88004c0c04041000c03001049906844e010b00c18824003507c0e01d100426000d4901403818540125210107800a25108a07111980d11006105444992588403001840304035500c030781310340015200040000c0c2020b08283d40c8111100c01c240f20110109110380c1055 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 598327688 1250 598326438 598326457
    0x40b0a030b09091e0c03070f080d020a020f010c0c0503160303080906071b0f0510020c0114040c091e0903110d0309050a150e01060b0903210d051b0316080c070b010b 72
    0x4030707204500701022074103042c0e1f25407011023903a45201d81045501814451702088031810f20140c1068506030380003408400e0948001c82c100030034080e141e410442d0034824440901001000c6070356155500c0d80c20031050040b03000445c0062a0b00d07000c902c141d080051014050300494442604034020760030081c2d1205007151050346c0d0b4203030000b130000c04141d0034080c040883c00030303203000350743c030281c80c0000f038207580c807616401501310026000c100c0401c0846140b2400d40304489800301d00f8078906030f0000c400001404030100c009150810440405030030002c08800d814007181900d90b030300c1e40b030002542100c28080c0d0190081e04480f800c07c0014040220701c2000440d801d5000600710304132481d441c01c5400f030780c1104090001c001424582d80c5010400c1010042e66640014031810b034001414000e030040c000c0c000c61a41c0c4407408a03c8014000307002a4001307062550203500c900d0701c03109040c0c2071402403000401241d03014007c0345110749a003007191440c40e00301c0710050040c1d290040c40d404030360018056 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 598328938 1250 598327688 598327693
    0xb0403140f13030b07020d020c060c070b0c06040b0609041101050708190206040606151d01020705060307180603020a02030313060b030a0501050a060905010807030b0c0d02040b0a030b09091e 83
    0x404411640d0314080c094034554201540442c508502d001c00300c0007409081002550320a5160b11201c0382d00052046480c10140d910315201d05041c080549009490340100b241c4940201d040c490030440056174911a6002c0c0001d448140c031a001800003100c3c087e030303010301001c0e5101a4070100b94020b400420b5840e00c00c81c0040d19280c004400100c001c0d59074028a0010b0300030030240400c1c0b0056000386c402800c100d40b442c00ca4080029009080d40401c0c02d03000c000b40380c64410385c20540c2e000b44000c00040c0000380200340d6a25005000400d03c07014075041d1103059a40751004038205100344282c8400001c0d5030021842c54855004c0500b11600c0100216010307034030f03148039000384d442c05e11540c42407610940000c221801c054a40d84142c41d03144c1c0080645614180040201082c00139111781202e800000302034141e00e4040308450548200004200e02500000700003514481103070051008055950703040180d4403a0404102c10000c041d504050250311050414104042407104100884601000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 598330188 1250 598328938 598328947
    0xe070905060a020a03020606030d0f21020a1e020601050109050918010c030903081f030206030405011104141311090f01031e23010b0304060203062d0f0a030b040314 72
    0x41d109600207210040140c020210000c1015010080c842d00560120054020010140b0008014055001e56001000b0240d02200380b1408040e01034660f4081c0a0030940d520200750201401503200030412485120b096100b12448900c0450301905840050f55045940f602c0d00c400c0250103640505280325070000304000c140c48110900c944045204691008501d072101400c5c0680581c60003042d071094072214a0202c41c8e04019003443c01c056980c121030342c03900e03500c0d01c0c01d100b801881300a41c49066030100107030204031000c81a40580c40b040c000ca401c005e060804102400c00d8174502e02d11083d40700d8090200c09010310b40f428440b0320090061400180040e80a0140c0702c0000c400da03c4958116503405100b01280014103941c10042c442460849e0b065141840d44190f9200c02072020b48410350100218400d6960440440c4c0303100108101030040c1c00140710b070401500c1d01b040b001c1d44580001c81c1c000341e05051019220084030b4000d100b0103c02e076075503141a0f811414080090250607010070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 598331438 1250 598330188 598330199
    0x8010e100606121127010e031203070804050f010c020601050a0803090f1e04050a06030b0c0c120a1e030f06170c041116060b01020105060d021e132a14040e0709 70
    0x44506205007001c1003454583d2105c500050403454192101c01d000e03400c0568103558500340031086036005000c500d02613240385d603981001e41c1044580c0e026036a0b00e5003484280700c0660f50004446050360300c215030600e00180d4440da559900e2141174005038104400058141c000d103408221515001c2c0107079400c401d9010707510005400c41d00d048642d118200d40d164414014050102ca0059000003d4040320349070410900341107a6924414030602904403001611041c0540301e12410001c110041c00d10031050032a05034050060508101140000c2c0c0c81c00a00250360101d00c20854440c0c048180903007820596001400081c00600d020881e4203401040501d01411107002614446802800005900100c072000282581c4026045a10410b0812800c0e40560b581c03414600b500c51040000302c102c0c81d200350105003584605884203d50300d140c1364100d202070303010f4000d1041c490740c400c3e010407144200003401d450010b5613180306944540c040c4418025002030307046164020b5a00d05108680c0c65541 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 598332688 1250 598331438 598331467
    0x20a0210201e0712140a14060a0b0a0b0d24060507050c030c0a0909030c06053105030304030f0306080109080a08180c06070201110708010e1006061211 66
    0x940c000070103a1200b80c40d00708980c0c41e6205100428544805082002d19041c0800c1d4903c002c0030b000f402c80c0c6905003001d03800c1c02003004401d03841603110310108801e900c1c6c0c2071010f0300c03031000300c9118480e203080c15a9640396140880400e8144e80208004a00704a2140240c400a03d000700480c5580c4030a0414410302c5502e44185100410701ca55400342d40f440585015418114020f050700c1c000c1d806620f1100d45503588c20000001e0741c81c0100e002445100310b040c00c0301c0210140d00098072642c5001c0c1400850311030508103102065a1080b1402d00944600305075401c80718808000d07045810500c0490006845901440108901441d022031003a84400c500d03402c40b410040100e03007410f00001c91381562034000c401e00f68400c000c0240c400280e01001c0d003c075103034261000031a101d02030014006003168000c0545442910440080b81c4060f500d4450340c0f8001d00c1110413a5000303118a0030b01c01650710132801600240c0d0b840344c0d00c0f01600c481034070f48a80038000895a071f590003102484108245c1752003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 598333938 1250 598332688 598332737
    0x3140a0c1a0d2a090b0307110a1a01230d02040c090308040b07120315140105040f0f05030f0604031b031b05060703181a06010c080a030b13020a020a0210 67
    0x50560300a00c0811200894155640180042c1c24084001020071208005d80305480d0b00940c00d091500c0310008592000341003022403203008001c07003d010751440d00f400c500094035050300d501e4401c10f604d2603a11a40918a0755082c42d00c550301c820319071444401401c05400200c12500607061404140d40c895031031085581245e00000407031a00880e0503820321082c0b0031299102082803c041040020f00381000c079910040d4010f00c41001c070203500085040c1d03c03031004c540c002d11404c040308045549500d90a4080c50040c031840b0b1180c802c00088180d80b80011405034000e030f500da120240f542124100b041210f046065090b028440ea901c00504034440100c40400c6091082015020790310705450082c044440641420082c00c1d40d0603002c1c40081d000e2802e0103802d0282c031850211940d10240100c0c0ca05852000c010a52003012500c01c450a4254000c2505128112240c0460f0380b606e043d02003c03801341c4403145006a001d2510140581801044601d01d0341540c034081400407441d580000c5134145 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 598335188 1250 598333938 598333961
    0xf080601171905030703080f061c080c0a03090807050103020310270905030a030606081303120207050304030503041a180d060b040c0c05061e0601080907050d030903140a0c1a0d 77
    0xc0082c81e0410591700600f03248d40f000c420f000f400076500380500480c4031890030000307012024407401122018408071500307a41d10000c5c124201d512610541c9030052100c41f003032040c04d00328840c05401240a6000380203880c811442418810780092074550030440091034001c0320000200c1c014019558565240035005926004000a550328824440b005044a8040d8845030420070100d040c056601d0841d1801e030b401980500d0405041d43c01148000002d1194483c01446840002400020003078040042c004a03042c01d81890500019080d6001c1a8400c0c10a180003400c2c40c0700e100c40d51458900404c07500c450048900041860000010070201c03208a0303240c0003c40e0a220040301040410420140e00100800601c034100c1c3c6400d004880c10600035081074107002c0300c2c4000030180e050410614000740720007008482914110b00740600507849900040e0b8041e02d04140c4801c070740000041c0d500036140d0040203000f505141100d441c1241200745c0d00f401402c0340c104158a0000c80358000c2e140041c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 598336438 1250 598335188 598335193
    0x160f0504050d20031506010507050c0a0f170c03031b0a020d2111030d050c0c0102071a011403070905060a030203030d0605190311060a05190f090f080601171905 70
    0x1040341d00c0001100c0f07410448184a0383c00764140385500484d840007640c1007a07003800e10584807041071400c24103005600b48502c0e04a0503813000010040c140799080c2c4100c848040c038148840045008245c0c8030041c001c245501944100266444071140c6400c0b281c8044d07a5030b060310000603140e400652441c41284060f07807054080c027884c6049492894218195009a0a0007041a00d614180c15128059500f20309000740d42c5030002125020000f0860b0844248500215500d01c458503018252504140c1011000340000002103030f1200900415551214018003c0c01801d1034125800060400100a81d800600c40301700040141c8003000900990303c0c400c100410368030304244c18459110500608043c140f0070034102007000c00d0b00e2002c00c2041d900280c88031540d80c2d48008041c1c030302d807141d07020383d05995548409410000d98400031890030500a5aa0f04841664441024880c03502070300a00c034050b00404010020703504100780c642080d40ea01d106aa2400002c40c16482891030343c05015100394 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 598337688 1250 598336438 598336463
    0x20d15020a0909230c0f04051314010506030108031b032a0c180712021314010809070f140a050406120606080601030f0b0a0902030105011715160f0504050d 68
    0x3e100c1d0103408009070b29031003680200000c1614280d8540c0018080501e40707080042d081e0f103880505c400f2200600b8000c2d140315049500c585040b0000d080f80000700b45021448000410a4031703044046034100e80403d80190700b08103072040743c1c0040c45000710120f1600d01c020880d00d81441d40c400810a5844600e550819041540200c5c060920300005107551250200d8503154120b0600c940c00150020b00e20700c2c1c5489800121344412000740b20301c601e08150280007401c0041d0341c07985008520b5019074207a81d9403809884000b651030381c44402d8002e40c144017200c2002072004502401c0c01841d115402407018100c0c660381c1011904aa100340c0010311001044554017041c03080501544005101405c010402c41d032460f10344402006880785c00501600c180c50101d40e14080700e030448010560018000c100a5946048011080d00c0300104902103008000030170704241d100c5000e0350b100300210f8001d000503107100181240e00300400b0072070105002041c800801c080c5c03a80c0700d603c1850b5100c0c41560402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 598338938 1250 598337688 598337699
    0x60908060a02190c11180a0e0a08090f0f06070501150602030c0304060318050618010b0d021e0102151303121506050d140c12070c0807020d15020a09 65
    0x415800900703070140603004125200d10310010b0f1010102c0103643d403604144240103450f10161109503c50030541c031079070401c0b016101e40c13a442c854601410502804011002903031030415200c00b41d41034013400c1c403a0180005005c5003000c0b0041d0000c803a00400849582c0103c0c00003413038503040b100f02a14260f64883d160741c0c02011640132200541024001180be00004e0f0165030359a04c5140030354001c041d10303038004104a0325021406800315502c01c0685465280c40303403440000c81001d04844105600f40075034010a414868099030340d0a0700034046104442400706103416444040c02403034114030038902840780d00300300c20380c1007401280550780030b50065105040c010150341d403403507000c0d003401d14180340e010f07044035041c0e0994100d65842c14100c0d00e5100f0700b80c0c494000d108040e45e0003654640482003180c103030b001c140188044410044048901d855442e402c5401c04020034004006000400822016241c80041c001c0c0b003030300c03070340340c145084078880001c805a07001440b400000c90f5100d40180803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 598340188 1250 598338938 598338943
    0x150a0608010b061e092d1005070b0f091501030b070206100602341d010b09090114040609140609070e010c06090507120804030b0f04030507060b04060f060908 69
    0x2000b10201e40050034032440d0a04015040300c000c00f0035030000e40004400c0d540b9190720248104903a20400108181d04e8a0001c001c644030204000c40c1c030413070311820107a612034041c601f5980300c3c581002030280ba0781d48050b410224001c01904110203403061000340341201209148850295104101c0b07540d40d400e0100c0d0180c5480ca001c2d040701521006084103009842e80010540c00c500743c000382259603422010155503003580750610300320036040e8440004c14203003035040a003951840100d010013030b80d0380da45614816038042c01c544160707c4030014004228900c1040119040558001d200103049580c4182c01412148005c9101c895103000b4000c010b00382c42c00b91401035100c0140d00784030f0301d03841466000814051703030002c1c01003103559114101424482c1c1001a400a001944000e19102c01c80c0c1c00c0c4159103420900c4216400d0b05038100240c0d066510b00c030000d00a0b42d25813581410024a560380402900825584a030041d41d51310380040c50741d100042c5103001702010345030b051019061010131130 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 598341438 1250 598340188 598340201
    0x150c060f0c03040201031d06090102040608010503070308092803030c02090a0608071208040816030c06020a0507050f03010b0a15030b04091104110408011e0b010c0b041202150a060801 80
    0x3045512204205800c800d503821254829030910300054039100c081400140003004030002c420741c0c03045004000f0a0041540140140c4410380c0b114081070303070703100c00309036540c510f83c00000c000d42c100b4084010780741011281c0a82840c620001c26541c504104550401421141d1082c0c0000313890710707004000d42c10026140b540220b04918144070450918003a00c3e9202c425114000e502240a120300041c00038450960700035006510980e042c28504003580b80701386d4940c0c00295108600c02030009101e9000150310001079034051301070f04595160008100642d50348202068141d501c07001984e071030b5621095444040d1076150210300301e100d4850001030450300038010581c00360f443c12002601040c10110b1083ca01d0408840200d403001c060304482103203001e103601256556080150303040074090424280d0408806041c020840300800c8001182c0304211050050941e5050030301190208000000032504600e0600464120344400300035550450403c50f0040340725991b0318410b02000d40280941d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 598342688 1250 598341438 598341451
    0x21003050603120a0c0206040e100f0608071209050a0b07030f0b090f060f0a0b03011e0608061219030e090c030105060a0e011812030305060103060b070f11150c06 71
    0x308580d280900200e41d6900d14800e400100000c04078404100d544104c0c000b255480e405081c86484655500e00d1402003841514805080c20002c8004a09015034041c03c000f181d500e0b64940c000c5444400058640c01c8101c1841ca03e801c0d103a180c01d0300840c50401a030b140a1344546000042403501000003421507034140110064181070030007500440d03580101440c4c101d0494a80d00e881c90300c64000140e803841101c0c404503088080700da00000d00d80e4248000e54100e40304503c104070340c40f0200301001c100001c0d0303016404c00700d074035400826210b04151f5410070300921801c003142c640b5082030035014103503031040000f140010704100c070003680d5081c594003c1c2c0d0084d4003001603a06550422000907041c9c02500d41d5202000283e00d540051a0b00c00c4250743c0030f070120400380794069625140703c9800d580294400f98003081c28007000c90415403081c400c0d101200e0000200c1c0341801043e645142d8027401d5448242d460744659075122006540e500c00500006c0d14181c0c4d0207a503865440c2040d410b000d40281314 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 598343938 1250 598342688 598342691
    0xd0c1b0812062d040f06170c03060402150c07080f0102040801060906030302060c07050a021c020315010b0a03020f09041d10090b012c0903030601111f021b0d0903021003 74
    0x21400d40d6500f82d101d80c48005201c000011001e110725011800030050000e030744c4174150030b21310000703440d15800c0e869100102c002010343d240c1482e458140b541e10741056400075000703c0100080e80e81442100b02078a403003842482074940b0b103683d91030228541034151440b070320180d600290402c02c400307092203090300600a00105106242c55918042d407600c400900c0102400000900c04040000501105506960080c40a50901c0f0860082c420120840301c0c02c80c000e104800300100400d4040300075604a0307500c007404900d006403441040b0046d400c14805958030300f0042c005100c0f25542c1e805015081525018401480300780800704605c2c10080b084096001362a090758940410f1402d41110705444c81c000b90700c81c1c030700b0403c500c640985c80b50302601d402103001070303083c0140200e010000718012070003641c0f008016104000350a40307480c02c1c011103150f01000003140104200c000e401411850b40301030206100401c910a089080101a071500d2001600d0b004043c41146020b500c02c1f0340d619a41d240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 598345188 1250 598343938 598343959
    0x10615020109051e03130e01090e03070c150e03011a09010f0803070201030c0507020306280c08160207050a1d180307032304090f0c0f050d0c1b081206 66
    0xb03e554a4a0760781204010009410100303100b0740c481001110035000c140c04404d200d040c0e580d004541c10120a00407400f04074144175481020303c100005030341d5091741000310300310b0f05450f014420104841020402c004d202c09841c480f99142d03801e00c100b29140f61800c0381888200c0518040001d49a41600583c010603c9000203009044000064450047c0c0c2030034002520002900d09844900407868002d5151080e0420050f6136490105051701e800d040400300c8007507200403803288054031803072244000000c40c1c000000e07045144500340107488001c0c5005039040b59440303c02155000c110394100b6480d0541000707141c150095841c148960201d424490401000c981102e0142c5905ca592005400c100082140300806480080c80c41c405840d100e00b0b281c0d456070740b0781c51f2501400c0c480f0b44070240980341140880740390b4010380c0c901c0c12a0005555580c0f50441701040c080044c44651141c0b420000600e4084d1030600c0d4071402c00d01c043c1c1c015090140c41d241140c2c8005869039008014a003d40c00350003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 598346438 1250 598345188 598345193
    0x4140f010f0215060a030b011e051c020105160b1e01060e012705060d0b031504210302070203030a050301140a061e02010b1f0f0302070210032c010615020109 69
    0x100c00100b59009940035070980c450b10001540c0840542025047c0141040001b410103614409640030b001d105541894644e07a0707004000c0035103420f81844881e10400c140d0f01c4010740c400d900814101580b0b90700d07004811801d48802110703410445001111444101c000414211303042c04a6005000390b241420341c0190000000304004401c01234001d880c40da840b040300004401c0e10740c0342e0140c07201402e0755880b80e11080c6900d01030044204080c0c0a800f131a24000700100320100341504c6103070080045030307941900075a40c0c076041e100003221604042d800d103d48401a98240000e10300c0c40110b41c0d0340e540700e504000e40c0320354504100c0c00341c40c4103815524040240e250000c003c2c03a000c410b000140c2e60020205441039024118500d042544218801e120074260301c004c10014182ca0301c10ba4030300c0001c82040c20180d04034451420060340c02400d40000000041c800c1e040780e0203442d02011480e0103508000c100c0742c00c40c040c0c11403801043c1d450388010310124400d40c40144540e04140300a118580494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 598347688 1250 598346438 598346443
    0x3160309030b0a09110607060b0301090b011508061005090d0b07050301090f02031b03090705060712080c0a0203090d0c091406040e0d231e09030709060302090f061504140f010f02 78
    0x10545d1400303060301103140313410300145034401610080c01600a0005511a1404400d04402400f803014840e100d09000f0503a01d00c150303000b51090101415052aa51000038155410b8108a04096000744460408800101e1060740f1038012041511807035160350412066805842041125a94080c410300c1001880d00c00c0d082401d56040300380c0c8015036a070f00c0b034904d807070308104054010a40040c4c00244c002d00300940c00410200a091564a103143c5450f10080e07006584509613030140140c1c4188952030a9142400d6070040241c4640d915a01041c1c0d240060b0069591901400d00e43c42500400c1001c6424140160052000c1c0100078160500e9030120142c01034a0030030242002d40e200e03036580c0104101c55822242d4440c45920301610313890a04400c03581540c403000e6610301a0240d1180001d440036a4040c1c80180c96009082004590312258003040c480070082c80b2035031051819500500015510000740041e00c8a401c215550101000a01c030f400210381e182039041003081c210150049030301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 598348938 1250 598347688 598347713
    0x50d0503040b0f18010e030306040605030105090709021810030905061b04090f090f08070c060804020a031101020a060213050114090a210b0f04120311190203160309030b0a09 76
    0x1500e092440c00c0d211001d902c07420f0313000c1141d60034080d0718140e0080f510320700c00006544035100459040c8011503c1e04141800c0ea001070701c40368050b80c0100300610030802503802403c082c507a01060540000c8001d0005403c0f815601c024801099550410600380300060010540c441690840d442403030b4005d04100456206611500001c030380e50310823482940b909a00502982c41e00081c04130184595800d00c40d5060740300c01801c0f16001c0000e40f00086640c05030401903c5a42c00a2400c446189035848158200b01d0341c0401c2c50450281800b50300c0011480e101821071030040190341107041e030528001401d01646401d40d10f0343d07040c09001488a0b95a200080303401d40381c1200c0104580031054080d000f0f5000c040070000c060f04280c03020429200d045503900c1d440380d801125403208000b03892200303038200d4508610740541c80e40c040110b0301190030000070103445144d50b44100ca04d4420410003032002d2070086d80089000950b080001c00521035003003003450b08960000c20800500c500750307403400032801c1c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 598350188 1250 598348938 598348951
    0x20d140414030106090603060e070603110313061506050d06050a030c09090302120f2703070e100308030408030a150b030f040c170f010f06210528050d0503040b 70
    0x1401200d9041c980c82c01c0d0030400c018100c42a050140c242c40c0d03e44800506290a610b00b03a611403801c0c001021842070040c24211040340e60401d265444079540109040700d03059050782c4590b180c55507401d00c407609a282e070700104403944d0f03601e440c0e1210105243c140c514540c401442140007076010f2000c51049098801100c4000c0c2000484200a12303040c0c1c14145514540040e1900c045404098491080018058896280d054815402002c0b084810b840300030303c15280c0681c4144000c2c44003000740300b0115008000c00032040703034840d660f6035643c203164000c403800c071690f40d8080f0a02120320050301403106016869104030310310a0510031041d41d11b000040000d01018414808281803110162000c0b014207202482c05245460742d1409035036131761000707014900d0b035864900c07010152891031155405488248006400b96a00142d841c2c250f0300f41c40905440074001c1e6000300641d4030300f000544c1910b01045600b800c003080ea41c00e0060811200c59110814490100f04000000380400c010990045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 598351438 1250 598350188 598350209
    0x306060f1407061404080406032012070e0d050a02090105030c0904080d0b0d050105040314090d060209120a030c0b01060201150521010609021b0c06090904080702040504080a020d1404 80
    0x801c2c41c02d01101802040420250550040307041c4014130400400600540b000c588060040c07100160701480782240301300c03030749c50284010310200c1d170300740600c0030440c2c1c000091345450b107081d025000000d003c01d61001d4048480e54090001c08085052130842680148000c4014190b26450301340401c21202d0000e000520080000504000c5100c0a500125641001030006c0b5007a8802d1702d0718500030081030f40c051b80810440640300014540e02401c480d170840340a49181d0070944143d6848000c1d400095606600442d40c10102429260420882d900700d03000345d49402ca0b98000c3e0802924000040c4c022004590412065014100800c1109000c4401c20b484505022081580200300c2440500003128a9420000002101d03569a0050050000f010301c1c45204451100b121641d00c451124503980c01c55401e100c1d0958614140c00116405400744412178070786052035000401f00c49040350b08480c60800031611603031403641003003552b51074180c9003402482c082d8129000e542d00d010358450f90f040f14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 598352688 1250 598351438 598351447
    0x80c060307020a050a030906021605060a03110f0304080a0914061819080d120605030604030e1f26040b150103200702270a02070c03050a0b06010306060f14 68
    0x602c01c0085099194100080d540306401d00c0c903006003407101e1840b0300d100500c20103841031542c030f03443c030508000c075040201558544208004260040c0902c00c6807110581028000e0208040c00c282c021031055100b240c3c40c6544084450010f8080b0340d2540204070704440110308200161501c80441311604100c01001802c4034440f00001c030300034150808002c030402040000501c810b800603085030004c1040e102c900c152600f0401c40d1080f1611841000d500d5071084000c1000f003070040b4113075020b0381d00c09009015120403c0c074140741c181040014210025642d480c841401080c14a4500280c00d4901c900004c0345c00c0c6512540c0034000e0182264480d0703500d007101d4903210f0307000b9801002030707100365060b00300d80a1129601d071502e82c00a02060340100d5200c070059540304a944e40741304000000e4030400c0e10545030010304030004e4004010813034208140e090084040748041200c14401d500c100091100342ca40040010251040d5910020503c4880428440c1c6142c11440d0148100c0ba00103060b61038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 598353938 1250 598352688 598352701
    0x405180714180d0609020108150303040314011508070311040e030306101b05280b0a02070f0c0803091806030d18152003030f0402100306090c0306090b030601080c0603 73
    0x25035000302c00080e0b014410708503078420840d491304011310990007606d401c14076985014415000c104c0141403035605800810050000882c146100203850681000000e00e02c0c1112846141002094105e200340341c1c0155010820064801060078406600769010301001100e000025621300028103c0c0c2c1c8150030303c01d03000c0c3c44140300c0d015080c003d0360101c0c20511608858181141c42d2110715940e8410004a6030340340340d07400107031146d4880c0e1036881410691107a40314101c520007900700c2c0e0701c111440c81c0c03138644040210301c804d0b403800003505020020b10380e81c280407020001e402c080c032a9181c0b00101c001081000300d540c04180c082c042d00740d604005e01560711150185d0700f40040e54000d40d042e00d1a940c0c0113800d0560003200e00c4078061060300070304100c119000c0d185d03030303039020480783c0c03071135802c5003000150040c1000c1042e44100e101604020035440c0c2c4480340c2d40b042e00c00c1740f4079080019603203001c20007400c1d485000300252131905402515a5504150b00d1a0702e030054810720b0340c01240d0000103e00c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 598355188 1250 598353938 598353967
    0xb06041104170a0c090618020c0c010c08090a0f171209040f0f050103030c020909030412020111010e1e01060b04180908130311040e011a0411040e010801020405180714 73
    0xd802d51091510741c0880e05d40e00d80b20b0061240780a0a40c1080005200411040151003120201002900200f1000300384800440e4006640d0764111403610b01848403c01036151100c0040240ca00704104291a500b0201c225200ea200b4000c420500c1d481400480e88018042003250150f480a035804146442c02c846280c0103072a1344c0d140070103002c2c40c03d0000028950b011301c0e0340c0c540034401c554031003950700e80481d019603c0c01640120801c6201d0ba456660066029502884c809810540003260280703441d0001418500313200b012071041e40c9200313801030101c0801c1c82a200641a004c03112810b090422406124803403002c1980084540e0300c00d410000e002c46841a01d40d8002e80c200c400c46c2c5140c8170f141c2441d2030360508000714055800e110722031b0b54581c410f0003904a00462000c400300707000c1e004d90400c0054500d42442c403210907400c0202041030041494010f0207000040c0002d0b070fa45140905100501c80000e450265251280d0244030b03406500c00800c4001d0340385c0d4245152908040a02d161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 598356438 1250 598355188 598355203
    0xf08011503020708071218030b06060a03090615051212180d0b0a020d060506030415090c0f2c071d060d0903030b030c0405061005070507030b01060c0b0604110417 71
    0xb00101300204034a8100720303644c040c0d03146900c42a918403903c410b00810640240300d03180001860b001986c40003608500344440a0840450286808107181c60117460304c2046514010022142407a51403090103d420040e901e1590a083e4200505499211200000840c003d1000a0700319082180c5909480c0d600c00c00e521a100e50003900719242c038100300d10060000c0d4800304600000a0a001300003626103042400d403480b5507009a0a100c2070351041c1c04000007003000d00821950b444450305c0100d403074103100c214a80900141410f024241c40e00e501142c0301c0d0056002c260342c40184941c1000000c0344c1c04181505082014144601c9041c1c015002440500035200d1191245280803000403d240e41a040200040710135001d580c200e0040310240000d032030017200c941d900003e1194070441c2c0b02e40300d03500400e4014041d030281c4031181c4c0c80740c1d50302800840aa029000050310140c0031410b1040c40490241c10880c215801c218a501e04008118103004900c035200c529075601e4150514202d00f40000c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 598357688 1250 598356438 598356443
    0x90306070f0e090c070c08030d050702030a080601051335190305131505091c12050c0106030204060608100e010e0c030414100e0f030f043b06100f080115030207 70
    0x180e03111507e401a2a40e40d0300010701ca02c038018248008140582d00200484401c28080d64030b409942d0740d201c005480300da1140070900c030008491400000e01840b80480429603003e10400030898211440808549011020701e0252940169065a48000300220707455005641410000e445500740d0080c6d8400e4030072580210b883d4080e50a540c503609030f0001c010700c0d80082c1290040c201587d0500303801d42c02d0000000017004001d40713031900c542c03c0d4007902c058400316241000125450303840e035011400780c030300541c45040890103443c1801007200d011211080039041120401d85a0340c0b400305a85801d0380d002c1c1501c0318003140080818103010b851080b080382510340404450b82d040100c400e8500401a0f5074429809000c1c0603d507480d01600030003221070894007450440d003814101061000542c203c8208038121103c6d080030460003c45840300a04003000c5d100c0840750610b092070074040c1e29560b02503050100203800c50704607441e541014681d170549520607003070f140c0281601c50a070002d10552802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 598358938 1250 598357688 598357703
    0x102100204030f0210031e20070b06011403070806040c0e33090a05150913050405011413060b0f03070f1d0106091802040302060708090306070f0e090c07 67
    0x10041c050307410f03601c1c0800c610a84e4510300408207a4400ca0440d48203801008051a0301c5500c41485070243c0c00480c6401110200600b840c620b101c4100440e0344940c00c100d41c038a41c003a080141a68101d06607421070004038180c1491490b252a008001010081c0a60712a6584040081210707100e44401c60391544003500343c000084a0b80c0812060103480c0308043d04001c1d211241e0000215190140c0341e0411020f003011a580c1d0801e0204150203400c0181c22600303030424045c100c1150341e811600c0201c0c955110b0001010b00303003803c00c942500d0001ca001c58030702108400b8040d218583d5002c02441c5904030b0070010303542c1d1031030000034000000305070070641c1481040804140000544c00d404100d4040044103141c0707160f5100e0700c4050742e100740724440125180003401c000100004140440380f29040100500d030a0712640015044e0f040504203075003004000c600d80800c0d00b000c0201503001166402d08d140107414104000700b801c50341c00c5070140525904408a004801d52100307590f6200d034400d07203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598360188 1250 598358938 598358947
    0x30c071e08090310150e04140610031208010f0504150801020414030709060815180a0804170604021e03070e13030207060e03030d0527030301090f0b0d0201030b01021002 74
    0x1c00c106250000d2208030310900410841c2d88007100c00d40310b07980c2a041d0540c1c0d410215850003103241c050000040c02680e140340c0042c601d8001e40018400340d44500e002c0084d51001c2421410030192001480440500740a40900188074441d4464040710841d5400c4501150000c201c650842c1808683c0d072003c10740391700200c2c1c08222405101f12101540f8000d4040703c510f9940c07080f01c001510611b10610581da0810203114810000c0c28a0032903200050b0207200c1031071320804500d503180080d000c000340e500003400f06042c00481300107114400e002c0e166100030705032414250001403081d405000e81d0080d4084010b0f0018603501c0038480c02004204001c40024035240661289034200702c0c484089006005048000c140131f0b0003042d8003e40840c0180c0214103203501e0703400300300080401610499004c00d81940c440000704074441d05120a1000b00d000e96141e515000300c05065400c400000d8801504011044207030ba02d074104540c030700300d0302440c000c210140d41400507410203c0311158002584d00016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598361438 1250 598360188 598360193
    0x31b0f211a0601180b030c130e150907170a020c010f051503060915040809040e0d0309050609070602100b0a0e040f121704140c060a090f080703030203030c071e 70
    0xc07009100e00c5080e00c40400c4d102000380a42d218200c24040d4a00072003007440410540380d86800540306940021a00503015074982511459070802100e0100c039107549400c403906036040ca0580560464058100100f0700d200803104602690001810800c1c01d0f0341c00704800c0c1028001b5007000050910410082150342402c02080300e000c489500c0d41d602907c292400b00b40d00c180b001803000244042400d482050351141eaa41c02865031052240f150b00944039915100c1040381848101201a140e840001c0e000d2032070f1601030304000008200740101d0f00824002c001c541e4011519008106c5415400216880d61500141c43c5290b980c024801e103021030020003003000900d00c8a907400a001c1c404074101d181402c401206c80020850400b9048400c00700070900081100c1c840c4009030512034251502002443c0110380d050700913031485d100140c49424104081840090303044e000e840d0f034201410440d8219200030350380748005482004d100d400040c2c40700030321041c038a000007907a40c0340b280e40e1100807550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598362688 1250 598361438 598361483
    0xc08040b0c010617030403020604090203130804090b280e1f06020d021c0909090606090513140705211c0306080607170a0b060f03040606031b0f21 64
    0x40c0030b24448030491804c0255000c60001c10344044942c0103140c64a054100159500a50405442c0340c0701603501200d2500051083c001404c0680415000012800c2140b4100400f0f200b41000740c0100380f01c0300d24400103190075010041c1c00e0f203403240280e680907100e43e81900445190440200300c40c2d0941c80000c01c0040e0b000c1111a02131400707600319986c035004400e2416490910000c80400b0540e8868100700d50032441d0412040607001e4913001441a03500c9920b9410346408840d0b21044a41a505540402401e0a002e5001c011000002c00045087c2303c0414184403004900c03c00030b00b811a00c040003003404001c101a00d070a94402c0310000440300074080d01800c81170190070701c0c2d030040c11700080003240304480080d0903800306501c1a200c2d0300c6000702440108405c1170381c2500b0071410400e55450100041c010b501481c428800015080e155017041d080300741d0100700320000801201c00800a41040c540c114082e1044083c41a01250021019043c20011300800070305149500307010069680c0f81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598363938 1250 598362688 598362701
    0x503010501090603140117162403020301031e170a0203031006020f0c100306051c0506130330050a270321061a0c0d1d010c08040b0c01 59
    0x80c1c0710b03810301c56243c0e50f0503001d80b01320b003110241070039080004010908040c4407919441518405540040d03000700500300e140b501d25040481a40840c0d011075080030740800200510380300c03e2900b18210750440d0b9030280c810600c213001c5c1c905010380140d02c0702130015644c42c0307417a480d0325203074065507581810702c02030344a800c101ca400020320faa90400003500b50010505400750400301300a04141081102046070000c01404840c00b01503031910007003403d4030707210300c0000b84c14080080e00c4240c0702c80b842c003545001e10091010031a0400109076000003604a03080400403007860040c1e0a554506018211103048403111440d0102d00b000c1c00e00080d4045503000442c803032502c9050152040b1a0540f1140383c10f011800100000c81d00310050120b998400003001000c48004c0001c5601c2c1d0751458003040c034402055180d08814400100700648100c100304400200029042c424103240b10800b50800014110820305c1c1480820001034081118590855002e000c0f404501500ca0810040c82c0d4001d200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598365188 1250 598363938 598363949
    0x9100206101202010503060d0c050d0f0204050106020106060804200d0317071404030b090a08071a0a18140a050105270703210201230402040b0f030c101e050301 70
    0x2541d07401090340d0308070460600031030390181c54046c80c503182d01d020700c07040c0302104200361916903003c400400c01d80e441d8084164810302410340c6c14640713021130040008131041a8408002d40e03140080420406811900199005400100c1403511806210100c15654640184258441a940554400c16410004600000c021401c906030b0a64441c88195a4a6401499801c08000a000070000500f010a006a00626050507200240000e030344455064101c18030443d607041c40d45042c0201d098806142640c40b0240c40401d100044d18007074003d040d4002c00701d024000601841507100070f5941044030510840d8840e000b080a8549400300d00d04401610b06104c140c074828070042010711200203201014bc0750070140c8a14034040107414851882191407007101075548540d5040309003100d203680101c0541e18884240e880745000d01c10401113440488c21240700300c08484100c80151000580840d0483c4180c070041b4540c0340c0032005540030580c8490340180001c2040340f030241550b005001c2c5040703e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598366438 1250 598365188 598365211
    0x60c030a05100302060d2a170f1303050d0b330903030a0c0f080c070f05042904020f030a060501030b01020304030f0201140c030d0507020d0c020a0e0c09100206 70
    0x100d8400502030321190b18400a5486070042c0180b000495299108a038030990003108001444040c894803c0d85a800145520100c0d030114828608480c0c81c00b034080d8440d9100000314810326100c0000010352440403005400c001002c03480110a40c000da01590f01510014204109800400048400240005180c04111000b1000718411000400541d80d80002c010081c5052400c441400ca5007809034200c15118011091058008241458020503002c94940013415404d07007014040d00030001150701c0310b40201d00d030110381c081080b040400940c41172107004a1005840740034001030040e0085060040001c9000804d01c001d0040c903903c11811940b0a8070203002d401412001a030b2a40154440900038104004180c40150710801d483c4501142d4450f5044c14144690400761964218441a4503025507600c00e000c07405404001e080302c1800c16203442050b040055010803a0910030303103d02c060740b40c100300c003007540410004240c406144014040d45421a03001d1002550b40c81d0940e00d800060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598367688 1250 598366438 598366441
    0x309060f0203040f0611092202190906020d0e010c0308060a09020a0806090615030a1e0e0c01120501060e12030903060903030a0e011107020d020d0b0903040f090c02071505040305060c030a05 83
    0x1c000480544001f428014003980c0c0081c95150302c0d80b41410401c14030301c010740c1d0802850400725074403051036604607800c0c0d40c0c0e6907586007011030203498040c43c1c0e212081400300e900c5601e003c50b079200d01036480240d410300c0c20080e0b948504000c9440c0302d1f03540e000147d115001268a5000e1948498160300c01ca004407400071060310383c0801d200124501564099800c1e00c1000000c2c11000325400c2241b4031352189602c0990b10340016104422a290304d01e201d2520f400919070440b00d580d0241c0c40c1d000b4071203024cc1c01c00c03040d4502000584000400d0302e44030300869504d20514680201031050b190319440280542d00790781340192002d44ca80c2e104a5584041d0761501291a0829005104440100705030800e00f5142c03010b21340811105800c000310482c1c0c40481850050000740388510910300481105005540741c0b8105000361160f100c0c0e80d00001d000c02d140880718019541e00007600c1c42200c5039603400c03100100301d00c54110b038144502c0c2c00181c650b108034170a201d442c1c0c40f05d1000751f214160607407041116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598368938 1250 598367688 598367711
    0x5012d06050a030c0506070f230c0906060901030c0c050d020c0102300f07060606080702010c080907060810030c060203030103140f0a080306030118050606010906080112030309060f0203040f06 84
    0x41030100d020244c0704c00d00807002401503040410040414038041d2048c8558038206a0b20800788803102c4002e00c05500110070005555a010001942d06420440d144072403440d00501280b42c9004a0508504241e1207440c1841424060070302060f000d60004180e40400d50501d10282d9103000c003039030850040c82402c0d0a01d400001d0192a0482c034080e082a4540443c0c1c400b000355944d4002e0250448604e208101c032b540080d80c5803181e04002e0a03a03846000c00751030310400c040e02b10380d0319170421000c0c80401c01c100035050102041d4501030b0341c42410300c82999210810000e42584668000504944e005540800c1d82c40c0c00002550480c0c0c0f00d65220840d202d207042071541c460b80010100200c0b540011390b00c00000311524050b542c09240030700005072500c401e51030061101c440d40000d841c0d6402c00002d01c649540e101d11181d01030502070070040b803254900100304c98440031f000e50190400d03a55805010400820360890680c0807070000056490b41000e003004048282c4c5814100d07203082c6044d42c0380c080f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598370188 1250 598368938 598368949
    0x20109080303011520010c080103110f0d0204271115040308090f060910030204050906041e0c02011b0e04060e151212030f100e01120f05012d0605 64
    0x588003660004035002c0429802a0303150385d0258203100e00c81008881d241c400203000d10032800c84a900c0c2da5243c40310351643c1404184005035604803401003036208280002a225403924600856060380d00007460880040d08283c085403205008040c01d001e00324400c14040200703405101442c007140d00c04030341590030401070464801d82c8001001440700780501d403c5480e0080209807802000f414030391504240d080054080001000b50001096010030144002c0c2001000a5070081003a41c0070003082c1d080441080b1441205c8004151071500c41011211580c070030340001841105006200ba00c0c003291100c0038103201c90715056540103e05e07204000416072a1600c01c2c1e40100c0c070001c0114141d00340388042c804196041152a1210304c1100e2980c401440c0f1040218401c121288900a45040c2248904056095a80b02c6401091600014040b030201c80300c041d01d5403640004c05000354a42882c0c9680903286041c91048a1581d4040000307850700c0607590100e50142c201810055103484108011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598371438 1250 598370188 598370191
    0x6060301090b0f04050a0206041710090201022109030615030613020108060d0c08030c03130b0a0806091302030f0d27060f050c06040f020108060d031403190e0a020109080303 76
    0x400030400c0b9404035042803620409144c1050061081c0c5048600c5900401d520ba03000781c1c40011039070940d03888038031040f20601c1101c0300c04058107001d105103010754000039540c0000c0c146c041c40c200d9141a894144000100460b001c441c0d0150580d0258a400a0700342d0b4001110500742e8000e010b10000a054441003071804d40d0703e10340c143c5504155071604802d001541c00341d0a02103d0451038540085500d40d010000350500064600c000e580d1003200390b4400605c0c50281d0702980d4008001d202c84003050303402015950744600241e4201105503140303144e02492040200c00139405011780000552201c1d170202d950f450740b51140d22034035207101b080d14502a0401e110f02021105030704084041c8850391044c8425a4000301034a812410240e100322002c0c1403440c00d580407950301c0c5864408900b1560800d0f18140d111000301c0c0c024000031540d88014005448030000f02c0625100000043c01c80130060103071030315844040800704080340810f08410b5598203080e505a012507040800010101000030849 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598372688 1250 598371438 598371443
    0xc0b070209180703030e0f09040b0114060309060f04171207270314030c1b03010c031a040e1c030608060f04030210050a060e0403080f010602030a0507410606030109 72
    0x100203c6145403804c0b90401008030718554030070094462030f0a01d54600592a001d03901803242c9c3d407a2035140682c000921801507200a0040308207004001c07040e85c000c18025403095409481958603611031402030360100f41031429801c0075030b01142c1c90081e483d010f582c0318495810b98440b001d034441c40c0e00107003070280c10151098520030381c00002440000d141c840304c0d40543c9a0007044a04006020100b1420620402e00040340aa0f0403e6030401c14602406017694400840c2420030410700140d0f0241d01e24030701d690803580259164203502401ca00b04010700c3c1c00380008945001d1174a1442c041c000e01512103032080151900c02c1202003502d42d41c1e400540c6001d654580c000f004640214611400134001c0141030481c01551008001003c000c0c0400d91351240c0d20a559164003850501c400312a42c00060300410304543c0b040c841401d51903080012511820b402100c80c8200600d1003000420b8034040c019802c20301c00700c5004002080d034042b1000d20540681005071000ea07a01c40d070615003240c26200c1d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598373938 1250 598372688 598372693
    0x17090a060306050d030c14011815181e050f07061211030712020418050a050a05090d0311040b0c010207140607080411010c0f141e06220c0b07020918 65
    0x7800000e070013050f0341c50320588240d07400704e0a040c3c0c07590ba190841c5c0d000c3c00344641240c5032811101c200440c803107807202c4610ad000d004000082c00d18410b40c00700012014010010b08001180103580e4004e00c8105010303d6110003201c0c400318840c0d0300c440d01c1c0e400c50300c20900030a2410001c60080d4020707001c4d0031940c52148007024116903030032000300d03040b242501194050344c0d0308010105d01d9010019400c1807210941d0310115407800d02c5200e24044480c01003240d0b04440c500018000420310101c0c2621000000b4034000c00c68899203902004544910390018040200002e0000040f81c01074018002003401080002d411440700f070882078803900c040705c0f02000501480005400038a07044e0003e00305070010301d00501440f0150341c80003113450b055207094a503810710041e4a40160810491109803444c49143d4921501c286040c1c0d0760340d40409010300004201c00d6400c010420302c8940c455108940100c000365440359140c03800354995010640980c01040d2150002e159030703104e502c0b5504e440901800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598375188 1250 598373938 598373959
    0x61b2d0806060706020c010501031509050d0509060909090f0d21020a03020c16080115031e1b0e040b061203090907260907051917030717090a06030605 66
    0x9046900400081181e80e0001c028442d0101040d03032480078103150b1781c200000084c0703941076041c0302210040c5000c816491900b880e440c0710000d00e0100e5048024a80c90401e00e4440782064002111400313a86201a00035248608100294034000340341d0080440c01402d8480586500a04440380c500c5103120b0030840240030040e0720400310a41c02003404107940d140050810000058050400305510384030704107007440780300a102d0700c0b03001c0c03043d510303088520101d0310300da24550f81c2c50501036403205d9041d50035505200c2d980c8040c000b040c000c000207001d103505a46480c0f0707110200b407000514142c6050364450510000030318a801d02c80c1e60080030302e04141c0250708083c00b2500b04038401e04001c00d42010030120742410088080c0e1944490808080e203440c56175030303240550100d860140507511485c882c0d0a02c1411644a0344080703007060680c1ca100000008076000703820a1441d41c41903003001082190800c0c0d00d600710900e0403010b0304080104a50426505035562012419116603001355948005010f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598376438 1250 598375188 598375277
    0x1503020c0d081009050106080405070f05100c02030c0d080c0d0e0f040c0e041a031018080d230106020c0306010b030c09010c0f1127060f030a061b 64
    0x10000360f800000c210404034010b850340d03041d10583d0b4080e400180170540c040207000400205000600145c4140300e40045010f2a2800060032120500040c5d002d1003403901c0d8200554400b48805031401201030821000307959a45880180c070340c0060380652a50081a01ea0148240b20304818401268000d0481010b00152001c02001300068190881845000355a4584944950150345481001d00e0103e101200e01c0006150400c800400c2d04500a4a8000407000d80e0380d169900756102a0490800703a2036801da0442c000007080c500802089075000807800920101e003c81095041e501c4a5003512032074100c48007415a01c107000e024403145180140300080581e88100060a4004014500500c000c2078a0722000d40e4505080f50a4400e888640e00c10882414048440300041e5442c04030075100b020024070001d0600c1d8064002407203180e40361440312807964104800240d4a030070220410404801010541071751404e49240408a00580e901c0c800c01107451044c490707002300380c540300d041c403041c0704 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598377688 1250 598376438 598376447
    0x40621031701031112030d09030905041a06031f030503040f090e010e061503120c03040311030703030219080405180105040b01110309090408070c031b0506090102100c110f01061503020c0d 82
    0x200d00e60340510047c811358102e001e01d800b44c400d080b40240c48409205007004103200540f102a81030a071809900760711b0110a448400032a0750260101c451129886015410000740044030f034405002480041000705840010224000403184120000c001038000030800600381c9044a51402c0160000000510940c2c04c14541850190303000701511142c404103400b6201f15004941c12880341d0b40b0118050040003011100c00a0f81d0000310010282d15140d940c0095071450300c05107002141c901c44188000b0402ca8506450250000070400d024240030841d82d0040244c0074450940b1840c10300380080200c0d40136148101d5842c01c000c000e580b4000c00041400b82020000e01b08490304d24041100f44007041041002c80065172003085600d00750075401e00040e0075858580c000507c113210400c182070043c0c4e000503103011401111400421000d00c021001e8981c3c0e90709040c0011140510040c1c00760269043d803184050b1150f01001c0e4050030004d074000c074100d0180315810481580000072220800c0d009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598378938 1250 598377688 598377709
    0xb03133908100b04110f071202010905030406050a1209080712031109060c10050f09070b27010309390b0a050c280b090105071d0406210317010311 64
    0x151021514032495541000c05d544850309000600c8001700d04c2c03d04008d0351042c4400c1c001c101d80300038800803520391101a02c0f84200e110302c1c8180030000681c020031a025910040010442403820011070846082000c03040e44045000c03035404095100c00420a4001d10443c400109a103180d00d0415455400b800203a0b48268003084e01c921500c5070b0043d01c0d0580e8090385200e40241c60307038602d85081644100e8986032994118080c240c505011014a007003010016940007510324002c4102603071aa00107800501c5407050103001812402c0c510031040303094031500004280c0c4100c5a81007101440751000088405006400d07003c401008203070005840703078001e0060501d4880507504030900404a80c08104e021a048201403d8019030101c00d11440300b2240750301c83c2420000344801c0c40c2c104e20013465890380c6111310200700810298105c154481d5800b0030050b007a6004031180c108600035090040d0356415204800051943d9007048448018188150480c0c0e48031041c02e06505040041100c540728 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598380188 1250 598378938 598378961
    0x9050102040305032b02030705070b07230a0e09040503070204020a02030d020c0c04060605030f010312020c040f0204081212040312091e050d090f0b0313390810 70
    0x10240004004200240000d04403001c00c1c2517084404005001801c0380500210314a40c409803062040050301c2e60408100c4041d02c0d0710203200c2c101070b40d03848000c0c1c41144001101b82540f8900c89440220b20f41003c0c01800024030a03114107522080580410035542c104071001405030304107019840040c101600a012081e1460050301d0420110040780022604807890b01d11050b48850740710540c038107003031040c000a40a1071408a00d58600032039424080201031000901c2d40030400418241075100380303e50710306104014003e110000c0200101d038069000385c06844018000c1411403030440d0311610448030141d052700c50440d21507a076502c2c19102c4640881c000410b283c0c941500c0000100040303440c00400f42c0e100000441281141041403400c0312066458007440740c034a03014404844446142012220b444801542d80c0e661070034034a01900b074810006004103410303200246005a5070010107640300240007050400c5811120141c60781c522442200300750b800409115101070b100b500702101100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598381294 1106 598380188 598380191
    0x210c0e0c09182503020c0d05030609090703030210050702100e031206011d060c0f0304060207030b06010504230d02091e060a03020913030e0301110d150b0d090501 71
    0x3ca104660340d0843c0903c080010702403082e01140c485010500c207071110071a0544011340b5540095558622480d10900041c86264000030000d0440e03070590300502c00c000715407404800604018000c04118020300c142004070a003540610f903030a4286000445e61103523461008130520303001030b001c641082200c81c26a02c15074020311584000c0c0004943d8a5502c1e09103070031031481d08040c0c000d120010701003c075001450070340110b020401c40c0d01400c5a05416600c05c00115000d00c1a4025a00310b100709000003110300c2000603043c0b0140d68050203000d040050754001a242d030754120b488103d80c0c00350070070084041c1041800507400c1003066441803102d9055500049620200402500f00e49110314124800c2c584500c90501d0320b250003500800c80c06040300d280011690010b0704412400e400e08180c010404940804c05007150040c001143c1070520044481010b0050302d4000c1d503140d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 598201438 598381294 := by
  have h0 := BRFrame.cov_init 598201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598201438 ≤ n) (h2 : n < 598381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
