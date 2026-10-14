-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0616
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:45:05.815309+00:00
-- url     : https://prove2.me/submissions/3a5b77cc-a1f0-4f06-aa00-844e9dcd8b4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110611510 ≤ n < 110791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110612760 1250 110611510 110611541
    0x9010f0c0804030b09030a0f02011404030e03071502010c080603070501020703020d0809090411030c03010b010e0d0303140f0732030a0209030a051c03150b070f06020c06040b010e1603 80
    0x907403241c035451804c0d1030844950191b9800061103451082c0c01c5041300d81c03516007600c0280840310008131000140c00780548010140b1164130304c03650155406001c080041c0c42c801d22a51445210003000034081d01402c41d90b14003107000d00b00031440034200499600160380c81a001020707110b03c1c6900b805500c1c0084607040d201c01b070081c8030012440e994a1042070145018110607040c140d1210209400c0508038611a4403c0c0c0c5072010b07103c0c450f40c00030030100c14040112024540c2c1d088a040c1130740602a035140480703a03101030004100100c9000300241307004807400c7ea01c4c140c180b4010051002c480f41c22036410304000c50701844505030040440015a8882081d15015041c11030f4040400c0c0f81c8014900100c0b26600304081618003145120740d02098220540360030b11004041d444814501441406054000000019020b09008a20190902d85540b080045690b08484070f01d413070b11001c045da03048030700d100b00d4400082c407000f002c82002d0003a56006048001550303007100c10b900501a0b5100103602 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110614010 1250 110612760 110612767
    0x305070c08070501090e10060f02010f1401080d050a080f040309050d060504060b0a060e060702030313090b040c050c030a08060a09060308090321120c1605030d1109010f0c08 76
    0x10811010381000304034280003080c480d0b082c00c0000d482542e01ea00303c9141c3d2140e81e4104188500d40c81044411283c80e8201608035500c03d41d8224050100200107282c8c00e41802001c0c0d01c104408014141210f12900c1640c66416285d0011507284c410603481800003400500401d01c4595a0726503242c0103072207403c2410086a1f1040072400747c19195006481050340c0310100018045a401a0150b50703404407064969281001000b40c0040146d014090240740080781e06021503c0400803102010444040c0c0248995101185405402d014502d540079a00307201901807454000c90644040c2070340ea00103581480d8411004454802300103090a034030600f6400001030032001482690059809208800ea070394401006040c038008054042041c01d0f101d130100d4141c0e54155106a8400440e2041051513544603030101c24694050807007080c0c2007075100c01000b02001400402440c2140040c1c00602ca40d9114145020003400b4500a09011500c190b2201003058801c0c072855840c2d520440440b0304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110615260 1250 110614010 110614013
    0x303050f040906120507060207050604031410020310060e090c030f0a060b0d1d16150908030a030c0e0f090105010507210c030210020403030f03020307020f33011a0304030507 76
    0x58403140d40c000d64502040318400c0041c40341c2481b9a03c09480607000404900d031404010400c10700c501d10024060031001003c84240c20014003100caa0a042d1840035501c0707042c103180c18040030520740310b06000314503104502e1825040115200c2d02c03405103074801906584c0d40395044807914400816440c0d10956401001c59071136005006400101d155000c00281840c64000f245102d250103410707214540d200d4141e400c500c03114001c00000f0b840d81d180e00c1ca05203003100c0c40c1c1990002d6254014007007600002c502c640d401a40f40d404081603080c15a40c03220083d01c4a01402540c00c88034102d550409008001481594050030050026038490103c4440d00826402c07141010003222111343c0000300c20800180916038100070210062140355001c41c40c1c60700d5581e018101110803103e440c117054010000540c42c500074007000340c441e90504203880e0106020309524500210104480c0b40a0030741e01c440c503800c50201e502300d506a86210000040b1440740225400207a0070007401101044000c104180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110616510 1250 110615260 110615279
    0x4140a050d08010f050103090f060e0703080703020d0f0503071d01020a060f021207020f0703230303040c060906030605060904050a060302030712060c030b181b0c07180905070303050f04 81
    0x4101c481941d840d003995504100d030714040b101d501e6028504050230701404401090070704143c7c50000740d1182c1c0004903140040350180c2894015071000e0603800c0e010030302c14281600441c40e19103101e066650044600d6005c64190755038002a503900c0c0001d0b8491040036141c0321001507081400740b050044030748201060341c5800075a0000c20b02c10f81c01ea50040b40c0444812000d0745819041003c0707001030940d15008011440e610a035a03c0041c2414022040c000d19075908102c3d02c00501000c40c0a61340e40c1d1816062400d000c001620031040040d03801080099058401e10a10082d50402400c40d4500417141e400c0101400014202498084c1d45850001c0180d5080003110300401400c8000854018207040c0403040701d1610a004040c10304050702000729540c0e600d01085030441140303070344006446840119514040c0070010030004d072000102074107150800600f520031a069600c00100800c90902c1460540d412080d00411581c403034502400002d0040025200300500d1401190519644000c0340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110617760 1250 110616510 110616523
    0x110a170408070f080601050108041e02060f030406140912070303020904020408030721050f0412030c230f0d020c1302090603011805060f150a03020403050a0506060901091404140a05 79
    0x1c0d03c0350307041e410303042000940a0244600401c02428190618503103038442620956581320502c00315201c01010800715500c1200392842003162018803034482c680341c40c0060042006603988059420759500280d0846030025a42d562110110901428100c51750f4007500a5081107500c203a109400380f0001c03800d602c1c2080503144c500c2c00380703c240d0b20304110101400c40c0240c20035035040800108104000340300d110760341110f00b00d9500c0b266681c1807010030b003000c0f03e15002e4032000502e100c0c090382c980c16020510908075180764010105a81c800300b0061074170340c0d6900f200c2e444c03000940c0000380c1920b07080c6000c2a8091b40c40040c2580540342058500009030340d58001d070801c81c81c441152908901e003004921509520500944080c2e010030601c0300003600019410304004140b000000d10100ca040c402d070103071030065034410111032160125280240d01c1301011541c04d8021000c00d0000110f50381580583d440d241c071000c40704502a1105d0311003020076001400b81c06028030805041200040040211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110619010 1250 110617760 110617769
    0x20306040f0b0c040b0405060708070b18010b0f0306010e0603030c0102030703050a0f020c0c0616061805160608011e1502070315020a0207090b03070b180f01110a17040807 75
    0x55115100092070104001d84000e0300c05869040f00384410300509840908880940d402102c00603217454851804141c11311450200801c003004a806006448000c615240e00007020003000b8480010080c0034040a10111a80e095240d0300c00c500402901144255040d0046405400e5074505010321346000e0030b90b4400d03203240000a03a1a403c0040030201840344039a103034406a0706615045a401d45540d4841000038814440d01c00094030040340864401c0c50b40019610013814040c40c00c1c6103540280c845c11a2078103803030a00500800a100f00120440c0100361181911903140c075909008840c0c034007405800c041c9401c42840b01001c0760444d1490300c0c004202009900a014084c11460020030300e0b201c60845024050052202001c1560040340013001d441d03031400c0000381c00204100083c60f2008541c410f020703403100001c95003000d014403101c1414001e03082e070703006108a020000440300c065484039264402e42020040d0f4000036010b103100c92004a040101c0342c1000c0c5c59410301820400168030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110620260 1250 110619010 110619023
    0x1e0b07020714010e100e360a05040b01090504060216050f0d02120a05090a05102706051204020d0212070602010f05010b03061002012903161a1602030604 67
    0x4108182c564280308001c6056084c40c1c200c00440803030000c145c60324a42d000181c280318500c80d03055007039203501e4095001c0d18600b100c1c118040a2110006021414010103107521110042c000360141e44d09001d0140280e078000d80c048000c2c0e203411501c034000c0401030021102c0039001c0091000b044c0d60b0301022110580114003901500ca02ca41c0b407189041030b6100700005541002d0a801ca0406414040c0c50326a41c0900304280d0301c4c6500c0d0300241038000190020b550003078030300c2200400990b1050090304c00c81c1c2d1007495001c0283c3c1e502202013080c040e500c50f180000da41003028111800004110b10b4000b407010f00081c46548071640050320001c40114004200d6112000070032082d42e090042402e400d03110b81c02049a54105254005503100080c200d80c0100a85108400042d02c00d500c20680004800d5048044a09401c500c407a486004201c2511030710a4401400c141000c5170401022901601807000c20b00003010040c0c805508042ca1807600954200c8416001da1030501c2146c2c4100d04c100d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110621510 1250 110620260 110620273
    0x6081009020d050f0a0b0307091104050a080304060f02030c2a03010c260105181305070906030212010c02060105120a23060f070503070302030a0b120109150c0c1e0b0702 74
    0x7070142c8241002001c6110711806c0c51164444c84d02c01050000a9540c5000d02160000411648018910aa82c452500080c07091000a0200c030040080d00c1030361925640e2100c1c0481040e0100e0b034902a407922204584c01c00b040c000f040b50005c1e14400356400301440d240402114810000782120300005680307000c2201740100711000e102c0300e903a001c036568420201d101c02c1c0d4106001300d204040591000005c2c24010008205a00a92120352083d16030000490741040e8035031400340f02411080c030040b8051405100400b40c415410300403040030301001e40c001c11140c0c1c41d080420003c0380660702071155a000c0c0041c144040b40407906000001c01d0020480c604080007600c1c40d82c9010700060a03082c941c2c2e181018043e15039445800c494100c011031401686907110381c2240303001401040a0507500c001c1b8132048031160032042d00308184040c003900540c80210001c85141080c0c8005c0c20703074540000c0345260121b0001d0204e8200b00d20002c00040c150011412980d1070202c096001c0e600701e4050390225 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110622760 1250 110621510 110621521
    0xf0e0d0201060501140318010905072301080c03160e03010e16050603160c0602040909050a0605070801050d0f0503071209082b03020c01090203061305060a09080406081009020d05 78
    0x2402860700400d028a081d43c1d051520803c5ea110502020f05090741009006c88142400003094101019440c0c0040a840b0059510240c00440400c44850704000d041100c01c40c03030056001e0384685103d103c3e0340c4600da1840ea01d00f4000000601c411811506100707181c5210549031b2406d10418031785181c0d01c00103105000440c0158003224400c0e82c00540301e260108200900340344412940d50b502603050800401404c6107103000d05c007174000c642040071114503210448007030000025540841c0d81c010a01040703192280042150b0118003401850b4006405d041c00c140041c4804848881050040c0160390408019545130007008160400310385c00075445103014402c3d2002801900714078004035400e210907402d00311042d42c01c1803035040c8810625a020541c0d41410724203400c0f41d506035500506032440c910b44805a080104000c000517943c070700c0703600005a602c4d4254400c110240742c100004604040c074091044480e020001c019194280000c0000a540c04260024100030801001c0119191401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110624010 1250 110622760 110622763
    0x605070203090f1e090c0403120507030e090405060105010c05010e0d03061e1508061c06020c0706020f070b1c18060e0c0d060209010302040b0309010504110a03030f050a030f0e0d02 79
    0x440c920244134611000103003519082c07026100100744000e0300c2c454500d60310b51106c240d05002d9070340080e20311048100101070f1f4170391100085c495a44a6100e02040135200e00a02802c0d200884006060b0b80c0310000601c0b840d0f000745200c00d101d81c8681d0004c900034941c59500c5041c005620b074524082078460740140b0501c0800c0011403003051108504180b050b00d40f40503418500c020514090600030748001096854486040411402d0000c0d2a415048405442c05000940c0018903529180c0105d50010070451310100e2003413610f480241c020150281420141501030340305a80c038068a6212980301c1034022024041c0c17014004441c140c400c2c005050b030030108240c88844802ca82603030465180107501d41d0b01d121148503156005500161280e50813001070300244580d4101640b840340c0030040212860301500260b00c603500c2601d40c0040a89804103000304104036000c004c02003a1004110703610244200c0180903000d60a00e0701181c0040c14890060840384240103400c45504036280718000070383c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110625260 1250 110624010 110624029
    0x11010809030c120d020c0303040c0306050a020a0203070206030604022503030507090509070c0602090d0b041b0e040308060d0c030f0b0c1602060304082503030c02120702040b0d060507020309 83
    0x200075628044031641426100c030340810041004038004a0103d0098060742e050303402400c10f030001c895070390626040c10071080d080c82c031003120b140f41004002010802c1e80e00903258a10b031a41c00840c204101c60303080100d00d0308010003c03600160b0910400c900c1e000d404000811140101d85100b6200107030f07080080170343d58014003000c180a11010304110a0311140030080e8031036194a0811440c1010740341c580082c0c41500e082550204010511509004210303024600540c844d80c48440d40e554203c3e42d20030b40c11503500c1040d01ca09101c40000740031078000e200c2654030003402061082c0300a02070b0b990801c034000c00d42007540d0080e41405007208100c07403450140d4010300005001420010640c8101d81000c0e0030342c0e4028015040800400d00b040a040c0030b40f049520942440039600b104508030201c201c80c058020f40019041ca90945202800030640d103610400f040052483c11105800380406000f180c00888e4014410030b0496010440c1c5100341c074000c3d28503a02847c0c0d610102c0c41001644039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110626510 1250 110625260 110625271
    0x703110115060f090e090c0418020306040305030c0c01140402010e04050f0109021b0d020d08010b0405010905040c0c02040f020a09050306010e0103140a0507060315090213060e0f0d110108 82
    0x1c1c5061803900160116070900760031103046161400e14460110030488906a0320b51100341407140300300a000c803000010981d2000d1030000d032001c10605929000008503090f0009001c0c2d055005100800d001c64800c2d0002d5610001421045103031111011102e0f08580c0e100b2500303030349050b030342003400215a0301400079034032000112020b0185040059080c2c0344180706208103042c032a40010b0340498072401c0780c4025112001d0780141c80c0c40b021404806511044e40740d40400000341c3e00400850201c1d01c5205076010b9a070103a4030f01d1403950801c418031005100c2d41902c1c4081c00080360154005940303074000c0440843d40d200000d40c4500d45404040d01314144e54000901c02c2d001140107109280b04c80d04600e045942040e0b8058000452000c803905100841d100909507005c1c0e241c003c034055802d071308982c0d41a8000e00a00d9100d40d84d61140004a00450460b4182e8481d680020840070f84105011845400c0c004c004d260400404400607210000c8460211f81c0c9005a00c1140065030300f2001099004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110627760 1250 110626510 110626513
    0x804061205040b06041e05010b04060f110c040c0c1b030b010501140304110a03080a0314060109050d14010605300d09030f050c040507050310060e0109052202040605070311 75
    0x30304143e525041d00c10b400401c800d000f140c1c1c0701000809074144555401000c1d22514041040d541c50f6944100c4a43c054040c1c4070204201d80707800c0201d14480c2c85201c1201c005040034002c090394120403c0f01511100c04402c0812a0302014807000c00c80e94040030342c018085c501144141071541c9492440008140c0c0080d0500c10843c5020800c80c114404503507120340e02c10130300303284042d1600020f51050069000546920b401040072904690198040c281c20540b50a414515989803401100c900c00580901c40c1c01c003034240350880000340014654241c8401c1c400002c100c035512440812031803e880140d0648002680580703c400f0100300301c0203100750030040c2c050507800d0130103a40600720303640a202c000c0c10210036a01800c240402480341042d1900014401d00c502c1c200b0351001452070b0070641d004245035131030381c5001a9444c00303480201c00050041e103801c0c046504d01410881640d1101c4040d181c83d040842481b85224401d100074000b404c119114691203442c0743c01d000b440059110700c084080d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110629010 1250 110627760 110627771
    0x312030115030b0d050708060a05010909120c06060503121c020f0f0c010209030a060501150903030f03020c16060201020a080a09150b040f092603010b0301050d03090e010308040612 79
    0x203100244140a01208450401040c04448070000c94070144c8034400180183c01070200211703c0741400b0031083d014a003000381c180315903626a4801e0049841c003040c01400c0da24a14148400c05000316138007113485005140000b401e03942da101080c10800d101c80c2e0460b40b01c1c0d00140940f85203840100c0303d6100c108255086062540a0b01181d04610401c0691242050046074590071080309404540f410300000c0c0540b44503186a00d040d80161000f80201503101041f9500760030301900c5944400304480d055a030f10841643c184000703070020b502480510a245c045c04d0402864a1032100c11000200f40039030005903035442c940c5c0010004500035004441042c140040340700400d01d80035010041c0c403a04000003c410600000040040c50003d550703031007060502684600380f055100042d04440501c00c46000c85803080280218944002d010309442280e09100610250030710000e9030200078864200704840c40c1e00c4074180780d00180240d00403106000d0008003845081e91044001c0303144146d00805000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110630260 1250 110629010 110629019
    0x9080d11030108210705010204030b1509090c04180206130602060906090a021302070f0b040204060b0a0903062f0d06050609031c121406040b031c05070c03060c050903120301 76
    0x85410110a1303964942070100300d90460031008004456025078404021591945e80e80781109480300115642c5032848002c2404c10410b06200b00800d1207240d501003d800c020f004a0104030081c5000707108400700714040c0c017165006032030b01c00c014058a0030302c10300740051500e840c00080c42e202d8000d2001503d82c2100040c004111000505a07035017548c106d0708150358030800d940c180001d02401c440500b284004202900034030100801e014041c0d4003d8500740081500c4081000403441403c0da41c0000481750001040400c905600c05520f00d01c03980400c400284100742d000140c0062007034404924407000804e2001c0e05107600c50900100800c1e074030281400c4211000035150b10440c54200040303051840e610503454840c9072141c2c000e02040b1700c20490301011400c121098102292101c0c0600e14080000e44a480c00007101e6500c1d108107603103d400c10466001c1240c043d000342c1011204410480000310020700350f8081d202c0c59104a40d25107448000410405152541a03c0c02c0550142c08000500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110631510 1250 110630260 110630263
    0x41406030f011b0815090c1804180233040806150a09182310200a0c2f010c0503031303020f01050133020c2209080d11030108 55
    0x2071202c2e90300e0070a482c00740c1d07485c2400f4074040507451019500c04031500c20000b2203181e42d00030304044030143e464400311481c000305200803a03c200c0c40700d50313200500e404a1401807402001003030340000d01401a8004e4080c051260760104280045c0c0d88030200c010405000b01681004240c0d40421507599005003004041c020804503403042c02018030300303519a41e1100140198901807506c46a1202058062911410904602d90306414106c2010700400c0380b594860813041c044e0313030b89550a002440e03406605240b58503941e58001c289400500080300d14400200e8003401d02500f00c4817400010596400c2030820241c031a6503100d05040c184054000c07004042480041540e60107008940013200141c0241001d034075101c01444100c1c3d8542c24600007041002d41040980000d181d80240320341c1800941100041c054207502782000146e0010091030743d03600c0c1041f010f20b141c0040d5100c0c0d0f600340710742c5007255065440c1c5180c11748a1004c0002c01c5482109144101d0903210006e41c6c10905550400d003846 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110632760 1250 110631510 110631551
    0x3170909060d0501090212010e0106080102130608062106040b0603060405070e0c0913020a0905060412030c02130504050d110304050109030212010219090501030b040911010804060b041406030f01 85
    0x50158014403044802c008095110171000d5400800c1c80da0780e03c901d81400d9018148191600505509040c00050303003000500a6034000704003040c41d1030240742051000c40301c0c800300410841c0d0041c00c102e0b1120300301c200c0c0103038500301d091b004001e0003c510346800c18488006000e000c09000740c0c4003c04003c00f0a4000c10340c0d5040d1004802040300c0d6444030551803529008504490b035001100013986104808103034014000040d954032024000c4c0c0e959020440075000754410f01c1c1d071400c1ca405240c8000b82c410340314004030303620003043c000e200011903415504503142202c049405502101402000a8104aa68030190b41070300045251a08020008045c0c0c00b2606c4001c0c0100d411000142c900c0390290140d69802028203402141c0455510000740300440520a05000c40d280c4501902c07e030402e8000c43c00d2882d00b24850510b4881910011109002c000340b040d18841c5d070740c1d400303540c141d03449024181404c10000c0040d0300a0804404050618880c01c02c9401c3d5030b0f1525003822101000400203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110634010 1250 110632760 110632771
    0x403030e0a0e2401111002090901080309010c1101050d0c0c020a0b130603020c1c09030308010509010e13020111120d0b0904020d0818030106061101050709080717010b04020f0403170909 81
    0x1141490f1541e6001038503020610005040340d0301452109a000e0780031a40a040400e00840f00708016907601c40d034064480c032a0580c1280022800c0001d903011070207200700301c41403036010300d07000d49400c0210749a04200c0b098902c40c1c04c0000c5428840505514009074040083c0c140903800343d142141d03841d40e09224451902c80c0c041030513004500d42005d0301081c001050141c15001194222a2040000800c494154041240842c6201001003010b080c0603078103e050341d0b03070500301a8150721155007840102d012030f00304904014a03a481625541c105114418424461406490311003d0340c41c400c106036001c006900f4041c031080d908000141c1d403407600203059030740c11410040e0369550003104c94202c4103205200350f800d50701302400040c072554041417007034003140618002c00003912844421241da000030310640c5d0184c5e10044d810301c1b0144598180c54500c0700b0050000035031507001008a0144d80001103150043ca501040810500100c0110842c61080800506141c0031880c0300140c20715401400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110635260 1250 110634010 110634061
    0x5061005091504090e0102070506010b0c07031e0c06020708100912080c0403060e060708071814030304030501110a0f080f0a05040f0b09011e0e0601030204090303060b0403030e0a0e 79
    0x42e000d00d240c2100003281c001c3c20590b135041c0b1440040303604090207580020707001c8859100c0d000000901e0701040b000d035603800680340082c0804514546421a40510080142984040682c046000251954031020051240da000360403400c4c50f2190003400d128810b0308545109042401c04400160102c00c178010040c1c2130300384010340d62281c1d1880c0c1814001c070341000b80000d00d04021102007910000340944100200d41d1000003507903c0440884da14040c0b0901c0101c4407611044c18031084e1604846130205c090080c040381c1c1000d54075204c9030300756000000000b5540c040005c030103034450380c060360070b4081d1101804c00424604001c142d030031b58082c0040c10501d04580c1d550202e01040b0b0140844d0b4005504803420307442c1c9040100c18140240314140382c900c2c04650b644420108002a80200c801d0b80413400c010b814540e207550240f00284c980c005044007050340d698404296a0702c8a406007000e0b5019a80309200400c43c40107010513a42c89400c6030040181503010803210050211411040964030300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110636510 1250 110635260 110635279
    0x9040f050a05070f0525080a051309060b121b130302130507020312130212101a01020c0103020d02090307061205010b1c150b0406120b0d020f06221502010506100509 72
    0x30714000100f00c50f51001061880c00007002008e240c0e002001d04540c207d0603000c8042c0c1076841c0c2003102181c4291166140754902480180000100704003100c0d80010032102c81c0702c807220035038a01c4046500c441c83c01d040750084820309100750b0509807074850304503000110030891810b03c400040d69070b0096a42c0c0c03007103002301c1200059084111000e40c0140541c050280b50400f11041040f946880c0400c036241011460103049034060112840f01070303aa00c0c0c043e000341c0401c40720440114003960081c00c404000b16002c02c804600f90300d041010300020100c540d11440f1030a030f50390740d680c03e640041e8410040a481406004042260240002841030790000005030507100e80300f48c00350742c50096100346200407000c107001509540002403911080111503042001034030030020003903045030518002c2e4000514001c107100b903007441e100510166444441c4002180c5040b003080000c0c880c99042107440107248400d070b0303110580900a858006c801120310144c101040da900034994000d00c0d140c544200c0301a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110637760 1250 110636510 110636557
    0x70506061905190608090703020603010618050d03020a0b0c03090c211005060a0806040804090216060903020a0b01060318020415090513110604060813020609040f050a05070f05 77
    0x1a001c160003880082d082a803281c3ea04142c1c004412403c0c8925008901180c1c005502e0080214150054a500424460450342021021905250209408030f00062001004682c2d56034202510500610036030040c0380d011a503191807045002c0c041c1c1641c544c00c00c18814401484408250f100a5040545080c1d00200c240b40100c2e961250a90020038240a507000300341403450303580c2005201b0042519200f0000c4e0741c1c0c3d4038181d6660788c1100c2c0138020302e42c1448203101c24401074000381f0150154442811040c3c0702c1c2e455840c1169108501200581d00c1001d48004002041c1002c60040c903450508004001d400744d40b0740244030505000034403482c1c0d20286c2c40c619041e461918000f60440c624104907519180001c020070503d21401030315000005661a55246020300884055403182d945040719600c0304c070400494a0703030900c8101d911000601001d00181c03118810480e440900b0040802e09040003042d8070f08641000e0a1401001081107041c500d40d41c01500300c5800024584500611402da07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110639010 1250 110637760 110637799
    0xf060e0117070306050108090304060504050d051e150f0702030304030f11010603050304081203090a030507061404080913060506220f030503040e06031b0f0a09020c01061a07050606 79
    0xc8000c912036001c19242400700456141c0d0003a0103881003a2034031905c0c1d489110f00c1e141c0e240554420100041c1d0104002c0c0001e003410100c40030403c1c40391003100c448480b4224200140c200351030f54038484e0b41c0321415040e410a10079030102d0308443c803002d9028a0303081002c8002d440380b000a00107424130428030f10010000e4443c0b500d5010141c511070080040c0360f128540b50780c0342e0b0704c0751050400c14440c080c000000d0040c0041200e000300359500007804980243c1d5000e03074168000c201d05a90081e40e40c000500418030300b000c424172462280d600540c1d541c120300108040044c000c00f01103a072902d0808240210345918040f82d96800c200350140f511940100d04006001500e0740104083e00b140c1c46c800010400004060016039201c4811141c0541c1d1300010b141e5600d00c1e0020103800d00180c44500311090810a922a50754440600b160381c2042d00d40d0b4489060307074000794a0034075aa54921003000040301c5098003441e074440d01181d843ca0082651101c030307030354000904094800e81004d203955900600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110640260 1250 110639010 110639027
    0xf0f030d050c150105090f07051c0203190e0303070c1707031715090a020f190e03010c1403040602090109090f0c1b051c03021c02030103020411040f060e01 68
    0x40141203442400340200018182d41081e65410074610400c1c42101140f0703080300e00f403410b840c001791030480d0655481490fa91258006820b00051203c200100c100b04001c90200f54001c01a4107400760381c9041c50b000407a481c0d201140c0030286d1600c1d040411080420210460b0380000031441c0900d2500e0050a00200424111025401800002a0390000c043d0070029115401800548242050762005258100750010703c007a070b40e03c440c9440001e040480541d020300580811100502d05191018441040d840b155032140808101241ca0f1506185000d001d6169036a085180c40160000869031042040c000900014200d58000c204050203900c05c100050090000020a12541c0c409440d000d008024201c0c1c06000501d841c0707880700302a8654002036a006901c10014480c1d1040101c00c04400b00056000c0410142c081000c101c03902d10020380001d0303e044050700180c2ea940340d40f0401c000c5564440c01004401c000b400100800525450703080222115400c051803a0000341004035107440c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 110641510 1250 110640260 110640289
    0x10e030f070f0b0c070603020d0b040c090509150306040807030e03070314070b09060d090615080f0c010207150f03021204080304050105010501020613020d05030702030a0506070f090e060f 82
    0x11a1503000e045884002810000300d800b031000910742c05848014070989031080e0030780070710f550717200c1d640c20407441c1c0c0b203030b0300034020010b140c440041d000382d0440001c0d00f40c5460001c1e000000c2c41e90300080c4118a411110550814185070028085020781d80c040703900d51000400107800d1020100d40d51341854000d5101021201006056500050300c03440c01c01d0350012440c500105e244640200814504400c0d400c850303400d040201405d0811542e400c1550241400300011a0400d84900c08643c80303101d404096000382802401520958281802081c903101d40002200e0465000100c01c2003682c0369030031202c01c01803041c0b82031151185407034000e8000c4d04c81d4030b44d50b00481c444201040309002c1508055030055204500074801c0740d030303103800483c0d0340c00040d922005c945400140d114010b10b4100c07004000d107071140080e03c5c140889600083e0900840300d071b050355250440d00401415580c002d81300519603d050070b00804140c00d012285494040c003d0400303014200c4007102150590300e40c02e801b080784 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 110642760 1250 110641510 110641513
    0x80a1103070e0c040f060c030c0b04060e1902040b0a0b0a050309251401030501031716120c03021c0212030c13032a03020306070822062a1409010e03 65
    0x1410450f01e0521070358460302c103035001c900741600c0208416228000c58028940c041c0d84680c00007540f0740b21802003c1c405001190310603a64401545021411b02c9002100341d0007000014210240d8010b0000b41d800c40c2c0a510311a1500c1a408d00c58410648140c810304901c03490050b0b12592908901843d280003c02200040352111000c060700c08452059981590303200c0e103040c0c07488911000190b0554500780030003898090a525001340e1280018003400d02c407825541e841c041d0780e083e0345036501a83d15138209400020180c512a8060540422030100c01c8505411000800468904029120540f41100c0442c104000001c40c02035105103003510840084030f1119615543d8902c0c00102250300c18403040c003942e03c001a68500d403420320380d2010480b034019015107481d9030740280444460a00800440342007004821380c548205900130102507640c0b05180024401c5042300b55120355981009000714a60500044015070300d81c05031b074100d15601600c4001d0b485107441c000690320101d495004a130107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 110644010 1250 110642760 110642789
    0xb040b07230405040e0102031005040c020102070b01170106051f0f030603081204060e1212040305040e09031305061611030c060a020606040609020a020d080c0f07141006080a110307 79
    0x70240c1d07801802111402c07141045a03c100e000b5980c00d0740000c0b0386003210507014000070032640c00c242d08402c04260b41c92000601d010a20364660240e01400e030000c8921858090340b000c1c0f54842403054001502c0f0454441100c010f000307404089040400c40f400c002c0040440510284d10301a402c0540a143d0011001d900c0302120f071441d6100701c1c0100c40594510b41003403000810900040348000f000c0c078403406458900403011401d1511003c0260003182001010440028203040d814401805201d4650245079130b40401e500707400e551502900700307a20a08040200740307070708a503801402c010f4a80c054900c0501482410019050244038000d50390400783c00280c0182c0183e011402a00c10a0301311410041c0c2034a070070400f4101d009114000b03002d644000200c080c20f601501c60b05900166034031865190407410042884103401c1030f1001c560007403550b010310300480780900040d4210700031010100000382c03414044554602034004060a5541d8000b4540059101800060003070a032001c0c40302d66 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 110645260 1250 110644010 110644067
    0x70b07060218040c0504030b1b040609080d0305010b0d1d060a0b01080108070b0f180a09091101170a021605010203040c1802211909050c040e03070b040b07 68
    0x295000154282c903107000072030380703818528081c442c22229980d141e07986810542107130f494506160000c0c010345000c0c0f5607180048029044000204060401565181c071080e01e07020b0802c0c98801040204014141131400500203000543c0c11342e0b0900d8204600860082c540c1407420b0b0b140e200c1c80f108000203004110810010300840e400510a9142c03c0e0b072044400e0b03a03600314458a480305c501816250304001c00506412900c0d144c0540f01002c4043c0e006100170141c03a0000700810b20740c2c2d02800c603e5496000f031009100c900025180118001e082401c82104a04400911014028114800641d01190a03601461810b070b4420400307174040002c65603400c040c203015541d519944550002d818441081c01c4d0307180028001e0314200c82e41c1c440030042100c440c0700f807003c001c50010410040400c103180721034440b100c18001e000095010f100540b10980840d030500c000d82c0c0c01c44c3c1c200c0c095944100703c6400050709444040d90320a8014650f60040e8490700b8088403e5040c034081c1200140c03101c1c0c5000d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 110646510 1250 110645260 110645273
    0xc0302030105180108030a031d10050708070503100303110a0c030c08061315050402150a090512071811090307090209030c040506180613060b042c011403070b07 70
    0x1416104110f81d648008440966903402c000424000d44100d41c0043c80741020075800794101d1a000d034080703018414480b10b03400c4000d240840380e6440420444d203c030180107035503410070350091700825207251252a502c2e103940490303c140002c3c440142005131a029207903a96406024400c40075a000001109403580d906000c3c0c070000141c01b41401070302404010071110300081020904c0c03a540001701034003100d4011801d0380100300042050780c104103040d00c1c081120009c0302c001d020451554a8a40c2c0ba24284400d22910700c000b2000c1c0f0300c0540c0422011710803948000300e200384220154001180c02c04004003480d00c14054026540c0e003610030b83e80003003468155034016140b4810150211900304070343c44200401e0b9481a03030029044184160315a61032041000c200c7d034841009840c44041c03509012140c0c041391400e9001200c0b20304042401d200b01c5100046258042e04000303812905440112031205c80c442042c41007a491021030341c08805240c41c18002c10380208090041540c84888504101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 110647760 1250 110646510 110646517
    0x60f030507030204050a0902090c0f0d05090102070b460204080703060f0204030b130f0203030a090503070b040312110705040606030c17070f1103130303021c110316060f0c0302 77
    0x40341300724109400585906498401c4004d1035800410040007902e43c03130614140c42c2d000380701060b250300b4200910304003004640203a82c01130050200043e40c58085040010110101500c03044a1800b000020a1221011070603082175041802c40300900340200078503444003d0014500d12003450000c14005080040482c5840403240038050078032000300c640c149a1f080388a54040240f19140c4103000c9078444801d49a907038002c0c1c0c0b060115600d4428290002307482c3d85c100c144440300190035084144442d0409010980013029045041801d0908680e04e00c0ca40010052419003045840034100003090020032851008000c0035004000d030644440000b400740c00c02c0341101010402801c6481d400c141d001a12038480d040c65a10328280803000d84e0200c41960300313442508c01a101c1840a4105243c001c480c0b2001503200381c00502040c2c82c55207061190070050311402e02400b10413600103d140002108981242c48000000030081a180c64414018204076111040d800d14042d05054503941580c000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 110649010 1250 110647760 110647763
    0x1c0605070906090303090b0309030d06090e1011040509070c060f0209100e130203070c0821090303041205070c180905010f1e1a06070b06010f0801060f12060f03050703 73
    0x9072040207844810940b841d114600c0020001900500704209034a408409075422506501c240d0b03203000c20644500045d2017580e0481c828041c0d40c0e00c41d1408155041003901444418a0301c00e1102d10a00d02c1da20180d0b008500c111405240d041d0002074425210714130a800e1580c0c030220400c42421a048110029080608854084c806182c5811406070060b100444560401003420303812050075961400039400242c150424400c0f0108028001550100a840c0d401c0b0302c10040c0505880149030b09401a00192040445030001c0050101140480281e50401016070400f655180010b20f82001482901d40c450980d00e26007442400c40c103103144e0011300d02d15001d10000c2c8000582510400119203201185500c00c0d143e00043d400305425542207508038141501001071090a2140450b0055100ca1411078054602804002c40c0d5030300306035041c2a248081c6400c0d01550b0401070043c000081c0525260309001a91000e510840e14580102010381051408140c403150f50b0300e4101e5403100b4a010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 110650260 1250 110649010 110649017
    0x27260312070306050f062a0d110d0e061207122901050316080c090a1d0f0103081b0f0d180b03100302011409090103030e03010c020a0506151c060507 65
    0x2910f00d000444560b0100300100100e14018014a500554a05450a854400d1055a0411f452000a00108000070941d031208241d07103200b41a1a4245100380b10303038070144001e010402c24240c4940080c1c410a041c0042019801e4980100c02d840c0885110494580c0d13504280b258401c940c0090400884140642c420903c00344070318005441c58002100d5a29044120303c40c9010f04078880c034043d41d08500f450b1105c514014010340071400070301030341c0c01c03403280340114a2800d0202e924802c0350303e500c025650403e103402d50544e070b01d1008a110b03150b28080340401a422904425000780080f4141d01281411680824019a07003d8040a080900d000b00c42d11041000079014800c00110385c1300b48c5094604810403070a6600561b094484448000c1c0303650340038440001300d1f40340c403809140a107001c1e0703d0390200340a50504250a407864807a01c041150000c4007841d00140d00061455000070826804220544203000072032a0011442902c9041c060281e00440601c05070340c0c082ca000c4c651075617 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 110651510 1250 110650260 110650271
    0x31317042102091f0314030c10020c0a0f11030114011a030411060f0c07060207031101180608061201050c0d05010501020f0a03032d060501272603120703 67
    0x44120350030064030751010303410202e070f24002004d01c003000c080c0d0510030b59100c207803440c515201c1d11507a032003a120018030011135100044036801004100181d03442c040701e03010150300c1e111181010030f0720365260220007040104025000300400182c283d20060081000d802004481c04048418034544020302c40c00b440c0b080354015150241108008592055411442020310707150001c081c06210760025500e2540180c06101040326107400b804110014040c81e4010160503080d41800c2c001c22041e00c2800d4140118000540784040384400d0880c115800c2c0e0402e400741e03039074540100b808102034181c610215460b01c400c1000400c290400b40c2042d608078a4100402c0e078032180160b036205040c070f02c961883d90100d40041d0000344240c100303100340078505c84045828402110310800d61a122085010f210340c031020240301c0e41d41d01800b1200c020031080c0c0e896003004d0094a40310311000441c0251102d0310034807140400f0303400e403010402054040c080e044950381c1d5a800300e5405840416900c46e80000c1c10700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 110652760 1250 110651510 110651549
    0x20324060a1d04081308010b0109090c080a0e0304120b010311180c0304020a030b0103050c100504060e0f031203010b030a150605090d0302120406170f040c03020603131704 75
    0x4020070040d6900440d20302a207601240740c54005001c001c100b103071516820424140799040c005100310043c0b03901c1c4000f04080c40e0890024145a52903000240001d107401080640c4079070200d8440d82291200f0800290b80312440310300c2d8107506c00c41e0840c0350141482d400d04400c00c500302e43c103e8100ca004031105511842c0c5c410400c8004130251382e034454001c501102040c0c181010320000c5420610040c000c261282e600e82e10080e4014090703000780d440d9000600c4081d0700d0305240d030707580c80c041c0200e241c414500760612201130a22140f14014038080c0e80c2c0d104031652240c8082000c503640c2000b401d80680c0303a40c0c0d14445000542d10848001032010304002540c182d41d80030030020420354500b51165410071012500380070b03284030302c0417040c5c08520855915080692008000300f002c1d107040d59800214103d8003029101c000b02c09049020100c1c2e0035401c002c00b00d80f1322600750042c1c03941220701a60b2900c44a00c00d101e000e0b134540340540f50554040740003144043d2040100100e6403050340a10845500c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 110654010 1250 110652760 110652769
    0x803090f120601182a030e01051b0a21020a0f02030906070609080d05010b0309071706070f050f0f0703080f04030909020a0c08130603061707090c0c02032406 69
    0x80000001039030748510010701c40120614215820f5110030700c40090b00400303980170f0300b07500c00ea0f035640801203948250390703084c110303505004008118134003000034811800e02001c0c0c06410f115121100c5c60b10070021440240061048620360300740202503418444620740c0c2c4520170000e40c404040900810205404080207a0000c400d4440100006000c1400d208442c1c548001070315200d001111211010072001155009034455240601a04e403901741d12441d203a503e40b4645076060304940f84202d400c020100440301d0000f0020391203002840c003412100740c0040c0c1619640a00c002c040340d0180c0201d0004246076948000e446428080e54901d5034a4844014105002805940c081d00103240180c2c144120807864004000203201751406242d0846c45844100545c0c1180a14604c4000340000811007654140a198043c15003001c059004400001c0c4995556210380b054080e0320f500c81c103100382c200e4065122030b0500b80d0003038161050b941040d10111395441e101850290342558400c0401c07450b060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 110655260 1250 110654010 110654029
    0x1020f030405060d0603020301021804240902160c060e0414060102060615040b1612020c0102030a0c02010c080c0f010c0914040902030a061e050703090206032a040803090f 75
    0x6200051468142042c003804456803040950811694880d000000140c07400d100800354003038100480c0000500c840100300a80b91040505281d0700b04c000031102e160a5006d170404216001c1800059464044c452512250081020058030050340340f440006d2854200b807045500420485040140030920342524604450036110940168002000503c5c0ca08045000801d160300043d205410940d550f50b20405981c049400b10307128200d030402040c10807054007840c3d00078404500150007401c3c00800000d640340120310840c4200301304400034000f075900070b00e86a1a440d4115036047d580d80c0c0350403005075a03007c403056040c001d0340c45e01e40d0072441303144200f41d005d00352411140801c503203000880800c400b80c1105082603a06000360384018002400510072100300900003500c1022201780a1001000c45000401d0b1205041c2410120001640c03002c08a0354083c0401d1110350283c081c0c02d4201741c23207442e85d00d500d605c0c902c0000707400300d40350100102030420641c1c1114101c0700015142c051022440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 110656510 1250 110655260 110655283
    0x1409060f070f050a09030c0b0a020f01050103050619090f140c030c0f13180c0509010e1b031e042111030f030903070501020a03060509012102060d230906060102 70
    0xc01c0d40107110030071407056005103132086141c501a0055070300c070307140d0720407001040c0e0080b9101c40c0b001455601858050100c2c03045401480000c000d40c1d891512080d44407c401400030160b02004810071850351441e600260440d508408222a007159510b4070200303014001e0803105091161a04c000a1840c0001c1c0e80e050300e800103007041410004102c1031000030030b5404514800b00e501d50711a4041020500b0100c94258000e500744200d40c0d15010901c181e131001a08019109900081040012034105003003c0c0c601103065800c55030ba075202c0980b030040340c1040394900040750440080c8420712a40325400c1c0c0c07040e05101c00c4001d668550a81c2540d1400c4410000a0a60010700074880c280b003204c80903642c0110302c6402c0d240b401007a903070345a089030b000c1c032500b4001c65500c00c01800030341000300d10503024146501107030301c00e1a00154013240c07124010300c00a00c2503100050881c1580d0181e0082c050411b0b15074650301952204c1004081c0002044440f40d0051280701c2c006641c642c40055140b5462 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 110657760 1250 110656510 110656517
    0x50a0806060c070605130e13021207060503010317160606050a0b270103200703080c09010509090c160501090b07020a030f0813020a03050102090405011a090609040f1409060f07 77
    0x3246000d109946a400507030141c0540c6e400303075000088180d08088071512940d0007552000011400b0703c1003000c1c000c0145d9820040750b000c014207100840e001001c407410b60350400c01c0003003461101d6004c0d1365948114000040d141041c41491020890142c100004ad9001111615403298070f480001110f8000c00c80f0901240412146031800041e1400c55411040b1042c500030880183e04017007090b040307640e05403c030f10500000400005245c1c1c00041141c1004030603080b07619090102c0e00003002805842141e41c850050100485d11818000d021907003904403c0a500320348002e81e05016000b8a1510b009941d8001c032140055842c1d84081861024a580740c0c907620f5070070320404000c40e0300f0200101501501d842c09907250015995000ca80342c02140b00d5000035030b86803602000e010589106074410b85078203030009480201c44511a083c1d5003c40815900d40317407248690400600504000030904031800d1030111009185540303040014410860f0004550842d11903007104449000100c0340103000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 110659010 1250 110657760 110657773
    0xd1211151b0c1204080d02010c080402060f0a030e0d18050a05011b03050706050c0306030c03060601051902011806050f13020306010501030c02010e0d0f0e09040506011a070f03050a0806060c 83
    0x1c00812000c0c061940440003107803010520841c6a010076480b80d003240d5001c1e4040902c1c842d50960900414991880620704940c940c2031503400316000b8000c0350001d112000300465600143c1b40300394060300c0341c020142d0860300b8942c00640040d1452010030f5025500241c04080800c49040403015102100c5041c0c0d100422240e641040e4031801141d814118108001000071401241090141d207025040080b031582c1d4a040a4003014585500c0d5101c09000350801c0b810070005070307004400d860a480019400000200d1007150803801400310083c1000b02c041e000e40e00805100f620340c8054820110132070100740d0b070b403a1409080640840d407000254154001c0b001801154481d80005404074498000868070145424505013000d1418000c840002d06007084102481d501a651301c400e544203880800f0941005c1d02c81c0c0d5240d500502071040306500326400d802d84c6851103000c441d4116017050345d1102a06040c540101580c0c098140040007501c0403000c42c1c0145050030464540c80c80320001042c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 110660260 1250 110659010 110659051
    0x109020903030c0a06060f060c03020a11240a0305060108010b09061806031303120216020f012001020301061218030c0204020f070506010503010f14070503060d121115 73
    0x29501805156425010920038441c450000f0448001071521861021861030705005198071300090591003e000c10002110360310100b500825190207194110b1425496003045901244004420301c5078151603014542c0800940c44241020305181000703664144081e489650044482c820203003c0d502c3e061804200303420251408034010310020441e01e280000400c40400010359941049620b2800d601c00650010101940900b07801d441d00340c4543d003142030048805106041c21500c20000340240022000301c4801c3c0c0c000e03035509079081c0b010640e610310034030503214081c040d41080c81841d02080411000c90440310f45c501414100c1c000080d5000d00c1080d01e510100d82803582810140e0304580c0c00c0041ca198241000c000b02140c0380a913000b0160f55140a040c1803c50752001e0707400030040d02d0700b40850540109014030302d800141d18070b04543c60381c852100207440240d81100c024440c5658040c030b03100c070b1900268450030b581300c01002e59040c3c2d0000c181807150742d102218101d000b14080b004045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 110661510 1250 110660260 110660279
    0x5060108100e1b0a03021c021e0c01020d020f07030e06030606030a240906061b050a122c090603011119030608010501090209091005010e01030207050102070b01030c1d0c0301 76
    0x2a0f10103407008000c20122865412103090354012010701000940015140d00c51800c030441240e0401c94907442140b070070300d1017450360000c46445041c032041450001942041c081094040d43c0b10303503031280001c40d5a100768209203a0341c0e0707018440c12004900d140c406c80d01540741000c00e80348144c401501c560b1071585c400511100030546040c901c840c910601040504d0401c04d41080f0000c1c22848100184042c01c040c805410211130a100610184c40007a100c0700040000c02d466414540c402c19140302003002003000d0340e0b42458081141a101844d405c00359440041008803d58948162203c0203c1d03101da1090500342c4510000030408000200440d4400c4503644940041404651600040d42500e0f61005400c3d943d00307074001000380c0e03004500050203142904c507098100c5402d1405074103480c50b210018102072807142100d4141036010030703000c052003400e4044440c0d180d80800f03070341078641e10ae00e00070039075107020702070f803000071000740007039480f088014400502859540c5400c1d8290381c600044c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 110662760 1250 110661510 110661539
    0xb07030c0f0b070504060315030203150423030a030605040506010c0b100506070b01090c050a020601151b0f060c02010b030604080c0703150f0c03020301141e031207060506010810 78
    0x40755611503510107070010840c1240310ba4002c4081da03a030b040d5610b15100004060354140c0c040751130a82d903a130804000580c2d00064590081010440301245980c1b507050a100d0184481c060140030b130120781c041d80716000040000c00e02840141c400304141510f40341844110340c4111350b0240440d4803070f840b8102040d440180181e10070781c049503020030a0784a501240043c2c004910443c0e4079009900103001e0301506000e00c10501c140d40ca011810103000400095991406116801814083c28480f0642c0d1388626101c1c1b0440307080c614011980d6080746020802005811000e442d41c500d4089225000f92042c025146840c00007030040c078030f64455840c1c0c8201948042038420b0b80d13111350100000040c115440860381d9848420000514108400c0c0701015076181011000405104000602000c18052010700810b1020741c1c8802d2105107401d64000402c4888034003da043c07180429015103440d0b4040148074181c4581c00a004d651039003001526845002d0f04e4004110f84140400d010300341951001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 110664010 1250 110662760 110662763
    0x90203010b040903181505030c0d0b06040b0c0d08010b0a0305092503050c0306221b0b041e0602060c0d14130b07090f1e080610030209100b07030c 64
    0x60007144080005080318259a41200071032004810181c2c1c0c400d01c0001c44000b05442021403600e1039110600070f24034440241132090300980420601c4c140d5627a13030710a5008030009060103603a5500c500003041c00c2e400405100794644502ca48800d48540301e9012a03040b5040084d080f0306181e00c406040d0301a040007456030a0300d01c580840088600d01c6d086805000e0943d0f0f802111200b421414403d0510340e079801c070315009501003000e100e0b6030000401d444004114070f1500400ce142903192440c00c0f900c4100107840c2d2407401003c00301e0214803901c028012a0f491042011110081034a84144416140300d42030244c5c20280c0002d80b480d544034010303c002e1045040c0010a06420754180c03d9511007a11300b5000194016507a500b00f2145c40e080d650045014103000916070b01e00a00740c0c901c10002d02031110751905454000c14090300380c0614001401141d41aa03038646000280c400084c03150388010fa10908040c00420640c183c03510101d025109207181c0c1900d0a03039240c03000e603400c8002c4e800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 110665260 1250 110664010 110664013
    0x2060d09060b06040e01180b0108040204110c060412020712050c041112010305030403020907020f060712090b15010e1c111815010206010602010c0219080c0a03030219050715090203 79
    0x80c0310001e0b0741d02c0f00140701400404059203281c2d4103009000d0203210b005106da02050385860faa03140d003a80c2041010354001e904840c041000810390750f214036580540010b0141e10320481050008001c0e03400921418040c860b421030324016503c04c119462a0002c1801400079000076042081d030b414150000100d591000c1d4500389400341c030441203115000260710070358040c1c001050500440c600b1503280c0d500206035200411401030f120079030300e48074080038004030284600c501e1506a4003007d600030740b01d026040301e54240680b500c04a11404102003500c5540010004025a005480d014140c0c0610305038072403120044138010380d925855900b41c6a4541e60040b01c0e07000c2610500002d11003680700702d9008001e40c8010079004000782c40e004040e0800420359041081c20b580351540040c41c3e14003a00c0c00100c602d80c80380e050505c040288a421109181c50041c2c0103010300341605034000381007000c0d4203100d8007a03036418ad140c1100d0707900446030001c00200e0710005544160311603400520181d4001070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 110666510 1250 110665260 110665271
    0x190b0a02032502040609050105100c02010e060a08160305010605040b09031204080a03090906050102030d0f02040503070b1c150504020c0f030a09080f0105010302030a0308040309082e0902060d0906 86
    0x6072482d003200300394081102c00081411009045051038040c44c8001c00300304e18188803950510b0001a4aa1051003103402040744003001c0e04196032280d00c126035800000303400140e8079202c40300c00400c0c0c5502140d11603201038808080c80c417642e200340300b40c4d4100c0e00d040da2180c0c1040d04020070644154441d10230984d06100c0d00c01c001c090802e001e8001c0005194610050043d00d95610303014010304e0082d444031904601e40701c01000281d030040102d505084900c0800030b074000032060842d000340150b80085803d84904040468007900714402400f240c130405c1d000c5229807001220000540d11043c200c0501d80b01c4811003005035060a801402d0303018861810754016682581b02186550071061445001030031161040000078400e004001c00d211007000280010342c15034012a5072500421801000c2105610000f02803520410b5200042c1102e0016501000322f1149000c200020058a030070100e94003001c103040203022481901ea500b0b5014181d60704100800544200a0504123400d49105403a44d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 110667760 1250 110666510 110666527
    0x201080403050f1c05070c05061302011e0309030216031a131703100b041d06060403050a0320060402010e060c01060906080106090507021203010902030712090303050f06190b0a0203 79
    0x20003a00104800c01c032131061403594003590001361480a8105028464881204404540b02095041d8801c2500c0d030b044524403014030048400180038501b1840c10704490b03045044155041e0005501c2c24040c3d170813117501055900c8560611181403000901d100030000304501001c00041806030720105000d101d00700a0b4081d00c50011007240c6865000c0381c02000010464003074290001c480c06420b142c005542061709000107410542e00039966041c081c01e00c0400140301b56100b01c1168003070341c1e002d0b05490f080402454064104c1030034a000064140c50f80301c001d1a0751500207401c0c7d101702d405940d6000158051020700c080ba6102009028465403904004580e80d4040c2c02003c005000702030002032140e103400038050840754040c0c11203045402c880c407d00080c501c03480541c4d054418010380160f5035103c3c0c0c0002d0b1100003d1001e424030b403600303201c1341c0d034281505680440e100314101c1114006654a907020040b1388c14241014444041003e03c09000c000c15500203040103981c140112031820307000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 110669010 1250 110667760 110667787
    0xf020c0f0606090903070b011404110f040303030f0e1c020c15090a0b0301051e040906090f0c050306010605070602030a0603050703050f0d18030201080406090b01090606030501050d020a03020108040305 88
    0x140a84040d00d5807241052010505090007501c1e44003014002443c1070446550300c0c0c04000c0b81c18421000324543d908509070700c9581790361104100f240303420001540c80a8884071501c00d40c1052105a0109190941044031001e25001d1006281c4021016023100302e0700302e990000c007060003840101107120710000c0e0b803c0340d120503a00101400b02d1190303561310f502d02001008114a451b820024030044280f004102d6034075500d144043c18040c03040b2620400b003079100481d000700390400d4054404c40c100452941403003024440301c0910303070040b2060008240c880042c986c0c3ca9000b88103000010f40f0420400011030000c1e8059a00304a9049010980a83e0f03511624680784980d001034460340c000f0700e2013a83c000d908104021950101d810040c11900503004200c001070918071019061241440029080020a5105c10004c41e48407044544c2d95031610141c0c0010b100d140901c40109140030000b1845151050b691500d4503401001880ca042c21640111242c1c000600224107001c81807205d410300042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 110670260 1250 110669010 110669023
    0x80103260d0207020906040608070e1f060c02040f0903020613050106030609030f080f0601020a08070302010e011d0106050306010e16051209030702040b0628020c0307080c2b03030f020c 81
    0x22100700540c8a0240b401007050714800504030901c140c1c03419208000c0e80c1e501143e010b00300c0b0110350841031b5a84d41e107580980c20710b00e42144400140c0c1211300114401d60001c0019007410300980e0308010448000905804035110080c01a000d6402580014201c4420041c3c90b007905100750000701e20300384e980e66032005030f5406c10310440102d03c6480e07500c4100c0d5406280744d0f50000010f046080d4500784600045c0d2260b035000f40c05017000000040703180900d4001d410031202d00c2c05680003000401d14000d2081000f2001c0392080040d0b50030280005410700e40069164182d500f003054160742034031110034101000c80c0d40c485540510000380a003001080c8a01c4003640300b4140040a140c0da04002e104001c1199032080c94030307108080511001001d45c000c03201c4200c0f0000141c051084400954805074540780d120492581e06200d032100200740c0800100c2c180d842d80e031096a80c3c80c640e0710a65505100c2e02c0110032003400c250000014200400d100350026002d015920b5030061510720400071040c240300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 110671510 1250 110670260 110670277
    0x102040902040f060e09071205061c03020a050d11060115030e03031e281a03030c0717030a17061903120806010206070509040506031002040f0f0902090108010326 71
    0xf0482d42c410401030380c0040e50300b41d242d5811142c0c1d148524107081c3c0900404802800301006990320000601d45840c0c42a4100c3c60700907036108030b082c42c900e17460000d5070317041c0840702168240900b08525222501484204c865003024030003802c041d030301b0800318920301240700030801d00301900c807101c200c0f00d04001d10045016500500d02d010004040103446001c001c03010384525000842a104c040f4070000c0c480505003028903030400411030031a0080c034403c41c2c0c4c0c0c4000c00c03d81e150200144211001100040d424100e4800d81c00c1a89140900c0289545034015010a8408102d1415080340700800c0c0b50b091961010005250187c034264807030118104810300d42044a10f29059024102c203550820003484d403001c0e01748005c0c6214905084000c1060113501e280314080c584030030108440c0c0c2d40a2000d403621414101085480f6a41c80c00c041010413503522441071004110107000c110038403107000300d0300c41c150103071070740983c40c3d01e1940c5414100700d0300c80220b2071000d0100401103080f20014001d00303180303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 110672760 1250 110671510 110671529
    0x2007030614070e030309130b0a03060e030d0e0607091203170109090b1b18030304050411040f0e0c030f0603030c07030602090f0402120403111510060809031c020309010204090204 78
    0xd182c00030002e400c0031103440c02144aa403041c02000a0f5944000980c05188071320317180400c44904034008a10921225000200420305050418945520001c00340a4803c0307030040074403d44250031034245d151241901c0354000641000020300180507850301550300c2a100c1c3c03134009040880414800022082a007140c04c0640c1c540414000f44040d5920598008a684403400340c2907a100d00d441140d4030078001040b400001a02800f460780c1d409100b070310300800c80500140240f00803c2d450741b0550780180031f00e0030038240d220070100303840600290044c464100d0075005442c645131506402c640f1314000b0b1005a06100801c1220000c001c01c2c02000c0c000c52141c0005078031209683c040010f13980302580c07018061403040c0603003066040c0303450142c0c0d0401d40500b005401d10241d80340050074001c44460f2218814103480034000308901c1300c242c00040f2184c5590396a05501d5641d075203500ca1180c40d00160781074040844103030b00e0002d580d008503040b110034000185800d585a01c010705070303000f543c06114030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 110674010 1250 110672760 110672801
    0x30203030403090b280909022208190b0a0e150f01050d0819050f070c0603060e040203031909050a06050c010506030d050301030f0c0f0b0702040e070620070306 70
    0xb01074020840c8406040d940248605001a441c80d1012210070400c40f244050805c1c0300001502d07025040900281141c1c05042d56941111200c0c0400ca00703004440602c69000c60714005048040865400001e00080e41c2c04418000f0b5602c48801c1208080c0c88402400d41d928200004550201b04081e81c00300e03d680522003905c0c0440c0c4405503904141d2019010b1043ca101c08000140808111140551300a90900d1290b0354a5811a418051114103542100e00003900c00300340b08803010124111882943c040c00b032a80c8038080d2101da11001c0d68002e4059200340036660b03003d00d084000703004403541480d296030300c40e0f0b94200181c0404115481a8041840000e00fa15814401e000e0a42d200340254002c1551540f1300710000c00030311052202030300318002c843c40d140030048009000300c0104000071584071190707250288910140d02101c0120b00ca80d181c001494842400802d4007821100da40d01c94220044c20704178984200200000241c19600801d140400056542d126030700210445800c1c20a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 110675260 1250 110674010 110674013
    0x9090201030f15170c0405010609030b07030204052d0301020a09030204051602060c0f09040f061d01140d0320070f0603110f160b04112803030804020315040302030304 73
    0x200d03080000c5602001c2d0418038000c00419a410200c02200c580b0700c4e088a5101d400540d160500040c0c550441e402030410000080e40759000014106582c0546204000354550440a800320322030303886000e40001c0d00c50015644003050744c0304050303c0d40810841c405503d00c0312000900726413100d0903032000319444000c10b0040d030a1034441e1a0f84a07022300f0968850115180010f0354800000384840d50460001401405c240c11a50540c2c0c1200c10140c800c2c803a00600052182c0900018001c0d4482022011483c1c079120003004030b428100c80080c5641500c3c99084800c0c404000300180d000e030144002942d500d802501a00d00d500d0b5242c10361400380c1070140c1440da0311421011140c2c44130042600b420311405105a000c401c868490080155542d602c15000c13070f05400c104034030b0601030880007400341044140142079410380c203545800c03540282030502441c0c10010140281c00d100c000d0700f054410030301c0000d004903140d0b07410038001012101c12103050010f51107015403c03641100103030000301c203010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 110676510 1250 110675260 110675267
    0x409020d0b192904020a230301030b0903090d140a1407030b06030604030906030902010c06140a0c0f0203071725110a03120f2703020f010206070503040305180a09090201 74
    0x660001d0f20f040640c0c00031a410305404952905a20b8076841203500041c8560802c2c0074006a5207130b1020b5100d041040b1800e400c40d44120b81003480165000c2c0c8081c00051041003000c8115510050014415501c6400c2a10303071040000c581c21040506114120345803011420401d526240740c19810000d00d4000c2c20b614024100035809880303a406903008006202c0086c1d040b00c0302005480042c54005802c3d1591300040b9100042c4400c00762115142002c5845110081c508003481001e12800c1886480d11520080b1210b621041700d000c0160024000e14002803406002185035604950420782041d2800c4245031290401c011162495071300740c1c0c820000c2020315900b02149050407203150712014607546550031301035006182035040001d075540ba00722040c010528504980840310040e101490394401c141014842400264482c0000c4504161150300c00241988284004e44e0750300d0443d00c0d56039054071240c2004500354460043c402a0500e1a240d039403800004009084011a00303801600014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 110677760 1250 110676510 110676521
    0xf0f08090d11100c0f0b04050a1a100b0405060a0302090a080f07030b0a050112080a02100f060f05040207050c0d060902090703050105011b02100e03010902150903061608060409020d0b19 81
    0x10248005292450b0105112841c40c0c40705c160041006001c07030780e0703900e00142807110b0241c0c0140440d80c1ca91a007a40b941140111511400d4440c0050507841d8841d4080d0206000d641701711580001c0030025083c4140c4a40c0161400803000b03003050000795120340d405803d29441000300041d5070312100003042407104410b5103a40000c0302c06802c2015504096040c01c208842001c05840310200064280303183c1c0c420855511140741901701000070b1800322481202804185c4a00c19a000030380340c010800307161501c211401141e01900a201c0d000c072207801e002e69440206800c0d01c032140c6d10560b00d40541ca55803000342c49585190780006e130a6050000242c0210320011007000b0b0480038108903c0141c035000c10480e5920b45604003000e624080000090246c819610000d42120b01300c146a00e4031584003000c0c0c214003a04409aa0042c3d030380085c080c0400444094110004203542d01090080c00e0079848220300a001502070541100507841e401d505c203c09858410649461041c038096140c11841507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 110679010 1250 110677760 110677789
    0x307020307051507020304032a03050609010f02030610030c110d050a0f0e0a0302011d030703050102040501030b0102031e0702180f04020102010b0f0a050402090307120b040515040f0f08090d11 84
    0x2101c05034213090800a40da030240e40001050708c01c0711900b40d0b0110400700320104412203000d110075403042c8c8034640705483d440c05841244081d1300b8081c2e01d568030444d81c0241ea10446016101f110101c840c42da048010b407580704116030510401c25054404518103202c601508011074448994840a0801c0142000040398481081040081a00c0040d544a52012003143c0d02482d010000d107408040c18254074001d00c055075414400c440001042103010f4001c0c100300c640c00d0320208103200140c4c0042ea124072075104200e0007214614070b103888501c00c1d80050202c190028203000c0100c0a82e13041c0b801e1000c400c4c0c0c1d46081a00c0201c040004643c1c0c2401f454144010550700b084241c810800402c000f074400d800740300c2c841d58001c5500c007000c1d01c0401c0034900505042039408103011841c03c02903a040e4065078192454001c040c0322068541500218a00403640300c144850740c9200303a25021514440c01038202d420000030820702400741d80380c60f041505113005491011880314490104081e000d010b440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 110680260 1250 110679010 110679043
    0x8100b011d01082a0d090501060501050918072615041b110102070c030f06060503071419080d170a110304020d03090b030a020904150b030c07020d08030702030705 71
    0x50880760766440b48041e9044014150414a0481e412070041007041051801e4151110003184a520950882d0840e1000a005070002c01205458200440e9180700c0c804a00380c10454414407100100050403810340d001259140c80f0801d41085060807440101d104089148107840509000660303040d0348008094500407902005000d003200c050041c183c50340d00c2180240b24542001090380702082d0101d802c241d602106200c19561203180100d0406044401681d211349041c0001c030b420b041c000342110039980d01816900070854070504200d001e003c113101e040ca03410058100014041010086d8003001c203036070303120003c01065464290340d104100400c0e22170303040c0c20045006d000f4090300080360f40041d0140e4074180803940905041e20504100e43c800410044000b0411000c0710300741d405009585000c41c0e0911481141089000303551200380107803e0105020004104401d055400074454148003034460500340c0601d42307d441e100d410460740c002c0940c100207505001c0040500602c8d00303600741d184 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 110681510 1250 110680260 110680307
    0x160b070605070309050601060c05101b180501020a08072306060102010c17010303051b06150a1202010807080a06050d06050f130c09111c0c020106090204031e020a08100b01 75
    0x403103903071b642d14040c0b09410601c030103070090105001c8240b18800c500c03038144c00300b80445440b207006c48821040307041c800400945941a5003840d00e01418018044070b805900070001c400c4203869808255002e00c00882c1e800c0c1490074080b40c0541a411100103050308840581517070b2810900183c00d4900440c0410700300301d40440c14081c0c5040d608002070640e500b62070055100c01c1144000702c103440355203032261500d00c01c0504005030301d00d001300300c9002903100742c429104042c0c0d101c141c0601e43c0d1042d10000e000c250721034002141e061203107e40d5540402c414a01061683d42c60003c1094001c0e4000c080d500340d86c842c0c007000781c1d80d0104c0c0e4006030041c40d40d070708200d086d21490300c1d216840b200c140200c0000b41e459801c0080b2881c4000b01307480d94060b4002e0b05c0203410007202000d000070210108104050f509220740020b80c00180e10a5408803034014803607101580341c0510b07050300440d0204080760700100c1c090021440040401c20340311844010036001840f0348000b0009400b42c81211a00c10a100c1c101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 110682760 1250 110681510 110681513
    0x90b011e030f1203090b040609050706080721060b070506100b03060102030a030c230304050d050a0509010e131107060e0601060c020402030601021c02010f0e03030103170a02160b070605070309 84
    0x2c000d05010b03d4003d0040004090010002c50262240e544080c04040e078400510090010320351020540320321034411214620740e580c100f51222007045600340041400c5218511060341e40b8001c030403a424088800040b0f180c1c813000081c409400c861000d80d104c0c0e12101c208400c0302c0c045410300c409400c0b081d1065055140400c0002e54900c00c00001030105a1680880710301c490043e03440350001d8000550100d000f268481d1480640d4204460556a034811a1161540d2a0150003101e0107400c031990350914041c900401580c0c10710a6624194109000c1002448114594810703000079004098032070ba40da0700b0606200c03080c1c0b8a4042d4071b84c4113400007401004102d4011a0302001554150380146c0c981d03403181d0042c0d013858844d400070000f08030b602c0c0108034002c2d0706510000704020240010030840d030364400d806035a070000b400010002418803a280000503ca20080c0c507400503103104640384065008000f81e0003944c00d500c824007000300410b9410401180307000b0b131548080031703140c00c200c005502e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 110684010 1250 110682760 110682773
    0x6081801150e090f1f18030c0201080f25090e010e04020114130e0a020c011b0f0801050f22020706090c06020307170c010204030203030309030c07080a050307060f0609090b011e03 78
    0x901141c0c0d0714413809248440d0011703c1c1508006401d0f40f8010a071000c02c0784a04014041c43c1078080200d0000f0500e070001208140d0004003075000702000c00c00701c42c1b684100c0a0712521400d000c03051400388288034800003410a1145034840c00703402d035502d20181604107840003424241402101e111030080600c040500c1405650b02c04045604810980741720792100540e4200a00c901261001e46500f05024840c000c1620701d20307981c011007260b80e0020790610941040750b5100b000e001e103079484a450329006c1c055281075002a4140d20002c046035103041c1d0000002400ca07030005104880c0a034403034210f1024412241c4d0950000c14031350019500c4c00035141d8a1503100c90042d80368001900003c00e4082000c0400d6050b280035560150071039903039040a6112a680c0d0704448410805032154078004550f5100c0418080c007807541c00700003103050a1580e0b890038003a00c248005500f44951b035580c001008000b902941c020140900241080d550601518034520030006c1901401510001810800644d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 110685260 1250 110684010 110684023
    0x1e0f1005031b0d090c0611010c08011a09090708090d0e010f1d040f0509010f0b0306070305060103090b011203180f0303030e0a082106040c080106081801150e090f 71
    0x100c50a4250310002c9941c1000580220b5414042551030002c0800401080034241d40c10380702161140c1170914646aa2282690b140345c0d54800000d81c0100100170116000381202c140ca090180307010304003590107010440000c000c8035501d00191400d0207100c03d040040c45510328002652a1000b285007a040010b000000c01c505440c1c200314002ea010410301003000c800000122000b001804403219220b400c401a00c8142c80d905169460a0340303a61070301c00355100f0004514000b80103840703681d03038801b802c0c1c00a00d030040c210381c1031540300c403029000680481c0f80c1c94040c041a4840038940b03011814014a100d0041099991010380705409101d805400d000c0b00c01200e61525000c1504040d4109060401c840c00000030300c40e203004503d8458100314521804010240e00d0704040c01c503540c5104000540304e04003441404a0601c10040c00340a10540340d16601c0614122003550000b00c1c0c555007800c6840314106d2404410310000140000c40b65a1185504444140001d041001d89003030050303181c03507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 110686510 1250 110685260 110685271
    0x10c020907080415020d1a0402040825240e09090712080c0a0f020117040b180f1c090602030408070b030603070b0a0302090f0d05100e0a021e0f100503 66
    0x100030300040803c43e83c629801281d0380c03032410541d21400b401b21200007a044452441e0701c5c8021620600c0c11906152007550100ea220b40001c1c0000310540b5220300b85074244c1200c1e1540598200c202142924540c0300030700542c500e40c0210309031405004001400c0540d1078015903c41c0c041e85017440582040010307a1001c3c3c1e0055803e400c00c00c2030611340b02c502c6209560200200d805000300841c107005045038680c281034001c1e00c5080089e2001148103000c003c0032240140068814000300340c0140030000809800002e80d8221404d140c03884030100d00e4003401000d0540300354608000f1042156100d90400000e050034002541044d04001242c1c0c3c80d15850b0280d59901c1d04080700007000c81d5010040c04000f001201d00700c0d56651191a40200a540103220450244405502c00900d0b400d00c0c4d078507000d07166044409840441c040645a0000e800c00c420444440e105a0401c138003d80e41e9000d00004c1c810745164410000c0e440e607400d00c1614028165482e10a1a40f030750f4000415800c68103ca9210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 110687760 1250 110686510 110686517
    0x60e0702070611071a0a021e071202040f021b1614060d060e0c0c16060f14090a0f051804050d031e090b0f0a0b0f060d0605041118010c020907 62
    0x446503e203075460035410b548265401d80a9852903103c0301e800c0002880c06134030f00d500b82e0303040d00c8000607184080d80c0c500000c4d0405600c480c600300101c00c103810100841610051011908895181110080e60015042d55210040f40f140044680e00200000d040038004540c0b119002440c14801070b100540c615011402180d0000b54003600000603441400a480000000b032150305210f0320402c0e064004001641c00f603c02c45042014406907442240125107950341c91001084d0b2034101110099440701030305078118800d201c03600c1d0595851465502400f88043ca0510881c549820003161500010b24811038404400170302c004200081000e009001143c20085103070b03204c0c506005506580f101c44aa0f20504c0c10342e4030800c2164481c481c80c090190b641c0c0f0701c0444e0f103d90b4240402c03903418030403159109605561007002400e0940207801440c040560000320f0036134403004074040d41c100b100303110714522000401800c0751110304424808010f082c604850400c42c2a8003041d00c0c05406458141030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 110689010 1250 110687760 110687777
    0x7020a150b0303041517060904230f030a020616140c15041a060102060106050301170a0c03030201060303020d0315030206091f0207140102060c04050405130507060909060e07020706 79
    0x15200c80d508a500e1014010301101ea40340c0c2d98032107480d03203080980200030004100c1004070181d071004405050092000078500340e031680b1542d6031401d06010114040583d452485003118a00300300b4030213900000c103500c0246645480001c0000d0070300200900e0b00682c401c0b00511513a02ca03a102c00e00d502e01040e01b401203541c0351900c030354003403424000542c49031b0301c00d203003a0410007001014a00045000c580b03100d40704560310b8003001039031141c40900844002860034001006462045038010780100c88500075140741d001d6a4503111040050341d002030f00582c0d100c05040007019410890320001c1ea81c030340f4041010081c55034000d00d006089e4400070b03110701c50210f115181c5903141c2a101e02c1089000c840c04484110812010792905498403074580440f60507402d242d21035001182e00381c03180b012904140d1410707091408200042174050000b41400d15041c02100000701c081000304040d1006440344080705160035207a2003074400e9504458034418892090040164000035220141c8100b030901007030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 110690260 1250 110689010 110689043
    0x303070f02120d1d030f0706060603020c0c0f150c03040e07050301031a04020105090d120905060c10051e040311010f140a111c02070203060a05091908040b040b0d0b030607020a 77
    0x201e001d14135000120500001540055807601b0b040105030081c4228010300070190781c0c5800b9000c81c000ea50348400d25401003600310707401e4540b10300c1507031041000411401010f4245801b070320654003d042d0307160b942d42c0002024006500904070055000e0180d150251956045076556466101c00300d02030407600030034901003402c5a00a00c01c0d102c000c00050034902451440303040c207814110f1200c5100b4003242c1a035602240341d08101086401048002d0020180c001a0b03000703000003000c00400d8020080300c80d000000300c40c0a600c12185c0141e019640e000407003145444441d0854010344496120186060f00034042d09401a146035402440c401c03000400782115040c0341907a2107001c0910840e030b141000e10b9030340400e950340a003d086000785c04884070796851001c10700807208242d980d422540d224040c480b42607502035856001c030a02c103004190805d40c0c1c4084c03400b0640c000703070082040d008001c0351544041d0b201c1d105000d02e24000b1401001c503802c1408010703403600c101c4880602000c0e0a81c040c001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 110691510 1250 110690260 110690291
    0x60c050405060d151a1608040b07080307020106060f140d1b051c05060d120509040f06060e0d03140d06030512040303080f0c0901030209030a02120303070f02120d 71
    0x30018070010307000310f03500d6000400010040501c035808040000f800100410003030403000031a4010810003110614111400c0c8402e15581081c450403506003804000c0031401c45140300180c140d151052042d1a00c03800d02c40d00190a50300c0d99008442000b00324440070074026801368900c81d049082c00ca00d65610720a0803c490090b015010744200241c6428a0407003400e9400401848403208600800c84d41c03040d41c00b80c0000381c03003081d901e4a61000610035010080b440c0c21a88000c0c1403030500b045031a051a03007000c6400c0c0c990400c00b40070400d0b901c0c282000625000701209510b0f503400c40781d584284d001694090324031140000d03003103c41c66010807030301e1040341386034030500c05141c00ca030444d1003140302e99244164070b0740240011000268040040f5420145403081c041c0140a0044006c0c200004140110b0080d0022030466916100e00c03294800543c440a540184150300900512b40e03d180c002c40203059480280041011917100c1540312564a0010b001d6512441120f00301080e07510340002c800d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 110692760 1250 110691510 110691517
    0x170f0a030f0e03060c03070e0303090a05060309190b0703060902090901060815150c0f0a0c06081005190302010206060d0b0f04061104060c030e0a06080426070605060307170703060c05 80
    0x240d05441540280031700030f00b004c4055032003508266100000305411000f030640320b0044450080d000011501c00703002d186008000745a002c8140b4040b210380c40c55200400080700d0310030a0070f8403040780300000d2000440c0e16002e504007400e80003d080d49491281804520010030502c203110421441402141504401c0790051000d240000d00000410a0081aa18441c1d01441d442031a900c079440308201c524401180c00c1003015040302004d0900c07403134000142c074840740017401c0b01101e03501c00e00041000e58a80c1c010b003144989500062100074258800a460400c01074000e0340710310000e5001c003000411034000300d0340c40300c0714007030f01c14607500d40307140590160000000b2903201030303004100410b000307a0100400c01c85e00d019aa4038071403124010207002c41100382e800341701c000841a8001601150542c2207085041c0d00034030b1803406020364145e4a4507280c00142080323607029111010b01160340307010401c0e0005000700d00b141e50040e0007070300c0310030f9600d220030b2100038102034441d503103c0c1f1040d0240c4c054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 110694010 1250 110692760 110692787
    0x7140a0f140a05092209110a0501020d0210020a0507081c060501050405030c01030902040e0a0f030e0402030f0c03040311060702070e0901060605040614120720010b010212070f061104170f0a030f 85
    0xe004a80107447c01c05038a0480d01031650145150700c100007681e6100043c2c04540c45400e8010300f505c1c500001d030781d102030b6118294003018011704101190004003150020300c400344d98018044041c1080200450a642c85030780310a0401a0611060003155000300f008821f0072000d080000350f04880d440410050502d800341c08800b40034801000052000a039840c7c1104c5101c0e80d0f0705100c3c4441d0004210817400700340c8002c0c0d00d1044000003d030f86a2076007802075030828020b00f010b00901c15800001c40c58807004a8800d030068006400800004600b0409242c101c02000300074402282032842c01055801244504820003480d07924a44200590804a1310307080c0041090884074034000780060041c4070860300c0034416404201c00e6403014401846a202d00400581c05418074601810020f60650000c06c02520303040c0284c44110001303481c5100e4103c2e159140703000641c5841c42d202c506144101389210560349500000711808100c1c00104510002135818104106200d1100500f1900340d2400c165 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 110695260 1250 110694010 110694079
    0x30106030c03060209100305090a02010c0f0605010f081b0d0204050718030b180102090102070506030907080316030e03160e1005040c02010f15081507140a0f140a0509 73
    0xc414841c01e50010705e0204000d0368441c0801ea00c0342d40450407946c0031500350b2074030b4018428180c01503108111245506015103441c7e41c44800507240c07801143d4081c2e01c180ca0844a0490400c40180b0501090070020202c0540068800704000440d512150030f00c0001d1080340d13207000050700c01e40100000f1034503011f600070480c1d05640b640b80c420031149007501c2d0700001c0c402c40344240c0d6070004140201d0f606000181d003e861b2081c90b05040c0501e0340c0000d0f000c9240d500a01e50041010355081001d0104081003400300c8100c500c050501400e4031241001050094016542e0a85188100030005040750a0070b064901c00d03940c0e40780d80001e605040d8010560240c1491007104c01290f054100036014441c0e0300040041404050210241d03114610a0040c241c018440035904240000780f0240d105040e070907c829071560742104848150300c0fa41c2480b0126012020315801c15a00c04c1d608020b101c0750900311440c2c184481c030050003500070401c1d07092003081800c0841d4203c840104000340340600f041c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 110696510 1250 110695260 110695283
    0x6071505060a12030e0418021806060d0e010510050105030f010b0d0f09030507060501150c030309050c04090b0a05010b0a0806040e07030b0a02070b060f0603040305160206040b07030305060f1e03010603 88
    0xe8001c000411a50505206d2820b0880220b0440c158040704180342c1da004050061140c485910311035908070041c5619448907050000f401d800e030b91307030007415255003d160000866242240c88004c140c41c45401c468100075082c0100081041c00464540c1510300c01100c040e1105024042980646040710881e00d0f540e0270055818105500080079104481c4508420b001c144e0b2540c106840040c85110740c400002c40c1c41c40500d000c0390081e801248170300d0088003036480084e400344c045015210400d00843c1c00c804c0210810070044c2462280714054840491902d00e03060500d10020285003000d4071451050b503440200800d0079004100700802140d218441c5000340c504504844000c2d088404103680500301d11000692070705c0d00700c2710340c04004001050075040d900c0305d4a0803540d40e00807a20b000c04000c83c6020f01800340c0d031f55030058001007281c000310036642c1c24203140040654102500b424080d10b41c6801010850b501c2c1e200a1070b00c1c0300c1141440200b18071072800680505483c3d03201500700110f41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 110697760 1250 110696510 110696513
    0x220204060303120b2409010c05070e010302130504021e0d12080106090e0f13051005040b0403030e010525090e15030f070b1204020414131106071505060a12 68
    0xc0d0041000103044504011260a04080c050107140b07004240b00c4034841703543c3e4003180c00c0094018100340354041c508a13106000542da01490300180382c00000c0200c1c420f000401c21498902d00920a41032034560910543c203259000c00c0204906910440454000d00581052501e4a180b1078141540205521078080310840c405030004000780103540024240080200303600c8000c00e00c050003218054180001c030307607035040080c085403050301040301c0b00c1c014103507040e0b441725580c0506401603010341c0c3e03415018146850081d040f6017000c41c1c07036880750341800208072044c1005019120400c2d41003600c4410060f5800bc00c49002125405c480032510b486020b00c80b501b0040b03101100401019001c07120140384500c111503803404140306900d0009000c00502582c4001c00e030900d900148054400b0070803001000d00500050b1040300c4070b9502d122507c04680c00d21440042c0d650222200b507461500d40300c0d05889012411044003002a101e988450107c2c046454141001c0014000008000c8810109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 110699010 1250 110697760 110697767
    0x60702040507031a01020703030905040f06030812070e04050c19050405281d040807020105040509010306020c011a0d030503040c0806040b0411010e0609280b27030303220204060303 79
    0x400300c84e2401d82e65030601d000d00c1940001072081c143c0b80c064851607845803808040102030800b103010050f00ca6155100000004c0f0308034040d01c00c800c02d03103024030020302d0500d00040003508003141062040b42800d007480024030038041200c0280322404020703500c00600100540d06840b0ba580107981014031851055271401c030024a400405048215003000150b4a040007a2095a0f07824201c00640503c0d001c14001350200004119462040c10610b05059403100003e0b0b88034001d92056078103039000a0704d200900020f10841e8010682c681c564030100600902240407410015070040c180308000022a007070100490b1000000c0c00c824046612516017803400402d100c4c01035404460092000008040359806014003a010f00d0000e040181440214400c00030380003044c10702c0e0440760383e480c4444010704000d04842400b80c002c48400d603507034044007070070404410384030003400319000c0c80341010300c0d15650044112074001a0001c0c02d003d082c180c2c102845180e0400c400000d5215107410800401c1540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 110700260 1250 110699010 110699021
    0x42d0302091e2406030a09080406031a04060f090b0619030903081003021804080c1b130504020f0f03030c010c0305070e030604120f0c0213200c030a0e06070204050703 73
    0x442e444241a00d400400030580440c031540669200c0450000d0300380ba04000d8050342d800075041c540419201e442d915190019030058000743c0c0041d490391450140b02580761540129450241c5041003000c1c9402514089141140240c96000341c84206203009542c80780140c40c006540050345403014103000d80040c006188094080f0003190107075000441e6030215440300c50450785c0181122111001c001d4600340000700042046a201c0c0d028806c2c4a44a4810000e0507006021003040d15203e42500c02003140090396048003940050920040000684548403506940e40056501581100d1040c0002e03003180141d8002110a600e001150015640d00d900860702410703103030b2142e240c00c1090030141501c4031000c55000d80300700134034202461a14030401e2101c0400741036251440742c0740182d50008205031481030381d074122951511a61a60380240e011002c2012583c0d45001d4581902ca0322081d4a0740640c402503800c2c400ca020468503141c030b031481241c000503030041c0b04012616099002130010302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 110701510 1250 110700260 110700301
    0xe100905040b010509330403120302030c040815010f08030901020a120e06130e150108070c020411160c0803070f110a0909050105070e04020c0304170c032d03042d030209 74
    0x200190360901901d500111403c0d49d0300401800c071400f40b0f41c00103501a40c405088529550420000043c0c1001d003400b2000d60700d480150180000e524040349a42074071401c3c4c10068040d082084996103981c2c0008401d003d090340080050818142e8140c1034802091311140c1c182c005034006036546182e000d4103a050300796200c9081403015522030350b0305000f400892050713050205c0c00b03003004a440c65005095051069200030808609401c040c2400c2071260441100443e07103010394a8030404000740e9050100c0034088410046040c84e0084d1541c941003180c05101400380d02c8030f28160140c03500d80e00c007540088d001c3c0f40c1c0188412203030b5107070007402031004544110004504803804462031415000f114114040580154240f03401d00380801c0582d0b10045d00041980b04400300035241d510b083c0103003005050b040c00c9040903030107031034030345206070680c2d40e8409034903001040140303c0e50380c1d500141040022441c0301300320048014400c0c00b07690380554001940c066007038401c204100c0502170380319001c41d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 110702760 1250 110701510 110701579
    0xa150215061c030e0619090614030403120504020307050a0b0a1d01050307080711010504030e010f021203010b090310150806070801050a0605030a180b090120031503120d05070e100905040b010509 85
    0x503427180c2d4514041d40000d03a0014002031380c002d40340c0c400d4110b076006180c02c81c0c0014141d40b0025070710000110040400d51007001c451402042d44a10544c1200d03009001c0401d0b2014101c1950707000c0c0000b403082c8001400902807011003170100324090701c03400382804245000c1d4000c11076800d1500700904046140d1031114001008a50584005407012840c5080e010141d4500340c20340e403c0180082446e0030132514035405105d10a41144403c40034011442c10f0b04420358084245402c02c0c2d085410184001c20340c00c00e10042c0801080f10392983ca600d40c0441d0000e152103501c94403210642c402400d82a07560350f094034860030200c003e10082000c61801440702c58000c0100003600c1c00040041d808102100100c0ca0341800010f107046080103a203100080001d09880c5070704c4c081040d0021681141d00c0314014603983d441085040c80e0005282016032900f11041c030951511018002d00a01040c0245409142c43c0c0081084c5640203800b03030f07251008002c180f403007042500c6049822038140c407040c03280c40307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 110704010 1250 110702760 110702777
    0x31812051b1518030f070b06120303160c0c080618060604090512070203071d0106090e0f0411060d140a0b0d0c0605090a150215061c030e06190906 64
    0x209000040c0801070035a081205072803699043c080d2902d040011151030524041042140c0c0d01d070700040002c101c1b10784200c7c90034006003420700c03d02c42c0030a200650700034039070301c1001884940c04150000108400c01c52802d40d036909410314002c1401c3d4440e61040e4030034800c40d0b00780880185288500e40140702d5110803641180d44d44020041510600040a001500400c02c00d03590380036002d004002d0240043c00311015165514400c06040000404208400c40287c3c0140000c6a200d051a0002d01d010044601d00d8105135001c0c145d40100900000c0c0584102100c900540c1c0b10361050f40d2600700042400c00105103484400307002050101d03513040c00d503031500b5400c24180c0f5145648034010368102c2c88c03015141d41403043c01e450307590000d0764080d4014882100082c0780040c041601440001d40d40c09011441707401d56050b10007010103803a45106244006454181325284031404030b00030781600c0c20011880c0f401021428901c9400c8400103020495440c40141d950000c1100c4121409940c8184d107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 110705260 1250 110704010 110704057
    0xb09010f050112170f0c07090b060a090b0304140102031009060e0103030c1e05011514011409060708070b01272a0e100206100503010b06030703181205 66
    0x1c59109018060f50b1141950350031000c00c16000d4624040401040c08a143c600c2260400584d034200d40f08080150780300c86c5091100301621302800c0e0307030706da410f40d859030910b20030b841d001e007880c02d0314010351031080008000101408014520b40040c803400c44007c5589050801017600c00305014020005000d0801d1000905514900507040c1206e8066176140b03004020381d528160500d1f141304000c12030284034070b0000f000c50b40038070502242050708141104403601d0210f09428002c031040c2074505200c3c001010311560901c0030101c8241c418203c0f4103070741c1d401d014540f8014074000e54038090300e06c149041c004540c001f01d000d0098401c049100161a01411072054803041e1003120204000c00e100f07294014500d80001a401100880d10b41420600003101c0ca002c250401c103480307840801640075000707000c054220644540e0207414160b0081c090003180a0200340b003844042e040038200342d03a03203204c0d010409210b8004041e20f948281007800000d03480300c0041007a04005400094582e401101c03c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 110706510 1250 110705260 110705291
    0x315032303030910020c07150302180609030709020c0a0b090c041b02030901080601171612060f03120c0f11031203160f1101060603020c010c02010203010f0b250b0901 73
    0x38816003c4400410a0003056a01e00029411050545800e841117440102c2d0983e030048002072954020b90340107868030900c0c1010541c41211510319402800100000141900c0114400056940001000da40c0d100144034891030500c0e902c0000c0c0a0340303144020700800e40d102180c81050030706e0898090000d001c4119552541e1f00c5407210707035005684100a550100e500501c1ca2a0b030000e0705040100482000c0f40c0c0d240b15041d000c0f07c107020000d0b0b00c0503090036041e403c200c03074400030100c4410800c000350500d01545003001c030300d01000c0c100d96001801148a984202c031280c180035031004091b4903590b41e40c900b6095516012144a01c0b0307014603002c03d850001da140a40e4421403070700c51000384280c2480016140c07008940030002c1000012501e00104603002d015542c020724896900503543c8043d90013031421214448a001d0440e40100010040e0010020714002075800380c045d001d41c0c8190710403000e80c0d48604041c501ca155010810400148481098010300c28a8a00024460320000c4080035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 110707760 1250 110706510 110706517
    0xd031e05010f09110913140c0408150606040f060903030206010509160e01020111130e06190509090f070906091406010207090c02190b180105010b18010315032303 71
    0x480b0044110002000943c84942050258100b040304151419610f00013295420b10300c0c2035001c100a07202c10b1400005040d0030402e942c031101c41c1c0721103410b060806010079110952a00314032078491410300480e54039550f00080707034028006810b100445030303960b49026018032684d1105401500901e40000345d24180080c51038820000007808440d403043c949400c6c0e0740c94107070b07440981c119960744003201040110200100101241030200c24040341c607105000038a1100242440e0141c418002000391180445100320190f030805c48185540c0c1e524440010320f0410a0808103806215200d40000d10481c02d600200c180c0394010000d001c005a40401604003040596181d4010381c04000100800310995112a8210806206135003850388030018103031200c0e064a0056801c110740209008031100c51000640c05400f8200c028029503152408802d060301487c280c600c80c01c0301e00008442181c2c0b01e41d1100c04600c20f210114020280c8a042919550a00415110000200400d01e666915000065 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 110709010 1250 110707760 110707769
    0x9080105040c0302011b0b0408090406060c080d05061206040b0115030c0210020f0c0105040b0901050f07230c0105090a020a05030102040305190609020306010b1c0507020606150c0d031e0501 83
    0x1102c0440c2e1640e40115240803594000d42100006c259608000600c1001c0300c7c0d0059005200f0540c403603052008100880e41c41d544100140000c840d1240c0010f13a18509075040488a8100010a9034071540460b07a104d414a0010710700d070203000704200c10081c40e29040307816207196012400f00360b81e4083d000e404030b031010078121001da0b200014440d56010b02e500241507204948001c50304200151003281e09441081d07604403804039811040081e488824071510740c0c0110b50540202d8a07082126001c1d180501d500807d03003103074005920007443d002c0762000326080c2c481080001c22203131918118254407040c000c08200d1003980c45d03000000d614601402540c054a4020024103211094980c080403c00d200000458040d600e4440420260b90b0502c001c6000700400503a040d516030a10000a0354a41f9150a000000b0703d04014420f0707803680000c45c1c55100078113842c00020f41e034510442500078003a2011240b598415600c84801320b56154101c3c3e0303060b1503040740e4113041840c000034040c10385100340203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 110710260 1250 110709010 110709023
    0xb070815180f06010201110a020102030411010c0c03080708160b040203210f25030801060809010204060e0603100f0b0408070911160c0305030331030e010e0103060b0403120908010504 80
    0x2080300c80d150702480030f4000a050000050001c030403c0c20141c5a04105603140245c1d42c003008100900c00d9038003815140380400d20308003502000d00d648003001c4040901000d44001c3c404184102007202010072525500b0b9a5000c11405503031900d000c102030384080700e04901a00072001e2605141107441e5190041c02d030fa07079544c54107088242981032000e8000308800680300f1417883c00b06001c0d4100c00078140005011f592a10810340c1080000391820001910b400503580c41000708000c10303039001c000c8150044040f140705a9035110003041503059082500000209400400006242580000100b00711113001081c3c411103a51031200d00c04894200d2002c2a1840040001d21124180b0f0b040000e00c03644111070600e0301e66141e0300c403a461500300700c0380c00e5122196500c0c0c0e0006900d4508661140c84140070010520b6209903800404031f240240040d414015440da04022a078000c4c0c00603806071040480c00c5072101d0f52400d2600601c500384000b800801c281d4400400c141d0340600820f40b150350440c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 110711510 1250 110710260 110710309
    0x10201110d0b01050d0e07050910031203020f0702090a06080c090f01030305030702070b1305130c0c02041a09130201110613080703030f0c0c050105150a09050c070b070815 75
    0x281924003a000b0300e42114100901040444650242407140f02d030521142001000800c0c200b9051100380d820280c502001076000d12030820000b50910003000540d02249405621001345620800c12030294140096006614000300300312005260712100840c0c50038030856902c60640706c20f10103040d4040d40d0060b0042000720040c40420301a000a50704441e40b8412600081c2d81c0c0c0c0b200500c40e4000741c03100c480ca000e20b5a010041444c21381840900f400c03440c0402c01030400001e8016028844481009005903199001022610a076072400000040003400015051030504583d461a1031f400c5802ca01140c81413410782c2c0c4010700059036601c100e508550001020010740c4070100580c1100104a04041c0c655130522401801c500543d003140c030f21620380480c020b034a80351032800c0d00c20051650a030118802c00b9408240d4483c0745000c102c03407000d21b0001c2c00d41c0340c0900b0403105216003040034255109140030f010400d540b010810740f04094106c003441c0c0d800b45803c200165040c2e1500d03483c1c140080c89 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 110712760 1250 110711510 110711527
    0x9010609030b0a0b0f030f0d0f03020c19061506170c0f03040f020a030c0b03041202030315010516021c0c0501020102090f01030c0201140a0218030d0504150c0b0a06090b01020111 78
    0x203a2089104c0b00008200c82580a2040000b07880d0030710f0014012241d400141003c3e1034181c004c80224060403d90a082d0304200c41681006c4d40d8188686e6000440048240800184441541701c0c01c400010302400842403130f1101c3c0040d086820b002d001514122145000840c0407d12105440c00c40c40380c120705510790b0300c45480b610f882d610310000030399221500c414004002241120001c00070102c40300f9054991415042030310015a15403220015500204108013840c42c0380e50481080c50000d00304035407900321003020a0100110418001d4110032040b220240000088000441c4184540c0341415120b88070001203080c0c1c0519040e0607004405000c0c100352541c000d402151003610389100000e18116100c0c41f401c0d420605627050702103242d000480c2035009002800b80150110241d000780b1200c10b4101004041e8422441183c0b4030108280750513400a10036401c10318003940042d040e06881c145901c1800040c9038901c0b80902c0c80741780c001100c071254018015240c0326040c0c20401030410080c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 110714010 1250 110712760 110712781
    0x1030803190516021c080115030f02040e16020f0d0806030a0203010f0f0c020f0a0f170403050106210c290c060708130c0303050d0f090303090209010609030b 69
    0x5080d261100041c1480044060301c41d00c2050710622008181c2e00c000c189400000e07040c020351064901070307511800e00b61103070740342c22500aa0450381c99620000200c055500c0131030051601c8e01100c441d00d400020001607a55107d481c039801005004915054030760826820780c2e40c3d500f001402d01d507607040f12600080c5c80e400b512540344d200c0d6010301615106001580041e00312007102ca400301c041940c85400c40c0da400c0151040140c11007550000349103908001c0344c8642c1e1038020440080010801d00c440c0000c0050401c0c02c9090b00540800d0940c483e03840349030640c00380c40c641c010869108420040b007401808404214002103802001d921801400d00f42c8000d201c41d5200860342800301030340d182410390209940200061000ba50140860b4100860010328083c0c0c041c2c4190000910300f544140440d050302c003144200e95042c00c1c4a552211142c54040140052004404a040ca0b00f5400028181c254004091462080700c003420030743c2e2103550079079800150f030001034090654800000e0304000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 110715260 1250 110714010 110714017
    0x109110d151107080c01060906050406030b04020f04020702180109050a0b0d030e0301060f06030617010b0310180c090f0c050307050405060913060326092805030111040f05100206010308 81
    0x114642e1280740c5909501c8490141d40003901540c0d6076955640c04102500c202d106007000751108031810f05c1703207900e0364440110382e410280c0040e10a01c4002680022540c0f2941101c01240c0e010b0700444122804d05690000c041d400d2141008030360030000024030b0f0302c04500c140b114050004281f80c0002c2940c2c0c804403080c40c803056600e6015980e455020a070000d1004c0d540d4001e0004d95000f10392142000c010450080b61070f0022060b0b6030505032038221aa401151895440c02034030400200320411424110b50041040000380c12034800038000f09800150b03030803941070244454400e000031a840c1303000700c82c02d01c001c03a0800b000600902003445145408402440441c43c01010600030540c6140410b049480070361040380c40140a512000600b006025400d8081d00d40304040ca003020f1560b40419194002c0d094403c00300103c1459040b910b40320050754401611015000f04582010314407070043c0d070360113401282c01d41c1030030391000504e03403030300441030154601954050310442e4603507a10444541c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 110716510 1250 110715260 110715281
    0xa030206070e1f020f011a180103020d02060705070e0f0f090703110105070c09060b090135190f020406090e01050a090e03040b0705070303080c1806030601120e0109110d15 75
    0x51440040342000c0240070b402c2c0c01c0800d200f078809400000d881000442d202e5400c5231200c8e40c000d0030041016a5a00006041503a010b4618640c1c40d01c03140b80003070810f070454001100465003501404a40040a21443c0c46050080310350f42032600c603901607666881d00ea10000300540640861004036501c28006082003038491603e109009403100c400b003043d00c00c680c00038850b0b40401700d0202481c0d03030f000103004400302d81140711110782c840b16002181203c80302c180c0044107100100c08950501d40055000d5009100b070081044207604c48020322000e503219109640014007242030201c4da00050301d080e81d040714002452102070518182014020748101000960f56020600c00000c07288240d0380200100c42c410405810080e04514001c0d114070400341c0300002001c411300c02d0f14410589c05c40c84d10039100007280e08a8480d915400101c0e0035001718090383d4030030740c1001c2e0240b99283e415041000301138441c16990b4204040b510500545520b02d1401900490301d001c4a840001240d03800102c044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 110717760 1250 110716510 110716513
    0x4170901020c04111306080f010302150919032d1e05031902100203010b1b100e01050a0b0301020703021b1306030b070809010204080309010503060d0c080a030206070e1f02 75
    0x2c4840c640050121010b1060200300454002101001c248030342060388041c150605000020f420010381d1203e00d0203050000900504850241c80744081251068460740c0900804081e9005002e0b004d81180c010a0301c411504008100380c068804100401d15170f0720f001651200c15001d00b400d444021641284440c2900302907850110300011543c2400101034094003185000901072240100901d85005018908885807041c0014042c079488541251b00340250f0b0401c40b041c0c24141e80c0c44030700307050b030f40c2001801c840d2900e5402a083c0a040d04002d2084004110070482c0c8041b1009043c01c0c0d204903800240180c1001c0400c40c03581500c80c0043d80c0c402809420b41c9458008204098216482c0340c100b5240d9001c1c80081001466000c0240d582c8141410000d608081c03600000a07540e0081906103418007002000040040e204c510301170203041e03044900c2e44421a51080d01580307402115500b50010b000d402c000400c603501890b8001d2000f81d000e40501175044101522080d501000c50056045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 110719010 1250 110717760 110717773
    0x70212070606211b03080f0c16060c1403030c0301030b0403110a03030614010207050303250206071b0603020309030f03040201020c13050717041203090302030d05070e180417090102 79
    0x1060b04000003080146480f0620b002443d801d8144801c01080c900400d6191030ba201009200040c03a140070364074074242c15141e00b9240d003210b017801070600101d08010b006e051180400094130030303407008802c0c0c220381c00b5261490b40d0080b40302c2182e840788800c80f01c041684100f040100b00041c080b40742e841c2d00900070f20300303600005980b00d8a80c0c2000c84049047d400039403a00000d01644011032583c003840c010900050410a203814003290300d03401603003031a0071a40820304104420030090f030106c07651254020500f0f640c51419282c2000344a40d40044200020761031040400c989000e44200c900500e4003500850a002503e074000b82e5690004004a0441c00b5a13812080e00703807544103062098a01e200004103813480d1100c40280030b0002c4041001e1803407501410301010503803c507083c290312542850b02183c040842d060a92840c821100341628207032a2900700800580e20144040036040c0c11504019050800410802e0a690a0b036014000101540e140b59020604000030f00caa441c040c0151140c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110720260 1250 110719010 110719019
    0xf09150e0307031b05090601030506010c02040b1809030c1608031903020702060d050a051b0910020a050a050609010501170613031416140a0b0c070303021209100c08070212070606 78
    0x4c0240f00310030320b04564410f1580510036803400300c040c564002401e1804009900c1c1400c0000c1c02804140d4000c2d0040d035544c90700002e152503001e04940c00300c070100460b010303605200030b42540e00c1d400019941140e004402c2d082889200d040c04507011640c002009504041140b0300e8110300b0442210400c1c2815400c104e440016182c101c041d104005030104000740c0d0345010030112080e034200800d9041c0003072066520010564103441680c01c08101a0740318000a403071074605924101540001802c01d10940581c141000360015014dc4141e410f00300030f00460760380303c0c0c502c041100b11142d100e0351a040741c400148602c0b8011007d543c028041d1034141c2d29000700b4600703031000b60f04c41d60350b10600300fa100c01300005104d10849011180301c800303401840c842c0f5983e20740082040700602420030107100041d890b410f05210b41c05403070b8600341420100d000341c10b001180c50f958944860400720507506000c05005024050f804240c441c84a9401412204d64880c0401c000e40c0d200410840b40c2c40d90b510030105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110721510 1250 110720260 110720273
    0x60201150b030a06051e0103140606071103101107031d0a0b1806270f0a260313030311011a0d05030c06040501020307080a020f0a0c02032b0f09150e030703 68
    0x428043d5039046e80c06642100e00018180c8041000c0c54681078850014400d81d070301c40408540040340c12555000d20b030815000040d0408d4002082215054240062034990300142c42c01040303018441d031180e10000001d0000c0c0000540414820381e40458021170400c40840040b0003441c220030940500c524100e089800244c1302c0d0040821782003000000c1131100c003104800d095070301d49140704031074071b07518100100300003181802503015034a140740c203034850003c4481c1a001404059001702d02680d4807031111081e80a4803501902c02a000036402d284a20240324040c0708141c0c03448084140c1d0201e4401e10014405c040d0900d80701118203100801035400754001c00c0c071015000d00c0c0710704005640c070b0405a0000f0b1509001800f43c1c252284108100f07250508500200c48080b50030b41000c14034565540000fa003041000c0c81448a985e03188407070b2501400074009400301014864841da651003032619422100c0d18498003504c5620f1900e03040b00700c6503e00034980c019040d21300604031440d590b100d0342c540c0e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110722760 1250 110721510 110721529
    0x5030c011d0907020706020c0108010803070f08040e0108011b0f020c120c090115020106080316030c021c06090308070507110d080c1c02010c030c081305070803040311040501060201150b030a0605 85
    0xf140181c00141c01405001da050020040c03011091900c2e08041d41010750007501c81c42140801026440508051810000801c068400800c01d100c002e074090341e95018001c0c040c201c02a000d04ca01c03419000c1c071001050041828100c14180356008000c003009400620480401d0b0f021440e02c240300d1843c41c0310b91a920301072001d001c0c0804802c0d0b140800030000e0040d0070340782140c0081c0100c0e0002e214603502c40c1c080030a201031050b0149054040c0e0f104c64008180b03a04082100404140c2c01c40d4a54403c0c050306e900300c0054144242e44180480ea1954011207850246102c010042c64814000c0c030104c3c81c1c48000403400500604a040c68000301416040c5824010b00b038010302e0304251466140840d8083c450044c0c145200e0070300344080010030400410908d00200540d604201107948402400000c01004015045070401c0307a603140d4903402c200c880501c041c880e80d0b01c80e60510001155091060090040e40b15070920108202420300c2c001045540008001c00c2c03407150b640d000040c4030355404014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110724010 1250 110722760 110722771
    0x103090803040f1e05030702030106050303070203060a2409020304030801052403042a0f09021201120507031502120109060303080c0c0a0f03050a170106050405060703031107060b1905030c011d09 85
    0x1b0f40e0384103194418182034541c0d55228030f200b50424840c2c100035880114016a2010310580e00040441d0540c000c007a8403452911080500483d500002c5500d0401c0c2e030003140500c0c000d84030342540d80e03070351810400360b92140b00a110f50782c280c0d801d000e6140c04004010f50340151003000b40d0044041e100c0d09080c0d038025042d210404002080104000071444070510401030030b5488400c1d881e100c03c0b900311100300d50701841081b80c290707901803185082c8503003404600040e6501562003034115410015881c0a90005c1c5520004000321000010707040400f031040404680e03054581405954503000b80340318a81010301d000c2d505025202e009070028910102c08030380544039490f5191110103100004112182040705407d1074180640107120190300442614100da030210f500a550701a01d1034120302829002020900b1340001080b80c1c400c03c801900004000c50b0290b03100a40a5580c0084803060361507407103078a81580081e054a1280d502c1142103600350380403460000407040d001000310311842c208490 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110725260 1250 110724010 110724013
    0x70302070e100302090c0f0304170c0703030e030c1e01030914010624020a03081503010e03030108060402040b1008010b030c0405030a0f020306010915050405152106060103090803040f1e05 82
    0x7400c2c011840c01c5c030251908000d003402d135181048008090000d041c071010304060000a4a841c411103041c1c111421190401e0401054802c5a5600d1a02400282c110035075688640908490000315060040e010303402940d01d0340300b450043d07140350b0054005000f41c0006649801042c1e42e2911620424010f200080041010100700c0025002c0341c411905460544041103400c40c280180100b540a440f4903000454103640008031002c00001a0040482c01c50005035400084000540750b4004510640300c6c5000341e1741400584400c50400c4641c0e4440402100452a4100140100e02220000d5036012240d20600388c030701515000001e00c3d0020901c4102e074642500e41041c41181414401c480c014413118406122000d030007058240420b001d4080c80d4042c0e66140001102d103040d81c071200b80e40301c0740a0202845000b100709002c20300340000d003442e507403407080d070001c510954840d1003001c0c00c4035080741030303142141c0311561448100c841221050399184120b101d110310342913030b045085420602c40d20 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110726510 1250 110725260 110725291
    0xa20010903080a26040506160203091e030c0105031e0901060e0405010c0905040605031b03010f0c0c0506100509150301060b0a030204090f02030103020306190e07030c060206100515070302070e 84
    0x5007840701000001d10b41c402006113403014440000c0f00054082e4101080080d0b045402000b888124510300441c200b46501c003109446520030a113071614a5881804158140c039440f0002c3c100545642c8003da03415074004440103503081d141c05003e00c00c40d0700084403000200c3c0d05030780d4a013035055a540aa0f025161655110b45034120190030600701e0004000c1030300e00348005860600040d03100d41000941d40450f02800e000c0020581c0c00394003c0d03004c4070991004000c25140e0813001068829826011180c0d4400c10002c0b6101480c0d08801c40c040b43c400610801061b0303515448180c0c54103500b14050741640d00e0b0720012401803080e101a112802d840e5400685891516120b24140c0b04520314121901e0320400050002d603c000c101170fa80030041404400905010829050041c0021032401806005124002c405c110010070720b00112041d65080381d441c1c0c0c55242441184803403d00c0b840394000380b480b0340e02051081031000f1341583c5010303005440d005941d800c00c03800d802000b110001e10100f010b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110727760 1250 110726510 110726537
    0x507200a050601061d010f092d0602030a1101020405031e10050703051009050105090402090c0f03040b041a100314070f03060605191a0d0f0912110a20010903080a 71
    0x1241c601030002483d083c7c20807025110007824007010f60003040b00c81e600e40911000c88001c110500d00240720558000c184140c1d0b6858000e459410039034903500003826450002d00f070b8090500940d402d131640100a82182d60707420100140500c401c3d451003015000e4400d42500b10382080c810180305211940f8081110700c0d10542a100158403030308502111442c000050105032200c514050384581c0c1500c041a031503c0d0740c8600402402101020b002558002080004000c841950180100d105010204221900c100c0c61504120202c511803442e0b01e88010400c00308486809018501c41d8107000d4848a6031200d40e0203d0f5150135410664420340c88040c02c02ca5402c1c10b2201d9444a4806482945a02d08015440c024a070f19450f421240c80c4000c61840c146c4410f55000c41c1d60101c8044040020500a182c44e0b107000100001540207d040240b2201b503003040030401d0480e807580100d104110300e08200c1242000c6040c00c4510f81041845100480010744010017071400340c1240d10742000c1c0342500c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110729010 1250 110727760 110727797
    0x10e1302160203100e06011518030c0f0b07150c270302120127030e09040f1b0612020d14040503040e010504090309210813080606040507200a05060106 66
    0x300c1c00282c1d013403072a01082c42000c40f0f011030a00e0540b2002c00c40f80690695101d0700300d40d158034401d11900c071b052a041d00001001405a640012503615041c070745d003aa46d4078040e01c8014014110090020f494206150b01c4056940d800004c041d04a0b0070800314001074002c550b103250b4161031800d40341d100202018420744c40d0481081202c0c4c420300c40248545043c5000390250903200f90340b0544001c819038001000c040c005c03c40e036204c0b40400341000b0b40e01e24040c1402d2004c050f05a07402e4801802d14895a48401e441040340000e650440c0c03110100c0c0d01014450400030340c0803803031013401680d0b40c00003c0501c00030401e045004034008c8000310340f40d0341005c001514a0006911591007541760205680010760004000011194400c02e0b81465268100707003a0107510500d40c000f413910400059000440302c2d040c000c0e00c261007044007202c845a45007024003003220b409540c1c3c2c01c08600042441d480101421340b480c0c0c0405e11210540b43c0038117181d6070320351801c002a00050040f076640040703042040c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110730260 1250 110729010 110729023
    0x11030a020f011a0307050607060905010c09091a060301061b06050108060711060105030a02101116061101060e04080a020718050106031113090b0a050607150b0a0b030105010e1302160203 81
    0x40d0350050541e004040c00004c3e40e201451310030203008803008070394982402082d9100803462500b000003071251a8a406c40280708601074003e0351360581c54100407040307034192140c8402e40d040c006030510f850369017482030a47d80a98100c0d543c00700d42e220704500400051050181030300803c90f0748002c01c0c01f410258005003442103141a422043d911100040200c1d50340013950b91750070b9030181c2e1540200440d2001c11149211b032001e40030f440307204495070420304034949907950342140c8103a03031a2a80c00200052241c207076801c2d0b211b0308103c9130010f004200130407044070042005044a00482e020702d82c0c2c403a42060055128607a0602c0c440d40e4200402445406016100720200b100d00010701c0e02000e0035184401100c28012000f25a580d0748a0303403040d49a0515100180c2001440c0703030b40341c164602e00305016000006804800c07506260680c0303581d013421050002030f2a40464858116801c15004444046510848a5000700f48480700e000c6a96148003d0290b51450f400024000c02d140c018140f17400c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110731510 1250 110730260 110730281
    0x906170613020108360d031103041502040e070507150204060518031609061e050109090e0a0c030b04051b0109030209060607021005030901110703080408030711030a020f01 75
    0x300208104290039581c065220152642401c1c03d004075110840c4840f481860308860034108018140a85500040003440821284200b021100d01148a600c03c901792089004024042c400503c0400c0000d40c03010380301c2060100000c030040c1400d548002200f08140d00b566880082040002c0000a0108603400c40c0c28114041d0000d5252529101000700b10303208400100c1440000c24803218079640d02804601107146403642c0d8103803840d841d118501c005181038801c81020440c82c00c1204182182102000f0031590141c4a521044c1d280080d0315001e44800300040065001e44519980040c55040c0301c0740c055402410300706828034161910394940000080c00c1401c60501d01d1402e00540c1c1d2120540d402c8d0795054509020544600c00404c2060044610081d8013004482c1c100c0b020766800005144900b02c42e100030300541820600b03110b818850390078090000b0b80f41d240040c0116034007800454200d038691404041c445903002846055810045602c4016044180b4018200109024a480c8103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110732760 1250 110731510 110731513
    0x20c0105181002070c06030f0e0708031b0106060215070e101106060d110d020d0807030503040308010f03030906030522031101060e01080606040903020a0c0f1a0a120e0115090617 78
    0x13509490b05d0301c05403100d02c05d4008158450100c10b245107030355003015000718490400c4880058896940f941c40b9040900103548204d0ba41e021207283c000140601411030721303190042c00c40102101c913002c03c042001000101400303a5400160a00d4960f0f000303124468800e41d0f81e60205529040c0350605200c40a0301c82c9114002c400050000b0a01c00c0c0c0603540b00d0481220311019400451021a00801d00840c01904002c03010500700d040c160440004e5121758400e60b50185160780752102c0c80404401c0340800740000d50b11450500c001030081d400690403100c60014a1403440c4101e407955111884001c0440000b03944c0e64071015504401d01a00e401703043c0804004140750b040a00159603101c006041c10f11071900c0e42d084000703142c02441032911580e00900c40318401602c0c0c0340c1d40089c000d00c03482041d4070b50303d00b0100ca41d401180402a0f07a015505a501c1030700d0705050701d150b81c01400306c80380054059540e07041c2c01d40e002500d104114004002d01e030b2000c50058500400c41413461020f50005485 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110734010 1250 110732760 110732767
    0x71a07050d0c03020c06160903050a080c0105010b1c050a0b060a120c0c170307090506070b0601080615070308040201020309060711090c0708030109091110050309061f1206020c0105181002 82
    0x60003001c10120b5100c110317205224047d0180d58411200403007103a10151082c001d064004041c410b8020040c6540c00000c4000e221503607a920a00d030b480d1040f800b62400c55441e0426a0903007201c507400140d001b05031402d0104076840c03040001031482d4006d22010012030402d036205a00714529001d0386e0f60007070041c02c15800c00803140d00c030020018071100d0140c03d00600000068415801a124000a0040601841c2e100d41c0c0b40d24014034090f000307449441c045882c00000844034500300e0020300001502050050500a40b1f079001c3c2c44650000d80300700d0643c0818400041d0544800021306003550042d01101103100d554002d10054005c0030b010190340c00030400844020543d024102ca04607104004e00103000030722030811f60300c11034a00b40480e0f84440c8500800c10407552003400b85004589000c2994040d44412011900a40e070a65041450104440302004100d040c04540c81140303020f145d02510388406488240d08642c0102d82d03044a55000041c1d02501c03003410442c180c840443c000d8214603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110735260 1250 110734010 110734027
    0x60503060105210115060207080c09040f08090102070e0a0204090b030c0a0b030c07150501090b1905130213150f020a03090918050a03030204090b040506060a05071a07050d0c0302 78
    0x2a00c1440c08000b44051520980f441c0154000b544290b43d03045446020741111034032140700035198441d51103014190f11640d0600f007101c0c980341c0c1e00d15004691102d00003414090b16900d4002c1c0d50000001d25040d8041c030080002d20030616081c00348101034075200103a071542031540540490300b0802c0c00c0c902984c0220796941898449483e00e40540700c104002c40d80700c1d0b451600b41b900f1482100b80c0280501c8606142c01040c4041b600b144c0d050707483d2403005001c002c0c024421300000fa410290100e5142003200400c12403070034552402504c1310f19442015182500b600c0800340c11600d2580302c03010f4000702d0f40d10280c0c91079109040410246081c401761a0031b92480c1c5000703080400318098400c44941e00c07048070004000417502c088045030f01c0010754004091b00c0c20302400a420502c04c0200c480e041060712019403801d07100d440c1c032444004098600b0300d50090821180e03900708541c200c9502031105072003000c7c10030f00d030400c42c45041c45555055031080746903550350544a030a1400c07800d0500503c00d052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110736510 1250 110735260 110735269
    0x15030a0e070b031302030a1403030708070503060d030f0c060501170c100807031a0d03090e16020616030209060f030124020a14160609050a0f030b0705070204020f0307030b04060503060105 82
    0x4d0304001d02c0d603c0f80d0b41902d65400040d00b484401c00c80142600030048050300d000c1c0d0040003462042e001da80b2402031540d034a02041c1d4591104950055000400d042c034030700002e000f800100c440035505d140a001e00b02d06035403044210740081e0080803c0f05010401c5504c2e504c81009100800c0350241d810001c0000c0d1075101400380030b000703001d0700305154441d00c1400b8881d02c811700800c0c1d80c07900208050b05118103030801500d104002c0c080c00c50580e090400044140b1401043c004030000264010030b45945c80018550402c00c811010304201a000c12982420307548080141900d02100c0003801d950307514120050800001a0070240111804410358548003900131480100c12900100303400d4040c6280c1e2000f9040940804d0407441e020004d40010a001d6400120002034450513208421015103a1448000e948440c0c0300040181035804002004a40714001410020f4070241006d401c0c01c07540c6080e00141c0d001101e40310002a9280d4540f85c040c07400303006110081c441603000e40171070b50400c030106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110737760 1250 110736510 110736517
    0xc040c0302070c09050c0717090a06021923011e060603090c030803070e060d0608190b01050d0c0801110901030b040504030509010e120114060a1d06010c0201020c15030a0e070b 77
    0x303d80c0640d82c85c00140406408021581030f20b80c00300490301e000c81d00c0d041c085d20603044240424010510f4103004501c160000850400138140240c480310301060300e685007905110440c58014480b42ea2800740d8800050902440b044228400c0050075460b4440e816581214410780c810810581402c12041c04100c001034100d00b0381780c1095040d0303525511802c0680d600c0d1584244241c1210001a040550382216802101aa02440c00f40c4682401c0030010110310014600b000e814165803c0c010010351420011254146104071100381d0065501c4116600711892203a10400c0c040b00055034484960385440b400b45512001c9070200094106620014001d0241400c0d46041c0f0012a5591550740c1d582154488240450070080c070070321044c03100840c08050291000d0b401484c040101242403800480115420754000d207070f006023940c900d00111160109a502681503001d880c440c41d000d6181c40303c10310110038503940c1c51540e03400d000c000d4000b207400845140c0d100c0d4120310018040c104020084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110739010 1250 110737760 110737769
    0xf150807090320190b03060307080c0a0501030e0a060e1c0215070e061b07030317090a02010819020307030606090501020c06030606130e04141b03100509010e0102040303020c040c0302070c 82
    0x1d1801003c01c140401c4058442a195000c048502c12001408469140040d4490308080d02540e580640d40d05e01d0070ba0703032043c070b00000754441d03501c0c02c3c00d000d2540b081c0e221641c0e09418104940c00c240f80e6441e00c90842e41200c0d6040026000b400d14030100f420740418000081e0f203180300600391000401d0200f090030401518000c10020584054101c86e41c400080d02e941d01c21008040c10b0007014000002d41c0d880d460f200490116503181c24444000921650382803040442c080075206001d5a03a00444016200400502081e840c0078801003007044a4400740d032181d6080d44001996504108010704081c0050744458115804560819544e40300c12040d41d41103403050b101c2940310b1200e401100301c500c1441d0401ca48149500301000144030a0040f000030780a50941071b1002168565400c07000c01c105144010342540c00080104a050f035140d114540c001030350300000500e01520304507503003680d220b94012341c0161f100842116107440c05104200d01040b2a041c1107103080c1480d521031078800142c2c030a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110740260 1250 110739010 110739053
    0x1090e04020904060c0e04060608190504020d0609020301110c1b030106080c0108040501020702100c0b06042d061e0603061409010512030708030124030501030302030d0b03070f1508070903 82
    0x145e01e60310b17409640d01d5980424000c0007881f032561503c000a006070005caa2000d0403032100c1c1040c040c01416803041500881d00075044401070b5910361140c50160030344120403031701503580b43e01c0e610700c10111401030000003a00f803001e080c005920105000c04070a44071010b03486645084000c2282040c00a81c10120500a08102c0c01ea41e0307a5052175802030081e6000170350408042a0b03210380342d0b9030240038100d8007803007040b01110a0320380d45c06110841d41c034a0f400d07010140c540640c1861864140300c003844980c540000116005482c0c030344008144140d440c4c540c80031141d43c00d040c442d15426000300400b82c60000340d000ba16001940000f030040c201803140c0d81c0075030412074400c0c29040c82481111074480c1c110400960300e503507512682986050071103610b40d01c10b81d030442c074600b0340e40300b4041c1c14100c90700355000b14180508204040003d241240c05654184944803002951401c00f8100340010048481c00f10440092000c002e090014010001da040160360701c0140002220142c512500004100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110741510 1250 110740260 110740271
    0x7090909030c02030312010f06030b01080a0207020d05010c0e0319110607210f030b0103090b190b0307080105040302070630020c0f0d020d0f08150a05150901090e0402090406 76
    0x181502c00c0402c4840c040e41500000074843c4d1a1b2010206c0d080c121510481c600c1d000c240e485908904403143d040c4998005070194011912032851900a80300301e900080601c1e14108039551200d0864400c0b0048202259034014120300a14003417002080c039902c440f1401000240d150b4034400c02e140100023441c414040450309800f449400d0115802c403800451000d00200f41800014110203030200c6007c0000b801d2840d40c0070b02d94440c0c054401100e03070121001c2050f4580e9045172080c0300200085008641c0c0d00c030031503081650100160340c010400e02c00005206c0c102410000d061103901d804c0700050001210005078280da940b84218940c1c00a0003114080754207030900840684244c1207183c2d41072084103509060700d000400c14a200e441c1c0750f021030310503903000442035446a001c491500d01040300400007503514545c4000c00440341c44014101080c040d01c0341d001800441c108278659004640c049912220395802400003000340040284005213403400381c1c0058a80800100005d06203034850 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110742760 1250 110741510 110741513
    0xb0405040c030e0a051b0a140d0206090312040e010506040302090403030c030f1a04060e090d0c02030a0b1008060601050708160c03080a0c051002070c0b0c030d1b0e01020607090909 79
    0xc1e0300c070310100800f410a8509550b240d09120341d9850007200058503050b0560350184075468039141e4841110a201c09805406244200301f010343c00094000703a8111400300b140300c6484c0e4050044200344c6001043d9683c03103a040c500c071900c601c60142c11131307070140004100c20320260361401d01550740a51715280c089420307115044218050a900303440d00305190f00f0308111030078043c0c0c004801c08050314107460801009c2c0e950001c543c0308000a0740c00c80e0160300907180450b401d92003400014581030000c1c040310496041c43e520f04071360b00812200803007001e03881c06007400a41030510203280c1142d82481d050781880b8158032001d40c00e1154641c01c4140030340111030320f03007048400340000d002980c0282c07001d500c96200003409032820000100c01c5466000701248c00500300c000f80300380d0b2002900036082050302d505000c00101d4542c403040300385003944410300851500e41e50343d0090304d042140500f0b6004140c1072014010300119040c030552070554128070300b0070100903032107245882140c85040d000309181420303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110744010 1250 110742760 110742767
    0x6070f0b0411040207080403020103051023012001090c0801111b0c03120d06080105090d0804080f0c070501082212090308071208090a0308070518061b070f0b0405040c 73
    0xb4180150060b0011030610240b00c0200082d0003220b00130f803014012952400f8030202c007101d19002d20030008142c1800440b0b503104885503402c49800604140440e00032883d401c0780e0399a04e00c2d1440c00700e603441e5012502003044c600100c00051034120000d0198070308070f0781c072000c860069100c00c0111f035080e4a13018501e0381c02000f50404012001d0242c8148110b4882c070382d40385500510b10704490509005c0c00080c2400148a1180f14204131703c0503180110204c1000c8482030f00240080e81c1280d4140400895400050014900c55000000a000d42d528180c005009028000c00d1080c3c0c481d200b80d908c80c0c65030806c0b48030003081a813000d680392448003400e0301651301e80c0103078002401000d00441c40d18200000c00301804c03c0c5039084d44851b0801d41c0c0b08404190383da2900e0200034001407569002c03944441c020400f0340141507045000d0340040c520100450032640005d141100400034101e0303481c85c90102400014045c0c8688110102c085003009031480407441603100766800340340d5a82e45010407610 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110745260 1250 110744010 110744033
    0xa0306020a030603030905030705090105040b0103021908010f06081603090323030105090907060c080c07211101090f1e0302120303040606050f0f1011030316020c06070f0b04 76
    0x9004000319101c0e9401e40d0010020142404201c01142101d07030301152038500001c2ca08115103009000c071a03240c0c02c0c5814440901600f510850615400744000301e9000558260105410450340e15441c0b25071402c003080c600791140c4c6d0b01110500200c002070120300360100c10014030011481c00c0101d00100549412145142c10105400c00200841d410380441640d000045040302d01c111359420158440714049500d401c001d1160b9804500058034900c005aa61400b4001003040d0340103840d0301c40e40d2955820740603014640d402200c00d0121203903104100f84d46849560004081c0303000b449060501110a01c00785a5001d500354040e8900c0452001a17070320314845003d5640601403d0f07043d4000034086070740740c205580c2118070b90f0a001e4041411300341403200918100d001006c00500c40b20b203500384409a00d5240c514420421002184441d140c41000114010701d4140ba50590000300c180780242420801c54020340305100030080d400c0030451a5407103880321038010121400c551201c1c500b5250484 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110746510 1250 110745260 110745263
    0x40201081e190e060106020a02010819090602271309061b02011521080d02160c060212162a03050c040506040504020a0303030209030102070b01030b06010f0504030503180a03 76
    0x1800104002c0d141e5005107411190032140c1c0700520103840340c05540c60b1298801d001c3d00c00103900420f03101d0f0156100b100700c15080801400710950070711036810741000f50380c00c0c413200746c0c0c24076000581c58403041c0b252606e04c1181508084c901440c1660300d0f000a49406825406600d101d89864509080c007100d43d21102410091410041c000d850509010f40a80201c644019080c180c0c800c001801260308804520801e162400d0411029429a02d4032841c0d080b50009003022135083c0603c2c0c3c1038080c60040c82290502840c96400c5042c58080001d18240006000c0050014144a01c100e041994400141c0c003550060444900b00ca040404640003600b514800440d1403010f035001013409408101e80011100a031802e10040d9140c81c1408165441542c0081d003085010404001092003540504588000103001526280142c1c4441140040030381095a45034840c0052208568000f61000c2c031a40d9241070860034107156480e42500c078000c0380918101903025010341041c0d686c5480440f030145 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110747760 1250 110746510 110746561
    0x7090c1701080606090f0108060403050708071a06040f0e061302010311030a050103030f0903030203160510020f0c071a0301030b09100c18080313031106090a271404020108 75
    0x56a4840c0456a01c0f0000ea40e0302c1d0098062101042c50440411451410380309090010041522682e4040300c856201e4a42034907900414000712000800140c4506d851003205808000281000030401003198401c0482c940810301c0c00f08507203200311000c44d415500207580b03444010b803505603000503000b4102244900c507116600104110031120958006410380b40660780c0e82081000a10302595269050f00026000d03038014040c180307031003400b041c4640c4c0d05840380d015600a4120408000160b0704122400d102036440450b084030b48030703000c1044000404038000340385050701610102040354070060001403c180809030015990307100410448540700a0014100440d03400800d000342541076001c44042540b10700340c0b00040e4448000143d845400ca1100c1912a03a455540c1d580210031400710455000201070141102d00c0d5203100d9a10700900078298205c0840141120301d03030042c1c440c8041c0300480b03480c003c06801d40120140045034071660a0078100c00680700e61002180c12902c10603c030650 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110749010 1250 110747760 110747807
    0x70b03070206040506070f0816030f020a03020903100606050306090c070203060c1206010e03060c090409021017010e01140609030f0601090b010e22020306060c0a05070f0905060307090c 81
    0xd01d078001003880c4140d004406a80303454a600c40111500c5240c400b200d00050760400c0400c6480f18820044c02841c615424002080c1c00e84082c20360a9811005801011950101d50f1109038203083c0071a807a403200c1d444041101609000020340305d8040689803600a080324400034505803034403030844070002d4000303084a08503d4600e0f1080d07200e500030f80700c00e01c6040604011980c02e5000b5007001c04a024020003610580d650701042e1041a0095051658000e440e0528407015840e011040698404c2c03503070791380c540d424114004209404041c1d20004051a40800402032100408040c4202c0041140c0312661025000c00003803030314480d9030725560680508400020109142c1d404100e01030300a03203c000040d10804d0070000a08101c0391154002c1c2100245e8040700260382e401035030701040090500d810300c6580100c1030301d8016048002c45069101100610010300149901c000074861258113004516103040426140d03415446100c020944401c0015107860080d0a60403000e034103142c100c0301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110750260 1250 110749010 110749021
    0x60405030a1403160509060408060a0510050117040201030c0201110f0403030e060c0d03050a2a0906020c090f0601020f0a053904110d0c0903110102010c090b03040c0f0905040201030f0605010f050903070b03 90
    0xc100507034640d437440000e5040040c195024030501080c803c551045108250368680065000d04008003011003155a2004140c40713540580703014040c50700d1100d9240d9152811403038050302403401100802d110302c6091012000c500030001d0805259452440c0210310354031071824410261100240d1100351100752401e85c2561100b0720054041c3c03a8040c4e4580c6500d9640f980160707191484a07661039002840c0f4030014465002c820480f82d040101881101c14840030041130710b0800300800b5040b28290007203c582a007501d81d03030f0300381045052002000c11140034400d240032120b0100c01700031405251502c51491540f80c00d041903a4000806030400d015014140900400d041e150f804101c03015071003044850b01d40c0d4814424a000c8503a0780d191142c055041070381040320307074000030800c481380507400c100403510341c201506484c000c1245c0d09001c195400c091002400780c4001c0110000e0a5103402d20801c81c50380c0c0800034112081c4030341807041d07886c0510008a0708060060b00200ca41d004000103105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110751510 1250 110750260 110750281
    0x90c050405120d090b1c11121603050114060a0f020106050406080706081f03150e0102160b090604110f0102010209060a2c030303070807050c060405030a140316050906040806 76
    0x400410b1a55102002d81d45c5401d12100c040c00382044c000f0f861500041070312a407003910f520001d204c0fa4405a520f04154641c00c040b00101c00c01c440e1640301c0d0ba00303418a98021509405101c2c01342c044c0c01c410f0403403990b07010003240c024000c6404460030003440181c00c1c48860300070b5000b41d000d088064030030f0107042e440344045a910f080a21644000465403800200d1040034a86240400303221085c800388001d15503214031002180742d082c07403a19280d541d080c003428503100344014001403200c030340f0a520044041c201500d03150710040140c06190428000c120000300d084d0b140103944881201c800162805800040340280601c054107038000000181e0390702d00c1ca41040110000c84040450030380303403002c00260b82e001030351a05011500340d4018004522064090224140d0192040ca005820b0101030070001b0f00d006c5040c0c505a0345900005084130041c2d500c000e50b02085507009030401c0c510300304294403440c000891409202004804540f003d102e5840720112001010003108840e5541405101d05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110752760 1250 110751510 110751523
    0x70c02131d0109020a0b0304150e060f0105041e051f30030909050c0c030a03051b0a081b070503040b040519030807020108060f0301020c280c090c05040512 68
    0x48600000c030400407944032205000c2d042ca22075000e042e008950340b5098034009a80c0024100b103400705480840c05103410001e10501007070b8108003000344042d0406030360340000360034180c000e680628101107a0003c03003035991075030b2fa030300c281c41201c001aa0f58550b1620440d0100700204083c0803c0c0100d0f0000d084030180b00c4000240e07090400d100b145080c0c61120229038580288001c0229a017140b00b00449091540a19480006264458907002d01c51103e1400c660202c03040001090341e0b603080c0702001e00c20090781c060318007074042e40c00d190405851000d40346440c02046500c0c20300c3d0304046081003481010a443e00340b0340c04011603843e203485980302407181d0031a01815006468001d80100d41d994081465402c4a4000320003614060003900110303520301c8010141900407041400d40491610f0910003004401007100c0039100045e040c2483c0301341219441040b1009900c9007090001050380c4400e5481144d01c0c0c0040043c10816140003550340b4026580042d510540c0940d1440d0b1091010980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110754010 1250 110752760 110752781
    0x90f0a120807021f020a03080a02040f0303080901051810180f0b150306070f030c0201060506191103120c0705160f0302090f0c0a030c030605040f0e0d0503090a02040203070c0213 78
    0x1e500c0040c4c181d41214648000380c2800801a80114001c00119003c1d84010b5088400203030701619103a16043c001201d0304640d0300450004503510104030040780280700b090b0b04401c4942841480c60200342680380e881034070380c00c100300b07050741c412501c10200c07400e81150501c1d50f800103082c4002007003400c0081c3e601c04100c40c540028482a19058103d1401184c0c0600c502c145458114910900403400c60081504807100f00c01e541d41c40e40003040703550702c05000d4030000055070001c070300d03045101030002d02d1024982d2044079654020b205c001280d00c1440c44d8268001000d40c0d145840300b00713909003949000d0848601e0605801002404980f4144548140e000d50307009032241e0380107468059010103160021130315011504002e10070038030070701d01c41e07001004c445019140105105841d40d00080407a203400071024019580c1d07030202205e048051100b05802406420050b05500d09070503031903188c2e559164000e01c07903540000018030b05030141c09009010b40d0003401c09a11594201055030080103e980d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110755260 1250 110754010 110754019
    0x10e012607170403120b0d0c0e060f0117010e07090306020f040306050f1b09031f0b01030c0206040507060e040e03270307140904050102190905040b0a0506090f0a12080702 75
    0x50034091884080503490103144d06603140c046000103804803000425100802591020441060502090180f0300d200301030068084101554280300042100421052203680e0500119281403410303180400203280c11201846064000342c1c2d1042011a40348959802c000d0585102103800c009a20014000c2c20a40307125500c1000161504000d040b80c0c1e6100301d40f0141000c0d0701005001042c03038030b0b402900028174040c5c1242c00c480040402000041041c001040400b070f81c484181c0107075079050151114159860002e400c850501d51541a101c90702030055a003807285010ba801c140b44c5403a171229440d50119415283c41ba80440004d000d440340d900701c0d110030132442c0e10104400d850086092070840e0100c00701d0340c0c2011890030900918503001002a1941d540c2402200e034134540140b6003c5101a4a60302e0402c09814030341000101d40d007081465020300c401d04410302c10b035240d8404407801c04c03108459502c0010615400120940e440e41c10451603194a0040d0300100000a006802440c0c801c0700c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110756510 1250 110755260 110755277
    0xf03040e09011104031211030c07030609020916200705090a020307080a020a1706041407050406090602010621021201060902070b0c0c0307030c061814060a060302030c010e012607 78
    0x8220b2158003440c00040c00c600b41030b11b00021000d0142c0d0094009164241c103503410b010300340308014103183ca168010b840c841c0d103880c034100c1140f1f0210b0500b079000c5000c503500e000d01c0c002442e0040110310a40780d00f90b5600490a56a00f80010401c484801044000c0405a045c40c001c0b03800d101079041600c030341c00840c111030003241d508041c81c02955411001c980c2c5515410351180141c01a2940c0030307200e00e8009035200c1c81012544250101c41c0e10810130b41d140c6556841c64000014541c1c20a680480110b903d004800c0c401600d0f5040e40c4502164540000e1441c000240009401252101e503103146540c640700d00001c000f200b0350098108240516068501c541c1c6001145601d4031900c4000f0150350820890039001901030f205000710b4602600c00080c005103030b0451144003108001054900361f103804100002c0200801c40c45911400b944400e110091640d8042a510b050040015060003100c01e048400341c3d2080d940e4041080d2503039070302e1a06407111179181b19000003c1d140174000070117a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110757760 1250 110756510 110756531
    0x7120813021c0201030204080d0306170309010f0804060e07090f0b0102010504121b0804090504060b1c030f02010209040501090b03010506190506070f0212060108061509180f03040e0901 81
    0xe03050a00c8654020301104056510040c04407507003000207008906141e406d100220f2050070820100c10b00d0b811030784002952506102e001080c1c41c100003000050f40c0c0c170803c00c201981e40d104040c00c402544034200200246c8847c03916101401c003c0440c03e80c00c0c0b00d00c600010301e110058200715410003030032404001c02041c40c0012400d0700d40803a40a0314070500c40391100031040c8600017141e03400384069540d02c0c40b15026a65250680d016a004000301c0da02c600c140428002503200c3c51041c56800c4511101921010310300c2c45801d81d00701c4021b824045104039105005000b034044950381c90b8000d000308803943e10782c00307036000a129001e0000d00940c6440c00140541c24500c2a8000340911018521030700c51403e0100903480d481154200c40071918a18108010303103d030261180c00c10305420292013690704080d501d500c2c06d080282040c03441c42000e150b850682c0c50b0042c0c1941c01094004800041d900f601103824030f00407800040c0c11552200107800a40e18a040f190300b40501f450600078054010328 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110759010 1250 110757760 110757781
    0xc0206010e09070303090509040309080f06040b010b0c1005061c0f1703191e0504030c17041a07021903050706030606020d0921020910092a180b071208 66
    0x4d000007801b040030400b00340828505900c070964090322a1910b40c01d559140d507041418854039036013200307290780003200b40b004014151a049002d007684041c02428070041251241d0750795210700d07514402aa980303000c140c07141c80c0c3d40041d59600c003c0c8031512a40100501e03102e0204241488166650a035903060b030401800c00c8001c490080400011448402103076101820091413800c412a002409000b680320100016000d010b10031406a1035040e401c410740d0820100100310221050100c0e2010032090101078107016142c04c001050750744685d00c40a8500c0403424072100540f00702c00d03903c0070b07200000c02c020000444030709442031540c0902c0708036503a00c0d086e40e9806103040e0300360105641c00014461003083e080c0790131195141e11a07000b07980710150080b412000c1c05441c040d0981c07010880610501443d801002002042050200100502e0504500c081d0301c2020385841008600c49086808090042900c07018041161019a90f00e1040c6442d01101c28907428020103d000c0c10f00103031003401c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110760260 1250 110759010 110759023
    0x100f11070518070519050702120f03030114060408060108010b100306060804060905190809040606020307023016060e0111120d090c0b0403051e030904050c07060c0206010e09 76
    0xc0c0503102c0090001880880d4018a1000b0101070810805000072451143c200d02c42c007151144e181c03a81c0c0c1c0d58031300a006000641001c292054041d0340090300d021500c103800401c8030f04666000000140340c00c1401c00107800b6110300d03801950280b041a00215100f031040d880b843c101101140c0c0c082c0242c003008801c0d0b068503654450100850005000900402e00c3e41e0401c840c0d47d0f100b0760540d00c501d1a0b581c8280030503d030340344c01604c0c5008080390100f0181010301c2410042c140030700043d814028103a0000e80249044007601100d460b416034000c00c140e880500c124440510712090f50a4185103400203500f1001c240728060005012105038006540500140034015000b9400b0b0003100c6e540c9208000e1903881008014030840d9216041d00105071340c100e685000d000c010800541d120b25500b4428030b402c8a1001400c0c00800080b55041407060000454840c03a0080e01c021400c0d03076554055448500644502904071801c003000700c0191076002c07407058180c911039140c10b1010349640049569590 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110761510 1250 110760260 110760269
    0xc0305010f030b010e070306031a0103050d02030408030423130b040522060b01020f070e0a05070807020d080c0421060f051323070b0d06081506040902040b100f1107 72
    0x94000605c10071940001e40b550140c2a401c001c0fa0050381c9560307040c503900c20000700300380e204600300040c010403c003400840640c0e2000c6c4000d40c00e050900340ba03540c6038072031031154201d80c00c01390300a80000c20000745031424481c4014840d00b04c0208040d000c4024005030038105215502d401c000821144201d030a01c001119500c00d403a02100550340c80c0f200130700441c62814194420b04003500c00226081080d0406050030300c024031010300f00012944140c80c009404c02c4203020540d010442000e5000030038844072801442d200c0c0554450301446580ca108640211420000d42c84a8a05c01184400461291071040804200010343d00c0d080400300d51b4181e5016542104e46580e03100440d40c41c2518020403c0c10030404404206000001450903030958080000c250000c5080c0300349000e40c1c45104010400140500300201043e4080a02c018000b444680309569406040041d5203d59011030b80358440a002c043c81c1c500700710300290054500000c103000155261400d0b8500c920045014401c0300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110762760 1250 110761510 110761523
    0xb010f0504050423071101050f010308071b0b0301151b080306040207020f0603090a030f050903030d18170c0d0903080d0b0102120412020a0806090601090e0705040204090c0305010f03 80
    0x16042400b080058a00c1d0700d6004c00329000051010310455085070351a000f8078007a02d030701440b600c00042003803e40710024030800494580b403004101145407102282c6003590b000c81c210178400031440c00501c8154480e00100030700c0c400480041751481c0740d000940319000941e2619078140801c8480c0403071403981c0b400014203000c014408600c03d424640c01401c481e920050001403a070b503103003010035801d401c119000d80d003a50109000c0014190881c2640d0440c2501e03182040c13038080020003081e40c07807080c4030b450446180e81d48c07030100310001d0740800000740700d1303114044088030220589c3d41d0701550842030f2140b41901070422a036a0b01d60082c4414001c8982c0441c00a00340700c0a40301d100c0042003840d00840c154001c491110721103a01d280000c0c0041c240301d403d900036107030b02401844407503d65078001140940c0907009002c86030354001841030444889820100c7c10744203400f4400c0c00c1c039121307a102513041400400c001c9020780301c5410100e44401559810441c1340c0c3d80d0800002c01030300601c40902407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110764010 1250 110762760 110762767
    0x1206030b0103021e0d170906070f02040e15040b1b0d050103030e04090510091e080c1504021315050a08030c0c0d021509010c0b0a0b010e0406080c0f040609050f0a0b010f05 75
    0x403071b442c4030004e81024a04400d8105052400403a4113039010078001c58518840b240b0380c10461900703108070000414414000c00d40700c90342c015108200d00c409030001e8011409080028104001c81c500381c15003001c0f0000f09916600403200c19005080203000480c0130901d01d003800301480c28248136102020f03401500030001068000c2a043c001c101c410425a004052040190510f090a0b0791840c41076105200b52030f40c0304c4e0400d02050034462001e41c0c4443d0f01a1740414000940d0361202400503042040000040300040100b0890b807a5100360b01143e00036000c91000100100080040e221095095040c0d4500564010422503c00c0c40b00300d0003507102d40b07050107252490740240302030880704c2d0060422038042c00007a100d02903640002c482c10b080300c03610f5540c0c410241d648400e4150700c04000780c509108880c00c1c462015101d0124052450051070511452a80703a541d40d0401402070110110800150030a0310159a6401d0111000d8003a541001c1c1c0b080780c039502c2a01c2c03031000714030f00e130b9200c905 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110765260 1250 110764010 110764013
    0x106030506211219030501090603020d060b1807020f071a220b07060903032301090c18120b0106170613090b070807030b150f0a1206030b0103021e0d 65
    0x140390548424140d00c6107081940d0100f0090700140444404400e8010480c224864020f0650b08140c006428075030a1100c00c0006803076038840340c0c00460340030002042400447c000315030701d00600c00000340c601c0c80b44400d05c4082c940229a219108045c030040d03c4001e0b80f14050f041450410710780c1c1f500265410000c9040b16544401c00000074048000c2c40c5591941d035240070007090304004001c1d01c0e15556100c03000209a054402e03004c0c00c240301d030010401105403e52010386948148140340202d52584900c01003144545408441052110308010070213844011520803000c643c0d00c04c03540038400e480041402030080d00e101e0060004031000c09210b9503494140403640c03541500100c4400d40b98a400c00000d140305070140c1c400d400c150b0b41d4245520b0f14440060a84482e00c0300e060240c07442c03607260844200d40c03604840c01c80074000c2c1e021b60f80d07d0345100203e805104c1c4061000c522443d00201000300411855111704a034001c03600481c00c09025206c143c0d490954110070395004000c001e0640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110766510 1250 110765260 110765299
    0x100e0d08090d0f05030d1803120c050906030406051b12011e03050102030a1a0d0b0f100314100b09010e0f090f01020c07150207060215040c0504090f0b0106030506 71
    0xa0119000b60105000c4542c81d51082c1030341c05a644222850f03000850100354007652445030350440f0b0004036407074241000035203002d41400913124550780c43c16156050030806a00550840b620154040e01040d90b0340341c075080c044001d002c1071b00c40d11405c0d580c2503520004a0126015542c0300d200240300c140c9140d29000640c0c00b00100720a03040c4095804c0000000469070a201540c8101d11110011540f49178411000b086001d80796940c034803440c0c80c2e28118001c030300200e5105074041080b081718103c42d240c00e04800002d45081c1d000600d20306d20800400c940c0900802d20202d5100c60708028001e46502000300101140240146404004640000b450401204242540101c2c6110075113031620781c003849031030070b907400503405119a038050741041001d1150a20003058230f9545101600315241842002900c50380c2c0603140c00c28144511001c01d007070203180702d90700008110050080001444070300d0402c010000e400c0c0151028884140000b42c0300d070280c01044d215280003060215201c0c40000e060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110767760 1250 110766510 110766517
    0x307060806061602010219050c0103060b160b090102070503070c0801060506160b0403120e01090b06030d050a0c1109010303120506040501060207060c0804050406080303090708010204080c0f030f1b100e0d08 90
    0x782e0462144445001f03d4030048018010164065000ba06003841c4100c000b4080d52855840001016801c00141c007101c0d0320522081041948028040d2540d02c1e49031485000e03000302400584103001c0000e80504100c0180300503c11074144000a0110b1540d410802600d801044505607040031032488480001300300800c4030340d20038840d08110342d00c4160960064121294468030354038981d500d505001c00e0065180401d940444110000d0404003000140209035000d115183d070240540c07170882804008644021030302c101c0000d05590259030303407410001d02d0030176488215200329241001050f954140b50181134140e0380319400502c0072500e445000c031100000540d083e00c1080e0309120101c1e80c0e9030345000c3d040040c1806001940c83c5c0c00e06084c01410200c06601881050784100010041c0304030101e006160708804030b03840e48007402c101001c20308007030414080c035019002e811040d40d0070054000080c1500c42040d500003100683c1400203075242a8100103841d030080315a5a244006011030004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110769010 1250 110767760 110767763
    0xe0108010b10050c0312010e01061b02100f0909110a1407030206040323070602070512070b06090604020d0c020109060608120304060e0a0f0609030e10050901080901060f03080903070608060616 84
    0x1303c0389031446d45e4010000c1c10340d0a801c17240d4290805001000142c0c5e01c02c4032a510003020802c00048400c0e00d50001ea4048400300b400700c24080141c040c00111401103403004020151031009014060842c603204c2415440890b415010450800c07260308020404000e4804082e03154008004988550b2403e039000044401c00c0210004040f8006031020b1910010b8640c5500c510005038442042c0d281c5541015030302c041803040200140150b5000c00c0e40420203070740200043c2d580490071f44904001c10040d2041c4c00041c054a410b00c181e86e803d05905502a6110500886041206688030b5604030f45504121a00a040500620100b00490300c55484540c3d200340c0340741150740c0c44850350707105500141c0916064507043c0c1e81d10407074018160051000e0141c408101d80b0317a200c01e000050041c0c007e00544402c3c1d4100504080050541c400961007034000c5c000c02c1d41c0c1000000d0380ca242903541c2e50701922545c2e0090164040015282d0702814440d40500700081180d424040994220500707600140c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110770260 1250 110769010 110769013
    0x1512081e090102101d01020c03092b030f030906091103070504110912031209031b06070c0b06040b36061518090103060204081e19050a02190e0108010b10050c 69
    0x51030b00c50801c0900c0101194000e50009e1925064a0002c01144031f0141c40c00544101000800042d1242260000c04440354075003441442d022a885040313000300407000d00100704a00d445800c6003841303c12007818150f40d1080301160f00081e21042484280c400803803c1c8041da9009100035042d901c1c0c000b00800380307040100101c0c0d01300380d520601642e003210195440c290603000000c0003c124070034a085400c1c0c80d0a110024a40740c1031140005004540200016090120110200e58155126080209900b8000380f10742031948200e10028522003800d264a6101200302c41f441c114100c0494803a07110315801840000c208900066001c41c5a0020280d1100404041e050f41460b50302c4500c0c40d4003a6000d11801030702e90381400308007403610340e400c110409620f044080b000c240131800286810303400868109490020503900d0114940218060029805403036080c54545980340c1c0e00c4c8400c00c6603e44402d49101e03980e50342c10182210750510394541c07c64100c01c0144580ca000308003d0428016510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110771510 1250 110770260 110770301
    0xa091118070c1a010e1b040302030a030503041401060b0406030b09010302150304020114190311070b041103030706020708120f0702030406050f0d15050915010801091512081e09010210 80
    0x43c0da5200300100740c211001065219090180503800c81d6500150804541821b5107000e0668000a9456044e03840c01003c0010010008003005500840c584c12540b04200030710440361a050480a150418020000080c1c6012a06c01941c589581018122a005440c160442544081d442c405900c002d2042e4144449070019401200a10000f006900352040f4400d03001507203d035004050703848450040c1c2c1c00e19800d01010011843d041e00c030a800070b502110140404140802290560155010141c41d02d031012440c5410302c02002d00410840311017042d80081607454400d011501d00e0195580340c01a401031201340b092501039030080c6030781c00d1a280700d00d04080400c1030b100103a80d20780154042000303403a1004c100318103140680c6030300003e01e064480f540a01c0319000803c86041442203421142d1140f20700740c009001c1c0000307807000d49268140440043c0c212305004005500540300784088207407024490882c00ca0b00c0003901c400d1a01640030342240c9003c881e00b44040c280300180c20034800d8a4a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110772760 1250 110771510 110771543
    0x7080d090809060a090e0a09030206070f0306082406150a0c020103020702120a062a18050303030c040e010e130201110111030a1e1b260a091118070c 65
    0x481c09131601082c955140080e06050075403000380e200f0090210001182440002400280c0218819502c404903140c041c00003002a1021005404194060482800b030160030005007090a5100c850703150700c01c4520811519080e051150b540c0c1e412803c0c580a40d001e01c01e03001031070b00c80c10103422101e005140140c1400300c10380000e81c0340340d02601c80414543c401c45140d010003040d4000e00e0304113205020a0703c6550840c004005603c684841c0100c10060303582d250460f00040502c0c0e6801408000d8203ca40368640215043c031a80e0050090950710041c2400011700101000401c070303c244500802002c0300420780c0d00545490040e140403021035500c1c0e60101c11807841b441d01031486088840c2d0045910740c0d800003c1680036400e4030301c05ea0118144050780c8070a28851100349554201c900e020b40d10040064107030744036100c3c1200321510384401c1034280000000681c11600c0c1150140d016403100e080d00c4005c110308161004020400546a0b100040d1424003410300005800d00a44110b0000d0b01c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110774010 1250 110772760 110772769
    0xf060313020405130b1006140f0d021201080f0c13050402061b030d0609090b04020d03021207061d0a020a0320041d0114040305030c0904020c010c030902010f0507080d090809 76
    0x4ca07500c2c40740078100000710b003c1c40741d401d0100c0c0d080140d00310361150b494105900103081050800e1052800e90380007a090001c0a0a002199080410303120219201d6080c3d034103840005100307100d100b642d07102c1c0d80e02c08034402ca000304507030f22990001043d2120321110381c28000081c110061084e0f9000a00740611404c0000240f0720b18010802c00d8041c1d82c0d6103454401060460342c5503003024403e5880e110303034071b00001c1020000b150816012240344842075840c0c9401c2345043d01c1c500a42c880c07490040380b0072082000c9a001310b00d520203400460051102c545501541d200c400c200069031180740004204042400d03103649801c5040d00c141034500708207488003c079046d1040c0c4c1d4104500031070741b17202c8a04001002e1043c40c815061b808068401810107880060003404047c0ca1500c81c01e400042c0e0760506d960b00c0d811a00d003005140c0084c0000c00c59081c002cdc00608800758143d020900d8a180141000c0c0b040f0100d507000e03588800b8090501440c9101e440c01003000f06e070304481c04281040580c00e10741d01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110775260 1250 110774010 110774021
    0xf091c052518111204020406120201020c0409020307051801030303201603020102040815010317031e060d0b0901091104020307051e04050604030f0303060e0c0405090618090102270f0603130204 84
    0x606542500341405c143c81400308880702d640c801c2ca820520b0095100051707a0200300040040c10454011554110074000a418a890340e03002d2980129030600140e190b41313105080d0340c120390017510104485d130001018000c0d00841d00d4a1644001010003090603407041c3c0f06a4089500c0c000c0c0300040c20036480d02c14280c5050a056031120650080d01d0040007004030011031081da103010340d8002804c40c240701c4150401156107400408808002d4800111240c031034522140c0001e81224448456003030103440c0f03900030300c0294426240c0d030915001200241c10640200c81c014045952400d140c0710400c40c2c2068a400d02081c0c00030310340c008100010b01c2d5074400b0040d202542c0038030008040c0c148107182c00b03411600191300c543d010840316410446c03071840502c00e4808272070054076030380710301c0e9500d0703002a85041c0c0014088401d4000201407042280d0158049c080304100780d4040307001d85c20203409152080444c80710aa610242d00c611680c001c0c100403001d50740100384800724880a41c51680000c0a43d00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110776510 1250 110775260 110775277
    0x9090e03070204200f1b0106141903080d020f040509010308040501090909020609040b1f031514031b12120706060509040506060103020f091c05251811 66
    0x1400860100294074084c8911181d161480b615070b411043d0ba100c04107854000c120f4108003103c804103282c041c0c028030000101c0107103400340003000b60796100e022000720100d40c903083c2030088900407620060740d02074500900550b50051400390070b0011007001d00e0043d500201104503200d405000000d002c3d142c20101e00d019510880100d03813110b08100c0010400440d0350b0012403c241006208401742c0c440d0011035501c0381c2c0907600400d11114a40c0803a010341c036506400102040244817100659034190301c01c039455200360020030b04c3e403039580b5030b0f0b50480c0010300405031b456009008103d1401a0651031070100180107004640c5080005441c50704105e0710501c0c0641d140c2e00040d00d5410081544034000151600721111000790415803599075492900500c0d41c0c1c10700d17600054040e40c10000d00161080d0900044c41071400a2013001d42c00806100131004441d14403c10840b00c20181e2000502c0000011100c004980d191074040904000304410b04001142945c0d00380b0b150f40c200c0e0b02c41c001e11852 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110777760 1250 110776510 110776513
    0x90c020a060e0d110d09052e23041d0a090507090501060206062209020a091a0307051002030304060902130f0b01080108010c09052205190c092409090e 66
    0x10481c00c60084c01107807202c204804c442d0084040620030030b030054801010303031340e05481c10a18076140c4a240240e40c05951100c8411000c45185400401c3e446144d1182424103444500d42902006032628803d000341d008440c0040544024180050840a4000c0d40030420b11408203030342e925610b03811f040c11815080740c1c000540f00c00c01405440d404104140d08100280c549940920000004030004501804400c01c8142c4401500b0159030b51240c07214041c1c461010100103c140d80d003a1450410500082d0341e0082c02010800106e901d843c0e8131a000504a83d00074601c1c65803681d175844010901e0b010100ea100b0300c01000910105c020f4441d640035900880710000d0146030510016041190513401001d40f43e04040c1d001da1103d40c403010a0b811601d090302d0003950825995031248800d81c842c80751750156858002086108060041c0c0d550100083d004100825540401c003120320321254001c010840c0d4142200b0803040000a40040045a092511014075901d84040034255076440345404c00d603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110779010 1250 110777760 110777773
    0x5030138040c0c1a010b0a0809120a02010906050903030601050712090305060f0604050f01050109150e15130e090a0b13020d031d0402030115030507140d050703060915090c020a060e 79
    0x1c004e40f81081c560b5022050b01ca031149503140200000310303441010401c2e030412106402044600030100000540801030403400d1340c503180102e800074000d01904e035046d02c4071402d080101e0b24a103404022280074403410794840740350848980328240f000c09803040f40c0e8200711140900102040c400e1144034001e42c00d5691001e50f0b402c200c0c1c100400d841c800b40011071441d0840004005030313a0841505012286000a4101c6820403000142c81030200424940e81080c038010104004142084c02030440c07410680ca80e1041075154006140709940c2103803040c0b1550310083d02c2c1d40105071242a4160310054401041c40c04182980c080752082542c110100d0200d000255140c0503981c2e414802c20758010299401c5046614014100c03410706007940e0901c06040e0750300701207620a403140e8070b2001c0c80000602e140c0d540b61108282c54000300302c12160f450000345046004501f40980340112084000b011059441550426200600030301c07010300030b00250b10442101000090090007202d07114a03035100508038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110780260 1250 110779010 110779013
    0x6050f2a071d01050405071205070306051c050d020a1101142803050601030b010e04050c070c0308040608010f060c022107080303160908071a040b0309031305030138040c0c 75
    0x10002c4103802c824445c074180070420003403503400324860b041182803035004581d9469030a415401442a034000d113400c1284961b00b08844202e0001000030b95200390101ca110072011001241c548458100c014001d83c514020081c0541c423a0b800d0041e4414407500c9103103400c80304c181003c080c0200c1c20302042c010f4040c142d5a21300300c5c0c0500c01e643d4000d47c2030070b0600030100c01d070000a0103441942c4a19110750742d43c8003c42c111101d60703010b65003502d42c040300904550707440b41480d590340d40040c0701c0d1320300180d0303c039002043c442c42d0302c1020401c03103410b070703d807001c58440560811003111000791403000390602008003100f5a5800300f0100c001840782c00050341e5682040c460b25010000c0da04646014041c29440411140ca0001019011204031520f0129510001a84140c0078400c0d61310414620b40044140245044084010403500d107400b40700360500c40d070307440c2031500381c821140084a503000d03080d4005551400c00c81130200c1106142440160a20782c0200041c12100a080c400380051002c00e250b80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110781510 1250 110780260 110780309
    0x50709020c1b190306090c0e070c05190c0621060b0705010501140d03141c0c11010504030509040c0c05030307050405090f0603100b040e010509030307020706050f2a07 73
    0x500d60001c0c2d410240b401640c036060320f140c00c41440010300d110b5903500d81006000c180e2400e04003500d602803035610181002c1c0401040d03404c906000ba1580c0c06110106903034075001186e500d0119a0043c1601d01d1680b90840a907444411240c104484541e41204401c081e4518482d610280540c0c1e0b41203500c81c01d603800d01c0c43c2141c4050300501c8084070300041000342940c0d41040071800552514210000d01500303640750b00b441c0105084180300c0071420320500002e0b051030f040300410303807065924090041d403400701b658241c0d5426034000e00842c0007040030f08881d08094000038501c3c0d01d14180803040c0007869540358515030080321281c0002c0c60100d020303c05441d0203504550000a2025849002e02700140000d2b124440c0c00c280318079040d903d006001c26501c591700080030490450f00204170780d01d031102e15291690710803205140107000348000854030501a9007a251091002e41c01ca6050640fa0454070000500d146151402c0001c810281514003104001000250072441061450300d0b0410350b045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110782760 1250 110781510 110781553
    0x30d1206140303040e06060d05091c030506010804030e010c140618030c1c030e010c08061306060e10170a0213050904050a060902041b2006010b0d09050709020c 70
    0x107544414440480406682d00001507400307039014110218856214400090503902c500440704145c0d43c00c01040221003900454060340403001041100102001c6103011400c442c03049614034041001c0c1e01c04107001c0ac0c481e0641c44004841810a40300a608503100d44410448404803210640c1c0000704004881e040f110141c1e11400042000394140403404d4036880d01c80b985d0b94800c1565904072216080600c1c400d8000d890380c0c096000c002c101802070702c4401440720701c0864085000d00410358071520211494440c01045801070b079204140e154464040240c0801c40c01603104c1040404101c1c0c80301907049500c003d001e40381d41d00e801a55841d01807003c2600c058a50700c001c0c0b10303400c01c2080001142001c03a4134008180c2c412000158219540300040c010087c40030025840c44081207080c4081d5000144c0e0041c00403031009890f00d10381e00894882d52241c0902414070566801e00440c104404280c00206845100e001a10081500c40394501c0803600180c0e08203400b0707803040140480c1807160074480c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110784010 1250 110782760 110782769
    0x30e01090b011a04080a0b0604090c091407080108070513090b0f1603090c050103020a1403010825120308090a0501140610092402010b040c08040c0f061704030c02030d1206 75
    0x405003003a1a094a40741c4544101030087d01d60703000800020603603600c0d81d100c40c40040d801100a10004d03160304810380204140c0d504290f0a19000740401e100b00e0003802c10318100c80a0200401d21241400c1c18045040c040085255005407201c10b4100056002d070907003481150b4140d0072801b00c1c90b20380c008a401c400040f0000044c9407511441501180b40001c484082c0d8030203007400b60341e52200840c12181c007204410640395003d400300c0040740d10440464280c4401010300348110341080c8181e112400031803d4410260f402510500c400c0c0017901401c081584011000c00b65282070050380c0310203003510b8110118013200d8203103d041240ca460400c0c0f00d110030072004e150080165040c0540c4541203140c40201b80105244465240280ca20035003010000c144054010300070145041d10180c000c100a4800700c500407003040c030100c3c0b034081502080c0101c1c0d2079a5070b030a421003030607103900d0841980a00b00790108140a000440541ca0800c8a52041e49061b510302c642c0110311440c800446606402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110785260 1250 110784010 110784059
    0x420130230040f20040c02070513020f070303091b03260c060103020f060424020706020d020705010e04020403050102120919030206010b0c0f06091c0c0201120b01030e01090b01 77
    0x34000403c07034018030300460315030002c6002201c034015140005030384125210980e02c1414001d0051500e075007c1070407011554207607070201c84004103000100983c0600744d40e00c900d45009000a02c0480c0c445d802401c0d01e14040c0281181c502e0a001044002841907001901c904868010b00d00720f10002094035030504c0404c40340a403c25813040b4041382c0b1001d042c070001c1d200342440c825106580e91403604480c010040010100900321608000d803804c00103a40ca80c1e4058010a03100040301800414801d41002880d400303000d100b81004c0040d40d07a031507180c40058001f17a080c0404000168244014500718040340140d00252500480081c0b6150940c1c13604104d000c00a51000c00082d00000c885040d5203d4506c2c458540301908401840c1c90210211201d142c41114144407044201041005000c61311500c1803410880824064600d001f41d1940240050314a840781d4040300107560028442400524001c85e8641004100500395607050380c054859668800041201d40b090000f01c8490010460 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110786510 1250 110785260 110785357
    0x40e0411040b180402040b030102070605100501050f0406050a02010b041107021203040609091a19180506010503010902070201140406090e0108010506032505030d0f1704201302 77
    0xb00d2002903080388924030f040309440200e0110351311508072129104010340215110071413400d040000d014150b840c81c0d6003204003030020406500c5001100c1c2c00c84c07620520103162500d0300a04075001c1d400700080c14115503032881c00031680e54170350041c0c180402c991518a80c40e454a0b0042014290012000c1c40040e48100810011150024800c03812541900000160140342c0b100405400090142c1d095105000e03c1c06840d241d90100c2d1101c0689003840c01150040c004003000780100ea8080e148540801c605000400103412703150000c210b00c0384189040319190200b9982200c20740c0180c0c028030081891200103001c078056070302a450050500c44e0007400182451004203403217052051007904c034002845240940c004902d2640310040c40301030304681c0c548070140e0300102804c0303c4000610016070042d2400c0c600d64942e0b0619030140e5005504099440d0b180c1c0f10f05090400704a4105400900810416201c880c1e0351000e489030700a050824411054400c10814190140c0c4602c101c142c203251 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110787760 1250 110786510 110786531
    0x6090605040c03060807120f020301020310180504020102060c07050a0506151504030f0b040804080d0f0905010f0f080a2406020c030d08060f04020c03071b05010908100b06040506040e041104 83
    0x174a00e011541103415102450050341232050702c1c0e02c8040000394143d070000081c458190a8000c58904580c44d0343d07021484140701a45060035181309950181c0103034404404160b613004904018000301d481101200c0c0601c60070355445081c00402c8a0441062150000c40052814640070708040d000700c0d80c110383e1038181195603002c2124400d460151071802000006010403c103501210701400c0700400719146011001d200615018074071804800280082d40d00007035a50140c0604004620341d529000c0c10b00502c0d05080301c60540081c80f0300d00305a1165900c00501200310143c0502d900c6c60b0520f500114144817000e4580340e40740700840e000e540301198054080d94030190f03082e00070307a08503007032062000b074440003a0103030040d60105259800001205010400040304411084006071006900c90340c0c1c40c4015035090417141b217210000c1d001540c420990f21515801740b152082c0080105003010f07125000b04100350420780140d442c0450704424402402400349025151040840d0b05014403800b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110789010 1250 110787760 110787763
    0x70815031f020a1b0f11100507060b0a1a0d050f0f1605040e0a14100b250c0b0d06120206040303050c1e010204030b01050f030c010c110406090605040c030608 69
    0x22001d0040703540b640450380d442c20301c0c4107038807940d240c081800d0031440030011420407140c808000c043c2100c038941c0400c00c000c4c85003400a42c0c0c400d5208661503640c100f03038603a22000701800c014050507a000e4858000030864502040b0500051203960f100c4584a401002c6480102d40700901107038046403204080051450021101a0340304004903c88814581c0411050b105070140307401920801c500e4201f00400c3d410310303030301504ca101400d0500301c0080d110046407040d0301826008195078130108000c91122000810301c4040c4045130405040d88500081c0c0360040000c500d03401c4002c0d920350000da0466004158001c0700301810305104003201c0c0c000c0380e50000301644224800202408000304007400041010300c0041c42e808400c440400790400040c191034001c0d40705000840e180d9030b0080020415052100100c441501d028009082030020760f001507070310292450007103c040614204821f00c80d2250b0050034000c3c000300f8000301d81541007608001c143c500c080701d124105450910200600c040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110790260 1250 110789010 110789053
    0x908032a070c060f02030712030e1b03030d0b030c0d030206060918060105090736060215010e0c0705100b04050f071205090304080a080310050a08030d0c0e0907081503 73
    0x3c140c01c1c210086090380b84160f0550003114800f801d80c485040c4a07003c010b40540024a00d00d030190142d03118a0300c000240107044070300790340c3d0b180c01d83d100b4091301806407050b03403262512000080454403c0180100001d900d07420401040300142c00240502070030b8100619203c1d048066002d251703035800d0002c101507607103020501c030b091303c00c00c030007004030311602c1c00346d184203540380032000c20391040f001400c2071011500e0359204808511034a044000401d0340c03001c519603440310b12103220050303240d107080270442c192070000d0481480d101082102d280080d1040102e10b000301e101001c00300716246d550080100312a001410244042070035030810032120381c41255503040000302d8100194039110543d00900d980159004188544111503042060080c100d010718420510b4094010315a91100c06010b6400390502c44c2c25065407050282c10030007030103034210f00c441750001e281458000c003a403030014a010b0800e0312644040b848107414070440003440182080300305010340003000d0404100707440301e88600c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110791366 1106 110790260 110790269
    0x1706040506011e0302040e012d140601020c1219060207061b140a0302120408070203070b0307050901180b07050609010506040612060f0908032a070c 65
    0x1d0031030f02002e0140a016004036401c1c915420300020b0158041300241d555205c142d80050f803c0c0c805541403032140707d036002c010320300301100c4983d0488429046401c60043c000040103c030343d800181e064130050301920381541c0c0f0555100803a08203d0048000c000d0a15900714401c1403040b05e4010b4501c00380610000c01140081c0e10800c0c0d1342d16120700000c00851000d182c466003403107034a80034240c501c1d46c6040240c54002015070fa07881a5104036002c07a20303000c0209140f015420b0800015025024111006185080944028080c1c1c0034010001d0f0400080b07884488018048420f42402041c0b42d203035854403451686030072512366004480800c030561030003000644601e02402140304aa50404808014a205407102d4020b0204890311a01c200d0720b8000900008208100440c41204045c00002d1180f5181080004880c140342400c5c100000900000b00815040301807031080b01c = true := by decide +kernel

theorem cover : BRFrame.Cov 110611510 110791366 := by
  have h0 := BRFrame.cov_init 110611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110611510 ≤ n) (h2 : n < 110791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
