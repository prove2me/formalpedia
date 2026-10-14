-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:24:03.244181+00:00
-- url     : https://prove2.me/submissions/fa33750c-b990-4fb4-844f-bf50cd16911e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419784172 ≤ n < 419964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419785422 1250 419784172 419784181
    0x7021c05030f19020307110d02010c170d0f1103010b030411060f0c15040b0a0e070b0a0f1803170c010f050a0f140c030403180f060c120318020906031203 67
    0x1031032900700461040030781e000c1c50f000121a074000012210407590149011064413500c0003044803520308074000740e0501a25825610029090100c0c5016034000042c090342c94030004103c031001c40b0164081741841c11301e040000b011108114007602d0454010521003962541c2d10b107050f01c0c049a1a01c181070b000003000c176502520300c2000020340244004181100d05a103406607076030510240c2030340d0103000806090003086411105410140b2034001d00d034112406c003555125001030540c441024940005c50f12800001c45940c0941034007202d00c0c00c03410030b541ca00e055407507001003450981d4842d09910302c000f07a011710491080d0051403021038514010065450403e020801a050b92441c40300502d15040820054007104101d140c000c040380320b01c035406c0d9030300e0b546c00307907011000040c40342c040c0e0002030000107030b4640d51107080c405044169103160182c80a45000480010780c1e00610060505290814151081d84400030658a03011981ca07116070f1a0340002c00d00705031800001400d112000400c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419786672 1250 419785422 419785447
    0xc0b010b03010306050a0213050f011b08030103060501061103030a150306090609050f03180607022206321012060b09090901050f04170904020a0315050103020901020307021c0503 78
    0x41d4100e90054900340310599030442c09100724802e108525000342c1c640c10081c000f90071711042180e1041010705010a480202c0100300000c03500101045605840000040c405c106003801364900421003400d121402d1008400b140d0385038000100b0034000710b582c0e090034968000c6103682c10b400441d00300200700061111820402c0180010303110994041c0704060002114480000c11904036496000c0511740c51132440c402c21415500003901603900078000700c400020b10300c001c02900241001c5680004202d894990078401451013880c0c4c030580c3d980d000e501d01d80016002481d400c100e500c21a0b01c0f98100d200b4030030590f400e000c0c100880c0c0806151000c0811401c01e60710040c00b14034022a11030585903180e0038180d0994004a071500781c00c0c0d424401080020b0b80c0c5040000c1c103c1c240d004880d0a043e4460082030407608132625240000b61039048820480c2030207074861003d40000e103400d40c903041001c2d001030743d00d04c01e42030020300600ea83d0f9203881100e04500c1711411095440400d070780e030310590400309 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419787922 1250 419786672 419786677
    0x1020109020a2c0705130807051c0203010605180702100b0609010f0908030f0c011a0117070c1e02100e0603150111011a01090608040f020409051005010f140109030b13030c0b010b 78
    0x601b03502120314404200340d0b000113044811141c8c020442e45c4000800b1103e01040039a901080380c1540d21039a0108640d0ba401003426980c04e04009200510300d402c6500928180259001d1510189081071040c180d880f80000c89101040a0030046a600b604410464201e210795000100c540000b107900f00c201190140180030700d041351340c024000107000008004020070580c4600c2c0c04110030801180d00c0780070381d00720241c3c4110340341411032907001642c560760500e40301681510000e44c2d20304990011403130f003003e0080054506c2d1070310316481001400444c400d4031011704002040c1008084043c0306078862840c220308145080028400e48080c410700d881d00505d081c01c100d012481c40340303001c5801441194078500c62a00302904102004282e000c2c80300404510000703031814004c54103d111221090702a0798001c12600020000c810300d041104103000743c0345c6403600d04020245c882000440c0c900e841c05504443c080c595040c0c00e201601cad060b5276600701040000c06184014000141d00c0854602 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419789172 1250 419787922 419787937
    0x6010e0610181a0403050a080301170f0c060309010603230106060807020c0603070c02060c06040309080307050309090c0928050105191d06070b0a0b01020109020a2c0705 74
    0x805565a51401c0700680300b0340c000169000e101959860100301c20204411980d01c0c81140d01110b500d000d46a440c1c1030708211406405840108001004100704901d54220004500c071901c05007096a690b2484e6907111100c078088240b0070344020002c211402001c1d4005001160b2215a811040b00742048002d070820b44880040e1141d4a40714001805038041c000c0b41d84160601d034050000011082c040284036000501004d013080400c86c0b030b900060b01c401000b040e50498a40040c52145410301c0c000f0b040d08056080301c107041d0018006100001c0d000425038054002c01c84060040340d0b00d40d2080c80c41c90180301d0b101a401460002b0019070a840b040700000000841b000003804661180c0054583d40b054141544c00085054085440c0a104081d2151007122a00d11660203102410000d00240c001390700c02e43d0074450001c14040324004a1042910301b1800780000d02c17610015800041102c0c19504c502035003c4592100015810321110981c14294245000290141003500001301560000007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419790422 1250 419789172 419789179
    0x519050f0c01020a050d050a030b04020a0c140c13180f0c03060501050109150302031312120515090103080f0702092e081002090d05011a180103030203120408070506010e06 75
    0x200303900182d4408a21039914030340020040c80615960f0404035042e500484080c403c0680d1500d00300080ea03124001480d0584807542d0310702c2800c250b4148880100c4400c003151072564001c1a0203d207540b6a41c0004460310841540020908240c280748805208001001007001401d0303140841004050a50482640d02a0400f040181e8071800103480449050003002100c0d038581c40c0d00b80261744690015580200105d10204200005a507061940200100b000020512030408400d00643c58420103502003052524085445030780c001040000c0010300020703112030000258002e01c152440c04a881055000d80007219601d0280404542c181c7c000c00201482d610148294011907070030b170f0141c800e4890f00f40140820700d108840300002507221180280e001140240e211012074028411a8440440c4568030040244000d0400c4403110341c070307400080799081e07000c010720100b60b0010035205070b000505070040b041d89940c02e01039023601072a54001d00f60710904001040a103074010301a4081d46094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419791672 1250 419790422 419790433
    0x13051e0708040204020703031d010c030c0801030f02010e2704020114090a05091503030403060e0606060c060a02090f030a150b01030b0114030c0f030a02041d090a0303090519050f 78
    0x491a0611001518a5400540c02001040152515a0090920910034140003407400311031904222001c0f66018204c032145d42d41e20f441d007141c9401d809210101c00c05840e0220083d1b0466a0b5800604000c0c13501030304100712072104031744030345411004144110316580140041e02300801c180b00e002400f142c0032800902540b00b184024a003043c181c50110030018041d4800c14188014481c0400c0e0003001d000b20808100c030b0580c02e0340c90500040002d076004400104001c601884100d25241e00034180500030002045100100705000c40c2d46504081c1c0c1c182c000d40c0d2120010f0000c0d1070f0ba03140c001b115504d03001c0c80c11040304008101c034070801c1102e224003081c484410785400641c1140c038990070342d5001c18410030103c212514514021035002c170095803001e01341100c0c910302c100f0540044580204840d4009030600c0740a410144012440480128000c458640091120744607506044000c2c24152101d0142080250501c050094883e00c04542d205403500703410070320707a6000303100c80c401d46c0350042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419792922 1250 419791672 419791711
    0x270b130303090906030803040f0501061d01090c0c150b0f040c0302030f0a0e0304050f0d06240506180616140109020f1e1009050405040309091415010507030c021305 72
    0x5001c4c0038212074000803520708641e10313a150b048403a55401e10443c0d841d5038444000c50072510b0200d40c1126660105201e4400d90304100f40c040c102d458007400c02c010301200c0700c9500c0000c0c00c2803d010394075290120300030038110000b20200b03140904921107141e01a092850340101281d155000d14030a461a03c1c0400443e1101c03a0244101c0ea1108149180d5400401c0144014208071014803690f1001511100e101d0400751220012159200c0e1111802e41640740000300001c4102000c0018000c02c4510518141514086121b004260503080d4040d079408500e542300d402c81d083c1c0f4012038540003055580136107411501d5500070183c07d0303422882012250505001402c064030300e42203d24850031400950384189040110b45500308505004018800e030000c240e50701d0340d0207203600407071094480e400b0007800c002c1041c080d541c0805a45600e52070403000c02c032800034145205002c00c0000c4c20090f03543c007440e0030101d8400c3c00c01c1101030f4011010780c0401d03c1c84115907005030b00c1440100c0140c14464607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419794172 1250 419792922 419792939
    0x3150e010f0e030405010e060906120f0c0a02070e0c0702030105010b03060a140a0308070f150c08130f03111e0f0c010207150806060d0905011a040c270b13030309 71
    0x9000e8010b648603807081c0b00600c0254051400c035010404014012400d04d07124600203030003680020b016045c034085401c01d0042440648103400d420031021207405051004507c402907898819120b0002c0c228403481c0400c12820b00141140c00b500d030003800a0005e507071a04100f00c45d560042d642103000d600d00420005000400c0304207900c8019005103101c1010380b070350310344141580204400b55044440c403001c0100281607004141924010f580c80030071050130309030000e00b0f403a00080c0f00b8001980400a680001213840700800100c1c0da15051009403181058041ca26108028091081c4116911072105001c800015080c44250000c0d089682031406c403801240c60302964400d441620700401c0c01c03d0343c2c440c00350220991115010388850b0508081c884044191070000c44155001e95440c3d1400a0742d6001140e0303c40d044c1000c0c3c5040c480000ca0503130041c2074044008030f50911400c81d05668007100c0300c00c040c2000601070306c19143d480d0110003c58109114041c80110702144100600140c1c20a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419795422 1250 419794172 419794181
    0x311010c020105070b07020f070e1e15130213080715030c090612090206030408090109050910090b0a05030d02072310111510030b09122203150e010f 65
    0x9506070350f040d082420581e65140841c5000d02a002507000302107107240b1902c800c2000300000c082015036820301d8200030034080307244900100304481c520b04038003c10078802004004c00030001c2c020f890111440f001c10071210001c0c003508801ca180c0110b1040006a21040011403001b942c012800e83c0c60070314121881541240c5103a007414021602d5540700704406401000307156010042c3d08404201d0300748030750000c2c920394421241220450750208040c1d03d00c0d644004060050710080d5161042400e10310f29218000d196031103900c00e03207a120168200f07140c6030310038003500400e13000c0c04032181111210f0029440e04514060079903c80e4108400181c0c03592002180b520045000d8005a40d0b0b1504803000c442d84000320401e00c0207445104003112480c4108030100303100d03103259500f17030100a040d45049929428040e001180b158054151070206d032442804031075404205510400c004025480c03020f07801ca00c1e41d40040c141c9096907104902c455501c1d04604a6040030342d0003001001c81e0755075514200d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419796672 1250 419795422 419795447
    0x30f0c020606120a0f0614070906020c060a120905030702090c130b030c1b0601090c0503152403040b042a03060c050d09060605010e060f12151009031101 67
    0x141d2200e4003090b61803d0001800140254100030340304040007030b46544030300703030500a01140d01c81d503960028140d81d44001591354004000d1300d03140c2c080c9850010025038800c400088a07100e801c0008007400d1541c0584107003403503490380280c01c1c01405802d08200e5200c2d0030009051b40144504030014411000e910b08940680700c80101d00c03052141080c41c45081d0390402440381500140403c00c44404112860381080c0f1032100e14010500da41c1041c80540c15070b14580020400e004062051060807000301000c920604800c1d46c80d5440c000480d4810190400032140c041e00c8000d000040c0010302c118002c0892103540160000c070b1071a400030a14600d41034580d00c0e803100b00380e0402001d20000b040d5811164034440e1500d081130914115040345000c42d801d40900311440e50384d400b000c1026580042c4107000910b003c940395030030180801840c0f00e00b4070405c940c003c11450000700180940e0715691004815070360140c82c07111540b0705000c003c4c0c0729411501083d10098000704c403501107907103d541c440004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419797922 1250 419796672 419796677
    0x60615130b03150405160e01090f0e04170403030306030c0b03090604060f0b150d05010803030705030103061e020a080f01090203010b0d0207050a1a150d08070803040204090b090706030f0c 82
    0x1814902107030304020750005402010005581c0a40c0361107607071540103140c002d420014007400c20034090301d405403511401151840c10f00052102c1000b503500e801201c00202c07814a00c1ca40501da8492a140d510181c07050140203c180000c5004014194140d04c9401900e10070624658640d03110480f4908a0004a41041407a40604d001500240a640000e940e016400318041281301c3d0500c00501c20000141d007108501d1008507503900b01d94414055079004001c008061031075828aa40000c1c090722050001400380390f10345041a5440e204010489502c81c0c046c40115120780c03060100800901c8140e60000e08042c400b800804c0c0845688202c83c101d44070300050529240b0510442c0d0041c1d00001c0c01038809014585038a00480c400141c0b0750108841c0710342c800c030149030480908580810f0b84448901407030035000154006180042140e40c01c64000880940300d55807803000a024000c640001407440c9928400c0c4043c40e0800182c01054944684040c0820f10200c15000110384010641b81c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419799172 1250 419797922 419797957
    0x2b061418031c0f060803180915010f08070507051207140d021b150a0305243a0c080c06090906040b1804080d0e060910050c0c0a05060615 60
    0x3001c1c00c2d107521291030612940303004150b05582e2401107080d9000700001001c50240c1e00d507400460b1400c24981c075804240d000c2003c14500c12000024042e100d034082c0b0a051110060124031058000c00540c0c0103c2e03400411030344001202d0243c00d50a030400d0340c04071750300303100442041440c000114610488450b00e03401841d80a406ca000204401940c3c4c4a440d042240c56207008240b0324010010800b990850300c01091398104494155001e00c015040201010781560b085506c070340d2034200c000c0501c0f00c001510290380381e188040c468031480351501d400307000b802d00c24080200314404a0b400b040300e44200983d5600a00031090006501c038891002d5480002e9800158180c5840d81c0700400035036014010150700404111079206400b03007610b09036032221740826030150303404d00d5000301480d00790528041c14603401c3c50312000d550382c0c07020524650100d45520001d0503074500c3c5420745801607003040442c0d000703a105061032510307488213803401c6028900000104503004421400c5800c6040590103150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419800422 1250 419799172 419799217
    0x1061d060a0807081009090803100b2b0e0a050a0b09070e0105040c0302040e0c040317042301140a11070b0a140a0912141b2b06141803 59
    0x6800f00f10061884240c10311152006c20f0004092080d4824548101c01c0c035543d80c20130300681003131034800354014080f08408214101441c003080b00602380010011210040c8421312510036006019819a00c544030320904800a0a102000400c0075001c2e008002002e6036842e0b1150441c1c0b01c0180d07000754090400c0c0007004200508041c1c1c000b14440d11546001401c080d00c03220310602841c000d803244030320148089020b00903c44c180e4002d0b000d001700165820704c0c00346002c01712642012040151203803080c580903108440c0c0d011781c810b01c480c450880342c3c0340c0d038615013518081c09600c0302483c0d6a00300c0c072660b03101007401c014150884080c001c03551607842041c02090951b0780d51354000f62240c410051300103800214441070300c03007840e1814800c025140c007007015000c0640c33070541d0019185d0503400c1c01041840341504c503d034080001c024141c0122a00c1203294000103000d01c0c441800800c86481d0600e120984481c0150060085c86201c030b54600908a940100d80c1d41c1c059501c11180e0342c4001510340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419801672 1250 419800422 419800427
    0xe1c0803040c08070e150103021c0905120406050a17010f030209090115060309060e07050109051314040c0303020f070312080711100c1206140906031501061d060a0807 73
    0x1140c0c480c1c0b08200b0541c4141d120403c1e141805400ea10500743d104041c000e1040316426044415182c0400b031a04600740038201024013900b10b40f10965882036603485440c1c03428058144000303d03421440900c8150380d6699500018815440402c112001601007020310b00c81c510750f020014100d8a12a034000c01046c110303020803640305c4016004017000d48da0303140140c0701401c4e6090320320010080760b2070014008010341000c6059541c415210701140d00941c80a01030b50713070021000d10aa86080d10452041461010b9542c000d2440010702444d43c841402008100400390000d242640e2003a0700341c4800510090180766107103031500008000300300030416a01560701c200a440d502c5402444c00154038542c1c115103c0c10020300d00446104a511440440c1c4003503042001c50f0055201074408100700c51600c4600c590350400405041d1107440003001280040d0b40c20002d800c6a1255218518130a5035101400703810340e0300d019645541611150708840a40c9844000d40703804100030340b00c101d900d5071140d104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419802922 1250 419801672 419801677
    0x70503100518060f010303030f0506010f051308070e06031606020303161704050106090e0309060d2d06030b010e0603061506040810020c0c0303130902030406020d050a0b010e1c08 78
    0x290801100d2012008a90582c00c001441c05654102000501d030350440c240101038604400f03130384185500305001d0091699002e010a51240481e15080c0d40b11490310b00e941c1010500750b80078600612032100046031400d525112107016103005c60403100b4083c10444c545201036030314032821025820078000184440303078051811550b8006850411030707030480042d038a03032071500946060310350f42e540320003e1100c001540301c1c6540001081d40118109450440018400d100703034a08282c640c1d48074981c1c00101c800d0780d140a110b245200717a07440d0714803c0a02d00b0000800c0a0310099807025040000041c1e500200007a15001c3c8002030301510095036100d0b0312203013109200d504140c20600804c0001000c00c2c0520040070010882240941c0e1340f00004105460565401e41051017a08100010b0204000140001d421581a132502584030350380c40c200080207029901403160f03400e04150410100c104240d000c000203402c00d0b200c0142200c550824002e10651059184003290340c113411480104d80c1040c007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419804172 1250 419802922 419802931
    0x3050a08090303120f06040b0319020111070906080d02010506060702010c08030910020a05040305070e0606070b0702100f09060c1701090b040207050d2d2f010c020318030705031005 79
    0x8503803403c1c42c002c1c0004007141c82100e03002d008060318030600091745860b002d0310756080d03400c40042c400014842b00c41d10010601c401c1c0281405202504140740c460103008400050030406002c10460765136401c0c0d9034461095149080c019440c00000500903e84041524046038044c1c1d0b400f60591026507407a80b0541c40a0400c45451040303c7d10007511030b00e02e0008028904003030342c035141c489140d46032081c9000c10341c0c4c11000c040d040501c20418a500d44005480800390806800a0561071396101a070a1510207206c508110b400c0c20840507042903070790801c03840707188960381c100f05801c00e501044031048500c4850443c24802c2c18010040c0b2106a04070042d0703040010801171900c4965503c0a203440807031401180400c110500000d00b0352402c0e014000c0840703074244004690055400f004110b04188103500b40301d02c850302c440c540c890081584140c80b08031004000c0000f01d8200c84080d50301e402c100305020441950030000c41942c00c011610030112407000d4020010b2818440032100903050041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419805422 1250 419804172 419804179
    0x906090d0e0d050615030709020f070b2502070e0f2701060e100303030501240c030521010503010b030a0506041101051614160e060f030f01110409140103050a0809 71
    0x100180105609000d000d01a140311000ca0400017100301c189030824042c2d600c60400144188590011400c20304200c83e086980b00e038000b0703015079401d121230707800f51687d46921003510344c0d4161880d0b01340c2d00001c103c401d440006c04944019a41d000001e80304160403600003000e0700c000c2c00c059035071048095038102911040b2001084464440041c4c10607010100e80306118038442c1c00040040c903800d407241c1070145c83c1b00c140329908891000c0000c0c400107149820001004400303607040d018188604213545e581d400740307844640d1078160b116114403500d40a004d0244254600f20031004030745070000304100c4003070303021024240d282d645440d030b0384040c0d201d051030505100f020045100c611010150050065204031241c03804194011011851f203161555000d821a10481088c0109030210003547c4c6d2109080312421020707142140802d081c000c5000307446201e03600b45485504070800010190081c3c45010604021600004083c018802c0d4203103c040c02e507804c00d0a2002c00706020301c005041301d40014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419806672 1250 419805422 419805439
    0x20c12120a06083d02180405010b031501120518010b060c070918021203040e010f0315050714040f030312090803011e0f121e03080601030c030612030203120906090d0e 73
    0x10042440c0304c2c0815020400c805078001140c04a02044803940f10800390152020450f039030401c500030302030781300140440800c080c4a20000856030f00c942c00300e1032040400a42400381e4205000304000c035801c3e070415214154240600e07001203040c40320a8801c4048080010208186486030010007004800c0341900001c418000e20005604c2e100900345c20005014029591503240204070041507406030002200112204410000b044407122544004841d2110000301c603184c0900030b4a0000c0000e22401c140314000c10300013035035581e407410001264040d40303445400c085d1418203842140d80c1118010715040040c03005100c80b442060160042c26207606904a03555220400c1c03004107291640b00d40414121014084100043d42d5212140c0780c80404030603107200300340d0b50301426087c80181101c0c10580c5d51501e2070a228869001700004041042d001540c0d41c00a04000791654400800086840c0d8000c000c5031007046d001130114030805020000c0c011054603841c0450303922807014004d43d48001350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419807922 1250 419806672 419806753
    0x10e0f03150f01060801080a08030c090a0f080c0319110a0b03040804090b040c08010605031e01030803090c09040f080304140d09090b0d0b06060904020c12120a0608 72
    0xc10040565141c0700300401e06601d02141c0314200c1031016000f00f000c0103110001000680301c0090001200d59001421607100d6807500c4425926006801200350f00810302d0000180c08003003480070500b51101c045c203841d4a4404882410f50b03035a40000710003075420001085070041020b01d0300301ca803040401400540704660b2151040c0981d00290340c161406000024200f28000c02442a050001400e03601404502544400640301702c0c0c0500c64101844000000200418006140500d20a001032a00e1946584a09129000c6e4000300d40c0c540e41c601c00d05100510600d0045040c41c890303603225620700030342d401c0f650f1455856000a4001c9809040305034034900d40040c1408000b02628150703540040540c500039001040e13a04802049004207011244003022a40c504801c50380170700295071003030741c1e40a0000850001d12524014030304c00e009201d4103034450706141c0c0c001d20a424200d580c0c1102c54070b400c4180d03400c403901c070320454002c0d03441402c003c080115040501e4030501c0350310384043d02e046038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419809172 1250 419807922 419807929
    0x30109080307021513230c0d030201061a0c030403060903020123040b250c0c1d0103060b06031519090c0e0414010f0501140906120402031c050306010e0f 67
    0x7080da502c1d80035030480f103800248000451940e5621850342c458201c0c2240140d1140f100703814070600c40d1020040340c600342000e0502d08200030b800c5400e0241000c0b80c1d900c52814000d00810f02030003100440040440501e0707215003c40c055401240e0300d18003651606256a40e610010460114114195502e92040c0c0e213200c0d90002901c45904030701c4841a05500c5c1910740b03010017080062501141c0d002d0f00030011000300c102d81c1c200d0211241070500d02d11a00349810100280030300c5a0005600035510342c998a10440c1030b00001d8103e074800c00c4d0130700501d240e08041200b01d000032140c001c0808181d400210540c60603030602c0c00f00c0341c009140074401c241c03609041c44c1560103165009010400d9040c0e9011141130910403480e0009513403940d600c41d07504014021100610900c070362810001400032800c0303002000821940c3ea40c000800749070345c905100c94120501c0780b0458083e03119002e072030841101c2040c40e5618070036410890381c03000e10f543d440c030b0300544035810074120043d080420020703050000e45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419810422 1250 419809172 419809177
    0x51005070309180e1e03090d030c02060301060e0a0b04030b0604020d0e06010b032409060120011a0f0108070c0201080903070c080102070b0601020a05070302040911220509120706050603010908 84
    0xf800d4000100c0c3c100100002e4514001c4180c001e01c2141c0c480e0340f2400301014020040c0d41110b6011991900c048030717135041c110340c41c0c0e44200b400303544110004000180ba540001c450b0000301003e503a1039540c5695800c1c1300055016910020b80804000c100054462410364000d190789070440500048032000741101c50324090090300301d52510700b000000e1003541c03103504000c140b12511340f00064400485510200d42c1e800c10140c20503041c406500c1307020044542071442c00a184c600800200034100c401e207407041c0480032440b6854000da03144802000035500c80c4108503c40d0240d500c800e440c50b5000c1d401107914020003041000e241c08280081030018034014030340002485140300240c1c54134624240f000d24610f01034040750540d0301404264001070004035020040fa5012500001c0c0c5032068100342000e800e4030400c144c2d20401d0445103200c415040500705c52240b00308402048180d551003d0b00b96504000b60f50b001c1a06000d010480008186401c556031194000d400070542c240541c1d00c1e1090ba4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419811672 1250 419810422 419810459
    0x11209050c0312091302030403030912030c08010509010b090d050f01090f17070c1413060b03190c0914060d230f041a06190b130906051005070309 64
    0x350007030700c401485864100000c420340c3c1d2a10034010b140000282c0000c0c1454800020700100c10340100c001810306000307a01c40a8003e401044185001d041d4240007030003012a104d410010035131100002c2103030b0414500c1981030311524102c03685482440000c01c8042e0343d00382e8048840d40b09441282603981c10030b00954880c2d500c40c4180ca000b0803094a0405003000003400f071044c507111300340b003950041803100c1d41403001c07180c00248014a10815002017103102d40201c082c00c151500303120300002e00083d8400298418000003020b0b240d0f15118070110000e031805e100c03010300029480d040c2400004c1000c0030410196500502d19464004184405020307030303030102d00403040541e24040c0120007101100d02550721484070704100d6010b00e002c0c1c0d9001441d0f600c0241c411036068805000600c00c0c1c50388000206001100121042e62030340e20024062564800c0d405200c82030031003000001c0286050144006460b4000c01000ba01d00550000b00c5441d004548181c0800c148044001a55010550b803d20300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419812922 1250 419811672 419811683
    0x61805030f011a040212040b040c030501020a0507030323070e03030d06120c06021603140c120f0106060806130c02030d02160201031a13050601030209030114010f0f061d011209 77
    0xb01c1c5400c0810381d43c0442c0010b0890040f4010041d1103481050300701c59661240e40700094144540702d90510340d00824207500010305542c8009004914982c001e0081c0466603c681d600307100d55491420329241c1c41c00c9801c039003420f20000030080742ca054007c0700510381c6d50070301800b100d0030401803000c0c20301130345c403250b112502c0e0a40103401001442400c0705450041e0a060000b003665040c01d00a050300791000b440060f014200003c41d086540b0350278402c03080e507840000d10074008074103180c01e101e884840011003841903602c3c0c91380005070039014400c800e1060b00c0c002e0203108188207075240400602003d1100390214041040300d0384d514401403000d000a54401c6d48480d94281d05480003404450180306000d28243d045e00360581950384088094843c81c3c2d514101140c1ca80b5940d0040e8044c7c010100720319819400d180289100d60701c105000c82c100c400c1e140018181c0b50b42c616824558060074050701001034200314500c01018040511070000001c1031500d182400990342c29102140c03c9200101e66 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419814172 1250 419812922 419812931
    0xb181305030d0e06010b0a080105040b06040509041208010807030b011403070302090c0a0201050a11160201110106060e270f040c050d2f030a11031519050a15061805030f01 75
    0xf0400c40800942e40500b0700310382540d1522030442806004103905204070740c416500c40c03074034810035154242518000c00c0060b02540b647d003414500f07115914840420480010020000025807420004011044039003204021710b00303900340505542940080600d240c0c2510031003200000580300c1c040c1c0140310b80b081c0580309440c2d1001c401c00a0a490010b0400b001ea40d041c55200d00780d010b60075044842d1120018181440b074100303440160360010240707042c400c0319482d00b100080d5507a040303c40074002480c01c4400b402c404070301003c10403583e040340c24810706071a04000000e4460344540400341d0054017600c8900142da41d1a40003170110414410101e5807120b100b800004000c1507114442d5002e030032808951a034859000100c0c4d6102e00e000c0c0d0140030ba0708860003880840d2801d00030418403180e003075049800d903e40300c0d11202c0000a0321500084040c5010002001840070f4401c80c0600a2083c401140007803130440d00300c036168811081504400c0c82c0800000e6542d034100300c80303221840003000200d0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419815422 1250 419814172 419814191
    0x9090a06081207030e0a0e1305010f0606090602070906030308040b09010209061801021009031b030e030a120f0507032309040e2d0601091d0703030305060a090b181305030d 75
    0x10500744085c01322500a113800d2030b041c4010440368400c0c50b8031800402c0015000246401c01d00e0141c0043c041c83c00d01d60349044000700352294013899031000d46219800300d41303203035560305000c0086451a21010300041d00c8003010400203914540d1070b50f04604a00000350500c290030740020742c99480104403000700814900b040c10320b542c062065000031803000804100d0b81d1140e0301c01400d040d0212111550031041c0c0041c110405004024102c41c1e05005800c0f105d10a58900d020403200108549400124020340107950f10b0328403802c100c4601d0340d03055513103540780a100e03001046d80c02204600d45076400002d215860303041e00c840c0309840d40b540c03004000b0b1001500209111000c140990581240202c0d0040c21101800700042e0940c1100c81a4100084003000403903410a400b4003010911124041d40760004141680741c1c21060142c1811030300720621650310100d84084525103107100e508018440302039001c04c2e60356141a41c0c41000c824082d0242d030310310b541d4207007580e000351001d1a000c0d0390f0b5041a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419816672 1250 419815422 419815427
    0x1b010c0e040c020a02040e01090605010b040f0e01080706211a0f040204080a0b060102010b0604080a03140913050c0f04090f0b0111063103080a0c1409090a0608120703 73
    0x600c103403003041c1c40821400c04000c074025140c0403032030740c040c3c003a40e00c5190054914001350311824149800172001c1009586a1028a201e984544503c4403242c10404011a102034400c484c02d048401d02d06c003c100301d85c90154140e07001d41e00081c40418140c41ea00d1410b02e01d50503401340030b111188010341040071000010400c041b0f0b912040714036009920510090024910024150003025000821241d0300e46c2c61200413805005601c015030341140c03005c100000c031282c00080c6108038501c00d0300c800810311107820180c10507000c1c6604003640f0422170514640101c0d01ca510203900b064143c0140d40c54034010600890351a8030907130041c3c9550796a200204d071803003024414a00c005800b4a40507000c5a40c080f041541d505e0f002e860044207602003100311001803861681c2036002c034000e1a004280403000e05015011000803950b40150780d0034804415545880750b440540701c820966105410100c421081c00b0904500401c0c2c2c075101642c8102c0429036120801071550409808001ca03540c503a92480e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419817922 1250 419816672 419816687
    0x80105090d1d01050d0f09030c0b01050103050402090c03071709030c0f060f0103021c06090809031b01050301180f02040e010f0608060306010b0304030519020d020d02031216051b010c 80
    0x24200b0040101c2d00790740c030b03203008201e1141c40800902e070194861810004000003841e856250500c03045c80c1981420030140c0080c2c445010b1402075611601030703079031400103606507031003124005e60051520002030164602c0b28041c5030000403170720f07202848000d0f0260358003000744256011039a9500214040a444100304040c90380ca002c0c40300501002d080400108a6851040c00002d109840204485004866041c440d5140d070b60070450500524010f0300b013502c50b0303a00411081d4007070b00400045c48080041813482c1c85508606a6629145078030782000d0f0000709181940d000000380d119202401034403c20300250001e0041c4080e40507055241146c002106402c0d54050030601010408118403560013040702c44c111404102c859a07241d0340e61800702c41500c55641403078003404041500b903890982c000303503007171100311140c0031141c1010032014180e0b035900845810034100b441c00360002e1507400700044440b80900303071810001e0a010120040641d60840701400c500140c0d5100640800150320050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419819172 1250 419817922 419817943
    0x19080c070f0b0d0b060c25050d0b0403030e0c0d0b07020c0a0312030c0c061a1201020c030702040c050c060708091207021e0f06070b19020c061f0308030108010509 71
    0x4030808a20b072046a0300140112441000241e650340320301d080f191240c904450224034183d05542580a0614840760f1180606900d001580e0320350300042203038108001c18849a43e00140c409206030b44d2036400702c02422410111003054003d00311100040d13191811300800b001e20808480720f052074541002403500184440d00c5204001ca41800c00114949a00c03103500c44100b484c0c0403c258080f0303001078490702081c440040c84646010300e582d4920140388840e1084402c00c89c0c115803401030418000d401e03401640070001c1d10303805c1001000f00500d0154003249010364541031441c100b00b607800515003850011100c83c0041007a40040108000040c0329a00700d030205103201d10304020294020440340c0362082c441040541002442d06555641e00060500480c00200500e5503400d243c46d040306200c4003581c43c00039150f03201d0441c8e281031000307000340c42d000341122001700425903580d4141a00c0c1c1840045e10000c00c803032400d010010400311001076010384200c100201c0c050600380801072401c000c290 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 419820422 1250 419819172 419819189
    0x628092109060f0c030e120102072f190b0307110f061e0709051c0b010e090c131104150e01020105010e0c0c070b0c010c12052719080c07 60
    0x1001402001d8020f2140301858949240c10045a4294501030b5176000501d01c0305a03102d55640040d86503440150010800c0c24130824040d61441a058070743e041c2091500081f08040d488410700d05407134100a02118101101292007418081c1d884245011503401038881c1000980d11030025501c8a0081248000451101004041900d041598101b0026020400c0a900d1501d0320129032032520903030040002d007500030648101407194085800244542c0607044400001940001034008082c140c0781d4803c401c04e1020f0f00309c600d17030441006845102d0030525006141e42d00280c103c403183c0c0304003130000380402d0300080003501d0701c541c00584020f800c00d0030181103a05140040c0030551012400c550040d02d00320382c49484141c0c1c2021b290410b0030703c2c0c1255507c10400306d802210400150809100141e940d2140910780c01148024415110300303e0354015080311554280d80784001d42c000c4803d034070790f050341a240400400049904030507000042501c0307852006c0707440f0745400400e0018000510400303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 419821672 1250 419820422 419820437
    0x1121e1b0b0a050f09011808010c12090f1b0324060e090c01030e0309040e0d03060605070525150816090e0c09010504150c03030605011106280921 64
    0x150b4002d183e4412940258000400494543d65031b9005183d5506c2c9010300c001480a07054035045028020715240742d881d070005102412000c04480340348034502c8519000b4841000c074444030388034100c00c49046078402045c07505109000020983c5e15030005050410301e0a000242c8141c000b440c002d07201c035a0800c0525506980910400384000111002e0024080c00c0c0803440c407500210460540c018103003541c0d0440d0800460b1a41200081744515442500d40c070200120390316641c04581c240a00000104a40d109480300032207107407803c003150034100110b604142c610385c481c0030308200e66030f02c40050004105100300307001c0048240480d81600ea00d451a00c04500752802024841c0c005c4003510213101407500041c0b203041c81c0d108104803401f07072941c4040d000000e05030400041007840125015000603141190114083d88180c00201021003031f8401003400d40c65500f0075040c41c0b118400c0442011081c1d410281184d107043c090030b541e0500540c50000c004048002d010000640d0a49031001c00070760 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 419822922 1250 419821672 419821687
    0x2d03050c09010b27040e0a0f0507080601050622051c020103050f060f0607020316261609020a0c02030d030603031806080c0c0c0405010f180c02030301121e1b0b 70
    0x80c02808400701018003002d491104e800808200104801c00440703072079020f040351207024001203101e40b030606840741c4101c800f01c940c1d41d00c520b03864400a004684d03100304108224000c510581c0040a441c242e6902d1100e06940d0322000680100c40c2c00072040d5412a254011409543e050311030305a100c1e40d030f09441c404a29021001607288245e225516102d80e0010030540e0564074108482c05a4107440c060b105403441d00d8455603c03000782e03000c100704028402900709400d00c03080812170381a014000d41c130800c001810a00d143c8040d402c0860403a040202100c402805603400f003001c440006025100054202d0850030002c00c01010002100603003640314504004669210342d0386903000044464032500d810701d01c00d05d0360600f035170b0604013980075080000105411540d5035450040340c44009403072001e11f81c11601002500c80104403000960800d01c0108106035107d000640301c01d10030009140d038420104c2d40049000304083e01501c40c2121100000307000c00d20814454090505000341c0e03070030200e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 419824172 1250 419822922 419822947
    0xd0308150a0b090112060506042601140f06030f06010902030a0b0a12030c080f0307080a0f0e0c0f030a170c071d01030609061103160909152d03050c09010b 68
    0xf852080c0c0c0d0400c50555502c0c28203034080c0c0d2251025110007840942e440b030380e400c030312013800610141052140700c0b5441610f04180d0140324060355003040034580d44140e0341c0c0d000b540c040848002c1c51644c00d4041c00103132a40c0d031074050062a0103481c1e01c001c01030302ca04101491601700c0341e4141a0600586078140b0a200680c0b00350b000803039295244c0350243e0780090300c3c078004d081401b4400f03c0420501c40401407207031960300203000c40d00c10301c0286420407900d4154590f06c0155203403290308a038140c1204115040b1400c1c00e0b0300710019680060101ca0090030710b55940c004a8601c8800c1500390100412400341c020f00034020358000340b420740248207100c0421103542c40d1760300040c80010030b1903070307501d284504010351500850340130050481d41589038502000c0f00110a04140f03030000008a03006400309100d080c6210b0907082c2c00000740d83d880c4560070610503480d0207030040d00000010821a03c601c3d0708284002120f0003941c0b10344060021034450780c05010300448180c0140c40250004d000c040e54910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 419825422 1250 419824172 419824177
    0xc0a0606170f1203060f150403051b06030601110f0f06011706072106050d030305041104050912071a2d0c0f180a06171305060402130b0d0308150a0b 65
    0x880c0120f0300e9998450304001030300e440b034828119401115154180200300942000b03001184e0240c025038102034401301c0c0c10071050001411150f4029000c0c00400c0407548120840a0100c2c044421108120f1516408503c4c5c540d600f000c034001c607030101005000a5441a03410110044218010409810b20768006071045c40850b203140d994414150301105450004d40200c0d0090030003801c0c003165450207050007005080212016508103c4820000d24142410310500d88285031900c05414521030000041903560b2003240700352541c140c0740c03246043d490055104503028907024017450100a0007200700038500b00081d412507141c4656030301041f940c15410400c540e843c01c00a05034580e02d02000108404402d0020802600301c00000408596107400200d40a04855440c0060089903200001007800700310b4031600408540180c400705c1d00504100341d81521402070350b030307007c58030414030000318801c2018100258002080c00e0103000541100c80707428044c0e12025500a41c1032820320340329150307a2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 419826672 1250 419825422 419825443
    0xd0f0b030d0f02150a05010501080610021903050c15090607050903070b0702131d0106080705130504170f1b010903200106090e030919060905040c050c0a0606170f 71
    0x180c4102d600300ca4030034000c0100c21140084040100e041002c58000184424081d0750b01040460010072030038900000350401d5800d80b640101001070310408420b20001207228102e06029041c003030071103811405d000141e9080e810910501d1140741c0708031a070b480c20310090421000d00804202c000303030549000c5030f0041070340ca1030300b0101d584000b1480400e484c2d0640031000c8408074034254070380c0e00302c0d00400d800c0412500c04000a02c000c0740c0301c01180f03881d00414400e55901614010100d11171100940085074458000c001800040200b07094103009544071022000c0340b6100011034500da003c0400c032120140150500070404420030380c3c1e000d0040014080f0400e1074007190820951034160942041d03000d01002c43c0188000d18031041241d94a41000f05c0c070038400d607080050300c003d0483d0040c00800303c52159669003549868030f01480700a00c01040003004000042150240c415010845100868491a80082c42c14501243c01440307501d41b44c03808655410600e0740c1c100c111302c00500780030030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 419827922 1250 419826672 419826677
    0x9111912020915030f010c090803180409031701030807031d061209010b0d080d0606050a1b030c060c1e090b090f030a050d090f0803130e040203160b0d0f0b030d 70
    0x10703151440c181941d45107010f0550b6252261400d04103c413101034020505205194480d1030703285407111170031501c0b4080c0b0303007009407a0f8400072491230b607038074080c1c100301d9145001c1e041541c0d00c500092410003205170241c00c1030b20039040c00030780d8008040e44000b188807107100da050810442c9203800d002448505c10002d140c00c0c04042040031800300c0c50298094100c5140c01030031889441514a020f482c1c0d50080c0001c07040701c920f028400141c06000e5822038140c2009030b074803400b09035505111085011440d000640030881524141400101d4031300c00d82280c680d02c0e8403208650007503010b01403410480e040400d020041d09280401074442100c0950341140300454003d602c908010740840e2504040d030001421902c84d164084402039045240b200c2a56032003404050100d44416a85940c0d102d022900341c40422205001c002c4498002c0602c0d807c24801400d03100600c0109016412110b0240c00180408038001000120742d44144600c51708040c81040911a910240001988440d031380b0010a05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 419829172 1250 419827922 419827939
    0x410103030c110415030303050603010204060c030c0f1a0103060b0a030203101e0f05160f050f0708190905040609060b040b0307020f0607080115081b090d05010911191202 74
    0x100004455610701030b8101400412840d8207014407900032a01c3c5110640201c1e15100c0401c05078101030003280c041e10026184d5a507907003500d03a030032035581643c040142e684e401c0204184001400701d2802c07480030b0792400d070030141550460504c14103d0308c07620301851151303070008010001030f04c011565040c0e0b401a2000065a0b62840300751400030100030320740054041c030f4420501b521098a5008034021480180b14200c0c0742009402030300c03402c01e150900000b0a0301400749107010540c6200a0046600c220700150510700038202d0b02500d12011004203010648654081c0031605240c46100c0051107100e501780702c0c3c0c03032034204550580c1c8540d00916005180000c0043c00850007001102e5802a001c402c83e62589461180205050003c1c05119180030340c20303030120981c5200d40b10541c01000f56608641c1d40000e008100b9800e0741c0f104c640c1c9900305001503152030100d007081c4100d014050051720480201c1c1000e800b085240c90344000c2081503044005001d2001012044a00f4800c81d03040c0c40454 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 419830422 1250 419829172 419829197
    0xd110610180617150f071b0609141c030b011e09030b280b060a080601110706021e030301062a0b01030807020306010b0313031407020441010303 63
    0x2806050b8039004070700d090502008940f2840c400080a5403801c0413002c420b6455100d00710601c0002a0941d00080050030b00300d2080b081c111501401d5880d10b105150001c0d400ba40c1d030b95000761902c584490b25100d81c10034241c481140200001c0e10240f0383e49440c0410181c0c01060002e0482d0040418080311000148031111850340a80071803005580c014200b180380d4901204a9805045c01c94010641c41d0b0700c1014013042554240904000400010502800c200034842e04444c0050020041c50400980c60071524258105104403005048160301801103000b440203085240b44580c003031441d00358010001004107541c400780c010040b4200c91480d0148010361141c080c0e1541d80504050012211600000200001c51b070041460520a806440d0141c0e079988400c0041e000403640301da0700d04480f810105c002403148000c240d49000044d9642d050000700e4000c81c003142c80d00c520400c0100352240481070b40900701c4003400034075070940c3c860001c1c01c1c4050030944d21000040c40001d041c01809041907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 419831672 1250 419830422 419830469
    0xf02120c0d08130b0906071d010504140a09020a02010c090f050102060106050c01020f0a0f08070c03080604090507031406010e01080304030201021c1115071d09040311030c060403020d110610 83
    0x42100d804c95907001c0c450911604e02e07516048161210340215496044078100707006c00d401602d0328410305854407400c061510281c1e44c540341c1ca9081150380200f4802c0081607500851011b003001c40c00700c0d8000222280f1800c03000d0900e00c803c2d0002a08415207620400071a03030300065160540f441803818980310b1040ca141640640207140c80010b1280000c2000d610f01c40d0300920a9503e1207141c2c0c0d070f464040c0c07619502a590395440c000050002160400021a14107240c2c01001d01207109004840303109540341ca41c87c0c3c00851032840b00c032858000400405c00c0c01441048103000d841d414020318901480c5500207035652020495021010400b00c440c1e840c0d10707000b1200e6050ba624100e054402c080c1200300080d50915003101c681020a509800c080442020405400c0e20fa040c0501914001c3e1116241076464103444000c03600e840c0300070030510042c1541032014600980c880e03002094552120714000c1c10344588a00c14840541c4160200034412f5506042001242c051150202900c05c11001d06d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 419832922 1250 419831672 419831701
    0x403080304120c0c120309211218090b0f01170f1312031e11120a0908210f040f060b0f04020a080906060103060305070e06040603060c0f02120c0d08 65
    0x103803451010180001c4c40011905120021134844da55540d041500c5007400202c0d20680c006040f5101e020504203000127010a109250300707101420803246060100030410005103250300460b80107034890380e084035141400401c51081d00002d082c680400c966541d101d030715000000302500d1000c410b040105141024070038040d400b01e60000340420108603940d0014004d1b0039520056164054012400c2c05900001d11078001e400c0d070141ca01c2440c02600005da003040b0407001d40381000a55450010000282050005085000040c46841034440c034617140414949001400000c0d07840d0710404000018908503c00d4440c20781c0040b000480c0880745000c0341078004610f1b13803550000d10000d04014059000950181710f0000708044070070a989035070046094803e144001070440c2c0c4444001d120301030010030b000d40d10a4004c0c1002580c159a43c442e031058542030411301d00410034a81c0d4144543d07a05000310b115038841c0b1003100d80780002c9201801d0740c4e0810403031510100101c0c00080340310310403500340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 419834172 1250 419832922 419832947
    0xc010608060c0d111c0902032e050a06081906450506130506160807050a02030d06030b0108190203030f0702060c0a0c08070608090709090f021306140303040308030412 73
    0x40a0300c000380c0301c00e800401004241c805038030a200302d0000301c120ba1092655110441c03001208492745420b900c140c0d02c06000e01508801303080b0386030301022411940400851007013240303500c40c4080204643c18214120380004101e050010b4500b90380100c02c5030701c4240c949003250340c02056100d07240002c10a02e800c0c0054440105540034403414880700c010005020343c1d0b054042e40030b80d101e6450360021007100c441c5140c007030300c00700d0400c02c0080c2019020b02c000e0502d510460050700d2514215014079000c458040d00103c45a49080700180001102044112802105a4030200590b501038000940d2400356400103408441c000880200319120b81056440c0c0c0d848540449091042c00c0c50040304011140c0500c0d107851185000c0000c565104900c6107000c2d15540c005031140f282071015960180c1b4401c401560400e0014088000503143c044254240b180c840000082007404c008c50500c1e1540c0920000b48260300a00091000c90307110b00031690020750000748000ca52050507801d4500718101c50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 419835422 1250 419834172 419834197
    0x1009141e04051503191106091809061006030218040b0609060f03160507030f0f1716020706020a020312031302120105063a060f020409020c010608060c0d11 68
    0x1400b03400c5030081010f02c08040c0850a85000b403000000d980075031074031044042c0170300ea50b02d01e80c0368076410a24001c022403c0040c04056003d0b04030310322211010804d0310720101603845841040240c0d0034981d21907021b000c0707910302907180c0f0503180d5100340d00b040381c0c0151601c0b95940320412250795480604664154002520460320751007070805266107604100d459032650340c40404010038051142c03044841d00e5500d07446821100b1640302c01210090129540c0350300b448150681d2000800340780b004d0031720a500c550b20001511032071200084c14000680d0240c0e046d903005403030b89401a5000315420000402c002d0030303d510307952840c0c90b0400344034040d8001b0b034000610000a121050064001034490ba4060700c8565000e00f5015512682a21103182c120070800c0c44004104800c1c0c0d01180040024080d04c400f05070300080300c110000302d9000343e200d8511182d0018861942c00000e02443e0000c000c0600645014a05540b08201500c2a20035a480c400d50b20107000c186480c01d002912002042074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 419836672 1250 419835422 419835431
    0x2030d2f030c060a050105010c06050402010339140a08060607020d03080a0b06030c04050105030a110a02010b0f060703050f0a0c0b0103031d0a23040603020d0c03021009141e04 77
    0x104000d5225800181c07401e20500907030380003580c006003900881c0d04890040e50345c0790340c0402c161903000003020090004c0703041507155406408241500c2402c0c4501c0c4019801085c10110001c5000185810950000d024080031b00c029820a00e840e00a6401e000d28030304207a23090f0394415000400d14441d8043c000d502812501440d014075511000d082e1048604130020852000070305d0402c07941380000c80780508009410807080c06a07501c103070301541c0c0140140d24045107562a18070500410740202e25500c0050b0740d26030400d443c501e84942e252400c158141c645074503080031b03514000e01c240705500503c160800c000480a0a071489807201c4103c990704503070000c0d85542c6030b10380204141c1003201d0813189041800304035115440c0020b07070b1000b01d41d412034112a490000c0c0c41e01c40101840c0200066009072358410000c056281c10b880c80d5429072040800b80c10345420344c41000005070804041d54200051030038184a818504004105046c404540c946001c0b0308111501038822007088000d5001801c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 419837922 1250 419836672 419836757
    0x130c0b030a090b101809050c0904050102090f01050f09010c0309080f0319021501031106220614070308011a0d020a030606030e030711131803020d0306050d02030d 71
    0x15948203440c990f106241d500c3c0302e0340b50700c042800705828500920f01203800c02c2c0320482c00c11010754404044103100b00c040c1c81000b900b010000704902d008035003d55142e50001000e030316038500308080451030030003401d01074103010070a60b20481e940944400766041c081c414881d50141400742d9a4907000341075200c1118803503209180e10949a40045560000c0c03003000084c0b081b816800032030721072091200612042c050360f181d07441f40f600e00340e000401030fa000402081084020301c5030b054240502180c0300d103003190880c0f030b080c0c1c02440c1a98148000710001414856440040c1d4000301960443e003202c10840003030a1003480c003180b20300c901e58048186501c0040c08856460b0503421070030484e00551010050815280c41050316446509001004610068131740526442e080305001e03e003001c4800009042d540840c884195200c00540643c0540c0c400c111701d440e516030501401001d40016290314003455240e5020a0762005912a00c0c018000303400074598940d04070381104980e80500b145542210500e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 419839172 1250 419837922 419837941
    0x201030e030a0c020301051506030430080105090109140117122a01060f12110301020a0225030309051e0a060504230607020d0c0801110301051905010206130c0b03 71
    0x90450124061b5090500041034044480c561200340301c2d01502403480c42d9103a070b1b50f4a040304250107400c1c8407240304080c801a1191100c020308510400fa40703401c00c0c103505100400450f82030590051060905200094200302d02c0c65141d141141c001c59030030303800c40d85580240ca080c56892210e4000600010409040c0b8540e4a4a04882c3d2041281259a1544c80c0740d030207030984229014080d030346400308104111a101880c0c00d140ea540c0205e12002c1d1444940d00000d007039a01c5944100d0060f444450341c4415031f44101309e02001801c00c820440c1c54285590b9000d08107140d680305142c07040b40c05100c0080d0204000c5007002c092071008101a0013240c642c1405030258025000742d801082c84000072020544c914040e080441c0c0c0c2c000c0246090640300d9003040b040d501c44005c1110400001c2c0e43c001814036003400b031008644a5107220580340c3d810700e000d00c00d00b02e1480d0410b903c00281c0c0761080100d80d03004115150008801003041c80e88516a04201d2001c0b481c65100c44c41c801000410072802d43c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 419840422 1250 419839172 419839187
    0x70e0a02030703180506070e01170405010605030f0318060f0705070620010204030512071401060f0306112a01061a0307180b2209090c0315060f030f0201030e030a 71
    0x1c00b90384081000031805400e1605000d580d040041483d801000070803a2140150001c0500070300c14905410300502c030685c0c04150036400d840842c0c02c0e80d16400b06100394902409a40b02201d50440150f080c001f400701e004074100b60044120b400340000185420380b201d9042c04036020950070108450280d591104000c14072086000d0000be074140e41c040c1d00300106810f0080710f041342d800c80010030011a014040e00070a1f44405421280b03280008a10300f40040e081c0644001880304072a441c400c245141441c00c285c850f00a00c6c201e29071000c200d280c6070b012030072001004040700c1c100f1007581d16003c040b085004180e203401c00040001944000102c45505a000354801c029a0b80c6045480f0b0029090075071950313050050450304c65041c08207030703540600e41d50f13000c0c100500c0489007020a95141501c40c2190344404041d2007500350b0b4002070007400031070100c0320301848008504101007860141c14106c00041808000d0103802c501c0903100a5a00c6a0480d44840e540813040d203540d08420703a8003070441d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 419841672 1250 419840422 419840431
    0x305070c02120a0b0109181211370302030a03050603030405040f0915050108030301090507020a0c1203030c0503010b0d020d0605090f0a0608150402100311030a020408060f04050a0b0405070e0a0203 86
    0x38002c4500206d030502036402035106034481a40241c60070f00c40340d603030705603400e640d030141104115001c3d000c0480e1a40030454880ea100700e29000f0307080b540f00f142c5805840300c01548a06401c0f0b101102c14000030368000110744d0052030920300020182c68141c0024214800c9030301896101d070a00d2114030691403180e008954451042d50041c80300c040810001c402d0f203009200344503094205000403c9084819000b0303983c041568030540b020000300350b54128401c2025003182e25100f920305052402c0680503c04c2d04003090513030902c0f0f42550700d01554011144070751000c0d030018640114001c0f9900669400450240034001e0a022403843e100d10714104201c400c407080604a4242840000c0140012070301d403040d50503010304041d0075a40e07602480010010b03a9594020107985042c0d1420034110040030b18080c0000c650301584d61443c00791018900a8054400e1301510f41000a0000160380011500500381c0d01c115105426511800e0460a207a0154000c1c0d0a0508c2c40c0c041114030b00e03241d4000d40c0725 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 419842922 1250 419841672 419841683
    0xc01170612070308130608090a030206012106020703080901050a090b1b1201060e0307301e21031401030b1e1f0b070201200321090c01050c06070305070c02120a 70
    0x40e235143e001c0310795200c4003640003030007582100c00140403d541444206284100f148506209500d1036076920080768040c1d00c0c00d4001032240000d00c403030241d00b8003aa42d04400c1c1c1c00002d1156410725141c1e128680030103004452500d14200c01d072003594411206451625504844d400203560f074401016004000641000d0720901a00c040032030740304030710041c0e6055130700c200c041c1001c96040d166034071416914021007a01c0c86862640c44910800f22030f44840b141c5031064208002d41415600c1111545807006e4040051508000011500f200d0880059044982004410080c0d49907094000c4410880c0f00b0000700c05c1d1505800c00007040380360000c3d030310002c0b00b11488501440e500e00148020b8051010000d000403102c9884e0b6650025207445240d2854615081d01d24049049800c8041c04186c4400c0710b0401e440002000a040f106011501042800f82040340c584041c61640e1900c0707801c0201101d06040e6103001090f0390038440c011400329694054941d0342c200303c40d201c1e003c0c2d440820160403200e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419844172 1250 419842922 419842937
    0xe0d021305010e061002100c0311070302010c110723010302070b131704260f0304060c0203010e01050912070f1a161e2105010f03050c011706120703081306 68
    0x341381c10159000344072182194081c082d140d0315565510083d03d40c2c401c28200b05521031031548203603c045c4000781313012442500002400b510783d102c040c0005052401007401a041180208510902d50103404144406180503040c10090303000141d0080c0907144028124409000070091a100c040c600500864040e000903070030010010100a0103100302d000d0841c8689181c05460240240f0f03900180720000c220041c2c40d050340b0742c0d040e42451a0016448200010104807082041d420700f88600207445231443d001340a18548260425a210205001142d200310000751181c148039141903289401d56000c45a0400c1d81080908000684010340b40c41d59142602214009414010034010160400c0c0c1103040c00d45002140065400064a0201c5000010406009440c41b4140d00c10035018043c050302d030110321425400e00c60318001540c2d10303060500030240881030520300f00c0302041d07500400450350160aa1b009034402f604040c540d5000038108040412080040040e84105400b56000340d5034420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 419845422 1250 419844172 419844181
    0x507110a03030c0b0a060801020c070906080a0206041a0904060608150109051f0512101811030604020d09140c0f0f0603070e0316090606170907060e0d021305010e 71
    0x103080d503854070000740441c45181150000410f41c441c5180c1c007115806002607841d5660940d5826a4410070907802d06410114042c4000c04282c840c0901420001006000c001c420f5400305105106a00807807001040310485c04202001e001c040f1041c448010f00180000303a070318080039100e2030007510540004541c1d01e40c1c022176540b00e03041c201c040b203070010081d00c100000c000c0e10440b0b82905e408034130100601041114012070140410601500c0c50320342414495151581d0009040000840c246020303080c040503a01400c4030b101500d41111084500594502c2c0b0324881c0340041200c41402030401c0003400000c2d1318914040f48d0706000e104240d0b040c4500e0701250ac1000f048084825035558412801c0c4045101b951190206001ca0400941100d0f4031000451120202d003e069104034880c075280c9401b400f01e558800c4503c1c6c20442034a42d25038503400c0100c1c0480d01d400740340c01200100300d000168424160303120302d40400e0494010300181c4000d600c03441c17080301600303090107600d850901d460b0118 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 419846672 1250 419845422 419845429
    0x40509010b07030207060302030c0c1509060906190c03020d0c11010b0d05100b0103090203070b0309120702060702190504110909090307031b020a030c08011d011b050313050d050711 79
    0x12900281c3c0365000d0b00d41039003001401c0d002904050a880c070820350a00064100c0442040000e002a0b028648006146001e25100746003090061141d00300d40c00807401c1c031414540345524520390b5695640089a41c2d103402c0c8080f0000d02a01d4204070b0110b0420205280d801d401004d00c0032130b07405e80f500a20025119005001c08101218001410340d484092400a141c603107900c0208012070501d00401c2c03007403494000a1074801650000f01320400c0002c01e000410f01c3c00c03c400040149490342d500d091480a030002a018091100040e015044018900c5140c20b42803005401030301c1c1c001e1080088943e40402ca4102d900171040890003040c156001ca403941c5000019255182d82c1075485924040c000e0203840b0f81c400301d0700f00c22030300310000080c04800118050300c1680039110130800000c60206030003a10328141640701c90140341e40d00d4a24009000801c00101c0c44441a0b80e040c0607540703441d030692000341c80c10b130103202400e00e00130171500003040d0f1303808001001d8032405042648a00280f00c03040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 419847922 1250 419846672 419846677
    0x412140105101a0f071a070806010507060903090512030a020111030105150a02010b030a03030e011a240d15030b0703020c03030103060b0d1a011521050603071802040509010b 76
    0x102c150384211180d04015a40758a02c41d1010f071001e11050704d05050001201841d0354100300300c00c807041030215a800803402e441c140360a030b000394a89800d072460305103240060424460204003030981c5403600c244031306142c0141d00c008014000642500000742083c0206078482e04081000c60040d420050140750600481050344d050b41c000801080f5681c2c10001c0e000c0f0715610a12102d001e6548890141c071032560244007020305c081c0207480c04100c0c038401c0e03007801c0d007102d894036020801070030110844040d40e00d91081700301c0018641139180c0f0040c1d60034083c5580d0b5010304214a14190304251038074a0203445460a1401c80b4450307000ea590a481d064010b80030390003000300018042e41b043c0300400c0410030b40c0c1c1090040304405000841219259110100c4440f040500720107103c078580010402c400c9616210701e0445150f02e1710858103048100049551518883c44006041d1680c000c54519030342800203034010b08210031070601e12801d100210300650024820903201d403003d03078000165114600d04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 419849172 1250 419847922 419847931
    0x60c06072001023a090803010f1205060601052203080a03060509190f06031a0f01060e06070b04050c1f0206010b040b0723030f04080105090c18070309080412140105 72
    0x1014040200051075100591312188421a00c240b6005a10501c0c80010721419001d140070300d8160b5580d42c144081c0c0040903038150f0080142c9601d00341940081280821815000202403802554035800c500c504000110301d0441e54590204480c00041080580802420a060315413401e21640d0758070810401042d10803144c1e40040040c0e0b8103c005409029840b444080750810300004400d03031a038680b5444060202c0901498484260034031502100c071030503030780c01041c1c1b80c6003a180203800d84000c580c1c64045d050009003d8203c4d003000c101006000d00a03405030450240c0300c43c0301d08080c09519203408600b2020000503000703c10021441c0a0070780700f10760556035011b410529195940d901d400e04111000090f683d04400f13010044001c43c018802403a08801ea9141251101d0410b0b403600e0850b0b02c047d251810b03960001a4100240c1c54004122003071040402910026a40300f500540c040d085620b001031040c10009400305101180a40380701c9281c0c05a404e43c4a45030000c481c040c00c07200140c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 419850422 1250 419849172 419849197
    0x13060e0406200412320708030a0509061b0f06100807060c0312090219050f040207050c010c050f0616120c0806130b06191e0c02040b060c0607200102 65
    0x881804441004c00448034141c0c401c4440b001c03000000820a034146441c02d8032504041644045a41c052904000c440040c141c2c80001e540350114036500544244a85070080380605404070780a88881d03c0d06400c1544464040162000012002005c3d42c40b01b01c101c4950020210354900821014800640c881c103035021030321341030f6400308135440580c0c4020880030031641c400d03120070403440140c070b8901d1045162014080303208000c6040c03000f01310b4107039111010b19010b24418070041d000300748001900c00030941e0a00f0030b080d0640950403e14100001007600300c1c034a01c290424048140101040c000c40064544c1e2400c04210380c6002c507006848a41d0101e400040b0036201081c01c40c90403a10382d20345210740c408000785401010b0045082070300424a8420003e100006046585420005030203130300b00c0ca805c41030710f0704c100090701500d900495031020380513981d0b802845451b510364000b100c2c24921a40211584c2c0d282c144401810296140f849001c1e041d50b440521a02c1f08050098580d030880c0035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 419851672 1250 419850422 419850427
    0xf0507030509031f15080609030a05090109031e030e040911090601090e09030915040807090c050c010e01060602010e010603170915040603020307090f080a1113060e040620 75
    0x1514210746a82250090700e50500654189201c03100c01602c14100c40c880c02180804c200741441c003028001c0c0e410b940f0071031150b005401004040c910201c11540d100d002c904040303454100f03150040381d06e0101a00024400140c034074415240d43c00055080b07006900c69500c040b0300700c810105000a4525103200203101101c1412030006034a407100d4641d41c4506c0602d00400610b903100f031203100245060710741d507245800000d42c2c140e1604140c200d0035010460a0000e601c2d041c54410342c199500080d10490181507995804400c0709481001120146000c4000034400603d00400180c020845071199101540c41c180078081704040c18020744080780d41001101503c3c1d0f0745801c0f220317102d0b80300c003020a0340000308250004607043e0141c050400303010213542c016141e20303000c50040c3c14281c407a00499401d140003c0100920000010001c06444c0d000c03605882d103684220114111703242246a6824a0381004808140d41c1c2d0040035032440303203004a10a000c01c0c480742200c1d01032002c100c02c80741e41f00c1070708 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 419852922 1250 419851672 419851687
    0x602090a0605120f250915050f0a050309010209041407021e0c130b190f050307030b0106120b0a0612060e04030c0320191b0509011e0305060a02190f05 66
    0x64140190711001e02c1c817400da004d0866101007181d00810b086800c000c24010002400000040c0c100b003284c052580c10702920f010600c103402070b00da00035a0b0100003000fa0010024803004000c2d019603280101c003070010f1001241590756180042001c5a940c001132081c06259184903c89100300480140004040c1a0418200d0140000d041300c203e1480c90183e02e03094003d850751240580380d05059442e803181c00c0c1040c01e006081d042e200607070340101e00c40d070301c01c0c881480401c06d40b048490460380340c2e080118030180c444500318040d102c4280c60039402030a84000054603a005944842c074130861001c03c000e490f84800200202503025580078001400034000000040d0042e04410b0f6460211880c0032006030483d07144528145144040b45070300c01c03100140c01c041040c000e0000002c2e0340d50a80c1352113a1414400411102c3c00b0501c02c9004201104c4400191499801c0c04d640186410131305488880ca070010000d4041d6105070036846d8504c82e8171a45c2c0e82c501e0b01c52849a0703542ca0a50f55110f10f00b207113 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 419854172 1250 419852922 419852941
    0x60c0b1311010e06041e030b0703090302063603030610021203010905104e15061806031a010303020601050d06060b0d0b03010e0c0616031b0602090a060512 68
    0x8502e00c416400004c01c020100f0b1030030340101643d1030340f6140001c4210032801c625001d5600c00300a0070201c2858100698000002d4001c14455400b50306030200c9800481c900400c0417507070302c616946c0c1021103000b035500150803502000443c40f4000588404001558400080381d40d280e0f444c00c03910000806100500042d0510b42055403c80c1c2d0307138a40b0161040c1c44400100c0a1884a084001f00d54440f081707107104410000b0302501410000b980403c80804524902522001d210000030140c501500f002c0b2050382c0c850b0300041c0a000c68400c0c8012030704ca0701d0308a00040656000564018084900031000000d9220100b03051b690305078082d0600d03900c3c1000b0311030702d0803210404440090302ca841c089400c00c0844094600205203d80c04165603042c030080c182184c1c03501c041ca80098010b160308407a282c80e0700046134600300c1c11308441c4208642d07900b0100c034441c1710132640c4d61038449040583e1061018603000307010441001c9882200540da40c48051300d0b10f03c121003168800900000000e1207407807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 419855422 1250 419854172 419854187
    0x303010b0315060c0a030f0908100507110703050a020909030a09150201021603050909010e061e0415150810052d030106120c21080c0f0304060c0b131101 67
    0x14220010520b110038018000349068005100d558a10340c000500807052613884043c041c0405502e04285810f83d080c48105511200f5080b491200280c860010a111604c26030101c040d15002e00181c0380303066141d103072103a01c0d00e11001d4164071030f81198011130b008081c08011260789040ea0b448481c2241d16014818540d0f6600e9001c103070035035600380a00c07103801d54030b03120720070b1004d2095641d15910240901005400413040e000102200c0034901000140d44802422100c581031400448808114190018002c5c0060030907408e101e454145000503044a00c1140c21044012925444010342d211003d0450300b0300c26200d0554420b920616550040d2809520720106042c6804c0f0089442032500c0400d080d40d0850740211141209500c2c0078040c0900f000780d038005042c032403005100c50b211540c0c00c0c20303420902410160101500040c00d0440c44400c1001a903d107140710103484d01c1d55600d44025010501a440036118110740c2c80004071400760700194001015805000081510020401101c040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 419856672 1250 419855422 419855431
    0x103020d0309150f08130b0a020f0702150712031a1c12021c05030606070201050c03070b04111003050402010207090e1002040f080f12030103291915080303010b03 71
    0x1038000000c40c500803443d580702c1e5000f001c0d03110f101c0d503d13002c100010554140201000696500441400c0000700183c240c190002000c00c4007586510001080c02200d1081010013544020409501c05007004001c0107171000d03600803418104c000c414100244c081c5d0703200c130803200c1d1021004111642c1034600000640041d20203145424844040c659030b41099650166036080035134016a4030200304c00700302007804400b540c90301d0600e096040210125070305005035080241484404560b000d010042001550256030f0011400c40b09030030542080341406d10142000340c040c1c000701143c0b22000b80a0b0160034003d550690081c468035140c200c00071b00500c0c0f01c215140769400351095003994040c2ca4005080a085640380150032b5920703024075103107418141200b030709040c0c000c40c0e01c02c042c05600b2800d81e0304603900302d0b10b540d22125038410b0181a05c0403c02414108060001c00c1c04a030000c108070b040400813000100b0000d140181d250004c04042d14032405002d0344c0f0810045c458a00028017440c0c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 419857922 1250 419856672 419856677
    0x7050f04030506074107080d0b030706030c0203270d0f06110319090c150206250206011a16110306060a050609011d060301120c0b0405100c030c150f1d03030103020d03 73
    0x2000040d84e284803c80c1c2c0256101100c8ca40c0b1910b0112043c503041c040580104000d0404000340015070201079168007580c603454074510503e2313684a82c1c000c1003002062000000810b142d054200914100201848040d0191201403409054083c02107e03802103901803120300d003012070042c0d140445c41019221003807044804490010740010905d4105c0f0103070084000c950050103161401181c1159212204801012014035495241c02c245401280081c1550300725440b007038140500c3e40a80340180300c1c411120341595000c1044906104016112013140d0300d0440a440203606d41400f08a48865140200c40d482002004000e401c0c0d030141c0c1c004411a0347c1d00050680d0dc0802c0740000749190800d90107010903108441011040220040454018060303c4a00c613007818109000b0440d4644046613000621640c000d01c0d17005e260142e070141c0403080c1d00101c44003010740320740c000c50050b0446e00144005182001c030440a45100ca8140342c01c1344100c00020740c00c5a10399001c02807a40d0001c4c07001c3e0207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 419859172 1250 419857922 419857927
    0x1060c08071e0b0c070311070e0f070c1b0503011d0607030b0d050601090c12110703110c030d0306090b03010203220804080d030506010801080303040c0e07050f040305060741 76
    0x12039480040f445512480725154641c82a800c011f049008100c14518040d00440b60a000003140058655080101428580010b95407641c0503a0000410500585505043d46141124140349010b80040d24000d030f000740041094400d81040113410182c40e0032080c0c101600242015100c0d52040b8410080201000d800b1245600d400d41081c1d420381088400f01e40340e01903800c506400c4602c07003031400040d0404005001d03031307070780180c60900503000f0040412201d040e40c880420303020080020020700040948040c079105140140041802c0d11a8041040c00c103645c80400e4038043c400d5a124400700014152400c0c25a038003d032030b0241110007120519070a01c070110b602c902c00c0041300f04400d101c0e14009014204940054855001603000c0368880c0d00c01c104001c0001c080140d52004c80c0c0c2803c0741c03580541c45440342a103950060050095910b0b50200d000014004c0005400d40070311070307680380c1580314091000d180600400300314260341400e00381d0700c82951513011369848a2007401040115030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 419860422 1250 419859172 419859233
    0x2c0d210501080601061407030804080d29031b0609100306030510050103021804030e04150b0c0a1b05011b15050406090201030b03010b01020706110a12051201060c0807 73
    0x1048031000c0e004003456902840040c40884d81040c0c07826216080c50000d2801d10200d81c0d00282032a1004000400e8100701190a01c03035440f003a0803550548080ca210680a5900010040c0019800e100307054443d2095000d042d68080104840203855000a00310a00c1d0000510a0060b40010401da4104142e612213001012a17400d206c01c00703100d40c1c03e51010400303526600400c10350721060101d051900d1480014040025000060400480070655002c10101c1c2c48880b008201c140d55400400054000124400407039400718015a08070304c0b4400c2c09000c03060919644004008034000d040c0480c0514050740e088921844005082d030344158002c035500045804154141d4005031011603819480d090210119a09401501d00204094000b00500250b100000b540c50701c0030b22580c5d081c070490001047d0a180b041c41607841098100d00145003500c08100002c1c071740e40c0407440c44020101d40d040040ba1880c4030310301d031449194100307085500304010f58984e0310300e846500104d9120400c036003011030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 419861672 1250 419860422 419860487
    0x90501020c330d0b04150509041106160506010801090b54011518020906130609080307030903080a0216060908190b010b030601021204092c0d 62
    0x1000c2c042c40d4040503200d9142c038100105442c04044528410b5007084001c200c403075a92044003045a00890701c00c03603680c0b00c50400f0514094100c4560390491400100703c0d44203500624054000c41c400c001325802a139031616080e007210041a8002c00410403440030888801c400310386500c00d00003200e1200e841002c0c6001c20070b0721400020102c62a91a54000c1442d00c2c522110b507030b85e24058520080c808150119246261142c1c7c0707000c0d00c00e442060300307030442090102e503040e0380c80c0200141040d80e03221076076a81c285c4a10040e03c50300001501401e0003050034000401aa03111943c540c03200c402c1a4116038940c11035400090502c41144200b801d80200040c0510f6040c00900d000d03215800345504000b00c04c0e0610034650040401000001300540000e80c00c1501c1d0713811250760711121900e940356500104e05282142c4400e00001d680880c01182d400c155070300910000c002c2614101c80145c101d03000c2d122018100c0e80034070060704500075a680d400e016210031840114524810200310504c294075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 419862922 1250 419861672 419861749
    0x1060e03070f0506300a1a010e12070305010212060f0105040b07030c1727030d050d020d18061406010809030a030c18060503010509090c0307182903060601090501020c 73
    0x11104580c179410074061071202510445050320004180311400281590000c0d0146400c81492401481d02044241180380140145006180e001c1c00941d0740c0d80b03c0c2c070b0000140305029180f042c030543c0386000d4200c19600800c22130b01181c0042008500f82061910309807600750401070305844030030042201b4010805428003c0101d06003e0300c5d40c3d044c030000c0c44403100c50120289482c900903404000403283d040e400c0350603655221100040503070303a41004c210f80c0c4040c000c04000d05c181d44480102c060100702c43c0e500310720340e04c03101d03d05030a9441c0e4410740110750300f420070746240f142504200204140c40c0d1094120381c0f8040d005040c09041107001a0380200c138140d40c1e40c0007400107040800184a1454428001d82d00100ea140042112402d468000385e100e0516126107181450795000501300c80c4550703007064040c04600e1112080703442070044100c0c5000381e00e0b03940328801c0c05040c0024055600400c1d00101341c5030103a0060110490403018400701410380380800507448517130001081040c00003c0ba = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 419864172 1250 419862922 419862997
    0x12082101030b0a0501150c1401020903010219080c09060304140106051003020720012c03190201030c44040309060206010603141603020d1401060e03070f0506 69
    0x540302d1036241040c0340408540d01a0441501503681d00c40360341506902450341e0215075080032190000c980780100180c024801d894003550154004110702c0903501d0740910310082ca6200e510b5000880d91200c408464902c150b00b0003950140c02440490b020510503c005001603030400000100e5603164000034508400e0034880d94002900000c1b9102003000c42d402e040444031102410034080c4c1004000a0422616000320f420308c1400e0316107060018107040c1404050003005001d5903681c8035507540d40b001c0b141c03110a069021a01306000c117003c441c40703422040503102e1410304003050511402003a200f50b51826000311000d183c7c04210484013001107182034096071003921585843d606d8030001905011f0142e00c104241454100552a03045020800c1c65001035405501900021005015802405500c039801002d52030071032451100c0c004003012034140c0c0d005d600d4500302c07a01c0c00020156904118010103441200d0401d00300002c1c2400000b900ba8261000d1032040d0f18101c030000c80d50398111001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 419865422 1250 419864172 419864183
    0x90d050a0c111e18012102031c0f1710050906030c15031602150103120c05060a1a04020f0403110d0b0c07061b0806100302130806040c08071208210103 66
    0x50407540740c801213042c91060b280300301000341c0d854010f85d4210349492460326484440d84080c1001155400d1103000034071065114a10b0500300c89400060403c2250000e0070080307240c948030364807050f610040c00c2d44a0718003c94a6081c950402c1c0620141000203003070a274140c0301d55070790140c05903555080400f11030540151035490b450b083c42e5440710842101c074040c0545d0820344101d041c41d00b090a4150549800400040c11010030110486031900380d5000a0428003490b01444281800c80e046500040d110070540303490200c00d10100822031080500741c42d45c43c4010801080042c0703001c4400002d07904010200300d0000710982b9000c3c0034540c129034a004400000079403404010b5184120801c07018001503600b4411400e03203004d016064058240707840b4034510360303045c0480b5210743c04a420f00c10803540180b00c0142d803560220303034464050b1400c4400742c180500c003140700c800000c0e05000b19160707000d0041c000d51a0341c6440c5500d0380314100c1000700c130110a0103969201840c1c03403668021803040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 419866672 1250 419865422 419865469
    0x7080a0807060f0203100b0c0c060a11010e06162f0303010e130b04061d010c0207050111160e040303090503040f0303030f09080405130209091509090d050a0c11 70
    0x502d4070004541002150000f510710500601c000301a0350b0901500b03072141400c1c03896495144810941c0f0b0241c8020141d60300c03810000b84d0b0503400d86e1000c1142c0e0a4488600244080404c0000c0242c442000f101e62350408450400f08208851289482d1100f62155407103022007a0082e42d0f0410100c41109110407403940300100400180543c15001a8465040202840d02910303583e10080e09480141c00a03240c1c5444c0d4a0020140102c9003003c0305003000726000300402012a04042d49841e640d105036400725001d203079101c400d00d01c04140e40065041502685078543d00f40048140981c4020744107500305a5600d0004d00000d0041000f04060881460a20981851442c00034281c5001c0c00d52012070a04141d0038800207020081075409540d422a0fa50b10303644403800080780203025015800382c0c0040310505220325280340010b500d000400940d100341003a07030788040c0d40fa0780d446899076480020380100311032a04140301d2103c1c980c2c5113100e154000a03030352144000595a5400b02d5042414142e035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 419867922 1250 419866672 419866687
    0x10f0c05030a270f0608060303130f0918050303010306051008011406040c02010e0c010806040e0a120e01052b020f270a0e0c0c0109020604030503090a050109121407080a08 75
    0x1c9500f43c850070102d50752050303411403d009503500d42903458483c030000d104071703000852681c0d030f014000e90b110192103c0c0480b248503660880c00c140307200c1c0c4c2e2252010081c076200303640708140e40c07806010b41c80340e400100451441c3d02e5540d81c44000c00c4014010306800342c80c000c020505150a010b0f612400303050091218041c02d0200400042354081d0038440c080da0f00d0301d03442401145001c81c0350f504c495024202003803143d44002c04a0b018102e5480c1d0341c40f150046c3d18082040050035401c0403000416965914034500400f030066071584941d583c40d0762100c2d031301f0b1910741011255903040888408180c00150608251140314401e40c0c00c800ca407841012050551500650070b0300000e10490441240d0300d12030070f882c01d0840200c0c041b02414010245000040091030b070b580c00d40109035a90350140031299615a40c2c1003041e142d811050380301d03200e2070507018001460b40c45004441c081d10311585540000e01140e81d6850800d2541d031007411041c5c002c0f1440090488010b002e5042c200d0b0140c20000d540d26a07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 419869172 1250 419867922 419867957
    0x5060304120305010b0304051c03020f07051c0c05060a020309031207030507111b010513030503210a090b150a0f08070612051302011202070b010b0408100b030c010f0c05030a 76
    0xc051701318216610081c02000701042d0300040320a041c2d02c0070000304c2005642000120302034400d01010304c003c036000041d04810032400159900341e29164102c030b031600f00840b00c0101c8100750200707400b504552040d00401d0915200e9402136401c8024034080703e2900a800740380440c00d000c1107942c580440d54420800c41c2c210380103070400e0799507840680944608882034000d000c021441c4417105041040c0440c0046004014022050146402c041240e0300e500e200240b81b0071440070300ca1035507981428500800d881d00c00e03501801c401140d0009400106079903a1100004840d090700d1a640d0064180800182c044a144001720240001002a140300c40c00c203600074145c90b400c0c050480303005d494402000b240781010303c0320310340071642441c14200c00e40320508914064082d092020303041803204000013440101c4000244100c5600406464101550380d1a110031101c1d111080e0303406800c2607885001a41c0304140200d810581420081c0e458030103900c0c2d00e40742d42c0200d0803002c003142d40c1500d003680120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 419870422 1250 419869172 419869181
    0x3220818090402280906030b060a08030702011b21050a02010c0c0b04030c022b031412060402030604060801051305072115140703091e0807080310050603041203 70
    0x2903581d094142040c1d404a0307007a000b002110010b42040758100a44030030108001c00040003400701c00e02180c0e07102d0600300d8010034140c8107540300d88000c49000400038000702c1a02c2965405840b030003a84e441c1c5000d51860075040c0c50040790048144007180c01c0c1d03440600c04104c0d580000f0303903506481d0008490068219065141c4c03e8060140d03101c881d800049404d03000f04c0d401540761814051601c3c880c4040303944554440310123052150500d403203140741e81c000300f00300c07030030340c0c02a91080c4402e0082020007030a4854419280c880b01104000116035052035001160452400707080003e481760790740502400c4803816502440da02c0c0f040b107882800e01408100300701c06403040b010138030006044030000c002c4440409000034855007240c10041c0302401c5540c80806003c4100403203030128604280d005009044030340d0100e4503a0031208100d0703d003405003025002c0f029070200f035151070152a030325080401d41004240203040d4000750000b0407a51224070156001d82e100b180410304594483c03c000c1c0986 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 419871672 1250 419870422 419870467
    0x60129070b1b070b0408090d12030b10080c0a0309050f01180c0f0b07060c0c2306010608090a020f0d12120605040b1e0d052a03030c12032208 62
    0x381403d202650100d025403200c29041075004921b40c0d03481e0360180c08650941400c042c00391a2030201e0044505a9405800c103c0c0c5c003810803207141d4035400c400c0f0310a0710b00d0740c8107690039600d0680078440400e0f414000d07407190201c3c0380036030100c0d800000d1016902d42564a900380c00c2c865014200d24120030880c44074408005400341d01c0c000301010f420b15015034028015010040c06035038035904800542d0780640da46044e001c0d001a0021f14004900310301d03515081840782c45030581d01c90f82000040d0b003403040304440d0007170b8003240151002c610380d5001c01802580d80c24031194001c885108403000102e1a02c041e1305010380603100d2864070081b00242d5412605607901c00350065051020300c041c80e03600e002000e040030711101552085401e0890210b482c0410300c1b400200380e480ba40c1c0350ac50400d13043d0a40d14425a0851601c100705c464010141a1640110034190035a0f03440b291035001501012800746034000921411108866079000038a8101021544281d0704810b0000c0c00107050030b0001c080383c1c6070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 419872922 1250 419871672 419871721
    0x1210804060f12020a0e010810030507060c0b0a060807051005042105070608010806060d0f0f0b15031b1002120409140105010f0c06020c030904050a0527060129070b 72
    0x80409005c80541720006044141d410000c40d040080d038210701c02041c40020315008001c4441c070580320780c0007034180f004102c400c1e40c40411000c00a10341300a1342c0508401e4603620406024000c0c504014080401c1411003180140070081c4004070724414007c0b82040c01e80891024640c82c02101d0400f20b040c07511a82040040081403001400049000500641c01c403006490030f08a40100d4102003248100d0988020300000220004000b400b0300030000030300904882c4002d50804d2071840400d60303030300229050001c98400ca10851150b0746060007486000c2c51450040da616411603002c541500d40c881d80155040542e610002c0300028075440506000d0305e401e0070062808201c580000d01148110680141090b80001d24101940028010303201003181c094820720031400c101c1d054402070201201c403105008880640d020307180d00b85441c4440d0170200000503190a03400e000003c00b05030030800541d0454000711900d1002c00394200b00401c1d0040c007880892070349092000e860042005502c420894 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 419874172 1250 419872922 419872927
    0x7060506011e0e060d0605060307020a0606140d06090507050306010806042009190b0312070516240c12020f120f0f0c2803090801050f01210804060f1202 67
    0x411a0000807140400204444007a01c0e1710354030352020007515941e00700e650031484c00b0080c890b4441d00041c8803e01c45116900c00d01115845003404281c1d6940b240003144d0061642540d88007050b6280c0c0b141003040d01810507105950784440c0821f00e0101c0a90161030141c0c00b5504020602c410001030722046c60080e10a02d1000c041d0000080c108207000c1c1040300010003c00700c540040600d54000c0301a0100076080d9540045c0c400031174180e6400051090b11640500404850300d9170a031801c0c03100380c030b44d0462a640ba402c81d80c1f803145903801072440d00c0310034850000ca0003800704000f022001000d0340180d00034000c4040310300b101810b040101c66a03a042d010140002c428290030394041d00d2100311812030036520b8032402c004d0540303050703101e026081500d11500c0d0340400c1040d2810031544c0c0c05020f91200c5145aa850090350b01b2900c0446c4c00381402540400140040c81d540790b0f4551b802080131500d03000b0620552a00001a030050f405500820180b00c0c4108213f0f40004000c0c00488003a0011070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 419875422 1250 419874172 419874227
    0x504090c02011503080d14150a150503010317070f110f040c021903030f060303020c090c09130e100f1514031e1c02030304031706030a021302090301020706050601 71
    0x10310040c0601004040b0b403004180e090414580364001c3c1041e42e2148a0682c45040040c02d01520042d491023690007810b2014000c904c901070711100319240e0700944d41c3e4600e0b6038a107446c2c441c00f001e0040d0348034010303410402900703012581030700c102c94203213000e102d410300340c6003c40003000000c0401203a00c900031810302140c84042030300071072000b110a0510071045401802454220b00415250361004816403403c0f0001c03091660002c0e2103041104240d8204101d41c9070100c4446546c0941c8010a600c00d00740080c3c24807001541d04402d00c18425032085400b080800384116080e00d840c81c205ca48199074880804081a004501003001000b100e0f5410396640d01c9500800c0d02c8008580d0907140d4012183e03e1031500020030840030400310f40d80116030b00b1014902034000c4d1244e0090f2801d0740010f071082005c2c1e05408031418140d014020080040190b090580d0a02a10001031001034840780d07824481c40940ea1070070b0004240c1c0c1441485d000405142020000d02021306c11000c2d8072540e2001402c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 419876672 1250 419875422 419875451
    0xf0c010b1e03120d06050901080c030d080f07050a03060b03070e21030f030711060a0516110a03080a0b040f0f18081b0a020d060c0306080d0e0f130c0504090c0201 71
    0x1403255420381c5205581d0308503641e139000a00040e40c09140c01030070500001403266004100c0c08210f603011420307944408403a0310b080b1041101a076504e0b035003c1c4800003055225000b80028545030200d41000305806546007107405c0300d904200d80c05400b0400c1e80229510515010f1a24500c0041c9000d84410180f20000171558074000c40c08800404040000030400f0a80600e520080c0f65020301c084030801c0c84d0840c14070740940801e84084032400112041d1441807030090340c0d07a41001c940390004007200304550b141100c01c004060300d00004140c1c0d40c0c40ca0310194469016204604180002c0801d07611141a209000c407082a0f801841c135540f2003800600151456080750a07071228030142c140100b5100031400e0501400a200941c01001d26600d002081101c1d000340d0301000c00ea0301c00b0401c0c0ea9560000d40e46805850500e0000103502c03040c004410b1801511070340f0301035400342c240740b520008030440c48119580d1201c102d01140380424200801ca400d0301842e442055503200a01150401c0d40c5507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 419877922 1250 419876672 419876683
    0x6090e030d05040212010912030608150f180106080c030f060f0c130e0f0103020f090603030d0e03070203070618060929121f05030a0c0504020705030f0c010b1e03 71
    0x280300303005031182c020405550707580344076040300310044d0001c12080d01507142c6008210000c0682001080c14a68002150207021407500d4024484012604c22603542c400030380f07444c4d000144025460100c64680650848091003650080c3c400c01c030007480325440c1c660800d454010102d400c148607a204400b002024401e000000e90800351240b0b4098541303800ca4042100f00c1ca8503000080d05404590800051100c0f01720240d040381d000f6603510141740c0d5031205002d03955900300c829a805600400c900f480ca410035900054041901d4402e0301d0400c60a0350001c0d003013441c2e5510000000b4070322007044d2101e00c0211003c1c1c000b81414144406000d2a2548002c1d24071241440d011080720060212401c6101c160101c425170003813001001c110380b81443c02050320481010034811003280b0480302160b80d04002503d801d015402126000c812031504040001a40c0140740441e1140070134800843c0080480001c0c05c2c91443e0f12001180d440000c40520110200c00c03040900600241c0300c11024a440102c1d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 419879172 1250 419877922 419877937
    0x705010509030a0501050c071a0405060c090a0f0f0608130f03080601031e060f05010c021e010e0a080609010b04090f380f0a0c090e0402041401080604020406090e03 72
    0x300261203480c2480060b08010891001034110750816080160018a400082241d01d206000c0e001c080720103903030002c0204408590051155020401007203a45000303102912444400420301c428094840002c1d03518101c2075441035902c0b51a9510502c0520f0704014110780c00081c51f528040103c001d81c4840700144401c420107000d00030743c44c000c11441c0c0d11981001ca00c2003c0c455552500d2003000c03203d0002004a403280d91000100207001142030b41c400c0c000d00a000d90010210080c0030000c403612010398000d44015411b200780149200c0c1c858580034034500090940b040a0081490700c01c40c1c0074251604d400ca540c0c421450002c0d0000004e01d1007181d00c0b202c54000c079801c0f029400c1215520108500c07180480040d881c81580344c01d400840e40c4283d40706074400780306100141c0700c542d00c40c001da940c0b400204000c505c03864002c3c8621072811070115032042c002000440c1c0b1003041864800100e200b80c2251525400490402083d0308107402624020441e48400f08101400f030b850040c0c50303004444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 419880422 1250 419879172 419879177
    0x30a0203181f080703060b07051c08010f0e0a06151214040320010905033115120212041a06010c030906030f0209030303010e0105120613080702010201091b0620070501 73
    0x20205002d98860780c0032101030070640c80a030390340e2100d82c00d2081e2b40751511400d01081b1074019002903c2c0911400c2008d04075901c220b402c0c0001c60500703070520140c04008021400320fa0382c84d280055664542c12004814540c5030725407041040c0a50741c03000c10348070f8400c105a51100440705000c00282d000c0c1d52805800700c3c1000c0243c03c144d9284140c0d02601e007026001e07205100201c0c00c03071203603003240c09404500781c80e00680c180031042c00301b401c1d00e04040e10b00c2009200c00d1029409030003280180d0b0344003000074059000603e0480307034507038140e28240165800c1c1da00b403040003100d1404840c8100c007e50000740c02d00780240f07038148030b9a0080100a55000f41c0d82056202c080aa01d0180f4a40564111801c014162038903580c442c440740c81c0440342441707003170310611581007284290000400d0141c0035050300d4400716030030030503510f80d40c410f070b03000e000c049045650740d215500100d41d004a6a0a0405200800c01207480c034000008080d1190040e0407443c95814100013a2680000140841112030a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 419881672 1250 419880422 419880437
    0x203041409071e08101202060405040203191416020f0c01110307140f1603030c030c030e12060a051006080402100504030b01090c0f030908030406090204020c030a0203181f 75
    0x40d00c1100d00c40100343c081d079100c1c0761840c5010003258000c2d030301511844040c0c0802c519070740e0380c0c6144140080000c8000c0c0d00440c0c2000203119034140b54004540c4440b18047c900f4245030f1001c0203008a584c40301035000090108014480603009200386801c0740b4501c0d10040244980c0310342d145031215000c0d0031b00350510400002100700c010043c01501c491940003001c0d6800d002491640030340300c00364103a00304824010011a130f102009180d44d0441581d03010307031b03c20030281a5980c0c190303125070704510140c0030b101910302c00090940e03900d0741010380f1002130b001810b0380b400d210303415206582e0302801c42a01c10040c8002445003550118425078820340403a0b10741020418131905841c180b2440d0400303080d05071100c001140b002e4090300500f65552041d6202888265903440072811100f2024000f840c0c400100041070100d8910b03000400d40714001000103181450580c1014039540c821b00d4941d015820105582d81d0718507001e1003000314a4002c0d15141402c0220200801900f51403100610a07c042c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 419882922 1250 419881672 419881681
    0x609050601120f0e010e070e0606040609060806012312070504360203040b0411040903050f1c1a280e0a0603060518010f0e031b120414030d0203041409 66
    0x210707004084c154009600800c41044c00018498442d4661b00524001450303020103e44142001d00495045804940e83d10b0300d41c50400000700c61000020f04038a0400490b04104248414050b03044007a84100c01b503e5a601d40001510070703c06400144030203b44002807004010300d501c105a2007180c2c4201c0902c13613406684020f804049290001c148043c00c82c400310800c401c00c405000002d02403400350098401940d44041040300740c0d0410b89000380010420700c00c03010140c5124014141c40c2c0e14061318000c04900001d9010b00300c41c80250004020000012807800c4c5080903e4600d860300c031041841d0b280102c40090400c044480740c4107481240210800180b40c2100d6903101304051a4070241c240719900704a14800c400340000444500c095103400c6100c5541e20751442103501004400026608124070980a1324140000d50640700c1140100030030080d02c0304a02e00100068000c0f065100c141021000901d481d000302480e44105541c401c00092000e0100881c2c44006014110f07101c8066079603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 419884172 1250 419882922 419882951
    0x11010c05120304050c0922030806011e0e1003060e0f060604031e030807020d270812030703290618060a033c1d030a0207050103060905060112 62
    0x101c0d1006026004011080c80100726002c208505140d100315500d40807511800c00c082510040070325102c840003035485201c00024000c400b496800207050400c14100c444e210341c104c403200b800d0350504d4001814503403428460702c0c0c0441c1e180004121840c04002c0300c0d040003803a802c0d004020707285c000c4038040c0f040040c245075240b20840c3e02440d0310603500e849501c0710405042e00c116600d44110b0114014a0006018510029100300020880d90741c2400c41d41421a0030281800d8200c500090304000c000c1c0800e900e24208501c120028024103055600d1400440040880d42c17800781e404d82480c0540340054129922805104c1752100c00c88149070340c1e1000c02006c00b144044105c5840c0c001c0000b02e0100b2079103030142d0011030010100e1100010f8000003260024500602208061100700071072038003d80700310fa80d4400781024900c02c0101240b00c06980c900c602c0c0d03801a1754268010307400410280503650349406083c0c01005000e40500150506200203840b44038101301c80e40342c1c69a5414640f10303000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 419885422 1250 419884172 419884183
    0x50a0909020c030f1315030203040b0f09010f0204242c06070c08030703090506040506043803070f030204050f0d030306030b0a0207140d082202060406091d0411010c05 73
    0x400184140d9540c0d550054a01c05e52130301c1c403d450a0b42c11104006002901a0080368412640030071940e120740e031045003203085850060400a140d650700c03250300b88011040e10041c00074002d60468402d001d44d4106110000700d2210014a041280d1109480341b0141034050884440032410401600740c2d04c8200401c07203500030500301921040c08880009480003000c0010040e0034040e41d2080345140e2030701d05100d00c034030640c070600c1d41140c1c1c00c02040142003014030264144440c00c11242007031b12051240c0070030711541c90850304035980d0000148060150000c01d20500000300e414294182480c0400040200d88114126030244a100480750308040c4650710000140d0340c4159a50503a09008540c0802900300c1413003150080c00d51030340e401c3e00c02d100003a83c030314950542c2d9032840550f44d250070607000704a40008401103400c101c40301c030340140c1e0740d64060805000c885e503c480d03480b843d10445202e24610003181c1803000450130140b10204c0c50381d20303d01c0d4021400b82400d002d501c4080c030b049032624 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 419886672 1250 419885422 419885437
    0x6072423131a0705190801091a0603070513050604090204171b30010b010f0c020312090d080d0212011205060105060c030c1c0206390c0609010e0d050a0909020c03 71
    0x2034005c0d5416540c46600040701030705031100e50b030042001d40360f11025242410280303544540e002070140300007118288100d000704010382002500c540f50641c0c0d8404a0340c1d682268202920710750b00406e042c84010121007150915046440086c001c4404125100450780ea00395880c6016441c0030f0b200c056500541410341c0b2f0351048004407124241408480103000f0403040c4500d40c001032403501d413200054401d81550074113a8005003c1e0000917039402c202c1c0069401b001d003641d00201580400c2000c5004500071f000c110003201005aa20707405640c45150000c0141c00c488071490540b0401400b1490024185054500664034107075070700003d040241c6940260711306980346206440b41c03400142d850028a2110100c01d4088500e50340358480400c05070040000401c40110469026041201291900708281619449114649942c4161160400b80101e440184076910b4151560410804102a6204501c0c1e840d00c01d017803540400d40100b00c800c5034450644443c1e00440c0044c40000d09004480d1403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 419887922 1250 419886672 419886697
    0x240902060a1116060912170304050a03081b090d062403050106060302040506030412092d0b0901020a020405180601060807031a06072423131a0705 64
    0x103a566001005000ea18a40c0041c002802140f81c80d1001c84100c1030f2100542c0c0d480e441d44000c55040000840180e11501e2003650322006200380c008203801000002e6000344d0250000d09600c00b5141805400400c014040d005030340b041510023010b41155a051b181025030841d010f02505159040400240c600c40c00405142c1d4a5010349054040460311100100c80c4504024072901e40e545c6000c0c1c04078020382c4641900580104001b500094070310240d541500e020b814008689034840200c0d0101a501594208428921118610b1581d901c00c2c8040010701010410320320780264080001d44629030194001d0003030f6200c0f00131441201070301c900202c508800100f02d81596a540d08010241501a41c401020074501810031513075100c040100c821b903400141080e440c2480700c0d40ca088108420300e4618032215000e07003100c0600906030048501c2c02c0c22011280c409044066001c16000c24054421126082c89594120004141c910004540004103031041c0c59951003e00c2580d107480303200c1c0d5800c40d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 419889172 1250 419887922 419887927
    0xf0c060b0a121e050703151104090c120c090b1810020a02010809070f030f080c060c0d231303050409050408031012240609020c0c0f01090324090206 65
    0x284403520100d80842240508540002465003c090031120a040389000d4a243c00100041c00422000c42e140440304c1241100003079100003d4046042c80e07000754000300c0c40f041d00d0b49007a0f00404c1e44402c0b40b040100042504010351180040040c0055101d403141c20b09034403000c1441d820b11620b200c02201c1460000c1d00c0003205084001009442c2d0105034000c03408600c1640c089002003500140c900c041e594512450040c0d0313070841d01e603100745201c1608110303054101040440511441031015034041c00c2c04a070125202e0650a1541080c0c400035000840010090781d000c1c641d101c104054560400c403503403c510200065410106e034941701d140c00504519003080c052104001c0980b004511480c2000941c2d2001515140309000810309004007400900403010f20745458100c0c1c82d11070f445a8808440000c01d0780c0d9030a07001d401c0c0e81084981c005290405c502d0b18800313042a039002c5900031424a043c02e40b580c103550340c0c4038405418142c50741032441e0301001640804040d81c040c0b4181c6400416094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 419890422 1250 419889172 419889179
    0x160f02031b0604170304150218030109110307081f09260309160303020c040b3c040b0114250506040303111c0b0a09021b16060f0c060b0a 60
    0x2035580b4015101141c040784103594902d04400001c3c01d59004a0b070000511040c502c01e000400080d400047c07194070040203d80764481b00350341c24402c00024a10501241c4880781001c001c042c00c08002e03900c0071809800254407107103a001c2d80b0b0400c00d507000007002d0001324800242880c0000e032039058030340c42265071848107200c0d24402c0c1102441c031400c0c00c0c03411290340f5201d0038111441040a884020050790040d6950846454580c000420610000e4844901c003918005a454014112818232101091030503000100004a003500301b03010509403018420f4000c01c0c00000c002e502c7c070010350745070f640300070907038240c041d22200002941c1100030144220f440b02c0e90030803540380c42c0b0030b8808401081c68401320a0701000d09805a0764603840700c003c1700790b610b000301c2c41d81d1010b8080b1101c8107a200c00c066801081000c035501c05004000c14201408902c1203038030321107911301450b098402242d00700d09070f13040090544c000c880300f207104101c0c80c100080711030f240344c030070b000d40224840c1e9035000da040c80c03011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 419891672 1250 419890422 419890477
    0x5030a0204082a030d080105011110050109091514060108070908120a120603020a05060a0909050705070c291614010f112502030a0b040303060e010509160f0203 70
    0x1009843c0196154000c001e011002c01d640c0300c400344142000300343c034200100321640c055107003c1030000d4404280c0312a0030310b40301e1180807103030243c1140001c9603882640d1000c0c00104000c044000e00d217500b040043c101c0c020201d500d031450041c802810080803c0005d484d0511030519000101040340849000740080d14000300c45030040c0200790300044208e0740c0b80d81e010034580546012a9000380c40318403c01d042005101440d4801462030081c0101140009880500c2c0d20a1340d02c1a03101b0303a203064960040d031078070154014550b4402d4900d010140c2c03d60030343c0c50900c2d62140c1040030541c07555584803500441142122005400034100d0441c0e075a00fa00e020ba010740140502e482c00c0002081400c2026000e01c100d801003900c10400c0d00c285d0012030f0b030b258a944821414183c00102140e003000955540ea958240040302c0880009880e20420841c407050004280d01428040310940010301d082c3e44d00e45686906031904004101c030f60742d00030340018000c0c001c980d441002800d10744121021036409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 419892922 1250 419891672 419891713
    0x117030c070b19020114011809050601090e010b060c0309010c02150316080a0c0c08070501060b030a0c0807030e03092110051801020a020d0503100504060303021e03041505030a020408 80
    0x9400301c1c4074290340d03d2002c543c41071003044000082c500325422181d00b0001b0403040624601c00c40c081080e42d848580000c54001c0051600800c1441d1000c03d0800351107201501b9030740d00b01b40307840c0100401c0c08801c1c81100040103880c0c44500070310f4401c42d0301007075000007400c411903400003054100c0700000703020342c50340c3c1c40118208011032071300d600746030303848050702402154441d2034448001480d01840400080d03519005100c2940032340000f0524036110401082558000d070b0ba101100c43e03441c1c201d0742000f50007001050740100d0704d0a040010a0303a4031005a220302c100315615204e01c262410750068068000c00c09807046143c0c2048850300b400101e03125006000c2902c6102c00110071125043d01100140200c41c499162580a03203030700040080e0913165034202a040c4c04091646010105441c0c98030710078080114060350007820203503008050b101102a00c51050040381d00100010703c5131402c4134001107801c003980e00e000d5a60790740e41142d0761700901a54000d40000e00852b840a81c0485400d1103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 419894172 1250 419892922 419892937
    0x40c05031501110c010c170c0d0207060e0a0506090d061a1509150d0f09060209010305060a0f060c1a040b040201020f0a0521070c030c0611150117030c070b 68
    0x308005581c018000544480c10000b038680059404600700b10413651107000482c280c1c900c20303040303101508840040c00010360001b00710703880f19a022051500545034100b0030800204801d080c0030300b0b02c64022020681c0340400e40106401003c0001d20740486880c0c00345011006078014074100304502140214400c2003041d99001840f800030342039041056079000045803a040001801070350340c080e000c1d08048850304022480c41a0a54405014480309828021518802d1040b800142e68080c140005011144054a4a400f844019209000d107080c2c0702c821b401900c071300d41084602c0b40c002e0301d0211100b0314003a00c040001c87c202410301c010050141e220600a5100341c094841c080601449640e44140c100c43c0a0983e501078500503e070b41c02d40d14145801c4070300740f1303a203585442c140351a0000f86808581c03040f612030448450401450798491001c406102e1000c0203480c55602c0c60b4515490b901040c000e040782a0b11110912810810070003c88030303c04419400d941443e40e44006110f5079810901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 419895422 1250 419894172 419894191
    0x60210110c0d082d150102070812031b0a0903080c121308010b0105130302040c091509150e130b060418090b1005090403201608070902090306011211040c0503 69
    0xe409002105080319601152588031501d13149581e5a800800400b080e0b00e030f00360650084480c0420325100506c12003c41d07480c1311102c1596170400b01041749024650728950b40701e14000384460004c180d8445d010704101c0e40c00c505e4450300d035000c0514203414503600c115500303003c240c00100014420503c000307403411240307582c00030800c00180310019101d034411030302c01c113280101004042c001803525601510204103545861419240c4a880703251101d0104130340b4a02190803444100094a45114001d10250300ca15000d2008003019021034a0600c42502800d80340e0741301c4030001c00d141c403150706580041c00c0c0108800200351818408000030300364600191110340030a4001140c00b04011940c07002c480d00a04242034580e81c68a0403950b00c51100004800d08040c4c051180f420081040045418a01045400c2d01189488a001d15014690748441c00702401480034110300e80d4080313541811218015654183c140c0303980391030f52050401200c0a68032602c2e040e030a040c8294418091441190185c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 419896672 1250 419895422 419895451
    0x603060e010816170a080c030c1b0d14160e1b04032301141810050c0a050d0e01020703030f050f0108072601110c1204060210110c0d08 59
    0x1d191841d219a001d4045a400814003c02086621311014141c80303011040c90907241039807681d981c0c10116900c00240d00c006a403011a050f2300d002400d0011030419070000500070301c840000c5000c03c41000b40e00801034034000000c42d964003c81d0302885040c16448840c3d000d1040c0c149c613801d55890040c0250780e0683d80902c80c401c18294002c2c10012034058a030008092500c9803600400803200f482c2d54915001c2030b54072091200c81c011405812503004000200c102550740155440b040c0c5452440b25050319054101020300c401c0b1300320002151b4107107980340380596035000f0191640010b013244003003d440e40e6200003810320515078180d21840c8074602a10381032045840d056403880040d10b00380100361a0390013500e030400042c1d54880c5c240040403003e410402403000b910400d1070840d00f04035044002c40d000000c3c80000c003c8103120000d003003070314411001d007828244070703000f5990030907074510781c0500c0da454028010102c1010152490010900119141d41c0521007005110030829501d04a645014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 419897922 1250 419896672 419896679
    0xb1801090c110f070b0c030706050c0c10090c05012706051b0d0f08060d060608060105090c07030c030c080705010e0106060e0d083405060411010306030809130b06040603060e01 77
    0xc184650b066040400804e20700c0e08202d00000d05503c030040b0740140c3d21082001400040300380c0901ca105e544504280c0382c4075505030240078103050000c0a070030f08031480c0490950002d0b02021030801621020301c0c1c00d8014a00300d5894a52400031001004c4051035a03060014503a64041e00901002e10980c1488120081540007036540d5045038541c8004200d00803a00c003070b510300c03036544581c1c0701c5c2000b020303250780c6c203282d03241d00c82147c0064200c2c0d0010f800070401030181c5e09140c0c0641c0e8016242e115103c1c500038260b01c000f44040043d80008003000000610541489904e105070f642c5181c10600800080b00c0c442141c0f4000e18880c805c0c00c0104e00031514000491612008800740c05401103511450544401d03903030364180d204030401d64010800c2d40320090706d5282c68418083c1c41440f9030010081c1d4209800c2c08007001c03003440901810035040c61801d000103090702043c0c40c400142a221120720329000310400d0098003c1c4407070039801080110700014500d501d908201d0444454002150886e40c0f03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 419899172 1250 419897922 419897957
    0x303110f0a020c0f01020d0807050f04140a0509010302090c0306010302070624050102072115020a20011b0e010c050f0729032707030602210f0a0b1801090c 68
    0x5132a415015070040c1100580d02c0d4011182c042e40301e82e007468407610741002564407003410f80281d00400142001e1640175420b0f030401d69444800341c403088907104965031460740010540c00001741072500c600404030102d03080b6402501510b24850740500140324401420266107146601e1198400c0d03008071440300002d040d400030441d0003d81d0780c80d080c0001e401d01c4000c0030415151300e0020072900c2c2440c000c114140b001c0700740b000e003411600c180da030b02082d200003407022556400080102c03609a4949404560302c0010200b043d603014840e41420a20040020b00607a0007106140001d00103011f000c01180116401003012400c0c2e400920706008103a50400c03091300144c400b1349400c59140350401c00300e00c02c141c10004404a036a50b100b803800c1d1443d940310f240f80c10071400d6481224015004980c0881c1410142c040300c10400d40d03401030003600d1426412039010b007030002c0c059120380d60b5180d1034280305444860044001c00d10b06c00c0c40700055652000403c000386509440d0300300264458001010469 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419900422 1250 419899172 419899189
    0x180b0a020d0311090f1f18080111030423060405012304020a051903120c061406090601080a0906090b0a202209050a1a0103020a090905040303110f0a020c 67
    0x9141c840294140b4502001744604048454a02d40c1c4c0103007107803480407a03c1034409040800c6015903850318109030400c3d40441c44070203241c000312a144d0510902014032085c4000f030344c0e030240d0841001100c009070307804007516001c0645415025401064104024020150804078640d40e500c403910320000107030350a03500e441109443c000d503c03696941040041d49070080034203000d0481080300d01a05540c81e5a2000e03012145004000854a80d203000d6040c84036610a02104007459410500d2919140d00002c09440c2c009141d14103000e0b042010408800b0186e01c196000e942c410700400020b443e80c108100e0030700003210041d8010b82013020b4040c08140d0001b030054440400800c0a08081c644d0111001502a54079640c10400c484100090301d4001805454041ca4001600242c0c002022890780fa48400700740025042c180100000c007500d0740d2101d80b0008540002a00040c03d4486103011006007414807004c8500d544040b5181025094070001007540410380d07001c0f50314041c0c021382405001e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419901672 1250 419900422 419900441
    0x91a060609090c0307050903060916120b07080406150e04210f050c01020d090f02090906070c0204180506010f1403010c0c0609060e03040b0a08060909030f0703180b0a020d03 76
    0xb603800e5010030400200701028542001d024186541041d82d81c3c4007091130042e00300e44000d03c6500140c00c0e08143c156074007910000d0000c0c254544000e0801d51a002444c6801401c0c1d80200f00007000010184642d07a40040548142d00d8118036041c0e584200c203040901098800756044041c840300d400c2240d00042c1d24010800803503c40400c10030410781c00b901d02e13811181403035546540030004225a400039101d1290f0741482400070170010701d4140180420843c004101c46601c3d4003030424800c1c490303081044500513550407070b0042a01301c2c220007005041000100010a64032541002041414000358207200b51076001d501d101c20041304d04c0402d403c0e40c4000c0c540d0404502c52000d880041411a0003d84500b07009000100b84000c0c03409031545182e20a6100c40909100410106409584030b00704d60f411081c1155071007607a040485d44a9141c0c4a84007440a0600300042c24008060140d42810541c891000092861640e5198031030b0180d401448000014051085064440c0b4024414442070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419902922 1250 419901672 419901679
    0x1205060402041a0f040b0d0204060e121c030e01110a1106130818132c071502150c0403030f180302040f0e0109050f07061103030c09040f091a060609 65
    0x1d12065070f09030281c9500c510008450b218080102150664250008000c04072920074010380c0d86190840c0100390320f10003541c25200f4280ca100c546c2c8031400010300442050f1b60104907090302703802c200095000b0005102036032160350030041c1142d00d426000000c0c1220090540fa02c0f0342c00700c80154850b807035080c1106c0b0074080031031030004034001c0b90710b81001c0c003c15081c1005905501034400001a0025200b4101310041c94503a06034444803200403441010340c02001280410581c1400340ca0360711a01c4e1401054250000400c1c0c01005910804c01c14182103028041d0321000d0425841d109000d5101c3e0009501003000ba044890020340b1031090348003400100c014842c043c5041d5070820015041d04262121801c2d115800f50250f24002e1255840840c410700050a905285001842c1400000d40c0302200344522040401c40b090804011240d1101d0040d202e01c2ea00c1000b030000600412800d0020950303246040d81b1003007000260016440c40d090711400d00c900554070141040a14070034130381c08a40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419904172 1250 419902922 419902949
    0x16060b010e011404210204050a05060f030c130b06160f0b15010c1101050f0d090b01050904020102060403050a02011b0c0606090c02030f0706060b1c05150109060e030708010606120506040204 83
    0x80d2000c42170301c400c201089140184600681500041c080e64411f84001c64030079502da0501001e840e02000c0a010f11200307502070030000070b50710009502e2040c04000c080955445034409010f9030b564200301c41040b0035140343d07440140380344c6c14003040d064840003045688400d8880440d40e42c0e26554148500000140c0d00ca090442642d42c2d02d0011581f10300324203051090510070030340034100040c0030303180020020341c0008880c40b882c02c10848802040c0e012301c2c0914415002e200c09070742c1c049140380d40240c060600d1940c1300c04c128022030040c9090088200d918000b02120388070b060f44108031203a400d008050034800540c0700c05000040780c6500344d071003002d6801005000c10400740388002c0c0c00e410b4094100080c0c41c41d03540815284952000c03203140c8a980340d0b581c003e002e14030140700b000e4021441101c0d44495845031400a85014205d00503003090000003044580c1c981c0d41000031340090a40c00000703000300742c1d0b0f441c0f0280519507031a0441e42d943e410080010828203061090f201100c1c41000c1415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419905422 1250 419904172 419904179
    0x21010c09140f010c0b0a0218120a08210403110f0d08060409140a0309030308010e400305040510080402030d0f050d061e140d060c030216060b010e011404 67
    0x4a16882d480c200e0500140c0040c62020880c001c1a991003940c802d000980d0700e0341d40066109a00080c201d06501c2069a80100c602c031440000302c00ca00641d020400c0703aa100f0741d4203144041101032880794494000c20b001000100b680c4020840e1501010308221031180c4200c000c12610307007012a04040001c0e0600740000c003d131410340c2080308118010041c05444075540312403607040c041c5412041d80400d0211600b0820560b101600c42d0040c0391000c0011454100800808983c034010145075030083c880415820040486140c4240c554100d08866a40400c813480e014205401c284601407203000c0c460b200450302d90081c0321079481a079009003e0f0040040c038060541e040f2040c5818a000c000041c00192582d4031248180805841a5458050040510f00c205601c112146d00312502003019548900d00689601006c074501c20340c0817501150038101082d01310020300407212000d591500c51580c050500156500c00c6007001820790301c00041c26072020042d101c444000b84007407440300007000f040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419906672 1250 419905422 419905429
    0x30703120e0f060c130e010308030f01080303010f0b1c05041b050f09160e1804050d0302190c0204110d020405040507020f030307030e0709060801020a0e03070602031c0b21010c0914 79
    0x380600070405540010703854850319510541d0f01b090b0800c031901e58002052042c40c0940206032801094100010341c03540d81002c6041c0408001442070b00c0f0075810110304214101c4104e1080d071f0035034101c10010412440c15060200c3c000c04000742c5071404041462010841e400e0480c4001603a400140c0700f03c095071100d008a050034100d0840b0901040382c216101201e81c2c1e01c000501819981140b504452810942061350030100101c10890626104004c40001c0035482121154a48840c1c14103041c00030a50020138007070032000311541c400400c0040c01e00f000c44107507409001904e0041d1410030540e900c01200740e90325501c00c00900900e500510000d00128441d4008880e070b40c4c88074069443c40755846914071b003035446c0794100548a94001ca442408107600881c00c11100d10214014060b0f20303d01007010391280300350000b40100b20000d02c600760a05415400a01c0c03440c01c013405100400a162030b41c0e1824546000c0405000e50030300c2d441c4220716201d04c000d1002c0d075081c900349014624044040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419907922 1250 419906672 419906677
    0x32e09081611091005120a050106031a07080708072f0a050c0a062129040e070b0307030b030a121e08060f0103180b1510050304050c0402090a0305030703120e0f060c 72
    0x86059449047d2468000800c203028000c001c51080d12110710704d03055840b160360100d01c001e06074410008143c0c108240356a2006d403941e0840c0072410311001d0703070100c2075548160005914034060721000300c6011280004000520602050045040e035414040e14410040c000160b071141400149000405a81e40441c86c9088a0101d0040700c0010b4100020380895299203000d210f2600c0a000c00c0c0060310a40c28140101000410510041c280761814003000d80d82c00e0201804501c10035a0320082030103a51030410984801d542c020310341d616190380b50305008042d0390124501003802460f1081003000140030b021164012074004280395903691101e40110001c0242031400b0031340e00448000b80c0046042c1507401405403440e58520328042c524001409420a1005c0314002007200410410020a00104440f61140e104503005a628295140052500c0c80310390409480d90000166810030181c022040102d2940303404001c0c461801c0d03440c3c1280e02c410080c01c01101e11b4100d10f000540c0c6c050710400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419909172 1250 419907922 419907949
    0x10b1309050c180a0305160e01050f090a0e010902150d2403061109090a0504050f0a0f1103070816061d010f080c16050705030606032e09081611091005 66
    0x10421142e502d4403521f14001d1a2120801e40031a9600c051005105691250313000d001c3c20346840c00b034401c0e800e0101e01c07907000082c56818a10358075404012107200c00c0d002940901d40040c2244103640e000750401505901c03000505420b545060032128210009403c81d45180200d0804241c031146140c5620300944901c000a04040108004094141d692601154020078071503c0c00151807030945010f034a00a510650520250f10200d03000b00010010160201100c1e07210240e100d081d684400881e103803025503004401c1d503004030110704245c44100200881100d075a5034844443c00c02e07040c0041c488102c9441c0c200c4c002403903800f0f0490b41034003421945070040406803600b4584030400c1c90340b2000c0c0c0c07050385080758260046d80040146d443d00301702c02038000343c0841c058401e00c088006100003890304c0b081606040c8103580d2419038442e4059100b1116160000c28450303544003425903444c540752100c04111282d04202c3c85005050800c0d00841e0311888010290100203400c090801084a00303902 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419910422 1250 419909172 419909179
    0xf010e0a051005100e04240311031005070f03050105010c0804091e0608012f031305010b09040b010501021c020606130f1a1804080a0e0315010b1309050c18 68
    0x1600040d00e85481c2200420640c0d05d80da8000c08408210400054035150720403209203c800c1300c01600e00c03040c3c10719441c04407a80040c8218004154602081c00e0002064420f490b103850701c401c1083c1c1c180c100ca60801110f10541e41084030340c0e01d42d8019228030640100180c550304003407105121488540e40440e14075480c0703e13140b00c0110713904050101565907075005591103035102e035a0781c4605000000c4490f02c8034010f501111210504036041130040c00000d24051041940d014204288072082d44110300c5400060400240791520b810304641c00759080c41143d005109885220111982404025600303005640c060702850b05ca800402503801c0310000d880d845ca039aa1000480000c521303104440c174032142445480e110488440400c10304010f11030300342601e25180350801001641e400c00b03d6100c640c50b400e04034031201005001c07a00e40501e90780a0140c1c041030100100f14420000f0180441a900a061b90107c40d1034400d10700580300d0940714400c54907010f001804580114030540c00e007003000039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419911672 1250 419910422 419910451
    0xf170304080615032d010e030415081b0c031e0c25083004030c0b030c0d1d0c030c031507030e07091a0901031e020a15080603060f010e0a05 61
    0x302500e1300c1950040341104103612003240400b17444c202c01c0c0210185030f030800d009075080c10726164003801c02c40740b60034038141005500d03800101c0b401038030040d1240d041703425221661070750401032100d40c3e6070b40b040b03110410126640c101c0b99402d90102085504400d20000604110807150190030b170403000609240c04464078813803001c01d881908100c030700203601121a881d0103c947c001a221303505104103451080c024000c2200b40040342c2c0d01e88021017150646007180741d49a4451244240c0b034054040340003401070030500c40414020041c0501c68040a10400784d40c041100d042c01c0658585034041c00039050342208404d280c0071b1a480c4400c6502986505000c90402d6590340d590703040c10001d40010b55415074807001600355180900c94003402e0f807010354180b043c6504544506c1c80c2c1110300c05d1003440610300d00d0390f140115101d9001d008018900341d40184a68a4544805090b1708412107130f19000e840350800044c1140342800415048581c0005032421503128070380180094040180b007420340c80041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419912922 1250 419911672 419911693
    0x60b091e03030c160b0403030203070b09030f180f0103180201030902030319091503050106050d38040e030708030c03040507030f0803010504050a1e240f17030408061503 74
    0x103000900032458820050700901310f95014101d1010100c0d040a440c40900340700500c00641c0000031120f02c290000c45052035690f64454161a40c0300f0000c800f00f11070b0340411803d0880c02d8009280b4050b05080f290146401c1e0780c1c0c00110300f26200c446046002c80c0c003140c0303040c1c003550180d0302c191051400602980d02d0280e94500500c919401d2001080000d02030038810810202d865115481c414080c0ca410310480d4900f51004109002c0e1b606151a0541d1740e44802400e0000078890036a00740700a0401541e0717074003100c40d004184941e648a503028904144400d2140e1030080100c644603a4064001d90450319041032161141d080140102e40520034001c000c004076040d0703400424001d11503c80a9600e605050920040e030350058462902030f418203d28180c440f4080c903007103100c0c409007240022003503404c1035001c040981500703003031190f5030803441e02203500201450348600340c84100703480c561b103294451600d83c0e0300c2c8103e10800d10103403c41e0000c900b00300c481c0c2400040124004046072035600c907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419914172 1250 419912922 419912929
    0x708160c08070603140f060f030607080a0e0f03070308040c090501030809211c031508010b010201060e011404050c070501020c0d0801080106030201050d09050118060c080109060b091e 80
    0x150120151011011560104031200302080494090040c07440c0a01404598030180030301104003a2404084a140100040385501c034001e004115210080456100c0c0c01c04150140101c40103850b034402090600350b040c1556480041c03288401c0711684015440c00310b040d20201c03800d4201410440c0c160403580750024210000d4000d0a020b1402250f2982c2d844500c2c504108140b0107020031020000324801d42c442103003402040c0c0700d800002c071046030b00d040468a8001c074001c1c0300c44a9401174022403c1804241c501c0154040411281e080e002080150b0300d840c045600d070340d0244201c2c0a0301c0e0074140056020304140c1c100580250300307500c0c09d5062a40c10340e5950b003a6000a0380180c100d030b118405800203150321000f40c60040c60b40304c008204c45800c540001302944030703034811826881d4640e605807041080c00d51100100804c07135200700800d01c000385080f00141201013843c0000854072000401c0c6c0c11241c0c40382204444001d0b440c0791808161100344140543c004881104000c013075071020202e0345 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419915422 1250 419914172 419914207
    0x2060415020f100c0201060e090a02010305180f0105011404020f0f0d150e0f01050405090a0b1504060303110f01050f0402190b0d1416020d181d010e0f0610050708 71
    0x42e0f114404a50000b5800000742100d140d03501c6070301803485100600407024000300f1960300d100d8081c6070119980e5501d88280090403120420704419115450310103100f400107501c09810f89403544503401e0460b001c04204000da00580300034403940b0f0390411104500b40b04550090001e4a00420040341c849140300242a8032866684841c1040f5100b004022580c0a0703034602601401c0c0445042007103040c0110400d950b030628500040c007400301580441e030b09058810350b121141c04007c0080c061552280343c0180658400c0d8940422442039400120740c0c201c06001d00c611a4442c0c008001c269605c0c3e40801500c1140710181301100c0c200b2100110302e03905060020004061444808240c60608103042c0304040b0300248102004d041102640303241d5070f804102c030740b8034918918041c50460030254070700f554004690301c00e610b640c3d482c0440c6504c0030300c9054a14101c0d42e51081054a55484550011414404030307031076648100980c020f04407842c011000741c103070a40942c082c181812141e685000b0003c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419916672 1250 419915422 419915443
    0x50708120d0c03110901030902060f03010f031b050f131e02041706010f05060c070b0301090b0a090506150a0207120501061401210b011412040506060d02060415020f 72
    0x141400591004011078a00584448100d01d00c0c0c10401200c0000800080d8003030100c0d45810991641001c806559a2005640342841e0000700c565495940e521100f001c0c1b59076101c1164504249900705405214a00020046410180c6000942c1441204111f1072112680c051505680e40d68800c0c13103902024400034104100c285001a500e600f0200c64000000c0341412011065000d0801132002c2191120450100c4400303031850380c0c8803500ca441c49810a00e40b90801920403001000006040c2c84a401410310310130181c0d10082201c1d00c648509040d02c2013218156004000d10035100c0750070686400402c2c1003035061058980986d19900c1201048010801c1612240e449035004e014a80b0713241e80f40c003071100007406c080f80880001c0c0510840d06181607107600d2801c0e6181300898082c0d000e407030500340c0e4402031605141d07518070000039281d10300030560f408e455030710480d4000303910f0341841c1580c1990380b07400405581c1050310780140c0ca401c90300312090f500c085000310021000e90540070800001300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419917922 1250 419916672 419916703
    0x100f0e0303130b010909080904050603070302280506090108070c0201030b120f0f0105060a120c0e0f040506241c080310090f06050105040e1e09030a0806030307110904050708 76
    0xb045903410103510010040e005065640e191081050006147d80200d540b81807041c2c9002c2010340e2400002030800708290700217500110304052030780008032a4840c2640440f000c0d0070120b0019207400a01804e801400441800b1604c92004201e81031701407a040c0340f41c1481450003050224846020905200800d031030280c90340d011503001c210000b402d008800003400300340c1c000c00031440c0c140000b4180341040c1c86a500c0031200145c4403000d0001540c00f480160100c05055189400c14020401170a201103405039014022400411161b0120007000e2201c0f10400c0c082c2030000300c490041011084011060900051900704440000b40166001d548151036449851803070f1441d0020f07410079500e00300e03040301c139140c03414074140010303030304041940c0a84210051019003540c03002c0c800f2039a171420900200c03070003441400704030300d2010010041100a4480d600e1000e2502c9000a1503030724022458002c01c1394001c1d00b141a0301341070172488903610900a204a83e0280d6842501c6410000341109040c40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419919172 1250 419917922 419917951
    0xd0203100b090c1e030712140114090108210d0608010b0a081f020c010e0a14010c0206041502030402062214030d0c0311030f0f030106020c060c100f0e0303 68
    0x40c0385081c100c0c460b84650100e0005180202001d10749011035004c0c0d84520700e800e000300c0820b0206102c0c03058050000302e050010003800c20414403000c40000c092080d42a4501d00880406442c24410b0103181281c400c0c800030010201d42c60001480c40c0b00303d00c044c403110b00d0207000740c0010000c107020b1000140b440c10000100307400960280102c0d01090b4000040c1e56106990b0070a0b00164140d00c0c40150400a50058842c03440d0311045001d4203400307543c0002445001c00803024440703441640680b030860034008022100310100182d85a201c1203070050003600c0212503040c441c100a8004507031091004083c607150003103e142840752050200c0001c55075102021342400300018507000301003030000840040000484190f4028a10301d64148018100b003803195400b44110010815202c5a0b0b041030000350312003a682d19504100c2e0000d1055030014421080c0220550420800b120420030612003d4110700350541080340c09802940c1c1a0703044141e40d094145085030080c0040d50155482200e00328 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419920422 1250 419919172 419919191
    0x50c0f1c05010503060c120a021605070e090f0c060703020f1002040305070b030432031b060705040f03060504050a170703080105090606180d080a0918021c09020d020310 74
    0x4481c0705801960003680000c090107881c012460a4a04040140c2c500306c0c25951141c0d1082e01074086c4481001c4100f000219500802001042c000207407003107102d0803e45940c540e40035550300e00000c02c42c0400d5030030000c50f040940c105174004040250003401111414240d0191541c513040c000c0b03a0302140c00e5030200c0d0520400c68140050001008050b40da50b0a5007450384544c403802000c1c9000c0801d561048030131a501030021046a041204044152034070364041151000d0f18201009241005000e1a400621031a0241d4240c44c203071840c802c4141000b50940e41e13a5001011f000c2d0007079071244514504200081c100c48404121280c110b180319446149501e000303050400306030800c034071908041080045945552050350300c2d400c00c004085481c811080e0105d03501d000d4050019000407c00280f6080c00d43d0080d00041c111041080e207002050341c1c3d40d48076012800b5403404030f000304805003918502040c10350813111a5600082c89020007035003079030000303107000c0c40800d6a9403e26114207150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419921672 1250 419920422 419920477
    0x190b0301031101090f2115091104141605040503010c05090f010f210219090e070c050d0807030f0e33160c08070606170a0c0504050c0f 59
    0x80030301a00a007400300040e0f0174400218915042405001c4901c0c6103801203201098a05032481513841d003088244031140c18104013034016000400f81a18005007403041c0740c01a007000d1051507403414039004807640340c3d1a01d624101034071811001d40300c20020140701c0402c10341e4081c4503004800700c40d5181d40341e40e0540c107002d00c8529108070040078140003810750361a103480d0b082a0b0094040001e0725000c0030010401040b034009020703002c40c81c1c61444405858045094004484400f600d0182050002998840384e00701e40034030500200801503000701002070320b801d0241400541010450801180d210964010f92080342c48070703000d9840641c054018501c61110084651485840c1c5143e403012100b4241900300e084038000c1c040d5100e040000e070400d806a48a2002052940c0e44010040d48c1d0340c0e03050030280081c2070203010381c16961a2000c240404050300003400c43c1d000f0361006a04000500d01410840101002401c3c01c00b2800104841c0f0150307a2880001c11540f4220304115411140ca130142 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419922922 1250 419921672 419921693
    0x63d020715030c140c072c0906011d04060b090f0106030e070317032a09010212030f06041d010f050108070602161406070f03030f050705041203050306190b030103 71
    0x8078145494499000c0000f9400f108200904140d02c03c225950b4a1a071111403810205621640660b18a01100c444075180c40901410400703505100031071a0301d500e0f480e240c070b6610a00c102141c0380081e05544031440581070180380c0c054094400001d0022800e80410314810085466203090140000144400e82d050300ca0103140c255103500410000341595500a0300055400c90040c44110110000701000d100940c20040b08900c0d80c1030440004400840743c010340c02210f0054054081c40f050141c5110703805040c6d80c0303d010242c560307580580b00c007014040200528003c2c288c002024914110140c1024080c50003002400400007500350315103581c2c42d04002d0660081c02c02c64004685511401454191860681c2d0019100440550b01c100c00a22a1300c24120020895441100b840c02030503016403103100c0100031031070203001e95034072440700b15240d210382e00402cde060110102090020a1164019507480311010380360b2200b13152040d6620b40c2200e00b59000d481d0380080000140300f0400d07074400c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419924172 1250 419922922 419922959
    0x302070203013204050304050301240b0a0c02040b0307080303190b10020604140f12040608070903020603070c05150a05041a0c03010b03040f2004060509063d0207 71
    0x7036031040e5400050680d01e015101e0110040b068401d03c3c046001d001062080b1001480010000c003e00016102041c82c0c04804252004840c2c03c404000a0003003140b608a030700d80901075542c681d820070320740d0030400200f80284006415200e042008608400c01b080218088c001a64446070a004500d1826040e1544045000d008450650300e082000d900003071625005903010b040b10240d03090b00380113185003030303400a0b10051500c00c800340350352440c4140006105480302c40d41c2e0503941c0d07518180199107015503440000d400c500f042000900070340c4189403503441b442c42901507854034485070003050410203080d40c01c2d000c2160f641c0144000c21031021610f01008840c1642c1c03050030b2412000e1480140414899240c45c4a0004001020000e40303001c0c1e42101c9030721a100303000700014a0020300c411060808642e014524210001c50145480c00070648501402013505008403c2c0c0030b1b0400300d0902d8100705035080e240c109492800c88144100c03102d100034595008140f118940315003485400300002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419925422 1250 419924172 419924201
    0x30417030d0507120f0216020402071a01241107060320040305030901020705190e0402010c060507020610060c02030a021c080a080a0c050c06280c03090501140f130c0510030207020301 80
    0x2011fa94521f00c0c03210f58807601140c1c01a110501d5003842c600300d0030745031100c5500b015000000300d00c880203440141e20b001c80305164000c0551140d0010b803610303000110010b140354003a100400c02030341300340c214080200b800003070355480841c494965640b68109400813502a00f010405003010b507810412800200000c490101401026120580c40c241480c0070b440c107070210400014080d0f901642101d410079602281c03c01c03e51510316002174a074030701512042103428902000050241c820240700045640090180201c2d44076036082000c400051084e0b46003294081c4111000300701c41101a040002d82901c6e514924507041d040c000071035500c0c1d490b00c0e003848801d00c0040e4035424005900e944c80f10004c0000d0815150b5908000d0070302000c0b0120b851424142041820b601d40d15130401340d0f68034440c10090080b079040100011703448000f25111096401c001d00003601d02000e442a0040c011300a02190100ba610b40001c118051400c1000b100402d40010b22030046003800d2190030f07042084003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419926672 1250 419925422 419925427
    0x94808060928021f0c11061c0b0d05070b030415020f0405040b19060207030c0b0703170a140406060314010c050406050f040f0807061101020c030417030d0507120f02 72
    0x710300d0b9840303041400720107407011089880c0120031502e82007842c10400d408401403c0c0c85080e01c0d0001058160310345004c070b640750300b0310000f425603003040b03425108201040c0c25800f00a03104001407030f00410712080030540c8146100c1000020500500900c0003604068038940e176240b40500340a0395001d481850702c145540304001a04800300801c0503242651411203000c21101e80c82d80004124540c2042d220a5039008500d0010340c8a03000180c40d4105d81c49a044d641055030385008240e03a130700842c0d4010f00800c071014a065840301903602c0442e40071405000021b50003070507030550602c00d40111021070312a6074401c4d0900911545001c4541c4803244600240550300500000a15034010707881200284800406d8800340e100b00102903802910402c8814045c0b156111880c0c0d42d6041242301e0480484c150300250701d08120180200d6903848202002541f62500e00404003100b800c41c459802a207000138000240081c01d140035460080328166184100c048031070507000111400580c42d50302c0c03180304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419927922 1250 419926672 419926693
    0x10b07050a110612090607020d0512180a060c020d1b0f060c050c030d380f0a08060702060a0b0f03070e0a022511040948080609 56
    0x205070281c01c0e07001011419405000c00814824090205109005000002003050354a00068444e1040150b5422184c10f000d12983c207981c24461522600c5542018500180300c4161103141c0f82c1e01d1503083c0c4200e410002c5962a490221014042c40c0c40068015036041d02003640c1c450044100d10b103003114040802c00301c42c4d45212550210110040c0710f980c440001f12415401481520142c80d0b02c80192656503100c02c0c00d02000380b035504001c194450541d10310a0072114000450b8244610403015175074502c84000c100002c2440400f005a88081000000706406509016190003003c80360020051070501d080d8401c15611681302086c0500368140c0803c2c0703070b5900043c1e83c004403081510501080d40365042100060f20521004940c10003045c1c4007228040d22201c5080403c50151400c0741c6900808020001500d0a15401512200c001c0c100414180c41483c01607070301d480d44030500707400485010b0080344440c00c0c40c900038848851070130013000312190520070650310440301406802032100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419929172 1250 419927922 419927933
    0x6150907080a050606130308090415032021010b0111011a190f030c1806050d03050c0c1c0b101a1309110913090b15030a0b0103031106010b07 62
    0x2070080c40703614201d407900c0209113941c440c54100c0e050a80c42c8010440840e8890a040350994040705400e0301a91402103610a80440920a41d0950b5405810042e411400c0d00a990300c00984810455200c1602034000149543e04814034500d900098004169400300c2d0740051325134410f00440c02c1081c2d052180003041009002c0e8440d041160071100c4100c5d52038000040c0b02c8240e5940c1104034203050b460400f2050090004a410495441003080050b044140d045142580c00314840d20780c01c030401c1086100068002d01c080c11907070300c101045030345498903000020011002e55810180e81e101ea000035105000c002100c042c1d0100b40f0303c0c031541008d85020510383e0340006540b1200d001610100b60080741d822066a040000c2c01002c01c144140510004a15140e50021882921804030040540348500f014080e203011140c1141c910303040f03a51036030746100d20017025449481d81401580e00e40400a000c0d401044c1c0030318000c0c1d5070800700c1600505964a000070682100106a605110b1040080d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419930422 1250 419929172 419929187
    0x306180506010e150423090a0b032b03020a0e030714010e0405060d08070c08060a1b0c03170c0903010203010e09070512070501051c0c030b0418080318031b06150907 72
    0x408114505c90305150000c0c1044100942c0e11201c0e078080300d804240302c0948d0140d00420b42c00d98044043e11541e030049c00f000e8030600000e0001c02d2040740b510140700c0c0311078006c0d03010b81050708072030030200309400e00c2c100002d050034003d82084080c400e0070011000c003560320601c007103583d40f8150343c10843e5003407a0b4006481c0400c4a0070040c401d0000080d01c0013002a803104400c003d2414004441c45824000071b14806420204450325958600340d98010f1614403642840d1304107605a00c50700d00300039502c9240c03843c0010040a1400f0540108900102c644091004500824000c8480445070426500e0079003086626402103100700f01004280720b00e4400480c0b440119682400c0c901c0d13480c203a08803c04d008110101c601c10509103002c01450b0080d8258010102e030305404c030780070083c007181c0350040d220141500c900500481000e000080540004402d1404103170680303c2100d040c1089144c1c1d45030a0800d0361142a80758100609100070b24101045203504024211081c0d1850300e00114002e220b078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419931672 1250 419930422 419930429
    0x7090806040f05010902060a02010c0e06040e1302041815151a0a03090204051e010f08120c0106080303041a0a1835130807030203070e070306180506010e1504 69
    0x54080603107242c01c0040c258082c4022541c0a442580c8030b000c81d98000e4024010b01c40003001041c481032006046142c0310303040358140c4401541d00c41f49600d03034110020345c0348180b001c1240c00990701c5002114050721400e11440f0700d84100b41d600d1509071685150401c0e1000c1c0c42d07c0550f0040b2a40e030910000300b01414600c2060680111242c03502c0c910301c002c4020300b0f0f0091020b5041440d09041c040d8071f00c8401088201e03182682c03040000d50741c0c1d481c2200d0040c2140e203d003d9181d001018609402549017000f0201061181e001084442d151345016003185c3c0140d40841c0c00b01102c0505030600244904125444400c1500401070800c51000e105144c0d020444020b0120f1030b03940407041080519480059511b81c46101c00c40390310075100600000380d00895001042050005000480c0d40700001c5c2401502d50140142c40400c1c0381c03140c1c2801e11030011b4452014503490b10808a10091a006c1c0c01e0f1844031668804500f500b8000005001d106000b043c0038025000c6510800b040703600d010440d000c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419932922 1250 419931672 419931683
    0xe0402190f0e0604090603120801030b0c070503120901020702100509030601050105030a02070c1401120e0307020625060603030f02060f24030a060e01050f0702070e100503100501060201050709080604 87
    0x7181c00005088400240c10754072503502401c0400c012581c500d181d4002800c0c0e038420006482d00807029602540d01c0b09007480300420b902460000504a070240a01030506244140201c03424004842d20400c42da240c110703002100380c7e602003421001e41c500403007035403880102c0341051454162540c0c0404d07220981402850706020000010440d61402035045400c802d40005140034410f44401c04454000d000c44845400126440c0c022111701c2600d110343d802c4c0040d8100194a0304c0425801d00000c0d42208164082400c01d0441000303003c0300e10000001441e11400300010070038210714018045203100d05c0c8070030841d408001040140c140c2d42c100c0b560030851501c00d06c2442e11540503428070000119140c1da4150017500c1c0f5001c00c000040d00008124484240207002c0d65840362220344510300300701c0350440143c1c840e500c10001200c240f140541c01003c5e81d04c045003055290300c0400c1c83c1c0403084c401c10540c07075520001001020390a10603103800203014500783c0c9030140342105860340e8100141c4081d19 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419934172 1250 419932922 419932937
    0xa020706030b0627040509011a04050408090a060f020d0509010c030e1203071a010602030a02030f0904320606032404061d0f060f010906320a0e040219 66
    0x80d03907035001500e820408559855088402c03e44e0225600310700c00325141e003d40e0601c00460314128040c0a10920804c43d0316514001c2200b50703080002402d00500180c4041504000a0350b40d5161052810058840303525004142c09103204002d1130003019058082c1041024000840680e90120007400103035014602107024400c0b4000181094540c0039000e0410710000400c0010014411614001e010008002c6e8806aa07a200207903102d05c5083c4003140160810015150000e00c04000340112820207003002500c900310049003240540c2c1c2c0100342c51004e07000c21510380350808120200354465001d483c101d00310f0511160380f4400e40109000e250901040c0300402d1420f44407a40f102c0000d240c039140c1a01ea900010703948041508096072202c80c13000c4400001001c900f8070b400d41100d4410183c3d5000c64240c40c01400311040081c041d401480c035410f421844c00c65402042200b100031440c1c5540c4c9a50720b241d0a00a044000b1081c026800780d801802450040b04002c1031800310164641800c19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419935422 1250 419934172 419934191
    0xf0106140c070b031503071d061915050705010b0f060d09060e011d070f031509111002030306101b14030706140103020906040203040b18030c10050f0c0a02070603 71
    0x14100407954100e10f0b2031030b90100c200300c102001d0301d00c1906410303401d9050301c0741e864075814240203507849400100b44202e207110114403076040042040c21130108030340903c0407031500c42c52045808030140d030360100000c00214050042c460203100d00303002e44204458002601c007040f804a89503018121804000943c2c1d084c589080c003d142e00300451545200d030007008000c001401c40a07040030310b69a07400b068815043d001c9400f1001040c80002d0f00d81084201d5440c00000392114040c010626040303403130001c0381c0305480f9240c0b40d01905034110002c075001380d0345a107015828001c1c42012000031a041200b00c403c0900c1d25072842d4907100072640c02005645074481620101071441c890454020002460007918002d0040501d9410b07041e24400c8450b000c1a490303150421080c2e000075a4040d0040800344041143c644d01c03503001c045c8850b41380065900f8040c90030041400d14441144507011640c0b038404009014000c071100f945d200d41c00700783c560300317100415100039503500990068005042d03854042c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419936672 1250 419935422 419935447
    0x307020a170909010f0611060c07080703120c080402040506010c08090603070903020a080d02010b0409081209070f0b07050c011b03031116120f020f1213030b0c040e0f010614 76
    0x21848094040c3c00345140e03580d01c1c0d0158412504a200320000196030005118081d0300206078140036058850b2a51b0070300c0c4298840404640c80070304100c081c4030014020507042c00c100d01a4561044040c1c6928404d80b5003030052205070740c80100114100036030381a40f0000a0341c0d14040e6144c020041e16030310340300c4d42c45d038206035511403094001952054041c140060703104400150b1444e018401c0c2c0c0207100c520781202c10310040c2d51440400078020300c01841264184a08070a045901003d800116504503560340380700d01c1c0408071f9410803a60b0b00d030002070305400d000e01086607c00c140400c1c03801450b4040000001070006120403001410103803149515101104603000b5500400f140901440700d401c005c1c6000d01d10b0240d0100c507c80455080c1419101150000c02e0038143d907000c1202408810b1440c0c0e040c0740340ca5005003032110322143c0b02c0b0f20200114242c03031940d07849034440c003090315525402c12020f28070f0b80070001d01055030200350320018056190b0002400044007111004203846940b002880c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419937922 1250 419936672 419936677
    0x102011d1c0f022d0f030a020f010c08010314010f020c0c03070f030b19020702040c030c030e0c06031522090314090604030803131b0609050a0b120603030c030307081008030307020a17 80
    0x9644602c00e0217003a4402d60800f100030080c0000c0341c2c08403200700d441c0c1124682a00c1c2c602c600300c00856400001080459402ca5400c0f440600b04000001c828041e403040c481240c11602071003583d0740c0b00c912800501c0c142000401e000c3d003c401403001da5249540c1e141144004010800328400032001c2c02a0350200198040c0d600031940240b09200180e900728000303004118a19603040001c0c20285c07041090030011920350b40c1c0f080c0c0035240c1480c0d50342c8c802400c3c104201c0070b100075402085494440c5948540508000f000080302d103000718081c0c03854100242140c030350001e19080c21030200030b0202c1b0303681d420048404607039210603115144e03600c4040c03221800820002c007901c4d042010b55010019001841c010043e00c155840c0e00280c25101c0044c890500700300d0050158440741006002c00c0309078901b683e039600c1000203045900e06690030000a0841d0402e03250741c03010030030f0700c0c0070300030405900f850840181c02c81d28025811403030203040007592038214060241840c000090fa0342c5214140108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419939172 1250 419937922 419938003
    0x405030f06192d050f010b16060209030f060f0708090303070509360a050a0c020a0b150303130501091401120515120703050c030303010608040305090102011d1c0f02 72
    0x308003c243e4451541c01020b80030481d500b600d2421040004148170401401b40c0d050040b10b08001d4025540503980c202c002e5003c0141c4541c140720380501018070030410068180303e034400e0420300b00d0078240150b01a11401003d0701c4284150001d00400002c10b501000752035200d1000c80e070140c000c4e07040001804804041096454007040c25590b00101841316050050051398481400c01080d580e0307003541c0049621010048005800c05a0749a020030020f08080c0c7d0480c0a00c81c41c000e03a402c00c1030020780b03940d0200c92a00340b180c620000800070b075a000900500245102c505030075140d0750380000281103034002c20420305620b968401040e084c0301100c5000c070342d41c0d0004d002c0b9600002038903940ca83e1052039101c00c9420b480b8100400c089418007200f034a0484400d900c0305851a15907503015103480c0c10045140d8115035a80c480720513074542005070f104102101001030500f44d2100c00d011049041c001c0c14020903c005500740f20f031250740c00154003550880300a1a02070007203500c07803801c1c0070500381c15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419940422 1250 419939172 419939231
    0x2150307181211100c0807210909050c041d36071a1b030702040c09150c0302070501120b0d05010c09080d0f03020a03090b09030405030f0619 62
    0x807004200c104468108100041c020340c8032031007401c40c0d10108a21014003044810000d0101c5904100088102010304101d170b00c10305100080c4812004405143d841d01d1800c4000180c00380d4040204090038031031140c212007140d44444c509070801c180d401c88154461128491581880c000403184a40f600d02c448081c0e402c076030011102c918000010081c00054030034a0020b000d2448001009a0000340f6913602e0004041c6850620061000c40c000c500041307481ca42c0140810001e4500513921b520880002d107050b0b880b001d40180c24141d41200e6104411110018041c08a0310100403a4001a6980441d9000d00e00104401d41182c85040944031200e81140c220900320720b60300030020f041d000752000a400f56241d2036644d41d180c0c5082c0e680c01114a80c03002240b001a480d21206100750014412141c0da810003180f083c80f42c2ea100d00079010100e03400c2c1380036040810244003625007031042100d00707000840281920700b08003889403076105003000410070706a524600303041c00c0c50704051a04500c405c400f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419941672 1250 419940422 419940467
    0x1406180a0f060908030c190201170f04290103060c0210050c090108090a120804080c030307121a0102301602010f0309120809030f0d150801050402150307 67
    0x19001c001c5000282d0041e42d000c590104004507054000005032030700001001c00034140b000b910f84400d80c00781d02e0900280e04110b100820008641c0340e442c0c8141c02003007007040100c45840d2030705100c00440031440300010343c507407801f014086401c4a4804c0d41c0c156500050009404594030308146e250a80f440c00c0a9005400d010130000349044100207808100c01c00e0703e0344000340c1d80740e1002546560380b84a00505400400411134003d07485070a036507905c40d01c0781d61014a0000c060090320314513041200d80d2000035090400d90309811080d03008103102e281e4801408101841c0c8007001075101c0c4a4100640810019480030302c0c18540c206201c2500342c100f4481c01540c5a10702c42518083c12051001a1b006c44c0031999503981451282c4074048045400005c11240303580d01800403100c840001c1c080000502c4103001c64440710f40641c2c01068101100b41740007416204a4804030080401a404802180d04d07060800000d030311801c084050480d081070b52141d480d80d031038a082d200c3c49664044a120340c0c41c41e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419942922 1250 419941672 419941679
    0x2042706150206220c03170f0c060907050405060a060c02041b0f0212031e041a0a020715050106020c130609050c09010320042c25091406180a 62
    0x410114062040d0712140f48400116014002a00c1480382e801071000c0842c1200b000400c00c452000046600101f0666107860010103144003560003100007104280c00000900c841e0340c1003002504014102510309100b11726000001424010360f0384281c0f0706001c100f5041e001195140d5015032180100440508040c0c041840014840c121030b16402c1301500c221944030344074100d0b5030250780c070a1044003100d0b20f60f8038140700e55249841c0041d00403100b0301446c4801c60740c10705051924a100b0240e0b000e0044e00c811150420714140c00043c12040a540c0c82c0c00300500106501243c01c40f10340e60140c501c0d414480c0240213842c0240702c1680310241461506040c04281d0601100800900100341c0e401d022460700300621341408054902d6013280300c0b400300010410151107000340c06040c40c0c144500300e44805851403003610500210b444180d01c2d4641c044030f5a6610b2010603c2c1c011074668506071400c0f905000030444101a8140040c1c80303100b0120780166400800340742180d14501c0a40030519240c0d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419944172 1250 419942922 419942927
    0x1020304030f080c07092a0203090405010b19090305100506060706090f031e0903122d110a030f03021c090f060e010e150a2901080105040204270615 65
    0xf018011a43c0a0174500041441e02c6001700d0180c0d8010040c01d02e43e0202000c012110002d40e0000802540400c0c45a01c0c0e190b40d40d445910300071b02800d40065a04c04405d45030b80070050715a1514000e02c0a007940c144007140d0001003104a81901c10000115600c03000c0001d0494000c0400c010036581c01d2020000410001a50064840d40301c0e4072040c880600241c1a20086c4a101e9a81030000e03480d240c0800c0482c204d503030300d001340110500b0048079403151048205000c40c00303d190707104101110b0310b41011144e801401c03203440e44495000b03002f0710a0107690090100011124000030140c0204140030019501c00027940c51030403011003080b49441c645003a100b41c25417044240c0c0d2039407401d0003441c10181c040c003507414049200f101400c69942c1c1d17030000740142c140182c441c2850561360b8041895050200c0c3d81070054440c4248060030040d0220001424070105070030050184c1c3c0144020001c40c21601985200da030b4003140a420f42c204c00d2200b9800070a00c0c0d80c80101504203500b0290070564 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419945422 1250 419944172 419944177
    0x70f080d02070605030103021f0e040f061805241306090f050c0a1b1401110d050903040b0a0f0c1b031505010503060f040f02060a080702011b020d0e01020304030f08 72
    0x10580a0b188119920390040c0c915010904c0040d410400ca900303800c08009961a40310646140c42c03c0000401500a0210b0111030005446582566403900107100e07445540e0319514020486d180203008524103501d60640401c0422402210441d60389100c61075541c0b00064400108525401048100e03502c03a00540908070321600c400e503480c940004181e00d421a44100c80307102e8090344032044840303207a026843c04c500b0412000c0e10002440003401d04101e800f07010301c0c4001e0070f0b49035040381c81d000e40c491500105c82000e441c0000981c0100401c00002c0009070541d40c0614182c10300407100c0c2c1c4201c0c1d00b41c9050042c008000c08908070709140c13020718a0701100102c00c1d030740240d51041c41c400810588030212503007030091a9240c2d1007040014080810700b4070250740248a00c80e0700055501700e5021801c2ca4020343d0503503000c00c248200b080020b40d82441805d60848441100c2910495001c0700039440e5000d14600e90200210001d030103007164000c1040700c0040d54405200803481100703040440e110b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419946672 1250 419945422 419945443
    0x207080306041a01091a160305040e07080402010927050703150e010807030212100e241005012a140d21020904110c010c09050a0b030a0e070f08 63
    0x551034010407086582840d80403000d283c4041c1c55015a450514100c20003050301c4100036149071070100303c1c0d0348003031034450f6548030342a20a44503035848508050100340000c0004121408024111007007002503a4000400740894070700c04008066001c48085d807414001141c0f4045051030704000601000e0381d80b40c0d0140e90070a6641707820300e1442d503d030302204051210070710469900703600c81d010a202500d444000072900041850403184070a02800001d010382c2c0104180b40940d030408410002c01c28035240c203200307401c642c40f03804030403c0c035085000240c5403c142c0100350400c0108100742c01000e42c60141c414440302985102e90748282d091034041c00003d22594018918015081441c500d0390140840c0c40c00c40d843c48555040c400b001d0001d190083d0041d40101c6d60042d00c40500841d4984940e00524000c3e0b0200d0010030725007048600a0701c415469802180035050700881003000100d07410543e604420701207408a1a41c000500b00c40c5000c82d41d0b00107001001950200040d4590001101c4842c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419947922 1250 419946672 419946679
    0xe0f0306130210030905070b030c1201090504060f0c120f0f060e011a04080a141507051b03040b120603120a05043002040b0a031709090c09011b050307060207080306 72
    0x50003901000700c064801140d0002c06c10360103100c0a01560302d03180b001e0b40c0d0044c1205280d9003440960748035085003080a910422a4954034410301042c44070310b0140341000f40c500b083c01e0042d18100309000384804000d8108030400340ea0340c04500c00070011038010481c84900141c1c14001d868030b9110002060400303100d00c44a143c1d0602c0401e0301d85003880d00340c40c00c40e180c03130b0b029103051744c426202c00989800040521384540503000102420800c000440c60007580103549440d218040603820150201c140c840b00c6a00d0f50040c00200550188901140c01028240c0d8a01600b40c44503000b1910700382d125015144105000710f070910615510070080e03c226038840a40d01c07200c0c0207046c1c1c3c1d44141c1140c01d84864600c280e0404500c098200390b000f038030041c07002508081010341d80e03403900e0840c10800d10f404855181c00103040506860018200798000d5038000c581d5250441220000e0007400d80c0d10608100c5c450b0000e41a001d00030140b003074410903604140c0555039103545146c6111140c0c02100c01621 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419949172 1250 419947922 419947939
    0x30301230d0210050c0703052b0e0f040906180b040309060e0d030c05030909070909060f053f010b12060402030a08090d17131e060e0f03061302 63
    0x8140342410303444441d180c02070a000000420f00d075007294180c1c08200014075500c12000004002501001800480d00f0300040f41c3c07150020400a074a60801030001c10010030a0040c0c81c03400030364501c0109404980300312400a042d8600e498620042c0c01411100b51410000100c1d0900703002071503003540d11540c441c3d034900140c251550301c141d8451980642880d0007401040040c00024080d0000201c0180110103c0341800c10b68030004080304001c8407070500180c148a010172803400303d0301880c000382c0802d0f04085202400c10010610368541c0841035684c540e64500345c1000c1841110102ca1404080708221220380310610301d0901900c2c2c81c07024030303015805240c41d60303400d40c40120f0f01c0c0c1e00070b0364010081c254040b0075807908071054000c8105a41c1c80701801c5100380000c2d4501100814800310119002d03102d1042c1056901301c2c0e500c513480300680501d804105040074601049140a4503524101080c6200f0030401164a01c0c0c5c0c0c1e81c0c0d29507050b2081405000c41c058401400c128003d00c202c0e107022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419950422 1250 419949172 419949239
    0x6050c0a030509060c03150d02041805010e030412020f010302040e13021c0201020c280810050a0c1e020703170309011b020d1d04090b070206150603040602030402010908030301 77
    0x307a03a400100c40e070701e2840c80e050020801c061441d1250280c0d00301f0090001c481104103400180c1210b0900d5a113181400d0382404820800c882030003582142840500a10304241c50510310030309012080100074403c101c02c41410382940c0c000d90544018221001c400402413502800c00c8145a2040405a200c0d1080e0f682c00058800140445010254183d0180900d10010014801c1c040b500031a100b400600e00d0400100d803620095050b00100291401411030107031444c0d200e41103d4000d000d84110700c0c10a0011a40b07a5080103503000d108904440c030022082500c00102e04100d420340004040f003544040000e5109002e074042d50198000800070040c681c1c244d08906c0c407198151203014056041495590170490150070324000c800311120b612640d402c0d2400000d070403154101021107502c031141f82400300a07981000f860754000f507080410883d04065000003031940c00700400045c8141c0d0000002400c5922a1240100901e884022a512561901c01d41d0ba074015080d6450540b600d911201013 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419951672 1250 419950422 419950441
    0xb0303030c0f03060a0509070f110606091911040b040311030705011407050c03060a141e0a050a020c010905030301081b0904020d03200d0809010c02062206050c0a0305 73
    0xda014140d505903007440c1001d00000d10089400c000c100740c1c0c0c007510017007000031961616183c05100c0c10303843e510301d030074640c8104001d40404409072414500354400c00400c449a116a01603642010700c9842c102810701400040c407001c1d0201d4100c82002205c0810000b501c1014100600f0030b0304d2007081010465003100c010315075261100d200c2c0074009020f0a1801c00c001c03419000038801b0b80e0060741034540310500c100101703107800c40603613810350b1196540030302c1041c0b01c0c0340803030380e0b13400090700c01c1c3e440d42d04820310301a4214024003420b40c046050b40d0310003040c41e290304c0d81d04603812992500001d1004101600307216071079400900c5000d401e0301036005c20b40500c0a80c01012000320383d000701640700c2c0d40c0302d036000d11480c415a06401c40901078500c00c40800d525840001d010081c00001c0201f4903400b04800040030003201402e4113180740e0502c00032401140d008580154000030000b51014060b02030350030400f614000d140c014180502d0481031000ea100c031071005112883d0703151800c0c0119204c00980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419952922 1250 419951672 419951677
    0x14160b0a02060103020418050102040e011e0303050901031d06070906121e020f1201080a0201090608060d0204200a02160f08031204061d0109050f160303050d02070804080708010b0303 80
    0xc1001600030030b006000614165100c0e5100c0700307403a505828081e0701c0350388007400caa0060f08000d10b030600f40b00040060000e200700000741290801c100f045139501c0c641e0082c0c6180507524000f2706140d01c2d00075240c1d00641410042c003d90004800311801030800710806000000280110000070700300d18150034410442c4d00901038000c80c500c50541160980400c80320081d0000707806000e00d65400c011241e5005400c0303030a60f018080d1840a40802c030103500c0050200f128990013242440880d00030054141d40f40b4154a84164054401058120403030301021410100e10000c5030643e40e0203d0101c1800354000b0311082074003d00103518050b291195540701620240c0d100d6902598406c0101c1160400780b0035400d43c00520800010801b041002c60005564004909811a9079501c400d17402c1441020480a818400410040d14031901c040d85010401c1174503000c05410704c01c0001d4844c1070707801c0d0f660480707100039040301c20207444645540d00070b911800303580b107012115800c2a501018500d400b108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419954172 1250 419952922 419952937
    0x6020c1006080d031a030715080708040c121a161404080715050403060f0c08060f060a0e01110714032a01140c01060303030b0a0e0408030103021c14160b 67
    0x4005261481c441180a0440f0314060100d01d401d01741c14030101e803020000c0c04003614410b01c081071038025041c401880c1c14401014842003090307480a2102041060031203000f9242021206c102c0580603080c0300e009050326031251111503100404002045807004080c4440f900a070340e40701d9400d82c0c400c894108a000f28080c202c5113410202c01049081c0802071129401e0146080950510780e80c0e498810444048504c010409034880e4a00d46625902c1040e044d44440103c4085040c420160f001c640c0c40e01507048610f05102c0c1204c0307100700d42da000c0c0e50301006c060f218030102c8011680381c0e01110815413200400b01e002e40300355050b1441d886040030409112059001041103c41d100314011030b40920800c804004100d020050802031010a00800b406035029440200d481da90030020b000e841d10320366002d1444c100030b8205010006001d0011070341100d070100c0f84480041080c034400044080100c000500700000c46440721500c2c04003081c0100001b100b0001c1d40822656001191590300c9080c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419955422 1250 419954172 419954189
    0x2090f090705032805120304030210060803030910020307090b0c0106063506011b030f1404050d02090a1b030b0f09040f0f030201020c030d021b0d050f180d06020c1006 73
    0x11111441c135094034102038030240c0104100c80000101e015890340d542e000341c4043d0010703040001c40310301410321809440000d0000000031843d43c5400c1d00c0040d1248841a650b2080e207400001081007244603c50030800360a026289540d40c01030020000e00800d0148183e0011505005940408050b04c101c01c1161003054000700140192840f43c030204607000070640c60510604855000c00040e0604070710002c43d119032501a40103240110140820303c45d90400350002e18104418060740d200e8412544000d0390580716841680c54081048000c1c01c40c10b00c41e414403d407190002c9942d1a0700d41c01001c00e0440a442c03c0044400784418070030070074001c40b00a8158080501c40c540015003007150b41c1c500170700031f100040c2800e000071401c80c03c55104c40d403c0c2c0344154000c20040a00c170090218600b4182202d001001c140740c11007005881406014903100101a0102c2c00f40c0210424135034011f05003800421605060b000340c5801c0d0000d4002d0032034040039126414022410f462280725090980b131525 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419956672 1250 419955422 419955463
    0x51203120c071a090105071416170f0f070c050117061c1e0302070b0726090a0f0905060910051207030204060e01061e0e0d0f02090f09070503 62
    0x705240500ea0707000c04000c84521650740035240070204100c1d001401003204030004101810005401030aa54540320070000b001010404481440400090514101e50080c0d08520310340020340004c0d40e81c0100c42001034031840c0000e510402418900041c030001d4841d041c0400c06e01d031110011507503442c0300e0384900f10815244000c100e15180001d000000c070000441c1402150603269980c00d00e200c000c80c14121098103031501c41c810947c050280c100641001c47e0510304003545a10f821801f80c1640009204000d2803000994001000340c084580c5c00c2c4014005a0500d5076031214942d4402b25403151440507840c000102d130030b80c5044a1114050352204050549941c104810040b520050259140d42c501c02e052300080161194041c41c00140180c0e1032941085d85004000f40c4419000c2590b8080100c1c12200c3c030030641d40000c2842d000003800c2d60820916034461614070400707401030320003070340c07001500041002c142618000144507805007410b0703d158540c0c0344281a030b25540c00b0100585410340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419957922 1250 419956672 419956681
    0xf090a020604091a04090c090c0531030c14090a0e060a15030b010905060906011b03050f0c030c070f080d02100f18150c0e0612070513090605120312 65
    0x940c11512091310313540b401070b03d1200407034000b80450308203030360450302c542d41d03084204803c80e840e11560345803076400d080440c540b2400c2100c086600c81c0c3c507002504011500900491081d08147c3c009019541c4011811403441d254401d900c904001c0131040d0f44181c21450000f100341180b4015611281e6005004141e00d894100c42003018046503440541c2b00625480c0c000301044403000300320f00800100350002100e003050018844013000c010a41da050203802e00c214407a29000b072803d880c5964061070081d44880150485007007901ca82121a6010310000c50481d183e01c0c8007040002c11940641c0e088480d1955410b032041d10b031560b002a05e40542c1200340c032440c001c02a508100c030f40306164003001584200403a21045031903840e03002600c00060182d03030584c01c54400d11840764840003504104a69000f442c0c0003c5d598802d841042c940c0350041408540a180900e0503144e0070400d085001e64015110440d00000f000c00707100e003c0c07041d03203ca001d2200d144004011100501c2e170680981105070f89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419959172 1250 419957922 419957939
    0x30203040e0a020c07060e1e2d040507030519050c072109060305011802130f0e0a050f040b0103060902010e0405130203010510060c0f03050f0f04050f0a05031b010e0d0b0f090a020604 80
    0x542c8d424003a08489414140d1103001d400110004291042e00b0808500510741420b006c22164020214000e040c42c0c0f00502c0300134002c0c070010b080a0100f0807000300b050354404010b60f215001700f2000500c41c1c1c8141d100c142c0b00890b040d06c510403080c42603a55184403955074608500b529020301c9600b43d40307505221000340450580e0003d202e29000c0b0f102c64100f9554410301486914020750080c4d5000015030184000d00d5518000e454010030540300c0300d000c60600e5100c50260315810b101c02490107036549404421a40210318000340f2304030041c4100701500e0140207000c0f4002e00160101e100b03500c0e00300003130105803241c448034040d65001da45055420768695035a10412107062015810700c58140302d21038806003000002c050700a032a402031500d5924220038002c035050303130000071ba1243d000b49c40140710707544000602030785441030015501b03400e021b4000140c5c5c074075004451494000341d0000c1c94002307120410303003181c0c0511040049a407040e550108256150a1a418000d40c061001c101c2000400b5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419960422 1250 419959172 419959219
    0x30f05060601172a0307020313060201090209070f03090b01060509120105040c030b04020a0906140414190f0204080102030103050a230c10030624030506031b0d030203040e0a020c07060e 81
    0x1440440110031135204480c1642641003107808000581c000110741300250100d01054008080c0f07800240821000e590000340075100c0106107500700b1200c9950084424481d8210708142600300c2491500d03940c4407200241994440343d0910b00801060500c18404032051250a00c1960412410119182199114404400060011307a401040040c002c650700c01380c0e1056000030502074000b05285a0000300f0700c4103455080b11010802064002000031122005c4aa401c0c4134400c0c880c0040c4c01d42c00c20f14060000d0140340c010308525840400044100400060032104031402440205159045004411601c50310340000b0451500060081780b114204482043e070702d0381003400c0222b8510f1b2510501810340d484d00b22100c003c504200089510a50188a8183c10074415000382030800300580000c484802c0e880c06450144035085031013003d1510a2040c0d41c0901040e44425010781442561f0002a402103449003105004240e000900386004004500c0d10440c0502143d009100c2340703070800640e6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419961672 1250 419960422 419960461
    0x120c0304060e15010305070b070305031602240f09070312030225050a031409150f09101806030911280815010f210602090a030f0506060117 61
    0x115120303003590b00c146800f844000740720507038880a901c0942c5035040c1286001600e5100d150544420404803003c20b501c10300f00c3e9480308110000d004a000440cbd400c901e080f00d40e904440b096140711641a050904076800607000301854059600795840d48000103880d5140d61000a003032401c00d06052a47c0c0780683c000d0a00034100c030044041c840307403d100c1c0d5207080041883c200ca664101c400744000b00347c2c01c541040d00700c3c101041031604003210040030420b00b403038058142103001404201070000240c41d004039980c0100c0508840d411275080400580003001010b0a0b140c0b0003081e505c045981446803181c441710f10b80100b41e40246102d00404c0c0100d00d010711051041c04804901424400c103c02c250b440010280380f80100458081032030620020302d01070700403c2820030f40d0401000500018074600200c100e050100740c0d0529120310b080710080c842c040d400f903042840d941d0000144280c0996075499140200c096580503030318080111800c0c00032000b035400321b40801c4081014601040d0240e04007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419962922 1250 419961672 419961683
    0x209031906024807050f0307031208070f02150703180203120c010e15010603020a1107080c0109050d0f06020c010b220b01020604050a0602090a050d03090515120c0304 73
    0x18201d802402c00b4a000c0c0011150014910069901c81814490f503442001070b001080308103182501d0150301d644850361442050712903032040002c090280d5080c080c0100230340e8400200d682100303440358050500c82003298500c01058071840c0b110001400031401d80b40081c007404c1d1034041540e0f210400d400811400d190800580e80c1980100300688040268603030074070070300941948500c2151050b03401d551b1005034440345c58000800700320403c0200d42429054a245003005600c44800d03070700449113041401070030b07440351059041c001220340020800117400b000a0303075140d5615850303009021581c0c40c5010700512002d06d0140082c08955640d001d0704000f50300c0c174004105907100c0000600c00d12201007030550828811070308408a50031501c142281541c0a0010740717001d2810703441d01d946801e00000e0240420b600002e02a02654903502d00c4009007000900c1c1340001000c90500030800038850003140c0c001d13948401302000d0f5860041c190780c0344546c0d6254202d02030b610301040c5503071500301a01c02c840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419964028 1106 419962922 419962927
    0x90204080c150c1b09010f0b190341040503030f0709030b010303030213050a050a05010315030c1829100924090504020903190602 57
    0x3000800311803041040d990190000c26510032041c83d003825000780e0b583d135500307078210720344568030804207992a81031a83c0301c140021540c0f449010f582e4003407d0500c03050600b41c4079401484014041450003040403080b0180c00801c8490b80c0740740400241525100d5290810400f2400c00064032416101e512802c26855250b142d20010306510041158500006c420a0140f05035400842d4410400402517940381001802034004416864681c2c0030703582d0004052401c2c5190b0300135500000e00500f101c3e86401e0065005109803511000c090001034400004607124441a000030500c80804054140304440c0d041c04890104000300d55034280000300c024402c228000d0200c50840c1511403050350107290302d00365038240240d8003003401d01c869242c9103c2c020114114a0808080c0c50700d13206c6a458a4500700300503401480505500b5134021308030401d1801d445001400c29600800c401407 = true := by decide +kernel

theorem cover : BRFrame.Cov 419784172 419964028 := by
  have h0 := BRFrame.cov_init 419784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419784172 ≤ n) (h2 : n < 419964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
