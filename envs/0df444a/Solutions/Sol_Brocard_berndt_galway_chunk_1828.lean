-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1828
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:13.159972+00:00
-- url     : https://prove2.me/submissions/ac652c54-497b-4cd2-a1c8-4f5c19ba2236

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328597122 ≤ n < 328776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328598372 1250 328597122 328597141
    0x2518020c060105010e1318050703140f2a19060314060904030f1b06050a091202070305100e0703080309031308070e0412180b0a1119060506011205 64
    0x803030400038090340508000001c055000f10b140c841003990040810f1000000d034103c10009098440240480c12601680d40001920401c100c00155002e460150011030052081c0e0f850041700310000c021540210409607540481c840d00002003400ca60140c010b4490f212000c18408544102158003113501c148001a40f83d4140c1c2c84540d884a003a5502215607990b00d0920000b00380550300100007891025203481020700c210842c0329110080c0c0c0318803201e8521511038a05079401910701403815555601e020003007004000b00e2043c00f00341400680001890354852a442d6120a5441128503032540c401d001c83d00400e002400145d40d1041030b26499042c182e9104d95a504a4040481c025003400c001240d020b1001403c0b07421100d81c0d00c0c0a05166030b5907640c4884608202d012401032001c0c400140c0c484400288624024111612040c0c2d25031020b0180246045948806c4404642106140c0031525544480d60b500c099082400441e150319810f0049541c52000004801c8940c03810007071001d0482e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328599622 1250 328598372 328598377
    0xd020903101b0e06070b0402061e0a17182109040905100b090f0103030e060d0c0e01020d110a0f111c0501140c03070c020415030b090d020f251802 64
    0x108998591000001c21418402e403171003403400291850560340b00140040c1340402c01418804855850721088110030041c00420380c00c01540d001c040b0309a450007201520151341110350203c200035140f040c0001180d0100d480c1e00d00409404404181a85962071410140c411503c3d24a00a0010054007089040003a2517242c5000c101450f6410203000c4042803a1001d8142c0c01060440940300e4240d1969406a0b180100c0445081d0006400d120401c00784241d4401c0c1c51000b55903440d0b40e0038000807000028200402d444200081c03202c0c01c80f80544110002510f0301e52264021075102c0b01c0095401d01c411206104120303e50b0000707100c0c010b5141c207a40403e212107842d10400c000c0c00b01415003801c1d42c0046404030740d082005a01400028401449a18801e01050000d0000500403109404060607840160003e41d1030951010a1081c10f080412000003084100e03c040c05400904102c5107480f0100f880d082c03800c41c130510f15626110781c50040044020000f0b604c0b41640643d42c070031464080d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328600872 1250 328599622 328599671
    0x7110f070f08100b01050a030c09030f03020a061d19050a0803100f06050f03041b030506090309031c0c080a1205070905011206060806040c0c0512040e010f03080d02090310 75
    0x3030051400481c4083c0a501482c0700c1d100c41612002d0401b281410200d0050010081d08001c00000301e80010220313000007440750003103020354007400c00c91103181400c0e0305513400181038203440e0a42c010240500c5e500030070b822a40c8001e000c5030b002d400360207092040c40c01009620281049200000b4030500351002c1039a40c044031207020f0461503841e42c4180c140c6060203501c1d10002401001c00016000891084080d2580b184141c0b407880001d071241ca80c0391030141c0c1214910210340c40001c80b000185010051a000c0303030301c241218107104984901c000e003600c00d4002c00400462021464400e02e42c050039520010030200c0108004900d0030400041540c05c40b8451140030406000044c901140d0a018403801c1d550103854815035900c0390014030000b002001d05500411105201510014000b40840b46202c0b00d151015529079041441000700d11406034080340922203054020000208a2403e54072442c44102c40180c4950088000c20306019104e240441824640900300306410061f80c194140c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328602122 1250 328600872 328600889
    0x2070f0203160f090203010810020318060a1a06031006030b010203160c051e09061c02180619082a030f0601080c030d2102040e0112060f0c0807110f070f 67
    0x111a9900300c2a4101d06c028024940c454000444c00301c9100da680d0011a0030009401003803a582d544a03103d1414520183ca080713007166220209184104105070b05070300c2e01c0c03100311703000c600e18140420941c420450078407800c402e250721000b00018582c004d00640300403440c4003040310201c0e039480c90131a8201009020f03e6204800348441c800f0901040880c50524030005800555207440e240100107100031000d01c807150080e0701c50482001070b1200c00b5103e80b4420002e849403607a0900c2400c0141452081d00d01c003240095140003008040800900c80c1d010381c400411625600d40c0480d4080300603003045124907014412a5030310714a000e800680141255003841c190343d013852000c020951030300c0c02c5181d05400a0b520b044130184400032441e0700b40004100780c10051074175945d0031001046507000d900500c2c62100d4032104070240041070050380300441c80030354100701407000d040000c1d0504001801060810114200320102c000040201030b2250600b0f408680030f4503940e1144800c01112400740010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328603372 1250 328602122 328602149
    0xe040b0c0304050d2f100605030a020a0306150f0b2107170a0b10090603050901140c090d0203010f06030201030b030c03030301171903080601022e02070f020316 70
    0xda0400d0181500c0c05268490003601c0704408100040351035a0804000c0492500c50b804403a40d15a507450703141500b07021810141908151203003c110441d017503607101e64001d030012031170000145d1b21640180c0581e81c0c04035000a234845480300e4111080030a40100023502400000491400c940b10064001644010328154022000540001ca004415102c400108070120700d00c00c141d28040d0b088591100000c68006515052040040d41e900f09004002020840412050040e00d0345030164940c0202020001d20a40340940030901d0503801c004c0c002c0c8014540418400c40d55551070300c0c40c02074250000c00901c50752500880410062107079100c12030200740383c5000d10f07000341800300b1a0040810300078051400e41e860300381c8004245420a10510150042e01e4210011540500140c0c1c4424001d41d42e03260240b4110001a00d05040120300700c0c880f80942180d044520a0070380c080000072850f440141c0c0300d0106145c540c0c4d6100a600e8025850b00404240782d1074080c0a4170100120340c004170742041c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328604622 1250 328603372 328603381
    0xa02040b030f150d080a0f1b0c06110c13020904090c0303030b1905030607260a020409060b07020a03110102190b040209010b0a05160807050d0305010501021608060105090705090303040e040b 83
    0x145101d01c4d0020085017090118000c485d000303024a440540e16070410002d0008a08110f0f200e010509000b11032000c2c3c0b0420511000e80e101c481540c40700e6181e0010601000300c040000d4010850803180c00c4d042e900051403010380e072110340214a126600c0260074220b66103c2c07401078090608192054042c00c007040c3c019100f092800d10900417903102a010789042d40794440304a417030b645140006c0d60703040c1d0504600780da00c03011100c2071440b0b042040740050306d07281070041c2403041d00c096501508050707001340444c0740941d9071400d5460071640d004032030070503e01060006070b06190842188101c103010341640501030064540c4a507114900c00c5a158003142e0b203454186103e40954100840014014020b2100b1300302095a69546540140c01c010300788601641c4007458000400c81910010340c0b110010800b45d41c040100a9481900c00380b0354a4441c20008000c1d07036144140300c1c0354490340c41000801c94040c001e0f42144c0041402134162640c4d280c41d00302c11590740740c3c10340381102c6a14040f800038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328605872 1250 328604622 328604629
    0x8061306020c0f072904050f0d050703060902010305010e060f010c060b120a020909030301030b04060f02091f08160c0308060a05040c0f02100515060c0f010608010605090901060b120a02040b030f15 86
    0x80c126144035070b0140e013821f040c0418032a04442000040750403e4002802001040040007501300844c443d000c0443c40c1c050a2000506595040e0b10040a9607541c80600c40c90340e9030034103840711441081c031382100206007d06024010f0000001e420360002034000d00203224401c0494003441da07900031b03104081c0c2a2640801d80c1e6980c4000d12018184900c04400b04000a01c80c2d08007100080c0340010260a00c250036001944100d03d030030481045ca8210100040840e400072140c07648a6040c44c9402c035820307080003000d08580406400241002038405c00212150703103c0d007001c4060003019000b0044000a00c0c03002e02960703039502c0280301511528080104180c0603005062094070860740075405641c014007400f034282c116004411700c2d8080c2d409110780310a400d124040003410b02e480041580340c901010f01512480140040c1144d07410120180949100001224a100312410320710010b0355680c101640240140e8000d10f03200341002080c0001c001121300050701a280d44a0398800c41621881003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328607122 1250 328605872 328605929
    0x6090e07050922150305010c140315010903080c0102070312020a0504090c0c0b0c0310061e0c0f05060c130803130504020901112b080108061306020c0f07 67
    0x10039000803010060718506060500320107812030480081d80f49490384480d82c1c10155040458034040d010b103050010014170800340540c40380901c6030308001c403501e8054010040c880c44014108031100340c0342000040d540e40303d10900401143c10551136502e4990501da5a4082e6000c41c406600042c1041083c4d4090601d0f03108035400c00400703803a054501481d000b0018040d01412240310103122482c0303180c2c40806c80300052680f09004070b02496949140900c4c403003210202c2038128108108214900b0801c0c400d880302c0d110680f040707606200104401c145400c440020a45800412902804003441450184003020340f00902100180015480d12606525a64001c01384014070b086115503082029050590040c80000c2061404c3c1425100402c0d0182c98540c2c3d000c0c8031040700124651070800c3c12030446407038444504a1a0009195140c0802c80f41c2e114030250002c0010102d40d060003040101c56411164108000820f5640307000391070003065210856403140c03036680034000000c1010080104032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328608372 1250 328607122 328607131
    0x9081206181311100207030303150f09050a1b02010e0d080903030406200f22030f0b07030b041a1315060c1b15180605030a0504110a080706090e 63
    0xc0426290350b24968a15000816241514545641c610381c10700d9450f07088215024240540090450038514070b03005045408107038544124400c2c032001800505040d49128044400903403010030b41d80c9a140c0f4050080013170717014030717050107803007604a045568041d000f25900c0501201500e030300c062501003e1391100000c4513409004d400401c00103001802c0f650000d10900d140003540e8201c007440c00c0c0084035607409406d180c0f00340c0c0c401003541607104003c8008208150400946460a58030303596480306290202c29009010b9100000000c011621a5000e00b846140050081c440306401d8005410f410003042c1c0d981c0c2c0600c02c103074a0f250540c052402000c4c05080300515011310145405d10807500743c00c040380202d0313009560624001800b110f0402100143c15035180c1e00124501081c0090865400308000303c04113401803004115464124081e02d51044084101107065941c514100004c1600082800d50041501001149480e03000032602c00303407101c81d220b14104a448000542800034101d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328609622 1250 328608372 328608409
    0x6040501080a0207030c150f05150607020d0501151409060d110d080f19080907141c0605040b1806060a1e180f0b010c0b010b090f0409081206 62
    0x1295000b44594020710303116009192280e40030099543c0c0700c1c1d0048410001424590b11070480001d50740081c03050b1a00240311111b031783c0c1e42038005404110030740504180079204020041031281130000a40000c50358152400310260f0541c2c4803488030703018584020050307019031603c400145950410145d40c40e026500b01c0b40040c0300300500c40c100300301c2e91307034440d0b0840d08881c0520403503107900b0302d02000c0d101c107007884920402e10740c0a461000b030451500402000c200c1d4000841000706202a682c1110355503c00d5440f0709028030100c0c000b000c1000b10800c0280034900e040100001d001003500b580e4094801c0c60600c5440b090881481c03551645c0c191080da070b000103002010440c164613004c080c0c1d81b000c02640e00c800a5942c1b0003008010200d10322000c06480e03100c0c1c102c03282c810001d10900d000348900b400c02441c1d0a10030340300d51884010500031040d40950000c2d00358403075640c4110307490030204010000e01420101e894035601541008001046540c0f281d8041707101850b001a144002032140c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328610872 1250 328609622 328609637
    0x4090c0b09042a0f02120f0a0c050f070501080a141302030a0506011203080105181609050303040609140a06050a031503021005220b1b030f041e0506040501 68
    0x40c0300d24000e502800c2515801503652440304150a2481008101200c290f2030b5508101d0850310060038111401020400b10740151440c82c2c414452082076650b410003807072202c1e85881560105130303841c204c8450007601c3d51162041182003d0350001c0d0311800c0e03036800c2c0d94958082e22001810400d0319400e1420b6007100e0142c40006400300c110b858212101400141118030000d0300741c031b03030b0b0b0300340340c420b80050781e0240700030302034000745a0464400790041505858042c0c404d400ca00c6010307640000070300039440190000c41201c240764480c3c0c0050000c0d101c02019a940ca507a984800781111015100d211000100c003c03010100f4640b901d454000c85142d038032094039150720050200c0041c5501c00621048019503070011001d600e540018110500e00d503115079943d04480c1005001d10741c0344154503505442c12400501000106405481540b032840810f9a40c0c40c41c05030b0300500394000d21340803900e0f405002ca0b00141d0781084c6150002c2c0e0341000c60034220100d80f170b40300740401441140142c1d80440c1c1c06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328612122 1250 328610872 328610879
    0x151202130b030405151305061302060304021c06060b04050306011202010806100516120e040c0f05090307030602030c03011a13030b060d0605070809010e0a020901030f0c080a0f060b04090c 82
    0x64100940e070082c80340c015100401003486800015503406d6030802e0311550550a20001c00104114507038104001401205240940c3c1d80080c4c043d1000a10080c06408280d000c500f0040700c1040001c10a640318070240501a2604c1d6004082d81162199610034450707413000180002501400b600800d070180c0d125001c5130f49600a10030545070048010302084410050b491034451103003100f0403004d10503030714214480d4410100605102e5031361050352043d0319224170324030100d0700310410010314106030074441d8883c403169001a00b844074030360001d01301c14000001c00030785c042900b0055050390010304a0b840c0c0481c244035000840d004603500400500d807090310902c00301303521005075a48803000904548124110340c1d284401d54900340d0344c01000c103850005120f8108401c0c05060541c041100050032040c401e070300001e0700500184405414400700d11fa225050040b100035120103085800d003103881008192529050f1000078210589105240c003007406190b240070300600c0e01207504141900b13892401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328613372 1250 328612122 328612139
    0x105030606071b170a060501090506031023150108130c05190b0706060906140a0339031208090a0210020f070e090601050306010b07060905120415120213 67
    0x400c4032903540036041090002556030100c2013615001103400c0050b108503881840c00d6019590b042c1c00900003542031004021003a1000507840ba0343e216144000f1804c0100c1c10305400d0f10301c8141c203035a44201007140400c22801000c1a50502e41c500a0762600020b9a9440300120751215a100042290403404810000d41c0307400d480d494400a2140d6030721812390390350035010b00194043c402c11180c442e116101080b003081d0302e00c0303071702e00610600c00d940412403040400503005a480d404010400701820b000485c065041c1d0448040b590000c60503051801c0500c0b103411488000c9100031114503018211035806103102c0d241d1075004032045d9005003c5031065a003048640840301e040d05046100e0b034003000d0710447e010840c200003020514040005824107540850801e40160002030195001100410000c08040110340c5c1c1c56801c044006200c0d4414a8035a080c16100c00c102d6001d05130118000c100700d0000391501704114840d4440c1d90004040d66040400d07400342d4158002110003010040183c0d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328614622 1250 328613372 328613393
    0xf0311030d03020a02060433050703050603011505090c0408010608030d0b0628020a0c17100203010b072607150c0c0305191202030a060f0909020d060c03180803090c010503060607 78
    0x3c05050000400d8841c60707090303100e00301c042c410802390642c0300c1c0f05124206416214440e00f12000f0703402480503026510782840580c3c0940700351402840801c0000d425400940240c0f00a4216100280a070550b6409481d50300d40240ea840d0801905d80300e2524058540b510880f00507001604084004001d40882000f19403103a06610b02075002e00d011881c0001c0c500d00c50f030760291211100002e81880300c40d10700c0307150801c150100803c85e881040184103160b00c810a80701d16036400130498241e078000340505542c0240d0089407024601d40442c610702000700e074000b0f000c0e101c41c140508110300c1d482d40b0000c0718074041e940400740216100b001813000416800c41400095401810320b059403040c8030f0b100740101c2c7d1040303032001692691f402080c09510319203d1844000c280100080c080d8403920340005018406410006010365580c40d0b080c1e51080c020341126101d200d5240100e0714030b00340e03400c020901da031048880320114044c002401d046036010303000703031b9010380406400e0b5400c0c21050350721030070142c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328615872 1250 328614622 328614653
    0x2a12040c090614040b0d0f050d0f03060f1202060c0a05030d05090a030f080603071a19090f14010c0816330b03010e0703140606010509010e01030f060f0311030d03020a020604 76
    0x680100041b41c042075001e00c407002d0b0180315130001d00002026040050150000c9040c0808150901000700248031070564440b013a07410510003403800450b1840024414030400700700c1c8896001e00a442c0d01817040120142955040d92641401759560b03a2100d076480300c40c168801404290f01500c5108164030600d52a0f03402040a01120203c9440301300301d09210103d02e40703007290354400240300b40112808040f940c8508115061900b00d1038281040002e50141d14080c0c4514034601c1800c81500b40e2048103010707000342e0031039803250f92140c0d001110038144400c0d003002c2d107901c0601c2040e0070021075a559489a014103000041114503003884100014048000c403899041d900c3e106401e109260a10014004520a990b000040002c0c80c11143c1000d03001006030341400428014007030980d030007480c41c01c6014024a03001604aa8000d4040300074101030700600301040c061700340441004800740c03003501225011001c98031a101041800c8042c0e1013400a07550040e0040000b1600142c1e0708040081003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328617122 1250 328615872 328615879
    0x91b010903051b130e0c0301111e0306060f0a030b0a06020f0304090e0f030c0607110d090504050711030412050105092407090911042c2a12040c090614040b 68
    0x16040078240b400039242d030b04442c1c29172078000a92260702c0b883d09226001c0c404110400c028107020100340304840d444d0b8408a444500c180000014081e0364980c401c07106820007410446403184441d0000a0040082d820f00b140035010046020902c0b50002074a00c0c12407042000544c9010704019603038001e04400141d001603480b894110140c1008240f000d07100e02442840149a2413501080c001c01401101291054a81210042c9a071555001e03030300b1816102d0984001c205500e45502c00c90b5466030000c000c0c1d180340404100840c40718074000b06445070368000c10003403000b6120302d640242c03a000441d0903180203842c480c0460002e5a17440c1003259120800d400d04110060781c5c2c01c84403095860346041c0e20910f41c0700041c107000e944160354401c003d1181100303c00001c48610f03420b01c9406400540010282d6408101c0e00d90090920728010103810415272419485a04802040e43d1a1405540890709002400c2d404142103003d4410f10b012142c000701840040c03416131303081c4001400c4c5903031510381 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328618372 1250 328617122 328617139
    0x2405070b0f04150e0622061112160c030c14011b0f050f0304020423070509040608150a180f0b070305180a030807140304051605060903100c020c09091b010903051b 71
    0x840e490380308d200d07072010040c0255130360b40008c488501c11600c07008145074000c008008011041076841001c803d011350b818180f00e43c0014090402c0d03070320b030113000036404540d6003454007010720300c5070014110f686281c0544526140840701d44083e41c0300d0258502000001c142880002d025103060b822203c412600805031008901c22040078030048041264500d010810004207004581801d200b540000c10541c0c01a01c082031890701d003075246000c064400010b16440301d50b00a5241100c82d51010999800480403007003564501c0e04401400381140c031034011034603290002d40c810740c140e03810b0007500034004040d10440c3d103a941c05640100010300795100b000344054040352824a6071004602841c000c100400f4850b4428200103500c1002d031b00903500804080c49002043e440020301c0300c44814109001060364182450100c0c501407051640540c048241000e0200c40ca0002c035280403a1200c000380c0d400480c0c000401503a4400c06844010026400080c84800c10f100c0c040c4101c1c41040d00914110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328619622 1250 328618372 328618441
    0x1902090a1b0503010503100612020405150406030b0603160e0408210403020a15020a0909091511030a060b120106030209040f06060f182405070b0f04150e06 68
    0x104900c240c0d100398000b1420010040c80b40349020812101c90148181041c005a070510314680c0414000e890001d0003586c440700414210f03030480300100d110030b00c044e000b00040d540c1c0e4102450210020f5a60a019000f031100080d0001142d100d0300d01611041c000e06001030310b030b0381e0b1000300d950b01ca01c90002011400b2008828034501100055000740e000340c4c01410182a9070070031194055100e03c2000f035661040168400381ca41044281084544404001850003a079040110001255040103400315140c0100402c5502850f0041c500070305950404014460700c4d0180007199104030182d003104d50041c0b02c01044030902c250024201d030403000d000404e01044800c90034041c0c403950b40002000c10103000c10250783c503912005001c91074111140d80c4240303910b061600c0e51039000500d403084450302c4901403259014015011188a19800446c0b03070081c0c5098405d0794445241a00c08803515042074419541c030443e83e001e21280c1429000c00381400780c0740c02c08403000501012243c04c0d91000c414190301d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328620872 1250 328619622 328619651
    0x120905060106110f0d1d0103020702030105040b0f22020609011e050409140c160f1a07030605090601020c01030e0c0402070804060207151205061302070c090e1902090a 73
    0x14000d00b155281d018043d0001c0c1440307400d04c0c0074124512290760225240300b601d0b40d807140d2810040038a940c0740c00b000320b40b0075004030064070403580e0280d059804c100c00e10042100025005100f907008945102d030310b40301c0c181745840000490b03d80d8081c0c40c2800d0000d201501c1c1a04c010720340e0000c14107141d110700f040d18004044008004030024041a400301c0c040105500c2806030501500015299101301e10700702030940c0c9a0300840c13190465182d00550302e1070030051030460940d83c098001d02d44144040d901c0680130600d150440c0d0032030010b404c26500160310f052460304140100c0d8141c0142040c110100300440090900e90003860451141101031089034481c3e00c0140001c4d4050100305a0795410f000020340741003c00c0e84403507401c00d024003400c3c0c0165800b1489010f10180207601080980311400095003180708540c014a10610008a100c01c019504c2800c2045618410701482017006c1000da00392038845910b031400303080c06001c110100500e4800c103245d070f005120240010f000402e4074143d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328622122 1250 328620872 328620883
    0x20d17062d03060604110708070501060803030c0903010f05060f0f010e042a080103350a05031609140105071a10140d03050d05060f1c0312050103030f120905 69
    0x40a18000380c0072081041428103104040e0702040c1503030700f401020740130590301d000c500c101c1c140a8090030740420700608011081d003101c070040030702a0480381c40341050240c0c81160762201e41c40c0e0344030f076207000d907200010036250180724801c1000038881c0940d10216024010000d0403607400d04e040003110310b00c0311059503862007048001d20050005d0b0844840e180c0e16805900890384440c418804810010000107800c00090000b40c0c4d43c02e0140e61500170807020441e41c03042c1541c000303460b07490080fa0100900e030f07001028601c1010020000c042c0c01424110039550008180520201601d543c0100b00065000e10002c00030b00340319210f11a081544078055000c038000580e416080d5040c0c0420400c502c14203580c8040035110304032110368060003ea94003a09a20490081d0740080d520381c0f000988030390310305415241126000d13202d1042a6100c201d03900d6503c002000031000301d03060300700b03003002c0944511441c0d0680354183c1b41e411032000c4c1414192403410030b80c00c003648582c0d02d801c050300010b102400b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328623372 1250 328622122 328622179
    0x9051b0f070203344b05040e070509071b0506070c061a0f0d020a0f03050109050d03051e070507020301050709061b0512031018020316180605030a0204031e12020d1706 73
    0x1704807140758103000c1000240c0f90700d8203c050b11580950018089642e4a03050a600401d050604911170001c0071291840e078a407407800074005004020400270750b9904130b00c014000c42e00c10841004a204140050800d58449152132034100d4912a03542800382030010f2514a1540001c1c5543d000542d2011100c22040d03e580040760581d4441c40240d041010401c00f51004101d907040c1440b092500400c21603404003103030380c0460b41c01d00c2c65003c1841c00e0f0040c3c00f200d04e1503070007030020300491070b0003000601810414030a040c001f1301c0300f14054600309108102011030b1a840000f8110201001401d40082c0d00064201200c00c3c1402d000095070b502a04082d4a000864050160312403814000f856040f201480380d0200380540381d07200410800c0340d9807040040c0c8280d818070b6500da886001f40c110007805660801001040300350702c4004021024004100c17203c0c401c041640b5050b518500403a181d40b40c501c0c2c0308010521510104886803903001c81c4544c8180003030300c0c8528200300c5140d00b000580d514603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328624622 1250 328623372 328623509
    0x515030703210203030c0304240525050405090a3603031a060909190903090f0504060b0a05030a0207240609051b0f07020334 55
    0x60020074400d041d00003400e81200b240051070440c80e01607503243d0544002003006080e010006110805c1e02c01d41d26001600c040b1200d4100002e1801a003050941e0f10441164516000082c40181806125034222010303640094918000b40d04d40f06503003400782402d158040c80d0f03d426000d9290280d010003c10120200721228403694004d03007410050101c600c4007608030901004542d40c1d005644500c8203c0e00b01040a85841040d907642074000f4600c690300c140004445801c207101d0000b03050784164540c0070781c2c41b00400a0f0754580d42d2030402c400c494551040f041008414071400769404d0041c1d0186510110700c0201500d070542c190703a058843d914032141c44040380150402c1e184141e40307910400003d040c10503010403030380c1850702145a241011155280d0031540010360490300303a8152040d1a16258064110380300c0740041c0141c2c100d45110740a4080800200b0f42240080c40c4100c00d008007150600303409050001062614501810101c2d030311303104a00e0b61000070780002c091081070000d084290b40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328625872 1250 328624622 328624643
    0x521041a06010306060504060c05250302090c07030906180503060c0301170708060606072102010c0f0903020f0d0204091a0601020f070b0306010810090e03070b090a0f02040515030703 80
    0xca1204088400152125040600d8410140711140c1c014085400b51406420701e00d1030424030b40f0300359103010803406900030b2181140450b454503010204201050760b108039618140c6644145081c0c2c02801200c8001d070002e0f010520070401640110007000c98407003000c41d900312454861700402e02c1c11130140c0300da000000c0000010810706a0014101d42c00c100081c003d402030034a000700c119603030b050180c040f0b03100c0d80c2d0008207101000316001401101e0120100c4080d49030020703240103802081c044401202086d00c1d07950720000184150302c018152607000340044019107071350091000d1095002c20890708295a50441070100303850010364848140b10034100501454610002070500690760401266503200400038011000c00c0030950b80d01800c02c1c0b078129417954540382c0340c54401e240f07981308100c04e514180e940808a080400100310080c05209003c00d0ba48035810101d5070748e8400400a840980c48032024401454540c0219400405e080030018002101d10f002900b04080c65100303c980102c5c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328627122 1250 328625872 328625903
    0x40c030b0c070c1403190f02030105011d010b09060c0307050d0915120b0321130b04080d0c051e06190c12020d06031707020306010801020906070201052104 68
    0x1030004899018039040505810070445507228000034506000700c002c44c106900525049450401c840074443c1e0035101d00a8452600c1e05040051845000040c0e00950800b400800c1195100341c09015500712100c0c00c800d503030b103869881d0000d600300946455201c01c040000b0a460b410400180070598021000380c004188020b40289c825141a8841050803120154056000b9007010124491342c21444000c0b41802c1c903900000c2c10700340d214009650f440c07500500c030322402000401810214004103641030f4001d40b02d0030000e40f90300603445081001d81c0040020050070340304a140402d564461021070300820145840c450200c00301c404200440d901c56420004001c501d400c3d40f00801c00040810045111740b500c00074604200315170300c8040f85400080314124011a50b224000554110515080c08130071704043e84103c1c0d0020b4000da119100b40000860032440c10b03c00c5400340e1200034a201e01e40111580159202e1308100c0c0114015150051241440b50400c1107042c42a840313840c41292b080c42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328628372 1250 328627122 328627133
    0x3060203180706020615091506131e0e0a090303090501050c0c0c1801030b180d110c040e030d09060b040908090a090c141803100f0f020708070807050f0105040c03 71
    0x80354806411540038101b4001c29180000716580c0d84542500c040d140c0e40e444003401400070381d0251041307811070700c001140415000b03801b0213031054544580c05082645000950310411701c180780109251404913202040116210340c0c050310441e8802d00307001c10345500030340b1120300310790b021115150044d40004019820100038084071713050f10801c45210810b00310080403482c010105000c001e094881000118012048580c00d410705502c50000710760303142001160040c09040c0000e419041441108041043d40c82d0900440c4501000d034001541006103429070351303019000b003880603600740c1d580d01500189a00e4500680c000c4a002d0003a01e6079038103030002800b220001c00e5000c881e0003440c11001000090340140358030a00190102c08585a5120075070944d544039545041507418452109100c1c05d0302c00540004000c100e41403002c0012454080ca2902070b4494400c004000c4a81000850000f90582000d0029030780900b0886903580d505d408503500311541501c0940f01440342034020000c015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328629622 1250 328628372 328628383
    0x60615030617030307050a0c080a020d0e030a0510020306011202030108160e040302060610032a03110c0a02060d0902030d030509010513050c040b04111b12040302011e020102040306020318 82
    0x10b5a54072003150341c0b901c48445442c1e000180001040000028000d02c04031700c00c508011050b03070000340007076403020841d80c060740e500c0000042c2c1021070941c1c03008035698600424030441e13036908000a480c0d03a0054500752402035000403c49410300c0850a012080080a817014502038402d5030000d150050091411031801c113200e9000325000c090b071104000000e0360100c3c66030303000b040643d00d58150700c00c00c01061b80078180c5000c009600014207062284068144021191080c40342c1d102080902e44100d01d11901c4c1c807802d0351900d0f4580c4403414080060403d00001c084026900a0019100003180d00080c180300c4034900080009840d4414080700290030700c07819810800c40000002004400daa41d541c4405101040520941c2ea0300300075040b81d1500c0d0401c2205440e0728070941c9e84c8c0d196251401c22404a054114500e51041e12a00e180410b0044100c50590342c050b1248004101042c003107464040b010844001155000d0000000041c103d00145024169142c414003002c80425445850074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328630872 1250 328629622 328629629
    0xe1f0314060d030203040303050a05040306020a0e040e160302090402030f15071407020a12061401080114100e01180204090f0b180f01050d0206120a0c14030601050d05130606150306 79
    0xc2d90400310a000180e000404c50741141d6044c100a0b07124503411006581c180100d40c40545030500019501400700e9229011076840103044400708650740d03a4509065640c464150841111000c220091002d841d00c06620343e40241b004080707890051580500078204901e59808001810001c414010740a4020021900260200c00002d00301500f54000030302a42c010300c244203445c6500c1000d001072204540103035141415181d00c240095a648100301e000b0f14044003a1400d00318940301149030038050110001c1102d00881c40d061407a400c25a2030310b01c54510100d442400c583c03c22001400341700724010210310882030200050307812180d90134414402418040c910703920141900300a40204004000f50548005889883c0c04034698030101e0f0b03c5201e000600f08065000c041040103415264008903410300d150f0351107100d8415080a0000507010039030f83d0781d010400038488d40750b000c1c5440d0b2001d54081405031155841e40d03816110441140e22503041150343d11095608418081c0d050302412009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328632122 1250 328630872 328630879
    0x903010c030504020307080328020f0d18170a02040e10060806040c0b1e090604030c0e0115020304031a0a111c050903070807080304020d020a0902070b0105040b100e1f031406 76
    0x2000d1010400c0b0b100036048100e6692275600850090450034401c100b0031200c01400812103514003a10b01024081720240301d8040c03003003036100c080441c0a41180f14241c00720300c2c88800408643c0c05070360030440905481c152070245032240100c62101041980100402026202f000d0141d50a0a081195603000f05070041d10540f48100100003400c0b50b2100700912810b40845201e4480c514000000c0741403003954005011540c2032440030030003450411115040f00c1a410f103003c1104440003043e0f8481c000d0b40b001600e103040b80749541e03801d001401200c5500ca202c1e14400960941000011f8a903a0840c45072001000e41000800c0852540d900c501504460780000450401c900b9585081c21441440c600034070092011000c542151503d08800d42c015900400449078581c0358070f80d41c0025041001d00f5100312001000000d500d082522402c41868800781401441d00e140369419500d88030b140c01c0c1c0c0ca0308890291802c0d151300c1a064204110064241c0e4003181110000c001903403241c01c0074144522 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328633372 1250 328632122 328632127
    0x9030d0309020429191502100605030c09280e010c11120f070c0504020c0312100614031519061403010f03030813060c0305070305070801080718020903010c0305040203070803 76
    0x13440c58960443d4415120300321170b940080880c1e40c1401c4003640f00d80d0f11840d04410100060486140c01040d04e104281c0a28010003805948104140d5248210215241c0040c80500825a415401d6405246403d25000c449120f100c40507140c04c02c66590300cbd128034681c1d54845500b01c100b82d00000903074020456800404030a41d1807501021144111060342c1400903002400711300308080d0071403810080070010002c546a540300d6644a4803540511035030031074070f140320000812681205050005403100e90b6200c003007030035600200d0b4003540e04c040c02101080e2070030040102c5640c0c030150540e40804140c03042d400c0c11842c1c40009040411007203040c0c2c4420100780014419684141c213010120303030b0107240004a030344030800304440300c2200358000381aa40c20718444180302505500802d00401c520359003040aa62a10412030b503c0c9020301400e95103411150082000a040941d80035143d5810b4034010300d02804140001d084455207817044001c01c1e103450401c829407030706005000007480780c00302451 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328634622 1250 328633372 328633421
    0x7030c1421070515010e01050102060711060c09030313030305090f0a0506090603061210090b240103020f0f130608130807230a0605060a06090e01120809030d03090204 73
    0x1c2640000d841c203010400304601d424808100f10150300307103001e48559452940c581c0340d1106c403c2c03801d008242c0948510004508101c2c415504085602c9440014120036102e0b40320a46150388803074209030303045c842444071340c00354422400c401c40103503c01c1d110240d44a00e4107003404441e00d0100f032080c0c4606030150082041d074a41d0b00844140305000c803009641d07136540f01c00242d80030421a407064a00d10030f042d05090160801d41c800082680566140f000a036112079458801c0300c4092484070f0b00031904030411840d94040c0c0c02804045002e8410142000219102c02d0740b17a40200c0b0161240501d844000c00a0a030895000d0b6008212002440c10b1420262030381040f80c402d13075200924481c07140e400d04104400c4069484501902e14085d2000115642080400350409452080c401e419003880001da603800b4015003000c961221003038000340e03860302d261500b01d00b1100005850040d810481d191183e6010f0012042c4007a054600003100515401030008030390404400070b10324416071032000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328635872 1250 328634622 328634653
    0x20c03120c0a0f0606030c03030503093a0504092c010923070b070b070306060816110705040c0908071a0306040c02012418090804120c05030307030c14 66
    0x1100c02d60003003001041d48085150044c024640784d400502513100c02030001c810541d2260085003d4010501160618002e0f51620101101e0844c0300d90b13040d240c45144450700104104038407007040304ac0e08240d401d0658417440142502c03e05018143e0050920103101810013001411030b02e40da8540000300080f1040b070355103a400e6100000081c5e00b0204010486010002c100204030240890354481d07911408285041000000150b907054003003070420b403010424034410902030f4840c90740b007400c0348004400b01e00305462000600301c580b2424064014041080e45480c01100c4042c00350769941140385103002612404c0240b00c0c0c10181090743e034440180c48030009082a42d40010701141d000030061200707079013640101500340aa400308441d42d8044a0a46450301300e48084541301781c0001ca86211680025045a00402000b400108244824411245021072541d42540700d100301092003510340c000a4a140c114450440009080c03011101c00c01c05981015020000f190001308030f0f0b042100e054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328637122 1250 328635872 328635883
    0x4020406150e09251b0f03090e0601140a0e04180b040507090e07030227100510020606030303160c0c0803040f051009030303050a0f0f0b03011103250903050d020c03120c 74
    0x8004005c0c2d400221300490f5115488a0440c07a8001591859070100c1e20300500581104d01c911f000c8158502d00103001540034940322650041810721541c60300d0720300c00701528045010084140c000707036a0030701110710203e4200000b08850143c50300304010b01e00743c505036250071095000691040e0134960258100c00300042c91505132981141c2c0d001c4103207a0301c1410502007441014120000c4a18410f100c00890704807100c07001d07140281c540c41d0300300113041000e07603440c1d0041d201c1c960554070400018041004100d0f6042c0000040d107440395a01b00713140c0b01d0b90b0310180f482c0c01c5510990000501040700b006680d002c2001080c05542104841507032940c043c00d440c02c00d21014040c5a00c801c00190fa19041c1e038440d104010848400f000900749890754080104114481c89009611f0001da07105140c1071801a28410b0000d010600780881044c044100f4948090084105100017400e000c0300089082c000800302d451160300818213245034038101450100b00c9640f22804220401c032500c2002c901080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328638372 1250 328637122 328637191
    0x30a0c06030203191b020d0509060f0a020a020303031608070c02060a111207060614220903030b1305100f0f050405041e0503030a0501140f01030504020406150e09 71
    0x800585a0b41c07240348000c9414240e901d040040d500e4009890400d80145c500c41c42c142181c0d5007200c0e01603005002c140d03210b10909403d17a9020a040c81420010003944000b84103200036032050701c00c6204140d01191454001307445e1001002000307000e01000551004180c1d521001620301400c0e020b10715000f0800070320940c130300042040401ea100d2070481404200f4682191303a0752070104d80d62480b038203154005000b58000c0040240303c00c1c0b03949480e4900481c281c0841d00c2c1c20403005401c40a064140c1e40100080c460880902d62503a031900c04a542d5a110051068140e0703401003090714220800540c001040d03000b100b051425114240722000c03104c888141980c006680003e0141c80d941014012403c821103c444201c440401ca881003000100c00b460090700381150038002d41e41c0b40c0e540c48009840507146250018018044145298400c3d004650414000303003000504680715011401d10418400111000c00e9210002c2d40950815081503580310840c04507a401e20410b601c031350410300c46520b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328639622 1250 328638372 328638377
    0x1e01060c080a03110a02010c03050f07020c1c06090b0a1d1c090f080f1b0904020409060e0f0c12010504020d1101050c01020c07090c170105040e070b0706020d0605030a0c06 75
    0x340c0940742c0340a03601015080c0100607001c0c0d21451441c400078080c00b104000c100009003801c0108035401c3c04005407500480d1301e5006030880500820500901d1080e00c00004813402801241c5000300c0c0b154840c0310703c65405205010072610b0103154150941b00c40c43d07000680d010b0500880382e401480820107182840b0030718410300d6460401d000494904116811001a000c40c6040c0007588110004020810801c45410b40d0024042054009502d40c41381490381d400059842c00207005241c03070f5011032034091103001c001480c1e5221400b0145411002840064a644807441480ca42c0c80e1290140901d50000c6000740a0340c502075020a400c02c160801c0202a0804030035451042ea0050090b916640040802191600040c2c0c0c3c0e810b580740c0d854480c039281c0303920380701507810014070800000318290001000004241d18010034400104080b00252506001c4c210012070782400c003800030303c000340c040c000c096251b2480c2405202242c40300c0d40a28844c1c3d0019001000082c03510807040101c0e8103d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 328640872 1250 328639622 328639627
    0x314040308160302071505040507120c06030b010504120b0405060a06080a02040207020d1a0103170f03150a080a0f021810170a0b04052b2003040b040b031e01060c08 72
    0x1041d006409520002401b0300e003010305031650307001241d100901c13035806502116117459a5031844001d81c2c1070103e001d4040ca1941e401449007134041d40080025070018909185082c2e0364111071800c5980102c400c0340c00c09600803d20003488000c010207500041000410800c1919240016541e46840c25000340142e4021800c00117540d40d4540305005030740c1010142480d0303500c0c6c45e0280d0101c0000d000441c0d901307140d01c501c3c13400001d82009030303040c072082c143c0000e00c1d540341d110007030024498011449500c42e88c510000b066006d020b02044010038841c04001066681510410100c00030000441d08641c481104200e4546203107910242102d142e6600c2d0107402d545000c0943c103026075000080c00814850040c401082400503404252401e5040c000c122511440b0b04184d091000c0c034a044000364400d124406d002c44126010350b11040400204c0307150695505150020307401c17584c003007404d404020080100c0301c0301010582c808142c8860742c41e1110742c1400b00240c0344101e1083d0103444103502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 328642122 1250 328640872 328640911
    0x905042310051804030206090a121b0c06020d0201110c07121a04150f0902010206010b0c0312100303140316051c050906070e010207051305041a0403030c0314040308 72
    0x104070002d0700c4003901040381e2242c0040310103420700e002d450480040c8120400520002c101180000c255948006100c174402d98020003140c0741d002c01f2102c03034650488544a03030009a003030348541c0024042500980703000052a04041c2c2100d031060100e6906000c100300d9207042031804201d81041c2c8000c1c40c0203103089440c500707003104c04c402d030311108020a15100d424070080c8000c4509100117041003400c00e001c03101000310482e050320b0b81e420f0001c0c0581e10100c0103010114624016110b5044450f04986c1440214000201210ba040d50300004030f4a8281050043c15807215103000410f44640c0d10070b240d820700c18500104000c141d008041000300201743c4050030800b2440868080806000070700140c10f06445150303c84005513648008500c20f4044180e0035400480e58008840000b03002c040044042164180a800000d00403105c01c6100c40305d8040c490083c035a180e010364020360f4002400303221108050100e130a481600540409000700b0040002c0d8007820055000b00b0200920000600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 328643372 1250 328642122 328642141
    0xa0b070203130303030f06060c0c06051b060406050f090a0c141201020d0605041b0909020714150402030d0306050303180402091507120c03050d0c0e12030a09050423 72
    0x445029824510030341600006145d4560007144210b414030404121490713a60b5419540016181c800610001f415802045500d000750082c040c0c54216025003004e00c00d1140031103003094000c1314212919641c40c428082c4c007041d070b02035041d84203c00e08001d02400e00e0315142d080c0550620b02c90b5080ca140508403e40e89a1150944188031908920003503455000c0a42841c010b07050a004682c00b9030716195080c504454894240403200189444002600d8100381032500a0340c0480780c01d440e2100240c005001c080c1c0100034107d40d02c1364241300041141401d00c10181090080c1d0520010541081010b10050f035000c01142c03045080e054542e05e40c42c859001083c080e0291040060303000d0040304c0f4810090410500134a2080e00c244204941100c40a4040d21010800000a000964180800d01e030741c41469211410100c041d0400e005c42c16061000aa08081041400003403600080b400c403224a8102804070040c0504443c14002907207002c4660401e4105c10034003150ba40c0501022514507171 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 328644622 1250 328643372 328643377
    0x1109070c120c06050412020c060901050708030a02040317070b0609072007080105070f0e030303070215090a080f07120c03140d06080a1208010f0b03280e010f1505030a0b070203 77
    0x70381c00701d010702131494241030004407003038209806000345c051404441b46901d040d001710744e000c3d0b20503103c0e40d0520805842d09a541d4100400c0240b416500300300204c041206265110504c0d8850302c00980d9030543e6250803002c6040141010303016104003414440e8003600510000e00401d60700d2030303d019503114208050710f881443d0380011003951918042c041d1599104000c0c07031540001e901c1d00d01c503914115040c16138921040342c807080140c110703442960001a0405d120b5421007140b030122082c0e80103d40b50301c1c8656011000403d86074030002038080811920100c0890010b04504103000c4921068601400070002c0c04602d03418628002600724100400b40c2c401070242403e441100c00340328140c0b902880040d686400400402c0e14200000b410071201c92981c0c5c155010900742030b0468a401e042010383d0890840d41c00c80f80c0b0035241c0400003084640c82000c200c100201c00100342c0030440c042c0c0380d0840d400d6814211402c00140820b0081c0e1b20001500c9115684c445111042ea03558068100d0850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 328645872 1250 328644622 328644647
    0xc071103031308160e010b030f1b0a0f0e04020306090a1d0f0a17040f06031a090f010e01060201090201081504111209060106030606020d0e04020f12041109070c12 71
    0x6000101140c1c5000001d29204c60140101d1080d820549500c0c50503d00031003407190504240d4200001501100c8002c3c515400ca441c0c4140000701420710782d41040d01d40c00030841500020342400c1020102036100102840c0385106460031465414010042900a18010100c14480da207482070003140082c446000910000c450080d95442201840415207c602c20131090b141520401811440e00a0754000c6804582840d0042d2242d40d290500c1607020701402d00400385003000b4840b40d95040d89414510f40c2c408d518040e00c00b402d0b5810306407160150355041e0011801c580c900400c0300c0040c1d07044641a90005000c0f121a48034000a900080290140c8402c5400003140802c40080e00e12030401e895014642200980d0600c1c0c0e00c4850890455855204080059110070b0f640006940110900b10b103210000d0005881d000c030703508048440e0f501a454004018109004100c248901011443c03034402044441480904010000600745800c05002030941207031064800c00082c010250717080d29 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 328647122 1250 328645872 328645897
    0x809030a081e04050a120203012009010f0e0d031b020303040e09100c121d010203100f080c01080105090c04030b0c09030c18240604030602030105180c07110303 70
    0x4034518604100340350408000c40016525044080c00008110380c1940d013603c901800d1104001e107001865589007a140f181640c165590b481d100e4081c00c018100c0d1610032031100100360341c400036803000401414550701820304001e00f0101c004d41c00e503120341580ba074031501032501d0b00c41e0150002c007080281107124030081d4148000a000180100d42080d6036100d42e000c84140d6a801d445e0241c0502506c02d4000940c0c0000e95400c0003c1000d591903100e0030700710242038200801072044029850890b40155160441080030301e0080109000c4034000c2405080d180000e401001005400070304941418000c43e0f03c2280440700081034166036006403801540c122003140d08030f0620f80c0c0040100c0d03219000940c000d02a540c414070042c00c16040405044034102280a80e9030340710000280f080c1d0843c5004541c0380d1980790900080e07a1030313030042c0c4040c5008400050741c0394900303800c000c0c140e41214042c0a0b51450310041140c86008a420b65003559040071120304210003010000b425441303580e812810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 328648372 1250 328647122 328647133
    0x708160303090b0f19090305070f030207080f01060506070f030c050d03020409060509042d051c0201150812030c0d1410050105272710060327080903 65
    0x5160703041e0030410700c85002d90703102d6803e5201c0d0401c84000c4001124221803803d000803101d40440300c95840091001e000f803429504002499591001c00e0201300703016801680007540070b114411092044003d030488030b4000308101837512001c05c8580c05000d10250503111404401014940100302e4207480644c80001c0d141d1807580c405c0b02400940060007812011451310902003480d040079940c0a01036a00001c0666806212120260325280d003107185004074001d40b07010a0000b0010007001c22510310040c0040c091030f080b00c6009003129012122064a081002410082508085402c1031040d260250300e035525a5031641280c45407094840d49242c0714602481c1c40607041c101e8400e103000700c402300d4400209994503030044659004d03600c46e1000111102403ca148580307100d109041d125406032105010b081d0348000507070362288843d0b02207005000c183c100302010b1880420701002e0501c82c24100500030548980346020ba00440302e688501c4078850891f42404150303019280382d21001003c540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 328649622 1250 328648372 328648417
    0x7030b070306080c120f0609240c09150c0d05070b060102010b0a0303030c03140a09050105011a0d1515050408060f0c1c110c012003130305031e1501080703060f05060708 74
    0x25070309d00341c0d074403107101c400254000c00016001d80c0103c20300a1000d4186141443c02c4001041401081070140d41c6100d242000b102c91008801d1043d00d07112140c6481e600d485e1001410200f461490052416045901d05500d8940d955907003031688003520741602e00003070304040c3d01009400900b010f00c1c01d00490f48408040040c0f003850b03500038188143c40f0380d000340300c0c3d640e03070756000424201005c0007050104811311129401448a500c900030500d5056140c1d01d405035290b110981c515001d1003c2800904005410f1210b102d08004042d00100500592441480c15000007015070080e005082002500d442c501445603046812500c80f45006280e038540d5802000c00c1c4600800221504c01440c000d92005000610903601c1900c0c1f02c0c3c08034081108000d422650203c80c036a200420700d40e42203005905c03140c540400503100700d1007a0149811500342c905410000340c0350100c01424003041600703212007405040d451680e510226074054803001d480e541c1c10301e002020750141802e540300054501c0c0908 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 328650872 1250 328649622 328649641
    0x1101050c072028030803040b041208060f010806010201090c08030408010f02091005090a09140403110307030c02090c04120c05010f051809180f07030b070306080c120f06 74
    0x7804654841e624110b00c0010011004000700300d841c810300d03403090018071245007112549081220480e000460422500d80f40d90b50b000560b002030305c00f0b854480c8800204020814500c4c0705a40349050380c20101c81900d44080040c1243c1e0074082a681007040742d00109229034000d400103001141c0c04a491015203803644461070381d030307009407090100c2903007440c03c00440068640700700d90310741c240601100001d030050003081c0c0e05070380b111202d281c000c00e00b20800151014244180c5500300050030f044681400e050070010718103410030151000b142c0041201d100003039041fa00e41c1c0d4105605542191403503440120381c0f1003902863b0722444107846220940300c09c000700441d10005a582c241c841d401501c0c1890b004680d540940100c054072040f804405003034919204080c00e500c10b024240f2840014000e540d500c0c00c00390640e2504940e540a07510500c1044000001540c0c002071615042044030b142c044505d83e03d8488100e407601030724a001200c11060414400c00421580c19811500c0508051005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 328652122 1250 328650872 328650877
    0x31a04050a0b190609090510080a06020405010f0e1c051216060e030901051c0216080c370213140403230a05090f090109060323070b0a1101050c 63
    0x80750b118185042550f03034080600b9207507109554541e903504e50501d0410440e80b00428001e4160006503842c40d00011320342204000000141740b0800000d030725540b61078009027079540145a14018842c5903544c02900d62240301c41d820980383ca03d6612001d901c058102030741000030034075030112a000c0008080320920140303420b10032542d2003010b04205003c95a0081c603200e000d2402520300080d820080341c1e015208802c008070360381d5544000103240041105915a601c000d8281c02c480090000c260f10002c00814040a4481c1421080300d90406c0b440300c406407500c0b042c4200ca59644022211040250346540b0250340c06505164820040402204129910032108503011800690343c01546411810294002211608500c030741c541004000b410a44003604240d1100e0340200064041d00304644d602408036008011913540044c5941c02d40c1401488180c80d120f12860f94080d4204550900303100044000c116001c0b0780ca41501c41c807100c00101d400403003403503a2000c40c1d0b08080900c021500c80800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 328653372 1250 328652122 328652141
    0x61602090a020f0a12060b03010e070e030109020f060a02031e190219020f0d05010c200318010f110106230117040b0604060b16060b03160501031a04050a 67
    0x88403030040d680c12144605034407600c3d0800391005024090303600034600541d400c294413035845d0404503c0d60384031070803420a41c1003640a0802c4640280602180f030b034014801e8a200d00040c0c1c000d03c840c02d0300d900440c0004202a8209000781d40010f44610320300e10a00c00d03160104611205195481c00031081c0342c04a40200c40d0490300c012001900d614941d000243c095041e55003c00c3d14801900540c0801c00741c40c2240c40ca141d006654042e410000980a00c030301918091241c80d11884d10465035900f510b2607200001c014440e038410040c0e07082003008a040e00f180035000b40307003071140c2035031401c800c4030905a80c41110f203445d13007019808114038561406020500c0d10b490001c015030f0f5016401100e40418038900c14061415070004138000c60701c04240251700c84c3c0f000c0d00120f9066034503140320049500c0b1001c80c032110102c9421840400446008140c4401e40480c003c0c615844d50f04036112107100d803032186074180350340c0d46002078025403411401548000000c004000700d180c83c0c10440301500c801c80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 328654622 1250 328653372 328653379
    0xa081501060f0e100c0605040506090c031f020307052109061b0d0c020316030e0a060203071e02030a06290402040b040e04020d0609121805010503160e061602 69
    0x1800454014800c045848108406070b94640c03404081400f03002e4001e40c050b03180c1080099410704c40010410a0141c2401140304000034450340c41e20f400014203008200040522036044400e1803000800c0400d460a42c80b5038518005a07280c03600c80c82a54680f0401e0710740000401403624681e50000f120201a20884040054411503503642507080a20010641c512108100a00c1406482420395000c850980c5040c0122440e101104601c0350090200b140c0480c0041c04819030b200c0309003400502c040040034035000039420400175585040950707001c060020401c0f0070300c6c112802507650400000c0d1085030400010003543c0c1c1862484642c1008080d116400045040d540b4496403c10b03200300c0b0221008491f24504150406024400c5100090700503640800c20301d2452010a0300c070700c1801d802038400c404100e280e040310309000c1d000700c0100c98903e058406401042100ba40c100f02141d89c01910520a140284880d000c01e81e500300200e90155000394001c1510201036000a50031150700340210b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 328655872 1250 328654622 328654663
    0x60c150e0a12140708180411031005030f0c0d0b04080d1509050601111c0c020a090507180521030c07080106090e06010305030a0e03031c0227031203150a08 68
    0xc00010004d11071444010314101c001c200d003000e40620303510020170070400200f0224200a003070f0880d000d2600261000000c0100d44603003000140350800c51018118244030192886281c0c100c00a10b40040941018110b1400030700081d0800201782c0455076001d00d00038080025a00b407a464419000d150300501125901d810b0215540398080c081c170f080200e00b1200241103a0002116464180400203103200c20f008100030746100503505d103540113010302880140011186000440288081070b050946600200b40ea1414806130706da1079006d480021981d02600c02078800c08030078502e0340c0f00c2c00341484000d004c0c941c0b011440d91010b4104d5021a54109801c1c046448101c06598803000300303100090055004210011050703009042c41001147c004080c2d03030a00d22501980c1e094050402000d0440f0703607001800300e4079190952521090217031714004000111100001080d911490101c06490142001c400600c0c5821144182b2000880203011300110950310b4440c5540e41e1481c061b5980d032035010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 328657122 1250 328655872 328655897
    0x30a090303140402031e010609060308071e05060403080c070b1e09070b19020c10020d1403090a03030f020904150e010806090319030908040321030204060c150e0a12 72
    0xb481c085500a58004002c0c08903840002e07008855200958201d0342c0c00e541798100010306540c14819a0025801010450b507128402d29100e00a080c1904600920301d1586090001040b03000a229510542c94188001c150700c5100180845000d201801030084203540100f103103090342640a000ca03122805140080c948a0080103511503070780d80600c4420000078000e00002d2000f01d81c102c00701006600542c5c0052580801090103104818010000f607803001b4200c0b40f05551100c44407003c05111142e003815400c0141d4269265003041c1d82c041d0030540c80f003142540500030742d8111003554034001d204100c000e00c03125481c011810315105208038406900000903042d03d0100e40ea03403017480310001861411444022907400f413a50801d61008040c1d030341401d0700008440c0e030001c0c406140140b4915200740c012204001310104102c000d10109801444204280e581216841c0c485c9030703000c110340002c1d2000c000802c0003400a002c2c140241c0c030400a460381442846050b060305517103156510828400b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 328658372 1250 328657122 328657151
    0x1120f0e06250e0607121e050906040302010509040e0102040602011a190e09011401061d04090c170f03030408030f07020714011d0d05010f180b2802030a090303 70
    0xc0040c02c844000c2003020329071401a20400900e0054580103000078201032881e2900c10783c5031208136540c40410340c08412400c81c0708600080401d4012146041c515001d5141d02161490040f480002d052140c0840c02070901c1d41c80c1c0d0801607401010701d00842d102d07652003c00074040d01c84440e461092020000443d0b066040814100003880b40300149118a640381c818085010343c80103089002c42d560b41c4401202409074002d85038020042c075542d5140c030284404030b60340303003248402103184103915141c1c440b00018a80ca4030b00045818000483c1c900d201e01d142040d007011455090140d460000008000400ca072800c0514058003401080c9480c1d0750391941d0581c1e6910303250240070340100c5a014620316a45c0b0030322020704c400c4180c8071200c1c511805d0302c000c0b480828004c03004484e2651207080f500c0500d90b5a1003202189141c01400004d902c0b400e885950180002420280c5840b911070f5a10820360049003940c40700d062107040c210365915000000000504407580100c000034148030200328034a4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 328659622 1250 328658372 328658401
    0x230301241509120f080f0d1a01020105100e0a0f09060f110301081c0504080105040506180d0c061d030703031a0402030c090405061f0c170c15040201120f0e06 69
    0x740b40c4507aa0b940450f05485a0a0640102c0001c407031600c410807400d01c80c1204070010740540441e50344041040300c1c50640d2000d0a0817215421411a0300d05020014040c03c0c4034020350480e040d032440c03560b003600d8854105018000d8045c0b80c41205051100c118204001a408010840c40006040008683c641c0c1410401d00c002e204824940e031000801180842d800000c042d0010b20714100245015500c032141c50940b4400c0b182513900cad8000b8410816800001b1a4522000d0400303009005215a4030201406032041c2680103403800b40e50721020200340080040300e80d848501035045036150311072890028041d01000e0762040070803044010b99520b6042900030b4a0056440c00e854030300b01340052041c040206402040140d00032603241030840c43c80b51312080c608001103a5514010255a941421300e540700c40903d550007803a20801100791900c0000c200700341d115a1600c140e05841e00e880c001281c801502e9003025501510f814100d083c00081c0b6030001c0c650151860076200d003030359142c00391010344 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 328660872 1250 328659622 328659629
    0xf03010905150a0b0406080a050d080628031e05010b01020604030804080304060b090c0d05090f06070c03031104060f02010c020c0a1701091203061a04230301241509 72
    0x50384203081e140ca00d5202041082d40c846450314001601c8240c07180080d05440039a4031604e49900304201c0d030f01c103005040c00180c2152b10307282090422410306901046014140a400418a0a00d0601c0040040002c14164011a08042c881501d40030038620009100c496030030803940380d860854050419400410490722503601510340c1819507840d521a40203940c001817084400c0c03035582051070f01c02e94900603820700800c25002059101d034401d0200100300c071405803003e08641c0c440d06d20b415504d0000542d03580c0c003280d00d01c0c0c2004c081c8000c0ca020f4010b0b240e425030381503e0b1100841c020462580c0083c0030741e605a2581d00901c010040441c003641c03505d05080c030183e0070a100340030500c6031070261312103010108a96000081c070703140e054480320641501103444800180e01c844007000300070701c0140180700c40c24012032843c0c40e1500c1c101d0420302900454003c80e1031244c21500c4210aaa4290f11135516a03d213001e05000d01d21246003072035154516801100c0c0304044000200c0b260600c42c2c00040e095 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 328662122 1250 328660872 328660883
    0x7081c08010f0b180310022104080d09020a121a15090402011b060f06030b070f020d1d0306040302010e070f03050703060b0402090a080f07150512100b0a020303060f030109 75
    0x1640c104003e550060303020240518500443d0381540549450400c07088440d22016400141c4507000760038000c407810101c424070b044d10b1075102c0a000c04200c8200803240c128511000000348a2205e20129008001c142d0102d100cbd0b0040401b0f031414403403915042100300e40141c2c0e040ca01e40da0741000c03007516801e44050403900011240001070042d4006d100200d030140c810f00560341c0703c81003983e8500c2698511000c044200f919003208008210203841e07490740042c6075040880040380c6209000f5601c00910600c40100b0407004144803465000701d103000c031078030005001d4401d1885e00f418040c1c0a03290002d0580094492200b001a0400e40c1c00700c2141070321351040c060700f0036528689503240540400c102140d402340c0d080004a80680e2481000c0008002c0e0401400005546400580c00c1c07041300c0d4050700110001c0c2401031600740e44481145c41132510324104030015240c11580304807034402500100e07000c2e100004e800003650340010186126600031510714483c80b6000c82450309035101d80310b00820b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 328663372 1250 328662122 328662149
    0x503060d020a1e1a070f02101404060905120f06040b0408070804060806011707050702210105100905070201050c09040203071403090c210a08031305030706020405040f0b0a05040902040e07081c0801 86
    0x40c41d0040d120350381d41c03030076180c008449c860940764042240d015038800c038042042c0440402650408829901514486001600c0c4441186803140d40340d5100400003400808032034009020085050290303a50b05070401c07101c580f125120500600904801d8a040c0c0c085641d40042e02c0180b90f01800e0b01d44100540d9032241c1c10000c155080c03010b0004110000c400742e5103451903060303405000740316072881181e808001c00c815500d040d01ca03d00f107610181201c01103905001c10010004000c60455051032801d07900103031343c0c0ea0f450340b045070f19072400800ca001400c00041401420300e000141c640382c910f0111005030712200b83da1840310103a422040c2038242c3d50030080e06500400c016070061580700d02c03600700c1d65003d2045559224150750203000200c41d80b560100f810700c240e0419101e0601e010b201c52800b000b400d04401d001641da00a40e20660740f1440c2c039100740f4421511030713400c500080d01c250000c45054548804c9803903120540c6020100348607110482e13403585180f050000307604940702c41a2804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 328664622 1250 328663372 328663403
    0x18080111040e15150c01180b040213050f0411120d0503010911031501081305030403030f1d03250b0f07060c050a0804020103110c030a1d0307060503060d020a1e1a07 72
    0xd040d009444044155503a840d0100d003001e604414447d04a03102e010180f10a2a01c1e2040151401d40c4c07210080d0141c0c07801e420070040c1c1104450a0342c02c160045110390b403411503180011200c030358404910b1818041c54025040359a044000303181681e840520a102907054203d090300540011265060a551080000e00c025402500c1541c0c10240c0b1011114100400b07407102451980664011000545215441801941c0c08142203584a182c40c886010000d007120010380c0d10310a9225920050003140b00113850310310b00c241154010480c0c2030030261162040108000c581d003040c0c200341c440d14106020442140d1040d01202e2003041180c4030303a401500d9540045005002556030600f8075001000702140c030ad0f00810242001d140d03195101c40408010f00303100140d4580c40ca441034002d81c00260301b0b00030960000c09913030f4065026a503030350300000b05000241c18040954410303451069000311161540c0941001303d030540340100501104041100f030800c441d4403541e0f02c0600030890030703009807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 328665872 1250 328664622 328664659
    0x180f0c010e0414060904110d030f030c0807021c20070302040b03070f0e040503042418050d0303240b271c020d020405070e2e18080111040e15 62
    0x1d0740242c02001d006501f0241c4c2408540c415028580c1513010034045140908455814010044d60580394a090041828100d0010f5560710005609a003070702d50103d001c01802d07100e001100c101642000c8410304215480c0c0000b900c6d40b120b0300090b4081e90402c00c3c280554100001c030780c012602c40d141d10941a40c503040e128441c1000c05031044170075010030800000e40080c8514131a0000350255162010020364281c0900505940c44444c0c0d1042041e203000c02031aa640d0320f801c0049501414085103004103030000300004400740d96081d8420100d84404034003007600f480505091046058840d080700900307054104c407007486450700381d4004180541070794055040070460345005d1010341540302d5a5025800103042d50720845a02e80041c8c640004103001e403400f1202100c8403403041d140381c1040c0c02d4000002005003000c007802c1d001e0050300301046e080482c21103c14801040b000008100020400b40d5644065000d44900129402c0f07280114103600d0b15291020798441000704452041e03416403220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 328667122 1250 328665872 328665889
    0x170f060906042405100e06240703032408060711030d090813080d030f05040b160507081206040605030d021b01030f090803060301181703180f0c010e041406 68
    0x14011441c0e0900103c07011a500b40c020700780503004844821a226060110103090560000d250328443c0c12241016030400b5842e0b10008404d118004005075104441d06050300500085410f1015014402d01d000a91001103901301d0706460329034003a519542c039502c004403101065081c2d840440c3c0c200b00301d5040c20380e01035446084070500c24181d160600e4000c4503805c00b8426541d01c6a9895003246000440300c0e5858800c140054400c40d008012908040e12195501e550040c03001c080d6514001078019064056010f0380c0034103502c20541a6102c11803074203140c4444058415502540c04c0c60300114141c40c0100d21411150001d9004001901003c06640f460700201000c2034181907440c006d2158080d0710780100c080d0381d801a0040d9569080070001d00d42162802c1d403510651952030b440d01c40004a07503140340b0880072099146203449407141200a280021464000c0e000c52080c6000410100404124000450000d0720b07440260140503042c081590b07100ca4003071406d90a04030000e1000c1c50448ac4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 328668372 1250 328667122 328667153
    0x50f07120c030612050f06131a07020703020d050313060e06030a05072109020f1906030e01180311060109020a140d0e010204031a010b04260f0106170f06090604 70
    0x2c0200310b00380d840d0f07503840312441120402d650301c0d040b1551805a02108201003504100081c04401180742e441e00c038120840100424441d42881c014045a59540300b02701000203103400901d84010032400c1e2601541e43d40c031021140c0030fa41c10b1a040010b45038000d4141c0b84450744050806451941c03a07035020300041000a003964280729403080d40c803051040911401c105250443c1c0001a004498010480808071441c9024072514094103c0c0b0040140080c184003182d26a00780400c00901500040b07000d07003e20039000c00c0e490b800340c84803400d1583c00340091f00c0c10302d0200103607401c59803608010320503031168421201c0440c02401c500c00f1a440e240300100862014890005031a5072410806c0b8260790203a07106545a581c4844400c1207400003014103801082c8400c4107500c1c05207882c491000c1c0d040341d46034440c246045548801446507051211025194062008002c0c4c16101c130720a01143c1c1486641d0740c00c038464051042a50b050002c2d18601030350f0303a40e0003042c00f55159503c0c02e1240240c0c41c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 328669622 1250 328668372 328668377
    0x1150309050f0d0207090608030304030f050c010209060d020703030c0206160f0203040801060b0408060a0b031207150c02030a030b060c071a21180a0f02061308071404050f07120c 78
    0x8003074507042c184000303000450756130302400c1d006180421039401c0d941103403c1196182c10820900001a8000c100070450844604080d41c5410262a00c280240201d500181d040f4100166010b044203103035000782081d07071203034504102d41503504d40101e81d2480f046500c0d201c0000300e09590b04845015914031000c445240c41200d2900761520030079030a50750b070b0358000140c1140118007400030450910225600c036126880410070b1001517000240e4840c014003049108617400200c9405015100381d0002580c1c41e0601d043c4605489000025565484243c04800291070880f00f4100c0346040c0c07040743c0c4061810f03002495140c0c1800702d50f584040901c0c07882c01c030002d0200310302401e4484054030710740040c000d80cbc10049245448440b035070740000070740340080361a0058000c0d5800607200e0452480d00c190151a019100e07442c4008042e42d400301904003080c2445000030008251002c000f510340c0c1120199018402911000550050f202041e1501d101240c400300c11195000e11a50002c1e46183c03552 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 328670872 1250 328669622 328669633
    0x31303082b05010e010b0c0318270604050106260c090d050708100e1005090705030a051e01050f0c0a03060f1d090606060406120209030d120b0102060115030905 70
    0x2003403101c9140d045006549002522600100b00060340484003134010148020840e240c5621141180d403640f15124000781d503007500f26841c4556888040325407403404840c041c2407400e2490b8a09941c503194040f85c02500c1941014004100103106000509070041c5003c170700680000e82d52100b10b00d41800a20018161030b081c40040716a41e80c188010386d10034000d001502442d401c000303909050903c040002641182401000504800d00107103440d11500f41c003130009082d449900c2001d007050340035031000f6414421030b80c03407005000e0081a58442003032180d01c1c00318184841c1c1c1d00302d401c0c2c4804aa100c0140843c0c5400180c0c0c42642c0c1c4010070030a0f5076841c000070165220b503500b60780142d081c0c01c4945a8501140002c070700031a402c0030584c00c0508075004044500d001d000040280c42940075800c10460519946902c0309101e80641d28200001070560301c0ca1040400018803140003c1d00401844c1e05101081419500125285041c2c440e100d00303100381c01200200c1034001d0411001c0443d29803141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 328672122 1250 328670872 328670917
    0x60207080a0209041a1f060e1008090a0b0703140a1107030507150203010b070515060a15090b041e09020703020606010507081612020f010b100f020712060902090903130308 75
    0x18017812501c984504050200da401c540301c11048201d0f6190003107010700261010904203591229144950980d440c900036199540301e00c440c0c0d0501d03915450040c5003a49020034440601d4140c0c11242c5240e81080381d25080c0e80d10100c200c800d030748851600c8904c210b42007080f100401d100380010419140141e21940d421044917400000b240c0c0268849101c520010030342e14100101480080c4880c0c0d1002035041c01ca0414a0005000000c81d10603682c1c2d0424144542c80001c0c0610044001800c0640640d40c0340c40d030700e038140321481d100b41a4203614144140c1c0045485503603031091b904250303015801400203640e00001924981e200b80c005030b0303240c942400080110404d102100c000c3c50b200788000d800942c0c416101928055041d012034401d82d040202903002d645408480081c5104649801d84602080320016810240b4603000500d100b580d015543e024032085402c445400361003550140d075503aa54084c03290b12802140f26214104a51043c02c10114002c10054041d10112603da440310245 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 328673372 1250 328672122 328672163
    0xe0a12060510080f0309040507051c20030a050702211602012703140a03080c07020f030f031c1e1109041e1a030a0b070311030406020310060207080a020904 68
    0x4c081d00440340ca510000e080310040c20320b4004c1e1074200e1401c1c1000c82c10301e5103800200f0026803034140304900b40c0d695103144040803103d01c400c00c03020b120795080d007039624100b8189000c090907003210b1900251160a510254004010000c0020b00301c0340c0300746500f0500c442c0c8850101020328601a0304020813500103802c0505080e07220f0b02c08a400c0540010512325529143c45000768591403069540c104800b840042500101c00c164013066000e8250307a59071440c40050ba4504904019542501c0b82403000c0ca01e00e14004020206501e103501c04001800b040006142502c06501e100c01c40119880400d65100d42340350000c0000c6410140340d2800c0c04948400300342101c030880013100c62034160031903401c0300040c40d02c5601e0100c030f0340f200c01e140741014030b0f0080b0340d4034120440003c09440314f9100103800141310790301006d0064224507240340e40f03081038103090010f03410580b008a40c8004a040c001460750001508404072200040070345071043e481d400300151606c004100341e800c1c001c85c0c0140ea49030700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 328674622 1250 328673372 328673383
    0xc030605010806180106230604080f0703030219110f0a03061109190e07110312160e0a0f090e010209060a0306080d020a0c030f110409060c0e0a1206051008 68
    0x44020003c00302440e2124101007034102000d0700c2005645881c4080c024486449410b280f480c105c003501c50104078262000c91034a1091b40e021442e1401040c42c01100d0090124518084a000c0d500700c8000800003100909071040c10170006046880b10900d81e045401c05030220701003a02c0c002d0071080c01660b641c5a00c001c2d50340420f43c1e03620645000444411301d00c2c14640b03000c0c00c5032030401c181310030350300f05914094001001382c000c00034481c458280e00040e0004008031104808803903100181420111383e8061150360602c40b400c04100c00b842880e0b40d0f8200180583d040341c00900b02104100d160100103001000340004000700c44d5000c020800c0540c07103180041526031041d54000070080c2c41c2c60710072800e01c070b95074040750119082044c000340840c040b05120300c00e0fa60007448640c2035016500d00061100040840310b034000342407140a40038400e8a6100000031030ba03907201c1c019564006000c126105250380100540d601c01c0720f61042c00b0500580c840d0f40e10041c00d0a162030301c035456003065441c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 328675872 1250 328674622 328674629
    0x408150a1803080610080c090f03030d0212240102100c050c12030a05010609080d0f030605040c23040806150f0a0b040303120b030d180b0f09100e03060a090c03060501 73
    0xc43e03c0042c00b106080c81003d165014031130f440c1c4050340e402d001801c04460700c20300101c03e209401001c101495650305008440041094490440d5240c54440441040c802c1c1140e802d108000100a1000101c0c52940c0800b01c20304164050465036039117480000041401c10194000c205050020189110701081302140c041c1880e140d080d140e140a040c910141e4405811550411062040421144200140040d900c842901f01260a08a04c12044004003015807005034440c0c1070440b4002119000f0441007030200030040161000c0c000c5138103032019442103100e4008154020400108034141c0050070104005000b40010100000c42c00040d00f0078030642c002e407003007a40c001070820805030001000b0701460701c0c0c00c00030b11035401c20500007600d031230420810505002a00841034440c40549405401070007900c04480d80300e1001035404031407600a803481d10700541851780610981ca000e43c0e00c0140c0741c4d41c024000c000c030b69200007180c3c0c084c1207000c07003c6460050125000c4005442401641c1c080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 328677122 1250 328675872 328675877
    0xf0f02030402030d0c0314030714030109020a03110313150207080c1509060106051c060f060207090e0a1e0f02030a0b04050c0f0a1a190c02010906050408150a1803 71
    0x403424140101402d0540300c2e01e04c14144100d020362100001e0f040f004505140000111041d00c07941c1e07a0806944081d9034003507443c80b104000001245202043d809011000b180340e0b02003100303404100382142c2c0c0348815030342148001c68000a900000340310a080c1400c600140d24090f0802000d5600e0150b1508048861180c0c0e4001803404050384e00140700c4507034070007141801020345514241c4042c24620072040800c1c141013100803003103c01e40031078110900410580b04100100d941c1ca41c0001c0d01c400c040d001355246c7e40d040900e400d2100c4c80009446401607044040c55883c00c8030000b4043c1014a00702c0100c5160310741c1d0410f00d000daa41030003803800850003209100e2880c41c1614145060003503000503580300340b00e1480031401c03039119031003000d040e244c1000702e892030f0902d40c5080103801d0113515003c5400c071841d591a180380710340c03100d11610a40d2007a00c0e041040c548991068030a40036a0060541c903078004030303210011000704100180c000000070303400240d4034480c0410354924880100300b50003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 328678372 1250 328677122 328677127
    0x60c2304121e051f0903080f0601050915190306180b0d0c0603090c0801020703020a020f030a021f0e0102060c12070e2d1005040e250e0901061b0201120f0f02 69
    0x1113079801070b654840c0c19441c3c800200b01c041d0051750003800501700a40100414240d140000303000740d018408945000c2e5004140d00a00040110341c0b0780b480d0321200b600f00b15a0b049a909100860090041600f91811a8030f00d1014291030200d50f1300030407005031601d0f480b0070220a041c020403078500c0c020000c0d102a641c0401d84240500701f200e5260b0081c0e01c54442c6a104000d064086036010401c0802c150b41196903d6080740200c0007c1c0c5031900c02d02019600007800c0c5032602a0194600e40000110380a44a65004003800340040e030715140100d5201c0211a42009000312006084003082c0d4801082c0c1001840d0089941c0442d208210460700c0260105100200d1482118005c840f40031555044510b040c8244c55010010030713502440c86104071342d010701404507003940103402c044c0d4540e510a1442d18446a0180c1008004914022030715008a2b100d02c0080b505078450080e0b020a10030110030206060540d6004403400350740d000d602c00350a44c1e01d16900c0028981d41c01529507142d00c80d580581c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 328679622 1250 328678372 328678393
    0xe0402010e0609090a0b0312040803181c060c03060b1b0106050411070b190c050a030e0712140f0d0f0327170702030a060c2304121e05 59
    0x145a040c048030341c40d1046005100d0b411440c1d44101c0040d0307210005440200b4110182400300e4609940c2e650b50031b44c1d0700030218006c100024000040c02c12507000c4620301061900c1a401d0090405030040c4008030038011200e4140891119000740348071039600d10380000d06690300d0000d9143c035004161405004150181da15070030000034000c0101900341180c08110301e0711f40710f403000114031840200500806186000840f00b00c0d04007101c2c80c50406d6080144854044560f00a145a0007503078814082032401a001c503107540000350010a807005030320558219078881d282c02c0c1452070780350185c40f500d12070440c50500440041c88101d118002d00d45a400c407500394210068191852500c1e0305101729290b010809200c02d84c0e0f501650210f40164059203c55a900480c003031520070044082e40502c00d0003012400c100b800c0c0c3c01800801e003103607a800520089411a00c052485c42078904055040a010500c80388081c040240e040758843d40c00b00143d07108805610003030135401002034916800c5000c200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 328680872 1250 328679622 328679627
    0x40605103915050f150d12030204050a0f0308070b2806080d1814030a080309030d050c07210e031501080c030706020712020f130b030c06070308130c030803010e040201 73
    0x3241e051241d1043c402d501d04114030050400004021004500180c90204460748074190000f009030741004000030b001103403003000b41c00396106100d628041d25020f4000601c0025130401ca80580b580b105a440c5000100d480d40c011910780500b004055440741091800000542d8100b451020b040ea940440e0646c942030340542001c2030420b196040c003101043c0300e080790740b07000504020b0303402c401008114444017030b000c24274000f018040201003510020a10200e86000009801d08140e00c010074042035031145500795a601a0400c020001e82400a070601000c1d048220303100342a40d00e140149401c0d0540000a2410480160070781d04d2403ca0b40c0148880d2505228401042c3d805070002d00c9500e107050320003540d81c60a882190080c1890720840303411556600c29013045800d0017850403680c100c00b04e5000000380681c04009120f88a2308020b4a07880c200f45058801407500350f103410170f8560760716007003898600302d207a41150300b5098088084000788042c0041c60191149011003035251900d071002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 328682122 1250 328680872 328680893
    0xb10030507030e01060f0512030405120a0209161709010f1a271504020d060608240a030201030e0c100206010f05011701092412110406051039 62
    0x441985d062500500005001c400c40800b113450980e00581194a1040c0280c15401540c00c11517002d450b0205a039034003c40000c655600340e00071900520a40ca03510060500d921031141541b002c100721160700402c00355092491781d0320014180012a80b0615001041d00702c82c2034080c15024800c0300d80d2000340300e00707202000c001f4089802c011038030218283e02d0094040c542c02018044400142e400d4030300b480c0c0710398042d58001c20484106100103502ca500c060449c034011120b050722164105400c0000d4000e10100e606e00c100c3c0a02400f07081d0342980c00460140c02d8500c0d140c01c035881640e4580505460b0031018403100400703a0b001d0849035042a008501d1544142c0c021810484210034940c08140c03082e5000d0b0440b01c1480000501d0702da0584080c400980b0610344004d00420030000249010703410704007201451046507101e4814807202d040004a80c03003030094903007040c190b043d0254603a00445030700404002d02d50519222010b503141c003d01068500064002c0860300c0c1840004200c078800e20b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 328683372 1250 328682122 328682141
    0x1a0d0b0303210901060e04030507050c0411040b0c1504080c07120804050f01110d08061003020c0c0906060f0712030e0c0f0603060111120307020705030a05030d020d0b1003050703 78
    0x1441ca04180b40c0d0260020903100641d8071041103181c004509045001d5020030000c00001d4000d2929103860305028020790841a03041e00d041c000c0c40101c440d6490107108a079018128143e0311400d0030b0600e8981c10702238014040c0091244608040c4401c0f0070301c52280640b045100709041517440c500c00701300500346901c41c1c0c0320501d440001d0f002d2000140d2610142d60036203800b959015510004580100c41c10314071a0400c004c2e42c082d18846e5003040d680314160b148624002d65440c07140b1039542c4000c6049101301d221200750b0f6001815400200d00e08038890581040c40100144d04100306100c0b64107051b44100400c443c0524400d000300b420707640501850701a80c0751000a0090702c021000130030031909202c802c0c1807042d0000400144544e011b103080f0343d1900307807071021103041d05d21260f42000c15600548408001d445104030000b002e1074001404148664031001035814400c890b1100c5001e90043c074503000401d40c071400e0903602c540301c4003044a0440810395001c1514101480f000e012280b8030b80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 328684622 1250 328683372 328683379
    0x30203120a090902090103060e040302070e0705280c021009030c2c07110102040e0619080d0c020d06091109010e060d0803040507030c030f0501050106050a09030602070c1a0d0b 77
    0x201d2514125002010340d821a4601c11000d40c4d1040c064004034024460380c0c110b40c4c0f44000c02001c0c4000d240e400506041590450000f04280d500d40f00700c20ba80502454400d012011b62510b802031304a041049023452800b01424800640080340c0e000819030340b00c4024003c0006c903441410824486101e00e048001c180d00100c04c4400713900704024907102006a40e14108018040012502d5948102c00c0c3d5246036036024000c42d1a1601c0d8001143e1000058465503c140c6d110320582c41685248103c40084894010040c0040030807101c00b030b290042c511341c0a80c0e02444803454440890918000c9a400521030209140d09a9044013040000d4006800c14000c0f01810001c01c541601c40100c003204072a040055031384c490b556454018500401c90b04010018410540008201710725039564145183c41103000744416031b2602030441da03038007a81c4950b1001841a480400c04110f96500410a0a01400d045890203465288450318064420144040e10382c1c0060107100c5088203100348184818120b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 328685872 1250 328684622 328684627
    0xf030a021002030c0708090a030c08030703140f0a08040807020604030803060907030c0f050d09020a0e060117060904080f1306050a031a0d0201140d0e0a020a050301052e0e0103080403020312 83
    0x7141304c0b21081c0182c038001481040000b8450b28a640c0f2100b050004680c80242506103c2d2915080750300c0f070301701190072030100e40f00440101100752541d0a83c1d08015030000b006046c1512902c01315509000a44141c41c0b800042242102684644000340083d600400031640d4170b0800b4401d12241e00e0000b404141018906022120815801107607154103c1062a02649032000000c00324001d052800000358010026800000c04070f0032202903a00ca10300980358001640c0c01190862105001241c82c164402c6480340000d0014a02c07101034103e200020041504108084c081d102220800790400004503c011518a6607517601d0b001d1041c00c4143d084200711802c1c1e20001203038088a0340800281400068840300031030012220039152081124501840042d481044094880c042140207038025201504081110f04050003010300483c8600c42caa0f403800b81a003140381c000449402c5e08010440032001c0020310341400300c2542d01860140101c1c81e501c0d40346104142c9008024062070f00744c400309 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 328687122 1250 328685872 328685881
    0x5160818010c05100203090c030109050106050f06040312120f090c0e07020a080315060f070b041a070c02040e19240b06030c0702040b130b0a06050414120106080f030a02100203 77
    0x4990180f00c1565440056120780305c5e004031508110344100003542541c8bc2c00c1c00c51052200541000c0225141514400d0400850300180b012600c141d00001c0c0100e070340c000240842ea40700e03c928040c800090b81000071f5540003030116100791003045500391900001c484050103640407160071640c12010f54002858180080e544000c2c0c1408002c00c0700c40003886800076082d00303131601003c5402481480e4402941c45010345031085c038440303094800b80e42e021502c1f000d1440f41250041e42d2800340ca01d07515110000740c003d0b802c01c8043c05002c11081014095000c00709070200c00010492007840c803075500943c2082c40c800480c0080740e07001c500800074600344001100b281d10b41c50102e03a00400d41c003485507514604c0740040303009000c1030700003550080840314802c0e000035116400030403881c20460750481101e0781c400f001c40d441c2c001d82c001c3d001c1c1c0c081c41851011480c54a2021381000043c0c06001180d800ea0f100e51040c09d210542a403048139410005d50114296418003645026006420045065060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 328688372 1250 328687122 328687133
    0x50a030e01081e0402210d0e061201030813030818031203160c0303090b07030b0f0108090d03150801050126060108100c0516030203041a030613020a05160818010c 71
    0x50b01d400241c075012000081340c00d41d214584007403984010201d607000281d410784401580c6c0d800e064280c1000449032002e49000b03240420841e154000320000d05102a401c545600d005030b8041e0750120980d01d0381c95400000901d1860180400b58075041d02e20310074101d00741c181410301c40803c69540301600c0810411100d1404151803400e101034030729040d501802d99141c15402406240806040d080480302006030895241e045984804015074005030b4040078580152106e40c800e982c0c11015400003204106414441d50080c02c180509a00b4801e616565200309800c42d8420303000142c1d8030080c0380a01d00c0340815401e00020300e215040c000d2401d0340c54034008989410708204030300caa0700e03200c24040b211280310f00d050b1008100d00d1300004030444001c1c94007952740c4d4002d108085225840d641d82408001400c000c0d03903c00c98000c0c1020004482280a400003540810140d0f01071003018803d401076555010310044590307100b9411155103005580018000e0752407444001c3c100312007031041e64005103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 328689622 1250 328688372 328688401
    0x606110304061b0507080a0c0902070302061b13030503030a15080601091508010c0806041506050711010201090b010f050a090501060c02012f0109060509030901170c1204050a030e0108 80
    0x340319140c6511030f03054090301c3c11050441c02d140035026102c5e4100100e1500c038085805841940328041d0a007000f0b40d07402041c4268000c000c4094096000480040d800c0e0071342c000b0403202600511141c9141000220003c01c440040e60000e59135540040100801100c15126100b04606400c41c6c0940a034500301a0303540c0c901050058103d91600c641c40150505008100d00d00a0007008000b8425a0f01040c1c00428191045a100d07114504110004142000c1e00702e0302030a60f40c00307945192800c03c013521940780500b130b000003542c1190350b07401c0b80c60302003900f80c1c014038082c0c0100d040583d03006140801b00403100d46280c10030104039141c00700401050350020076a144071682030820501c20f0040881c0d625181c0168802c016007158000c00e424009001940281181e038820b100400c86521100c01b510303624011002c6060114024120004140951081d82c0c0c0e4000080000e2500d00b2241d078440b0844013405450444265008914240070950840329020300b40d9402c4c80c01c03654510340640c002c170009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 328690872 1250 328689622 328689629
    0x2070210050a03020f0c0307021f090308131d01060f0302252d06060906031a09190f03020c030610050d1a0903190c02090109020d0f0c02010b01030606110304 69
    0x7800100c109002d070007501039030f642a0450304916182d66690300f2494590f40440c404034458820707140d1091018a514140348a20a519a00c880c0040d0444d59810101e5010041400c40d41e842c440b00010300451034495080c9402c140720b0702901da0751408a0243c01d1154500a03036051500501941300400260b09004500c0b8004070060b8004100e681004410703828807029040901407992030b14140b00006a8800102c0c81c81154100406507036081c1d41d10840300c4d11700004009499070385240800c0050518010f80241540b030654542601c0745120f00b080003980001103620803042c600702000d054050002c03c02c2c121040d40601918906070080074000f036000d0143c680709884028030182413003030303900040d40080041941c140d0039090020455540e5000341690540b0f2148030b0345c8180010344240c04c840d01051707006c0c01c080e08607404c001c00b44019401040c000c284007907840001c00440c0a403402008108045070300009000c410010005080d83d03400c0e04200302b4480000701007404414000100c4080303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 328692122 1250 328690872 328690877
    0x81015030902010c050d0504050a3510090c03030f0503162006010e181504060504030c02030d0305013204020309121b0d08070804030e010e130501050307050402070210 73
    0x8001d51006031080c044614000c0c3c090b100300280c00e00850f40000003041600d004841c4040b00c0c3d565040000110310a210800030080c3e0b541d1a205c00f58a042c0c0c10400c800004141600c01049014111401721140d00d07505540026402104005054008000c2c26503845286013051071481c2c2414260310707544200c2d40c5841000b0740740942160220085900c0c41c01d40300400192446540e4510001d165284191428400c1d440050700c050a1241c00040c0b20300056820f504698043c2d4450301d41c50003d16005000350f05004001401c00c0040c3e8050000682e1400507880005030b42d41000d0550000200c6041c0b010050b8910007528694220440301c5016034203011900541d9a540740542c041c28080d18400180d8404d801242c400780c40e41d1041da80f940703c1c07031360902115190701100d07200700c441c09401d0700c1c0207003c55100d4020801007403050040c1250810f06041c04640030742c1080104581000071007071500341d20f69403001442586001d03c25100202030450301542042940e800182c1d0f40c4420803410400e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 328693372 1250 328692122 328692131
    0x2a0603070c0213050f07080a2022050306010b130b030a050901050721050c130f03050c03150105120a0221070b0306101209061b030c080115030902040b0a09090308101503 74
    0x8088810740c202410b070346804a07900b0309c1007a0f40c10034011980c0003e405c0d040c1d108140c502d1507500441030104901190002402004907034608a0401c1c072542c80034a04074000e01c1107070710120300314100c03000560060080500004040c07a09015181c00c541021345000d040280c3c0c1e0f04400041c440741c000da9515403500d0b0790009059103030182c4020251213201c1c45000398074060840090007860450b2400100d0b40140181c07178075094007800b09907e502740780c90074001030840100140440c1c24000c0341032100811440484d4801d50040d00003c810b030203494410788820341ca2002c0f0000c484024050000201070400e181411410200001605409c02041e07030410030008101030504038601d03401403041c03540c0102e020010a00c0090802030b407148c4001c20740300802d080c416400d071200d20a9584078102c0381c40240b00c02d07500d001504224043c00e40080160380c001e80f9400a8507165940011035801840e0401001542d800340c0c0c030700034100000080181154089007901001248484800c640203208180350006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 328694622 1250 328693372 328693381
    0x12100b010c0203010603030c0b1b030112020f1305060a2705041b0b03070f0c03170a0204031703040b06060a080402010311040e0703060519082a0603070c0213050f0708 73
    0xd0700d1200000001e545982804000418103070400e030802007560180c4003c41503a80c0740918408902c15001d000201084100010061144200347c100840c91000349030074058510100001c010050326402c21407601e6442c414001a071800200707e0b0020300d1035604008003010345814010a41d20b84c4600c00e020f06855038001810410b20414001e0307510f420745000c06100d522402c0030746140d00111002d002082040290700c0c251405050300c44105036060b40c5040441105025440c2c03e404017a00303c0c0b60458080c800400081e469140e14108400c0c0c40001079220725250406944400c2c0c01b074001c81c0590802c001005c6215031007070b5034940c0250282004030f03c0345240c05410803280700e00d90020014400d00e10500c001d0710380c0b50300024203d94040350599090841c0311255210128903100d2000c2651102551002e9071080300d4020080f20b2621016000c1e17040c201c00820b4055100715403030f10018040c88000011482c0c5800da4290100700401d08024500d85401c1d940e01c1032002505501c00c1c00340041c00503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 328695872 1250 328694622 328694627
    0x81003140c2b082d0c06070806130903091208220b04030b07020c100f032a08060a050a030c08060106081e1b1303031e020c120f010204030308041112100b01 68
    0x410001901d01c107600e0004c80140076480907400a0702401214050b41d8045400144185491802424000c1c49440b4800d4590800da0003000700240c01c409210070407a00203001d001c651903449000c1d004071480c540d56a0012112880c0c1040c41c81d40d6101400742110034000040114182d40c1521b9110082d105a500d0720481a442c10f160082c0310b56210101051030309005500c031016207a542d40c5a01d081c0300000280c882d4042c803280c404c1d0301c150701034004040c10144510170041641c0201015114401141d00c031000f103500e40219401c1a034000310705403002c0040071010011207004210500d407011903401c0c140148000c5818204011401103442d0003c2602012400d10341c49403c010302e0607050755404445200c4180c03000610080d40070805c0e44d0502c040e03d60700c4004551b00d12040340d0141000d415060200000c44001c02d1080800d8840d08001d46030300d035001d10040c0007842c00303034032004e0040c601440d0801281c0008a983c0d03000b0990b81c503c8801ca4080003c0c0e04003c0107044501007010261807004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 328697122 1250 328695872 328695907
    0xa110f0705011e02180d03050307050d0b0d050610090e030403030507030e040905010e0f030304021315171e0102070210030c0e0a0e0121050607081003140c2b08 70
    0x2a9000d049001100018000c03ca6009028001d1600714148100b40c07004104030700403003182009400320b00c0400010302164810002171990b0b40564600192f921543c4020511181c1c1c03409046416501c0182031044254600c04468002e02002009001300064800103c3c0c0761300442c03200800b0b000d40071690b4030030036010786400c1000316005441007210100700d080c1140a452000c40001c1030340260301c072401001d00f012040740d1003540c02030010b0074840d4070406400000c1030074081c1c104400030500f1f00480c0741040b0150890020081030014801a846010140200390005498000c0c60788104040c6005860750440d16945015a007000200c91300144001c0c1c031409682010709901c0103010301c021070b0f00515003016905840071810301c4071030140710041c408003060074654054006e0f400340c3c0000780028862001c10341c2c401000044084083e03502d40e601160144400f8070520941c010400710700207818640c0a900c2090751001070088202c001c0e0709802d8541d60700e00704c0076040b02800947d00c01c17070700741b203141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 328698372 1250 328697122 328697141
    0x1a07020d0c080f031311031b10020109050f01090209010b040e070e0111030c011413081e0706060305010e0c04020301060e011101150602031305030109020f10020a050d02150a110f070501 81
    0xf415900e2900c6202105010154482158240001222070005060000e252007010030b02080d15680d80202030108038440000c40c000100711764032110240300203070b0103004041d1911010800401c038400507204000e0445016040aa00302c102032108121081081000341d4211a4a040107011111480300481e9171080e40d400895861200081d01605401c0551003100b0010301e000c0810b00e10749420320308007046582c1110252145400b80312070510115210b5484031780620607200e0398a00566035841d0001d84e04158000d0325580d54403803104061040611185122107001c440c2185558107000020b0500700c49400c10604101c1c96448604020a00350b00c90508a0f9280141d044066035030726000795070303622411150400e2540c02600107041d081c140550b0100c15401001d00d00d4045009080c04800c26419005a00714425445548042030052100001042d9980c1c00741c040c1d80011700743c000c511034025111b030b10700c14076040780b4141c44101c5e6001d039012581c9100019030f503281030b814680c2c0904941d16 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 328699622 1250 328698372 328698397
    0x20a110303010b04090b15070210050702180a1805100e0f011a0a090608100506190f170c031e03041503062412230a091a07020d0c08 58
    0x10011074940f50580c054011941004c800f801440403840502001070190080e880074610284400c20051030000780d01390220141d458000d00701180e5800003080080b80d12a00050000010140f04034000c280c010200151244204041c0b00001380d07881c1a0b4034500501841131050751090407082e140e01c2440311044100d010b0b03000b4007c40701c2c8941100c00c03081c0903c24032441201c003108009420407c60103044129005000508821010180403102500700107101c20f50210415201c0380001e449801000083c0a548004003c0c4038200804040256010011030440b640315901c202050769001419424000c011283e0070481c480c50180305140d4001c6420188800f001c0c0c080751191603516070702c01800c884944190901c6100500c0c44001041100020071000480791004101c0c03c1901e0340080c100444410900f174402c0c00e6042e0b2007140f84009445a04540751681400402e201414640c420381650b80242e5101c1c0e8148168082c0d0b84100102e54442070040080c85042404003c0080d60070003103200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 328700872 1250 328699622 328699627
    0x210b06120907051008040512180414010e0114150c030c06041118012d0807061206050a080601180204030c08102004180f29010305040f06020a1103 64
    0x40d0506926a00b89001d4a8000c0800b904285000c6100e4824140626041000781180702c01e4a204d19a569005010002d812509825400394603104c522a0300060310f4042e08a00403941403654107200d00c041a0b02c1403685115184c40b4600715581c0325100d8200c1014400450b9031070034400030721800c500428100c031295020388000c02060080840c044195900100c0f80e602d0031000782d400c485030001084c02403442d0303000c2c08041c117440c159154032107000000e0f682051a500c40d96800503c2c0c5040d40c2904244001040c1000c0840c1c0144607010380405003200b10740c00700503141000312180d03072a801440b4250001d480e40c0218142100c1750ba040360080c60700300d2200c2c0c0c8926215441255207a814500400751701e807510b081841301111490140b0000d03074100d480e0900c1c092400c82008540882d452120b00c5290395500e2a04501445101d002d401420410742c001880c00f10305403e26001e10400062814142010100300002e41d0043c0d000301002d500c02001a1070700721000302240d07080022400c0f503c01d803000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 328702122 1250 328700872 328700881
    0xc020d0b0117012a0c1502040602010b030c0d05121602060d020703080907051c02060d06150f020a05060a0504050f07180c09030506040609170415030507210b0612 71
    0x40003070030008406410000e00c0b05a04144500b072620103800300c00c0100d64070340001501464072a244d0003241c02d01843c0540006d20742501600100d034000c0c1c2c030000241c2c2d9078450340300da0f82c10103215115550703004446d41c001109050700d46c0b07070322484528a014000100020203504d40d08200d00201c0e0115000303040c40c2c3d03c030100ea00c080c0c002580005c0065010403003d10024040440001d0400207480700076001580b130158040558080604000d4200d80c0a00300b4400500b0b00d2190344078140041000144054039404e0b801005008000005c2c1d030b80e421500985010801320380b00050042d040354409a000400759120b04089041ca0305000510800e4001c640c40040c1000c4850059410400821420840072441e10700a035800c1406202c000c195400010000740401c3c425844281c0050260f101517071302802c0b4100e1102d2581c055004011003294203210003021582c140b1441d507120200c1d05000c1d034030101c80c2402d00302084000c1d480481868031143c031901261501e5098610750340c0080c034a00d50f1400c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 328703372 1250 328702122 328702139
    0x603080a03050f0412120e010f05070801060504030b071803020303030a090c08010924060e28020c0604120504122f09070e040b120d14190c020d0b01 65
    0x3040803403400290a0102060206520500b854040d070b42c044030000360702c2c1c4e0002c0c050320070840b804643d420103a50384011543c0c48400780685481103e00c034000040514040401605070441a0840010850305000a00004003514020380d081503c601744a034002130741d1801e114042c94117400007500340c007002c4103100d1403003003075000b000b4000d1040703120101e25903c0308a80e0b4226038091074007502c100d000c410601c3c104d94140d40c80c80c0c6c5c2c0d9140100041121030b15118501c42c801801d503880c880100c40c6520109030854210b08107006c0c44030b41c2500350f291042641141e90390b9400540090b0040c020415030040c601c0c0500c0480380100300440d0750300550350160510310510200e50101010261104107800c0f808041c1108032242c02c00001c1401401d41c548440844540c1019207402e900150389202e400361682c5d4251016502100720030050800b40f00800005112031503047c2070050214082c00080c80240500c9615400e014151034004003a00a5000180000380c890078050091015180081001c55 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 328704622 1250 328703372 328703377
    0xb04051e1e01020c0a0228150e040606080705092101151202010203030103080c0a05062e0f05060703030b271006081303200303060a0512280501060308 66
    0xd00c8201020781254401150a030321403002d446185070045c00d030807801850302c001c0741202640c07101c40b07034403180c9081a150300d921b00c11a008020442460a444c040c1d8a80c007d0500400301003e4400384401c0d40340180107440ba10000d400f440c01d01030003160142d001c0e01c909642402c1c591240800c08105080c407003109000f084891031041016210400c080313a080c0d1000450240c0e15411ba00942c910703840c1da02ca0b100a030b000a60100a503000b09000300b004250308000c1c16014106881504c2d04403083d02a01c140d41911685011450000075541000040303203401484046440c127490302e40d5240e00c0c82c50214000c08800c150a60b10040c510418081c2c0e0306203071184540c010300f0060031641030f1102818800c001c2450b20a0070005002d480008415041400101c42c140b0302ca030500c0809e40d042e001d00800704003103401c400d840c954004030802100707183c00841080102400e44c2c0e4501160484903034551104007003051000750540807541103114a03035520507240295040780007001416100d103040901907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 328705872 1250 328704622 328704643
    0x70210110c0d0b1314010504080d1406030d031a0301050c030403090602061006140910080411040902090c030601020f0f011406040e0a02010f2303010810020a0503040b04051e 76
    0x2071080450200450030554000322a480c0c00003031400d4141c0d00d101c42a880c038032014004841e144002001c0101e80d0509001c3c441c01140711301901c1c0d4503a0084400a422280d400b40c40d14400310b14030043c0b14440e1400301c1c0080d042e003d41e241c04903505401c21074490918448154158040d840c0208004550141030080d50007644240d03203145656541b01401c9a85240540362102c0000000c40700700111030140c12806210708108a1090030101c88000066035100440d600b940464004810030003044103c0f50000680907048804000301e00e010380125500d82d400500090392810000013180f4544c2c02008000800d42c005000c55030039140c0014800d01030185580041d20684110300030990500d4640640d602e611802e20082c814001181c004448a115034801c00d000e000030a48861854114025120a0166410b0340c441c0ea9515005025181c121404024000140305010200c0c00710761200842c0d0b0043c2c0c1000c0c02c024079071924103041781400b00d110404081c176500c445020b81f06200c04103407415030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 328707122 1250 328705872 328705907
    0x30807122304141209150408070b0c160b180a12080f0d050408120114060702060d0e060703200a051605101d01240603020c010b0a24050f0406030b06070210 68
    0x40d02207070355031b4030a41d0282d401940060340041d032003404445140f00c0544840d1400200329100c1e855034280c0c8901c1e050060b0041e03100020005030910050f400b8040c41f40070b00b2010740d0a07184032450001468127a0840a400605001c0d000039104801080b44007580c0749091203410401450034607140c080490340c450b440110f070030030f0701d6000000d80070140c0301000c03400140a81a0352070800e81c0c1d0f0030000564000b101d1030815507600c0e5040b131a03000080281034851849603c002034164074800701d1981030294080180380c3c01404110007001158032100b0b40351740e4007503034080107501ea0f05460075505058010542803156881e01111201c00e00d42d500f6004130f01d100c883e008110010601048c413016048003024030070344910508040107841d01c02c3c0d004000303618410000040a118400c00900900d12540c840107010b040e003c1451071601d4440c009483c261041e040582c90f00014408a02a03070140c0c0c8554000e0554581c500240343c3c540c0c00884264503801400e000d0006104007000c2c0924440c070058114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 328708372 1250 328707122 328707139
    0xf090819021f0b0f0102073b131a1302011407061b030608030906040504020c0a1205031503010e060f0a180f11011d01030902010504091401060318020603010509090703080403030807122304141209 85
    0x1c24ad99142c14a80242c8450340e2600d042210f0381c0064032003000e40090034842c1c00c410080200410303400d11480b4200ca2542c500380d440c1c8050a10010b0075541c0c01d8101c449180c2080124250300c0c0e0300c03241143c1c102c1c1c03002daa000d0b85030007c0081103400d124208101800a902103640100c1407a80b0400841c42560a804664200e08060080c5400ca54560501e491039900000102d405c80ca80074480585c0034241181c0401c2600800b031044a00f000d8440085520341d814402030710402ca144c20380002000310a2815245c0e500840c1c103c1d503100c0d19081c0500e0306040c2e68070840419a4480d404407405803801d45000e0107018105460b0098010f024864000040d01d40440c0049103400d0403600c2d020340d500101007078156400c0c0b0303007000070301440500000071921031003400000090000024100039402602c0d40c0304070b0b240650028020034665600007000a14090035102c2e00220042c070400340c015940e40c1015540e03514600700440016954404400748104040910140c6024004140840051381e1190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 328709622 1250 328708372 328708403
    0x90b01080f070b0301060c030c02040b030a23010b06070311011b1206060305010f09050c0c01181a011a18041109040f090819021f0b0f0102073b13 64
    0x2440380400c0c00741a0000e500042c47c0350109209951410545000520001e40020f00800092905501000c1200c0105000d514600d44000d121074142d000810b41009000801c903280004003584650b2200800348011720007241048070b42584850110642980719402001d004140505050800f141c0900114204807003c42c80768442c2c01a50b04a43c00d2010018845003052070074405028014015800f80302c09000241c081c9009001c0c010b510345030b00354060f9005d0024208220041048078884080700c89440c010448841c0f40c03600340c1103c4802c0c2c3c911503210180002d00c8204601070411843c1c1c0181032803104544c58035108010444030f40102c2e0100320040d600320540c025950307060009003404405014040c444950407000c0200108180b068030403a0706040c0c84900b50410603800001455900c11000c8a1820410104040070009000501070702e450912000c840846c903050141c1c076085c44585500002d01349440c2a1000b800c1d911603d601440c11030340865128142000948022070340d5804075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 328710872 1250 328709622 328709639
    0x1061b0f1709031b06030a090314120108120a080f0a2307030e060112110310021c050105060702030601140a05041b03060b07080301031e080309010905100e06150301090b01080f07 78
    0x312113900000c0c04050031940e49081900040c942c406041d402c2c80456040410703070740c160100505042d405000d40c91825418075150902d002003540030100f03020740401241d44410b400c0b800840d0b2181402c241150039a03038544080010b0582000185e10213001c1d0002c1c0d04294001107034180c400c3e4082d0307400b0407101401c1308070143d58030001c5c0b15401c0e9150340d0b418000c0209154000b80042040090100da082e001d04002d81022a400404c000c0010031074140014040022070140c0c0c3d00520003103452600f080000d030000b82d1141e6040c800c0c031144103014001d00c00d403910741d141900000d00b00240100100140080d40d031502107801c00d14440068039015000c00c0c244040c1041e5003c0c1d50300110030500f16800c5555404019490000002d00041c8070040800001c600500451043d5508000854460400c0c5400d603d051443c1006c3c0060754280003550707050701c8001545035440701818071900768201c44031020900408800c0780c06046a900d00001003401c044c0010b00f80c0040160b035007103840700d566810b200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 328712122 1250 328710872 328710913
    0x6010c0b061908060702030a0e040507081323060103110d0308010324230604050105060d0b0409080c071a040e130311061e0f01061b0f170903 62
    0x61803195040c011407524100b000300c03061060100b9460b40e812030707210282c403460410100c4210005900c00100700300402d5001040c4039401c1400c0d5010312285c205600c0107841c3e90402845500b20704407141e490310901c0821b2901e88915841007219103040380c511000c05071103002c00d0005a408400e180441034080c02c0c2240d1010070540c1580d80c41c1c500344d0031a43d46050200900000690040d11559001d820820760320400070081c4001d14008039181581c210b03100022070041101e03210740d00d080010011600d401d4201d03000203002000000c0c0c440441d0b000a0f00400c40c021014007034500c04501c68440308000180c00c82640d150540003000c60220070802000d5204900460f60000502408581c2d040010780e2001d030781030b21a0a000f80280401080c20703103054003c0324101301003c1070340c080d42100603251303580341d41014075040781c06000d605158005d0079004803900500354800004500303100f8004410340254106501ca5400544016151401c1c041908402091031190090721840044c1002c0c2029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 328713372 1250 328712122 328712147
    0x3190b0d0f0b0a06030c06030606110708030406050f120915090123040302031606020a0e04110717040b180f01020d0c0b09030d060f060e090f01090906060803071202060601 75
    0x50744440001d1951500003510018212440c02d9481d1003000c0005091000d90001501403590001040d07850404010036a400078000094250003600c002e0110040101c1220182c0d00d01303041c451f94510342c8100e40c1f402445001905408484000306000c48c002c2c010803d40e5910221030714842036525a05400d600304d88007040c40c46412048050002080c0444070a4241d000b8021b0064038104001200003900d074040300c00c0101c46c025400150115a541c00420300c02215405590401001c000383e81ca040e0a482441000b800e4440408800f05041c21100c0444003d03102c0e0f44c1d210340c1c94041005994048030765110100384920042820900c06500c0020103000360101c41d61030800d11540d5448000f105d242c09800700006001c1002540403e920350301072007006103c0c5003542407945151010092860b18085000d5100c1c0208009100b03680903182d280e241520710007240003c0404807860300100a04096106590341d000c0850058107001e40c0d8918030b681c400c2c5036026103e69503100320044032044421007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 328714622 1250 328713372 328713383
    0x403031a0405191112010e100306050403020a0b070513180216060e120702030613141b150406140c0106031703070809010c020d031805010e0a03030e01110706091703190b0d 75
    0x17004003c6000f40901044d00140e4040c104101261a61a08400d48100b12025005070740f00172443c008100c0307201c221315030110b114a825800c203402561200001216032040c50500700c1c00000341554009554101c6006405400c042400174000d4908503001d8104611954128022840f00211500c121402c4034545a4001c0160100d80c0d504006260007400c02442651140c515a040c51514402000042ea24103181507015070b104c4c41500400ca2511008821002103003002e220410020342c11045d455030940406581c207803104601c44100d0300501041c0e00103416902414203110303245c0c045500542c01600555070b41504d9039502214182625040207003580181e101083c2416220b109170f201c440707000640a03501ca070620864950b04e0954120f01c0c003010050304a56581010140c0520984009100090003804440301c0c009412229014412018010a840b00c0f004010440240c0d401c407504240b030344000c1d8590804041002c044110010303864056881d0100d03a580300d00d07007040f000c2a4030341c0c0f00307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 328715872 1250 328714622 328714657
    0x20a05040303050304050a061806050c0a05031303230c0d030605220b100203031603060302010f0f03090c15020c0f03120f070c06021501050f01080403031a04051911 72
    0x66030103c03180e03400100155031901580b8050b900007045070003011811030f40e02043c07400040040c10130100301c030b601401c08081c8601c1007080e0144690800f090303950101180e242a05064514103040e502c250420344440f90000d0581c41a6401100020140000d4041902141c0c0c8040c035890043c0d08864580c003c890780044c0a140c00c400c80c010b0f01a05031083c040044000c9405401c00002c030741c0303403400000041d02503040401041250500f03032140310f4004a1a01c0c040c0f003e0b03891070f00041c10b5410031400c848104400041c80c400010301a411489800303034040380da81c0d00999034202845881340c5601118005015014201e0603a150450207103141c858002c001d0310b09900f911140c41d0140e80f1400090b00a1603042c00f480b00840d0b513541c1502d0081c0807030340181c07210742030b01c0c03102d010f9840d0140c120707034810750103140c1c00181030b40d00c550010b034803940c1400c0000381050041ca82d01c101000c3e007090198000c0c01c12080010302e0041036251403800702c088400b88614095084684400d004002c5a00742000c3e00c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 328717122 1250 328715872 328715879
    0x203030106090e09062205100605030d140d09021518030f120f0304020a050901030501140610020a030809010e0712060f0203251202030c03040b010806011202060d1401032301020a0504 80
    0x420f40080402000340007004120f00c2030b1f62010304120340c0303d1391000b005070364140411503400c00b8084030b141a20341c2d01e0441c102111240c2c0544c254000c0070340c10142c19030b45240d05001c40d1034140c0d07150820f9810f803ca20b030b00c0d04105807220500760034081045009005100682c0744010001884c0444681220031060800c0d0110b68864100e800c0108281ea0000c41c40c00c0000e01502da0401c800c0c00385005030b0000c107212031500340c402501180541128003804511300711900103035001c240c244050784d243c6001c528a03220300175558003420f1454103080c0c150040410014031480200b80740d141c120700c00d010a104843d0012060f02c101c1c04200c0d4401e005003503501903228252011010b200342000c0504083c407603020001003020032a003048410304a800400000e00c020700c942c41c440c0314010004000108140e604004a810030030600a00c003d0007007101280940c4107404a81001001c0c100504c41d003880c56960382000c5400440310b05207100460450403600340003c2c41802103448540450319183d10701442c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 328718372 1250 328717122 328717141
    0x17130603110d06031208070507021c0c03020406080c03060901090228030c060507033f0608031603110f0607080a0b04060306060501030b1813031e0203030106090e0906 73
    0x1503101024070910001c21078140665014495600a54001d40301c02c0000055400041c004800152044c070500a06014103401aa511941c0c001c40c00031203c0d0110005c0035514203e4205842904004d60040c103004000c20038400028802e541c00340102d0031200b0640b504140e1341d00f210000c2d4406500522500b00500e020407141c0d000c1d69104940c0282c4146650390380d140d2131a42c01042c1c0020002a0b030004001040c1580010070320410700c42810407250102c9015909420b035034201560040d03808031100c40900030344096000c040242088819203a0360090824070402000e0489411000720b4510841444403182c00a040800040c0f46001091075850724001a144170200800701c48100e030301c441d000b2002e41c80d240a041c1c0213600c41e03c80840e0442c10701001400303490f50714030082d0159402c000c00309080240c3e07a00c0d2a800401080a03080c901c0d8540c1070840d00c190b11a200001c0d009015545249030035400001581210f03401e60740d0f90207560b12240c19241c011020384942000782d01c4000801c00092 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328719622 1250 328718372 328718381
    0x30213021b03041203110607080a0c0c060e0d11060f24041404170903030d020c03040e100e0a0605010509040c110a03080f0f070909051b030109050417130603 69
    0x11040040e07080c509440e55252441c40d4041d800c6501907004504540007010340000700d0307461071050f1401502080c64480b45c02460104001c140850554441c1c440c4152703030b4018861881e64136000001400256603800501c0d540e0140d1007812f0340050010b41d914032901c640454000d0264000842030a070030b8541821a9007844040912480d212550880910207542c503445000c0c40d442c2100c000c1c1404c2d2400e42003081c610840740980e20202902000700b90070b2503801000f00c1e14110340c0f2080058550000c002031500d10f019942140e518060204140714400c9041148207045408003118000b41da40c03414603403826200c9e1803060b00e000c500180110902c5151640240d0070340171440c40c00d4190a40e14040c03440c5005814581038011030304140030b00c60003040050185a00161790405400b246c100740c2401814030200c0d01c62400959680c2c00070480032000000c00d200c0201548a4068413561603084590040000b0307601107900c000d00b2000c0c0042851464240c0c0d17110081888911100c80c9001d400340c0160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328720872 1250 328719622 328719637
    0x151203050a120b061c0f020a1b0501060b0a11010b0103060323011104091e200f2a1903050d0b01030908030a020a092111030f010f15050a03021302 64
    0x2991a00000c0f6003a481d402c3c094440814140580d1000c425002254805c9413400912001c0440c01044031401c2140c00800d01c0c3d280404505c0c8081d15600c56040c07450050043d0f4110085441002448142e415402950001c0c1e055441c4003c009060700b003001501210081e00c80106441c002140000d008901d40c2244141340501100100700b0384682207160300d280d88190401c10360036070348000302c4540104400164003c5c0d01015810006420740142d82c80c164031400780720000c01c1e00300080241c2001031260075110f2034034004441d14a22080c4a192450742005203640c01d00d144107800812485105414620038440d8042d141c182c50041980709000c00391006900301da041c1a01c5e46000e40004034050015445100c80240050303c591401c0d034010070b20401a4044a02102d1103000d40b4080b2807400755241005503c625400c450100d900003003420003002440c0d1800651070941180381c69101604410803400b0003200410400e0b4a42040100a00d13460002075041110309000c22705e481000d900800c201c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328722122 1250 328720872 328720907
    0x9060905060f0c120d060504020301120803040206070b0f06150a2f06010b090f01050c100f0902030609070f05040e0c04110f160303110705031801050c10151203050a 72
    0x900400ba0107592610400c0010030341380038000588003042c50b000748601c1d0f0140070b0845003545503501d0262080650a066400036090400000c040f800f1555400200c030045a17006140c01901c0c03400003018400248111902d034001c20340801c4244545207078004440c1520840e485600084103a5516400d01d09507103200d90742c90b000e4035000e0303003980c9400300216030003000700641c911342e03c4010707406104010440b00c0d002818043c0c01e0142c00060b10000ca03088002400311103001a4004480d080d2201a080d180f034081c3d00360182c4001d01c02c42c0000401c55030180c641c00c0c0c1c904590107644409020842d280000201444d401040c1c0c1928507150542047c41c0101d08080c80b1030410700c04c5201c104255005518903855194100244010507806004100c80102d00c41e0701d160420301543c4584ea200d1103041c004140309c980840310928507072b02481c180c40b11809080111000080c66502c0e20700102461001803035038440580c800244003105480c100c1b00158140d58071030810003040016a612060b083d0300020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328723372 1250 328722122 328722127
    0x42601110c06060a0803070f0f020609090106030c08010f15180504021605011b0c0f02011101051608060906010c031206030204020703031b2c0409080d0e0d09060905060f 74
    0x140404a01078081068020090846424158100300342c008143d440b03000c00341c200740b02550200303420300c0855000d6034202250143d0b650091000924511030b80088543c0441680c0010900c1541a806031883c400c0c3d81d01c0d65805640c1b0b85901c401c8500485c8199a5402401c010003244144640101904020034280f01c1c1021a2188002826070300240c8981c0382c110103079110300051060900942c4d2042c050100041172031880004000c000110081e17000e424100000040c50031a485013155440b03038144000200034034106580360313040a4000360141070000300d110b008507086140c8100d420b401850140c6541d20501003654054908134030703602c59500a83c2c1e491000201680300d0780010042d852082c0d42c0002e070003001003049403602042d000400108000c850000c610714045508417000c06004640218200100c880010050542920000c0030414046442480d854040e0894402030303000100361100820503000846502d8124814840060f202d24001c000700e0400100400e00c0300340213a0b01c43d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328724622 1250 328723372 328723391
    0x606090a03021513060305090d110c031615020c060304023703140f0d0305060d2028061b0b041202060105010c0503070b0a1503080301080105070302042601 68
    0x500340802c4504142c03054100081c03130054200c030040b6403409400c0714102040b09040451015545400d0700c0204024882d0704580f071511011b040000d00c6000304001d048482060010005100110742d0703200394102d242c5007040c00246240003080e80d03402c652018009506640d186d40801000900c28810600541e40c030035500700c400c2031030000d9052882c044018018400e490361900780300300c4041609540c02600400071000b10f0b01c03004120382c00e0b002064580807405407900301c00500120050355004124100602c440e030070100710034810001c5104200c030f070b1000c440304550038014000f5050706c5074100c1100041c02485403074081c0d44106908d41d420714441e9020300c0c85603201f00c885442600c0c1aa0340d203400c3d404407200d05604100383c07070160500380781c1100e1034a800d64503143d480c010910001c110340110b400140500041d91300907803101d00043c0806036550b940742084284c41d4000e0292160650034600040d42c410300034001ca0f022140140c80401c0d00b44442c3c2c01414600142801d181c0440d52100c00c905c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328725872 1250 328724622 328724629
    0x30b0609130c0305031c0603050606120304050301090c030501060e01030804030b09010f0903081b0a021203220305270d0209070c050601060201060501120c1e0203040b03011203260606090a0302 84
    0x300039501c84c0000710f030b4030011400f4070145108041070395100107051a03000e100003000480c055400040c2620080070649501078503d045000e2a0040d5806618005c0140244904c104003181124080c00080040d26152000312024900074000a010398008200400000c1c000901555012024500025100d0341a13140340042d1030b091039041d4001286102803080c0d001700c1c900c41c840c074861070aa0399850b050f0f001202945440080b844c03800280340210009606400c1c1c85241494112840019011002c080c0f8002c2c040d908100c0c1e0349144485004c000c109600307856030030078112510040805203044910b40c00c002c1000401040704040040c07481000740003501c204400723400b81445800124109007410001000f501d03045e00340414442c10310f040c090390207400000f484c40f101041110800100d0700c510040c0c0c80c45c403d662007840d00d05400000044c0d000c942c02510352400e48a42d6070030703224204000004810100e40c1c91010b402ca01040c003c0348007442c006c030007450041e00181207035403410750780d4000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328727122 1250 328725872 328725893
    0x7020613060b0d0b0a0f0603120c0302070806040506100b0c0a0807150e0105011a070206090f1f050910020a0506070f18030804030311070e190603060f09050c030304030b060913 77
    0x125084d0000c401401400349a6000e4010400d0b19000204030540c6541c81d00c0700c0040c0e195807000d080c40b81402400061600c20712454015000030b9085407014203042c60050f0356600e044912080d545041c0c0004200600c2c948112100c03540440c004180300c50307298503690b4641d804020b048441552144071945050307807034040c0c4242d1112880000445600d0f2001100e001000721202008850041010707400694414056401040041c0c840800d006101030102d070174244100300e00301081c404046034000071a84403005121102c82610705508100d044282640c2c0c0380c0180b04001c000350081070000c0c0f0921300c227050b4101010700502d0042c058100c1120256902c0710590426140d0060001d014410316810503450f40181c2845030003841c00c54a0421082900d50300034203440c00c0c40013001051400342d80140c00c400090354004104020903846906800003c00c505401281c0c140a0020002c0c4645008019501243d4025903100c0d0f481c2d8a01082081c030f070400918044012500c09555008100368408 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328728372 1250 328727122 328727149
    0x131407020f010b1c0b04030302070b0c03041101090b0a03240605041a0412030806031507020a051501180b0402130618080303010b0409020a2d110607020613060b 70
    0x10301031075500466010b0a64804031030140c010060a04c0705200c0801c42480d281ca200e41080c10492a515140307400c601038440d03420f020300140074003024494650008402580a03500ca80c8041d04400c0d1300f60300665004843d4810b40c0d03084401442100d240e2030094200d0b1031007004400211800c18a04480d01389c0e41c40145e081100051000320b020301205050794070300581c42a40c1d0681da410145064004900d00f515910000e0402c240f890125015883c1001005c6180120045c0069586820100259601c4089030161510b215030103100e8007031701100e03200d1810394445815546200030100d41942c0508041b0800c1c980160742000031a030507800002103c4040c1c080390740c03294030700000a4103403118aa05500400a0b540003000104140d120342c0b4111001c8a161a50142c0c85032210002666503100c2701b20004c60f0580075091040d2200030405602001012742d441d036546840d00020b0702c40d901d80041703c0c1310015a010a01083d0261522920301c0345140c803d4002103960801200820307a02090b400c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328729622 1250 328728372 328728377
    0x1d03071502100510120201110109060504110108150109050111150a15060311090904021306180f091e0c09060902030613020c250b0f0309010e06090c131407 68
    0x1001c40402411401402c3d0008031300b41c09030124a0906a02524100059030001e050011002039071001d62002e40011880c0f68102e2010031042c60b2034284031101100c1d000c2c1d00e030700140503000001c0340f1007140d584110080c2e6042c2d5541622608007401586c4030207890690400901c9495102006500c0b0700400f240b050310444400b01d4025002c0c01088018003c0760009018141400c4400e009240000127407100c01004641141d040d85803070012941d41803029040b00310850400c04081030400840c540e01d05101084403007004464158a001c0f0102c694400009040319140c1828084c01c003a01e580071300c0524040c0301e01c0345095580d040d1070300c00c940b503035800400001d40110800c6090f2900540c6075004c520080001e61074000120002d0f0f0303e40710241c1385030f031003a1500082045a41d00440000000c1d000245006070b881d4000d01d9403403d2500100c42c660328070760903d01c04030003244010801c8c3d4015541d800c014041c025240e0200100f41942c3c0d1608507102c1d41c1d1784000e8070903c02d060901d0340a2070094 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328730872 1250 328729622 328729633
    0x9030b060a170d090b030f070e040f1d0d14160305091c02150304150e0c0604080c12150c0c011803050702090a020a0c031808011103011403010c1d03071502 68
    0x403800361031300300268810a51500309108006801b041d00f0803840d4404910714100c540181d140c0e00140040025801418170765103407448940c0e1900781d0300161055204007038100d138a00342003260300b164036011000f1507040c0c60a003449102c52844656041161240c46428518104840100414118100885202c15210310046901c0c154148101e1382e8040081000107180381d0f16268584660141001035440c410f26a01c1d40c1614146030140108124100001d0440755100c1c0d54280c0207030365801201070148030740b00e80805c803818181c000a41e40b8468180000b99036840e510400b1071040c82e00038000710046d954880048207902d6259585c0315030503902c05e03103655446809900500000c80c070014020000d1500c108542c3d81c85a40200c02180e00580c1031401070504c01070349111001e0050300e540813409541c2050400038120890708007030760584510300740c0300d04e5018032942007600380d070540d5034101d020400c400320380c03090805419641241d2260160071910103d07a00d494440041800f88a00350041c0c010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328732122 1250 328730872 328730893
    0x130b0d0f0c060e0612090c040510051207141e0603160e0904030806210f0618010203010b25050a060b011803122001050c1206010f09030b060a17 63
    0x425044081c100070703d86042150341082c0842c149206500d08149903100000000304407107020040b6420100002e442841203080c40d0708020880c03003250180502ca1116403054000e140000600b0342c0c01c0341d1304004e50300503158590003030100b000111040d103070040c080407407030842c9a115000110300500700c0c4c03070881000c100c41010041815180c0400940300381d1004082c0300c04a40e0040100d900244203d07601440144640303c403245480012801c4030840c05113030206420102d001c225a0f106940c0c0ca106400660a1001458200d00c002d000314180c170304003404001c0c038420303000030703005e0144a095a40d240b0a2400361a007030702d003030070002003240c1142e05d6144c4000f035945e0000d0603000004000c810303401c10750308503a07920307803680c6aa5520100700108620144a480603003402048840307641c030020030650518010600165004200100b181d01c440000716081e54461051600c58105503034900708043d0450b5901144100060042c0c0c5e40700c1e4015001140e410080c00ca203c1c501401a002007003034024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328733372 1250 328732122 328732133
    0x6280608030a081509041502090d111203120a020f0720011206120f110a060c020a06110307020d02040b062a0334080a030e1e0c130b0d0f 60
    0x811500c00003031392912441940e19500710b100c0e00070b0b520464040c1d0420003581c40c01d000b4041c43c00307015071140061429009200b28100c1680d143c0c1015110b2003081c21304503483c03543d24410882d60307800b0300ca0394400150f56024241d020b02801c0c054070b8282c0f071401009171220710700c0c54038803005d44141c0740102550031400e40c0c1014044070412048102801120314040c0300700003040d08048041c0c00e1840419146041089504919000754401418180010b0f00d41e04010101c28026208a029a1200201003007107070240c0803561003045160029882c0c1800307039003886104110418200e030000d49800d04407010b6a10340003d00101210800e0b0601c00d168120071440d000791045000e00080d410030060103070072041000c0c82500c042104031554501c2c0c00403003ca85460220b43d107024044101c04075111040341d40c117400802c44482004200c660b00810042c003541a00314980034100c081e0300c807241600f0607003800d160136007001008040004a10482e00003060745444000412196000c1070b407101010000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328734622 1250 328733372 328733387
    0x6161202010b1906080417030708070311160809040e03030a0b04150b090d14010f05060909070f05040c020c060403050c090a0203010b0d020d021b0309040e0f06280608030a 75
    0x4400315075030240c0e910300c8070903d84056100c2c0100d40c1001224400117042c0581e02900d90b450301c2d90010720355030301c1c0352060004100c01025242c200009082102c102e0540401c80306a5050130b61031002600426040d0361044001c1d4495120326820513221500c104000b03400b840654422800e600001c11080c3d1200d04004c00c4403103600e55220702d8041808180500050b0009403200d44004ac0c422408180c41820700f08180700d4400904030031903003029940104a401c40e00001d01900f800d0314501401d1300c541c3d05150f103d54140c0103004200c11100e2080059207001d8115810792092801500e081c4ac5000340800e01c00d600541060700c8913400041911100d0130080c0107a503003d603040100b14190b504084a2684901c0b4440621302c4181d00400c0c01510110550b048070811840e4942d80350000f4100303011075440750445220184907614000c0502400d02d40800c0020703003101c82c0c1d00a07120b256541810707059525007106a440035032a0a002c1040448814801c400c041c040c2c0200641e12154070307100c01803070312 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328735872 1250 328734622 328734641
    0x804291006051206061308061501031803021002160606030f020102060c0307020c040b01050904092102030a0806060c1f02070c0f12200613050406090b1e0616120201 72
    0x45070030021060351900c0c0f501595009241100c41641d60a000d8a8071464500c05030011842c41c0100403d01810040e031000c60419036500f030301d00340203008042c0c0d03c4008140304414060096049144078408020855000f0008071200301d04800c4035a04607101e0004982694004071015411070200205560b01005402e61002200400d145140b40c8210700075121103038584041c1c0a40e07150504548541c0c01601900c5030740340080c00800159404d400c28203404c407045200c40c001524a042d070001668804000ca40c190071958a5980047c0c48800510201e43d0044c00c40380c480703004040e18203c0d00a600d9140c1100342d2045080540c681c940d50070101c21862096002c0441d41207014010090401848500440141c104d554051401c0d000310215014158100695601400000741e03201c0310400c5660010658030152410400b140d12004030004035144500036560104082500024007140c000d4403444810700500042e040c44010715245201c4d4002079001c403809071580e015048115030921924822 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328737122 1250 328735872 328735877
    0x2512050a050907060c02061c0c030b090115050904020706050106050c0d0207240201480509060d0207150b100c0201090b0c030c150106140403080301060804291006 71
    0x10790030074108050b074410280c802d00050248403014801550380d541c00350b0b09800c010381d60700e0384540c2451040030b004200014180003c2468641d076003145051042000f41611340901c5d000e190410b40040658442c1c12010105901c20380130001c44000881c5401901e0007480985c8909850340001d40b541402d04461000c0d4604647c003840b41082700da0411050210504145405030000400d4a14200c1c050110800f80220200407200d543c403107501c202e03090586004842081184180d1200000c010400c03140b01e20000241c001e00c0005164503120008101c403c4010b21f0040c607008180d9a1403031014181440d40621955800307441d607480c1400b144a5001c04040e01d0084c000c14129800039000394013078000c0e143d0100c0301280c1d500803088208221450001d01c1000c840311080c6100c5c5440c0c070a2003d004020000d031001c0d641075500e0b205c000030741e4182c0f940888550b08581c01d051040310800d10040003034440e0640301c030307010b0500060100e12014080c40d020b071140c03661030070180034182d80c68941d101c00304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328738372 1250 328737122 328737131
    0x9010801022704390306150509010504030510050402040501060305160e0d0803010b0a0e0d0c12081b0c0108090c03060129030c09040b060f070204052512050a 69
    0x5007001841240b241d04101c07200d00d01d5100d02d020114008000e0520f0848041c0210115800040064844060014413044015030070200040c2e08405940e241d1007995440c004032240000100e0041003d032801d1078041c501142040ea0303036201e2600c0c260311802c04400c0140e030303841800b0650425028250141409080510940c1003880c12040d81d2949200a00200041c00091140e2a0344620591900395000140c0c9138807561500144001680100000400b16500a510441e1410503c04025403e0b80180100082e81d03e40030700350300d44107582e140494038000100045c1d038506150020400301908400020046103d0590000d40780c980080d0020480f984004041005550001005819a41040030404681e10b50030b0b94804008090010701120390004070810141c180108050a46010125001d10040c0560420301445214448205007807031303c10890fa0015080941002d900035070f9100441604507030701e021840d9491465204800002c0388044088a100a240907058114004080410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328739622 1250 328738372 328738387
    0x8160302090f1f0e09011a0904080d0b10020c152506141f151403191503060506040b060a2312180f030405042a0903020901080102 57
    0x45124500400c802c0038108403100164a110b00040510150b5100104680c03006840380000e550a00d012240c441d06503182020460a800140511014101016100c4040b54a558447c21580e038000846081442d4941034105803c0d2250300000011180d2139000e0281418032404001529141e404580084d1a05020020580b50002c64080c242c444200354180e05036504c0c0b810710098190051806403003180e900c10441e11145003e82000316000c4d149242e0586031f1242c80010840040e189030100240000029500800354130b0f00440d0480c0d1a0100d00c3c69070703405810214140c418030100c00c0010f0550003401c000300403e82c001c140d0480d00031102800300c0e42161001c11014010700c48071008005286103000b50b80c007200310400e42601c601d03c000f542c1c0c84c0d00300074450605410943d82428601c2450341c40c2005030101051080300240c681001c2d41c0303854540300400c07003c1c1001060512189100dc0000311a88014040e00c00c400c40071600e40700301c890314500410640c800140d21400305070b4010403d80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328740872 1250 328739622 328739629
    0x32103020919050414150402160204140619120b04020315010f090b01091a160602030108060115021906050601050d0212251b03050c030d0608100605030c13090b0c030108160302 77
    0x200f85c6461b0a6400507226840c0512446107040e260340c000c0d40082ca41f108043c01d075003c1a03078883c821601130781c2d007100c0350b40500c01503102d65056104451030206030f09411000207400c0343c401c43d08180001e0032a40c4007000e0f180290b0808400383e1000b908600c41880c1002071460340d0161280b085800d003080c0c1426842c10742c03540c030861204070140000c51030020700310f40c82110610350000300607000841191690784a640c01552610700b070281d0001401e04e980e09040c0c0903c009409441151008500ea0400392141d840e980a0140075102078140802800019020542071014111f0a417000126041500b4106020842c229220f210f0803844401c801a290400342c10a10400e13510422440740300354403807079050071038281c0541e07021112a800001040d60105096030010000d0f9850041a10134101c841d5141c1822112244956500b6070080d10519415141603480501c4200c400203020914440396a41c2c0700c003030002201e5000d09020b0200044c09504c40401010100c0404052806030303443c15034000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328742122 1250 328740872 328740901
    0x90c1503010e0907080a05100b04050c090909030d0c0e0f01020705031e0a0f0302012c0c0f1201020a0c0c0b0403030516060b1e120304032103020919050414 68
    0x202482e2080110100309020002c0108400800c042401d6036401d031210300c0c1c1541ca0b12801072040000e40d0500200d694145031511900d40146403460b11580350004030800d00c02070106c0140070344424003040c051000070310224010b51503140115910740a400c815001084020104c3d0340f001411503001d1001840301c1d850000d01c83d201c014035142c141e003039140c1105005140401c51040108a401e07400113103030030141c0540064a0120b1035078400e251129840783d40c9002c0500f41325001d160799012a0f9901a03a00307008032144000303000a08280c4001181644007420b81e440015040c00080725a1016010b100720150b480740035098001c0418a41445e68600804600803442c10540c80085032044070b041008503484011425800b030240c411031840d0740031050111069810582c0650090658104800004400c613001c1d0ba40c0300f00c002900c03100c031140340b4007020308007454603090690070400c5000f959a00c55520702c040010b003142d00c1c0881d0800003440180d0b240145641241350552090105e681e955850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328743372 1250 328742122 328742129
    0x612050a0e0a080304051207032a020f0f010306050a030803040b0108150a11121005011808060109020f0f030424020c0c010e13060f030215040e13060b0612090c150301 73
    0x940c40d841e601d650405074140b0707c0158100100e0310000505808054012a01c08050841c02e0b4810960601e8040b2140114240300c00080d40110041200c403040c2c50640650800b511040c580050110307120000702d0300100c10754000340e5801d41c01004100070042003264250141c1103030805401c1c2002c14031103100000c40f02074642c050381621100c1d00c6085010034815640781b5296401c0b0300c041030510a099002960860059500240007440071040d41151341c51800102c410540c001c00d0701c0c0c2c0c41e1000c40d1000b50441c268044a200b000c0048041c0380c03ca403000707107003d00e01940c0040019941c8140380081c500b0340b1000050014010700481d882c101d0040b5180e15000000e0074440d8484040e07000150b9000c0e8000858264186481000704008206442081c16280300361040c4040440000c007101c1e242c0543e00c250000e520b11440010110240c0800842c0c0d46481a14041000c910810010706a50800180c41031600300d8a0100051005c007009842c040038810346151080950350510704220740710500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328744622 1250 328743372 328743383
    0x1e0603040f02030102030709210305180102010e030c0c010206060d12140d0603050a0b3d03080f0a0e04020f09040e070306051f06180504090c030c0612050a0e0a 70
    0x501071001800c1c9100c0120390050085540f80742105010f4000300d847d020b12030081c19000e5544034200007607031040c0308490b01900c0301c5007804612189207030038030012980a0b046540742e0900c40c4507100100040d2800c4207141c0060540e41c82c2080009140050003410144540007568a03280440c60120301c0340e034503c000e45801300b04032501070042c800c14400c060703100b040340e4503006000044c0f02c1c000c207038240360714410320740064581c5450300c407406404c2160640c00344002103c0522007a40c010240d08041030001110280502980c81c3c542130200d40000700c2e00c20004a000400c0800160701000003403c40c6000c840850030070b0450702d426240d6005682409010b25514600c14900c0d0000700910030055030320000a00c0746240c0762040e01c40c0e103c00c2401400d9141a54000441c40a000d18002c3c0d01100c940e00d03400b807030245814100300180c2250362080d50708081c8801c000c400b01b521006072001030034031502c61060300f038001c85480003162070040c80691744600d80b440c800d00b050000b04801d1300864025 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328745872 1250 328744622 328744627
    0x1802040b040b1c0506090d080609040c1e05011115010603090305090409050d080708090d080a1b0801080f060c0301060809072102120d1707030f0e01020705010b1e06 72
    0x400101d401812607564503940306500071034141203070300c40610303941000d072150050b00d210303844040d1855070341d80001c0708403404607581e14001000d9013403c07000b0b6070f0b0160140d00a5444181d4801c1c0390440781c2c810101c05203403203502d20000e20007943c015940b5a0354200000040030380d034852100e069421201070060f441015103c02c800f805051260003034980c0300304002e0042020100500c0c04d55178400010b45501c01184103240080c04040c000c200152103145201d002c1c141441c010b2804480700b5800608580000360340e18034800300b00c0604080c4040c101c099881e01e207841d5040011883c07800c0b801c0b040541d42a4054420410b030445c4400a0320704641c4d46050110042e204c2c05d01c1036040c81c04035048403021010354801d0001c520300c44202c0c860740ea8000c0e0356051707000143d410740c103441d011080c4043c1b01159500f940c02c540c0007948200140d010780ca0b4900018042c1c020150202a5109030a609130180e4010420605200081c416441510812100c19641c4c2c0300103041c100f0310074a14003484e132090801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328747122 1250 328745872 328745891
    0x7210c023405010c0f0b070c060212010f090204030309140f130506040b12060f04060e0706111e070b0c0102040f0e0f01230f120a080a12180204 63
    0x8210795400516140c50146005012001d955011010203405a1001406801c0010994040d07030030107100c02c1d0001c1c4a029000e0442e11031540304400a4458410800101e4802c00440c00714400780000e8146c16058540035458030080042003a03c64100c0d01c443c0b40f04000800000340c2221420080f00c00c010001007a030b000080000d03540d5500c8000c0c850f0030506501c0c030b09140d0340b100d40c4070303d20a00003100e041114012072014020030410b011b141d0102c55200002050704518004040f540c02072180d4000318012168109071800c0c0040e0354440d502044191f0741c0b003c4807000500115201030b400402041c0c002107208001907a034503c07485450000280010002c1c5040e40a4040701c0191034403100e00d9210f1f60f07469201c03010150f0200c1e4001450001140041119035080500c41035000940039220340703141c140010000c8a042c400031141c0e00444415500a4102051000c00900303409030384070b5900c46103210005010300401858984030185022004404100b010390410322003501900c000560124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328748372 1250 328747122 328747127
    0x601081611031b061b0405011b0f0c0602030c301315050705010e06161b060c020606030d0c050a060f2901120204140f030709020c010203060907210c 65
    0x207404103030410381c030031600d40c8600000004c1c40c2c5002c1ea0340e10482c007440440441000b40903001c0c42c02030600040e10281f50301c0c10300b01542c050316203040c0151001010b1801ca60b0380d81110350400d0b4007650142c2c101040350001c12005121421060f0200e0318601110341c001c05504041c6504601c00d50302000011800a500407184104000a1709045007041184600713100041c1c513641000008503000d6081c447d9101490300040b0741c2030700503566207120042c4980407040940304051031800440390000599001c2022418038081c820416800c1e4003d050309040c4642131609090551501c030040c8200200c0d05000100c0004129541d590803041c00501d41400040c05d038054480c00d0360040c0d000c01d01c041100180c0c801080b0005000c40c00b600c441c03042c903c042d17000070180c0c041c91082d6910100c0200c043c0f0380340d06006d50110b11900c1d0081c25124203075140c81190f01240c101c3c66a01e0340c0c580d03002c010003501d030528054290300b01d8006d00b812540041009039502d1b0220780c65629004071503d4182208040c2e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328749622 1250 328748372 328748377
    0x11121c0e0f07091d1606030e0a060f02030f10140415150210450206040f0801140f151f030519020c0714060403020901030f0209060108161103 62
    0x482000c15501815030b40c0301c00c68050442150624071380114000e0000100d807001801c03440600004151880e0382d0314280d026402810710007103030560f1340a140382d8500020660700c6005c09400d40e5550041e120304024508031041c5c00d00030685c1c01c1800c4105824043c01d48500500d21980c1c1c0215030100350791000c03800d07008900040741c0c07024414503001c000d03551440d80c0102e84c03240304070051041002035034152248c00111008201188070075084240d130040d24190b0850700140034800d050480d510f80152139001c1042c5501c117501040c600002034609203e40c910a005402d00c40d40842c4a07048103003001200303190022405089049070340800915a512500c902102011019402c0709601020640c40c1e006805041e04403103010212419000f040c1220b1840d02c241c2c0c50882102d001003034410300348140c00d400440c0b1900c0d12030303200c1d40510000005a885541e500d01840c400c01840c2038240551040c01040d04c1c2c00f0f007105060080000810507054403506130349044d08420f2030320342d0401550013045415132 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328750872 1250 328749622 328749643
    0x90a0e060105041503050405151003020d05030c160906120b010909020a09020f0a02070f060806060706201b0c13020a210c2303010b0c011b11121c0e 65
    0x30304415110704451178140c2d0002d8865800340b810760b01920558118201000000c44101d403103101701107000c0c405410441380c00780b0b909100b003048030710780115014241d180550700c900c41070301c0f0704210500b0320040045014000042c140d03074150000340c6907641d031980a402c205000c1c001c040d940e42c2409409541d92000710000400c440740d81155206054001080d880d03002100800140c410301100180e4001c50082e00d80072a460b96844c040603407281c4081110960100d0001c0c5c48003610364140d240943d607444800e041010007412940c0d40c884608184420029020340080700c950801c102c01040b0307459649808007161040e4000590740e240900302555452119010200a003038901004207080b503c50f07010480756100343d11800d00007042c07600101070340024200070310744c07030001030004000c101b4000020303100c590b034010004951980380300c03508903030380d0031030500701000442414003700c4000d0240003280c02c80f081c0c0071059241900071715a007201614001c0320020420355a00c10a1840c0341d0902c01c03840d03807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328752122 1250 328750872 328750889
    0x10611150f0703330b040f06050306060d0c020601060f081003080a0c0605040c1d07050d0203041e030801090b031222050d060f1404150902060904020409140c090a0e06010504 76
    0x85030034a070014800001200c608110700c200c0d10a000c600703442405c0545046680324610070816909090b41200c48c0d030005081070b50803440500407150040050b020b004052481507009041075071400c0402006c0d00d40c580702040501c20114140401c2c0b01000050800f41c0c1e402080d031503603424010400b250790480ca1071010302110718150500c07040140c03035210481124640890410254104100540344001c155400d0b00411020040f64400440c1d5401842d8001d00595101d0f2030b800c2075400c4008014840903084001481c041c3c0148001500c0d4481c02900441c2980101200ca40d158400d20861241d201c0014081c80000c1080c02e2001c50454504c0241c20301500f1014045a980382000140c03400f4540c000d421814486d500400c90042c130741252040b40c0000a01c1e078001e10841c103d0004100c0d0171001e83c0c019604205024403610b46000610040a200600145001d009072202a10760ac4c09040848031080c2006481c4465413504031000c156510013001290548a150060b01d862059074030070f62a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328753372 1250 328752122 328752161
    0x7020f04090b0f0405030c1f0608010506090406151206020a20030702130f02040803040e070804030c1e02090c0705070b0c06041407081204051011100c020109020303030f010611150f0703 81
    0x11058018101c0c50201c23000325424070445407940100381c26503608543d00e80d04240e16100117008607940e50046140240d0329540c0b81c081e5921840d8100e03590f01990800d0310301d2500010190f03841a4441c0c055001c102a041740310a0340c0b002c3c0260107843c0d10a0901c06403181c4164442800c08246540c420091070000349030440d551030759440c0071520394025120b10721407485040006400140a030b0718151055038180e43c0c0c401d5030111070380c500d484641168100360005000844a10060300c40041040c040d51461003a40e40b140b449181541c82c15045801c00800740406210900400500150142c0c001e503010392000240c00002856a1909030715501c00c0c1e6552003a09482c4c050444400001e00546009070b038600014280540b00b51a2003511115070105a03000403052521413081c1d074008000504240b00200b010f042e55000030f441d42d0000d0b00c0c0c0035040003058004008083d00009072484482d4040c01404509282c0301c1800000030006014440c00f2080700c0010360342e00d01c01d40c49030b06900070103284c0c440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328754622 1250 328753372 328753393
    0x70f111e0a05120c0a030f0c0f0305042102061218030d060906060309030e040e100509060a0c080c07120c0204230a06140f06090a08010207020f04090b0f0405030c 71
    0x5540d880880d01c29a2035001e40d0203011103142da148100c840341420003000b00001c00c4555003c4500c2e1168004d404104210b03800101d0004841c03615004031240260384003a1218100680b0070113805003c0d00ca0500c0090f00302c881c100580322a0b09813184501c1040b049041c680e10060b1043c512204c00c1c07034000607030000149002440e5040d07409201a200400790401a20f61185010b604450550b5409804920141185030207481e09420400718090600162402a01d00d0000d200541d0303000d5444c0b6082d0b4002c0010401a28080c1c131403002c0f51441ba1a000e1081d0510141c4d12009200c4e404020f45140700b05904c0d072201a000c0d2000b81600390f4007401c00c00c588919482c07400403460070034145400e18010344001c9800d0306014000c030342c00d0310f0f0711030754440d5169032441c10040010342ca50704840c1c00040030f1112096230769840240c1e070028030480380096601d4a4500c1006201da80c1e60415620451405d05d45002040c1c01498990b4460010750300d0390025200e9041452a5004420902c102840b4560030034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328755872 1250 328754622 328754683
    0xd06020f0c0d0c060b010305060102031911190203011503170d061d040303150f0b09030a08040e0f01091401030305180604090e0f01021e03070c0204151706070f11 71
    0x480081c0e008010802c81c03111740400440a5074025a5283e0041c2c1c030520511158092006003000d82030b0f00ca080400000b4920760a450030100403140f4802c4040000703100d407041d41020f01401030741d120711402a0f80c0f0b00d81140da48580102c5a03010056540c400401c0c007002107008e640c0400064440c00b040c841c94410429030108080d9402c44044000a0810310800142d00740c06921409039010052001c0d00c4a00300105a241c1e600140391060b40341c42985205004103421000510180c0b010721400400c510f46107100c660040b4041c0d008202c80d9203000500c25020540c5800141501d82c5881c0080da20404200303180100c1d031002e14600c0c1c1c400307000507001400f009564840b1121090707a80541c0c8070084400d000030701300e024110f641c84100002c2c10039070a049441d5001594007176024101103528484540100d030865030007800d800c0701076503c80303002d0248a44800302c6461a078101402010103140045000b480b00880060041c12b104401003802503c0c02d052010200c100a084901603001d043c86016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328757122 1250 328755872 328755887
    0x705250b010e0103060c08010e180106051011150402060d320601030f050f04030f0504030c0602100b04020901020d120902040f05040b0c1930060303030c0e0d06020f0c0d 74
    0x4560061421b00c00000039070040c110141210303404a140e075150303510b90079154010407484a07c50900d541c0d468010805540b92100d21340c0301402559490841c060411050349441340e0400800c05000c090020000103030349801c111110307880005404030700021800300c400309281c012480c0d5040300f6000f0341c0950342d0769041c0707402c144108801d903010300800520405c131208a810584826040c3c06400000502090084912032181a5a45000c0f40750a5480d203c4804248003604a0401030f005680200070304142030044481000044808629085002e00080c1d5543e00c0500c900c4e090001110301e460026901e5401040d4070b90b00500107005900101c0c112100030002100e00719424000040400c0741e07580110f0659034401014074452207036100703006040d929242d50072444400c000e460945810014440c014100c82c00da01d541d03000c00c0351030541c03901509550300350ba0300d0030030451413160010003030780c80c000d140107461b03005000141e44405400711045a4816900e003a0554032440c25022040c56002c0349 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328758372 1250 328757122 328757129
    0x12110d11030d03090b1506120606091c110604180f060f0b07050d08060a0308030c07061811040203070212071103010203011805150904030806040e06130c0902030705250b010e01 77
    0xb00d6000f075510000311b04441c8250660583d04035800380b000c10301800b907142c1c1d902c0c1c00130f03c018012401c0440c4640054201020003000500b4000961004010802012049000301c0d4040724801d040505101102c0c1540001c00c0325000c055484800d09841c100c21a44180302504012001760f100a80740d08111107180d007c0380048940d071013148900b4456a118080c150b020b0100104120301251031600c846005070000f504024400c0b00070040400014228803602140100b1451002000c8400d400c26480ea02520450140164010010041d285030b000c94880301a104541d0311076101d60050500c4200041c200b080d02d6050f40c800000819034404108881c0b030b01e01e840c4101445142d89203c0e1502050803084c0203160005517a00100740024021460f05500040c0580002000b1620001c0c0034600074040c0c86100020300c10842880a1011000300f24000e07015401d419407550034101c4008001e4801d5a2130031010b1b038005250580502100004014031942041c61031a003075864400300e16260381c1c28030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328759622 1250 328758372 328758383
    0x902100504140906101101140f0610030e0319050d09060509060106050c0c04091103070b090102010c02060108120a180902042c01090e01060504230112110d11030d0309 73
    0x810782c001500d442c20845200c0c07030b406072038180d5801c640301c01030b60344e00264400001195241d1004800324241030b00400c3c461894000c4100b03590404c0020b1140100006440c44101410030110010018001007180c0005400c0c0001c0d0040d4800303014112014060007005030500c50030400c0080500460740c0040b400340c0c0004003034815603640c5c0c0d1001d580707521900c1e1000d5019040180071800c540b80036032018003028001d0030f5041202111400203401d003542c5803c02c5030780c0c4d140800c5404095a092107690420f13105800184815410300b074160390364050070401484080000102c69110f988030340b00c0e0300040d030b078801c0451600d261160742e104040d402c24047d03100d400b513030700441d030310100c85404443c41c140e41da0b1541c0c42c1d1280d00b055503d2002d001a6440001c0c41c1d034903440005031680f154400c0b0f588000261180827a03107036901c088522031400603402010200c00050310b510110301e502c040007540f20011101e10a0070180c2d8070300708803142c0d00111940d906001c0d00a10b0045550182c0040c442e0a101d103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328760872 1250 328759622 328759649
    0x801050c0d05180a1e060c03091211070b03090307050304121e151d07121703100b090102010609112101060507020f030106030f21090506090f040902100504 68
    0x1104000003451002103d03440a5018143d0280859010b00c00c08030b162040c4104036411094540710745059807041401180005d80e210130f104140045440e10596a01c034600d04a914080e07030700500e603951011405a4001c6410000108688100c05c008a60032694001c0a80c1d4980c0d940e484041185a0b454205039a01e1000540c094203007144091090003242d0f2101c0c0840d5500580d030000802481104544100c90000b2100004c8020040000d50000d200ca800201000241890324865000501c1418031420000340140001d41b550f040e072070320650718044089516101401e0040b0701401d015800115518581800121b08403000b02c020841c80c184074005801501103040507201c800b400344034040024900b0320801c0018a010030b80c901410308010004510301d0384984410b400c0702e609000c00ca41c0640c0103645034091007400702e501d2801e0010b83c02c1041e0258a400c0100d0294800e01d04200e10444a951170301c00b9568490744544000341c0c01038000d600e03440742c070f1501038020b902c14002c2a5440307401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328762122 1250 328760872 328760881
    0xd09120210090308011205070e010b0c0c0a0b090d0f0803011706070e0f060f070b090a0302070e0907030201110f0a03020c0a12020a0915180605101805060a090801050c0d05 75
    0x1540a0a00010307450b13998446982e20300809544840e803da00110781900800f2400a040000c03a0040d0b400b801c46034000701c0c0d80310150841c651500303600c41c8030b00c0d0103010344490130000c041e80300f000e0310078000b4251a20001d441032072402029000078030000078107400e40400046501d496451110054540581c1182c0f150740300c02c2d009440f2510102c00f616400312208207010030301d00300900600340301c0c11302d401075500303040e1240c2d1044c071407000031241501e0350390241c90b22000703150341048680c0042500051040140c181075144c684c40c1c07202c41c007010f418000703a8080c400085104100003d60034661906441402e0850710740203441d64949980b29200705511040894451029004a420150300414100c452841c122050000d00400c0d150821200705c41d040004000503100860f09010480c0100080e4150070001005181540c400901040013100702c3d09840d58001d9000c0359003a14011a485a00c4030740a2400b101c4c0d4004640201c0e81a500b400148103000d1501c40c0901000054885c4c2408240c1e038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328763372 1250 328762122 328762153
    0x9080a0318020f1e03030d0b01020705011806080c161109180a0b070e090711210711030f01110711030d0210090201031103041410020f0703050f0d091202 67
    0x7281ca202a5000042c80c0c900011031800850040c040e1a034016102ea41110340c200003401c580010717001045103a102c0b5a24401980d0511092000c0c2900b400c001046d0304528144107142501c2d400b411381030001000c0440c1034000080d02f641c0d40c1a2440c4c210002c060610b140008c241c5158082c05801045080c02060340c030212041c1c241c0f09210010001c20904000b900c600e0304048000c0d10600038407210720f8804c0c14588981c0740d00792085030301d078a0b1680042c207041801131030880c0090780c00078018130010250545280303031000c44583c103070450580b0b4000d4110b50700003410090204c4081c0400d600c0c01d52400210040140501035103030050360800301c607502d00020316494030b04941007140140c0107840802252511076224074009030041c58001000d030100704035901141c0c420b5500b907807100094600003008640402c420219900c01c070b9415410316000e0842c4494602600c8001814490701148600c00c004100e000d40352142802d01d000d0121009508182d13103041d0044e65040d0050007011184100d094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328764622 1250 328763372 328763411
    0x9180e1c0c020f19060206040b0a0501050f0609040f02030112030e030106080c010c15050f160c03020319050c0102040906030c08010507080c07020f030d020601060216080303010e130609080a03 84
    0x11a0340d1a00c07200c5411681c208045540c4443c9942d03480301080003d071008071400e21160380a80700b60b400800b46414142400240420001c01d84078020b0300701001403000f40c8a650180c00011400d8650603110049500000d001d010070f01f000c1c11030705101000006000700f4409000c2e030041d001c2d4030f03260189a00c4500303050030384400380541c90090340040d0003050306500c1840700240142c000e032200c2481c06041d003080c10585a0540720940501011014481c0b001611030000180711b1113410592aa80c80584d4003a481e4051440b60300c6c60303203060a9004c84500e00600031119000d8268000b156955141e413118801410a8001039481001c00080411004814842c035030154265843d01d03052640c43c0a1003070000d900ca200201d80000c0a80001c5410351010885601c821049801078403a560608070000d28007102110003003030321000030b0700420003000c00ac0210303810341e0017820040d40c050382e5200c1190701e860403122009003a00d2802e808502803003040006403a0b2014259424031003045c082c2c00d0000d004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328765872 1250 328764622 328764673
    0x90d090b040b090d0510020c0105150d03140c07050a032a0f140f10080105100e3a03020102030f01050a0311010c0507093605031909180e 60
    0x1c2c00208280700042c500340c0f1902140d01c0c1300710111502e5008414404050b070b009450072207841e0b1744445c00c0c01443d45603403a421120440a0350f45001d0b11405481c004c2090b035104d003400354015800510920301c548144140c0340506805007140d44215521324050041c048900011041c18400c1d03225419022940c11054049849035501210402d05004440c0c05841600710802d51203100d07150f2241c601c1d02c80c001940e034400c0f200d403034801d680d61401c01070103541003040851208000318000c0500c056a284507440c081030440c5a0307035001030101c09490070305140c0301d04c503114910021003500b10101907054008611039000c40c0c1807034039180d0b80e64003440b40d454901d00004110001040c002441355110b1940304d0720803401a01155a0b043da10700c410011180740131540700401c03111030007200c50140014000c50440313004680100d0002e0103500c0c1c040d1280904420320880113016603030880c0c0300780b04861000180c1400f41802a0740034421100750300420540c20f0600c40d6000e265034012505c0400130726018003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328767122 1250 328765872 328765889
    0x2d010309031e03140f060406050609061806090d0807051501060c06020d0b09011e05060909040b0c121801050702070b180303130807030314250515090d090b04 69
    0x1944281c0034034000d0350305110021040598404500d12981c0104c0c920a0050880c41c289404904010701804181c4030a0382007035010720401c01082445440300800c1b51b007003c52416840c000000003500003146441141c00e0365038030610030031864040c00361341d500826181d803040c0102c51340a00c02c41c0240303800c848248951408100b10600503804164185c004180716840c88500203034504028000403c00c0e082a004440e00c07020040c0d0600b500c2201d9000da902400d022508181130403880c600043c580c04000740001c1581c1c1d030140100d55140d01450664035003c04c00b8821690920340031000728054855440001043c0d030801d008290a02c0c0040f80c681c041c0c4804d090301c507107040c950090a20028440313003102e80d014441004640d042803248907020001d08101405000300300e20350f050060000b0260300cc40001c40c49c04101c921000724080c526038031100d807404000d000300003441c1415030131702c680e000900a03d0b000c501c0030059092004110b0381d03580426511082c4c10789840b4021445280928040c4031f07007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328768372 1250 328767122 328767137
    0x10f050609011b020405010303080601030e030c030702221e1116060b0a171b01050301080312040312020319061502061b07050a0506010504050705090105272d01030903 73
    0x1ca03540704503821802010469a00703c2d0440703203a808503045070000d078803c2e170001e0021400e001043d0f0349401800581c0f11114010740c1040300a0005a4070b922451000901c555170342901408081d050b4400c0000d03408000e039003049003507075051482c21800c1e030440e40e41c000689000004044504480d064545480000320304c8040690700e0740d500001081d80e04682c6900c42c915641c0011600c000130314003051954105e018100f400030320740318469003401da0b05809050000920051021040000690311400034078065a0300a40316820705583d00c05000700b608805500000401004003110322101d0461582e14104000a81d91501d0b41c140f6203060040b0f810040e00414041403603811006030861000382c820030051f1400c81680d680a10305040400308607010341000c07004201c00c2c0740910500782c0c48080c80c01d20514103400800028a0b62040780c48241d0104808140c1c04144030070703030720480b00350342010300000088105440141b5a032052101e000b002000742003440301540d407290003107030101503040d1503804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328769622 1250 328768372 328768387
    0x1501060e01030e03190e04060f03150c14041e050114040e090c120f010c0203070b01090e1c0905040513120f03181406070201110a110f060915010f0506 66
    0x1406405600c10031000c91000b44031781d40f102001c002ea12105a091516104001ca0740003051005903001c83e80082c50007240d188082010421096200d009004604030016580d20004410b40c0c40400b1201c3c194044000880c020410000c10171202007491445581080031a5403a001100d0000c00700c00541d03a4000188401c100311070040392096040b124503015650034a5514001c110040a04a0b1081055103e0003600300311038001c1c0b06408024025201070740c41c1200c1e5444102e2000418850058890340d1130007054520700c028446030f01050845138816100f024581002882e0912600406200713501d44008104140140041d12040645c40344122649005e9020140c0710920b0b00d0510505158031609041d1002c4a8100c41c140194801e000d0000e19014404c2424a0058000c0541042d60300d0b042e13801d69400004001d42c1da0b0b080c55403400c10310180d28081d42e103003080d4018190b24024481c01c0140003030000b001c60248030000c601d030030304000b980c2d070741c032140d1621451442500c1d00f0100410011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328770872 1250 328769622 328769627
    0x6010906030e0309310203071b02030c03060a02031b0726070f0501020403030f1b0b070903050601090606020613080a0c0606051807031109011b0c0e0a06081501060e01 73
    0x4072124500100b039a08040c0759501080c10412031a08000d1724282d07482807a003040c2d458aa0304400d0008544045085152105010741012880c102034403108650344c01d00310840d84c040001c444003000c00f40c01d0700d600c0d040030406000a50000e0702c0c0d610b42e10540001620170010401c0070707205001e8003c0d00102c181e54410161404001c041e580c50340140e2000c003c44070104800006122901d84990001aa03942c42d42c100208142209e000386820020b102a4455404000540480150341c10410f03030f102548903c5401d48115072030343e0005049005800c0006011040d9500020480e02c41d5004e03548507a50b034240c0e04000e0f042e91003004100c0c600c18060901c08030b128031302000c3c940303100e40c0703001601648401c009003e03840481c0e100d80311b18050408220340720350705002c0c602040c1240441e0758181102140080d00081d400c00d0803145403410b80c0c440d01d0030300500e90b6604004042080c000d55a609100c80c902e000761004c0e00500b00705102c4c28007001130700200740c80030754120740081d5903070f1300b09800c0032004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328772122 1250 328770872 328770881
    0x606010f1b03030b030a03020a0605060603011202040e010e010905030c0f070f03030807030b0d110a0b0408100519050f010317120f070c06060f09050c1216170c090103050f0601090603 80
    0x182d003019610b240310690703030703c040011500701400303a001000f20021904d03000d800e540d801040e00d8083c28080c4010032064694a050451f0305604850100c1c03108248100140101045040d4000079030074204e049080c072a000c4001d00c0d24400107400d4a140800803140150790360f280781310303031900c481ca40c810800200e0b1052182e0703600640c81d8580494004805000200e40d0304020905880c0100d1181007000545000a4004014602c080c0c0b50741c06c0c80c1c03401d640b075503c548181068940440d02c0e0f40000b0f0100200d040c540010440388603007045035003821410440c1241013404102e035040e4400c25941c617050803040990300ca409a040b04600d45035a44207507c0030ba400040d0680d000c1c0080c0301900c1c0c0c00030302e15001343c002800030400038005040c40c09252005a400180a00b61139990411814440005a4200550050006104d54088980004211100405c030b1010813102900740007841a03205488000300300001090340c0c10b01054a52a2150f03400400a82e01c41e030105d05500020021180260031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328773372 1250 328772122 328772177
    0xb031e010b030304260619090f020607060c1214040201210624110a030503060a030c15030c0f23070c091d030f0904050a0f0905010c020606010f 63
    0x2041440007200820f1468009400003103d900449000c41400c90999410720095500c80008200720b003010108500505040c0e5406040a511002e1500c14400140c02150203558007809865980d20399080c244020031100d902640011103800003c1180c0c0214090440854520050003099482e01e500544160000d140b4011104005000814040311640308d854000e010351040c2c103024020020a0280075407290350070a040c050fa005040f0040702d0001401603000764981411a500d45406001803880d8a060340010004182c001000c500c00f440c84005040700c1400391014004c9900f403000070f40380301003903195850009009182150007800d12a00c90701001007450205460108661110b0b4403000c41c40c0c02c83c0d100700d40c031000da010101b441c510301d0707440000b2a00302030750034035041c08000b8009100710107601c0d11898550f03011030b142c0b180070740c400d2481d00c040c40410840d503480341c1b5040780a080040480300c09400303640c001800a5004046028040003e039032502984400d2000003403c0702c02004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328774622 1250 328773372 328773433
    0x190311030a1409130e010b150a121d030d020c0601090605030a0b190905010608060108150106050a09050a03030c060f0209060a03050a09020909060907081209010c0f0510060f08010b03 80
    0x1090001220613510481200c075580d040003094200780031040c03059500000016022203001040040c4070340e94040f06400c032143c02280040703100d0300404120405404c07020480d90290100044105040c0c1c05075004064008000050f9101c503a40c81d07110f0700c1112024441e140d01504520081800652140003899000a00c01c0076480103032190623511045907507180382101c0c140e540c1c20302404502c008100150041200000810342c0110300f000d205410901880303500c09101002c115442428064503c0e5009404085c04a00d0701c83c1d035034100145036031869501600c249217403c000c9010358845008542c804c0b440a0085407524a4510b02100100001450112100d07038030800000103030743d2030b11001e000321310f107500034016420f1074000541400c0a41d4045001980320070384000d013030b942d800c05680440e40309007454211102c4a0070040003000008400910600034103070355009100b400d9006506454420300c806030003a85403044a401c85009203d07880e13156001410100a042450110362803a49412 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328775872 1250 328774622 328774639
    0xa0c0602030a241412030403140c040c030218010f0509011b050a030908060f06031203070315230405041106070c090204030305180103090b010611030903190311030a1409 74
    0x14a0000c40040c0301c542444090180c0c10414042c0781c2d04010a1060101c403803004000101091725502e02c2548802441040801c032000700e464130900640380c2411014009010050707111070020020341c030418924a1101c506060307022194820520100c40d5640c686401e4a03010680b0300548060310304040b0b10750390b400a504082c000a00c01d0003201c448611030348482c03031840e0500d40850b0401da0300900c01d00d440701140d02000341e0799800207075500300b844410400ba039032512400740841c090308001080100d0000d06400010303038411480301010b096409504c9004002c400e400802055403820b540184c007000d0309001980c03031483d0000082a000e44543c00300030b2610b5580484900307030b82042d0f206602048011903c444246e0308c2c00d00720440d00c902440c0c1040b851107503541c0c1c0c0481c40018024001041841078903522241020021244c601400070129680399400c0d800342c1e807407013031002c400310009101a80c481300e81e8a0000251b445480c00d81e12006171400400940100d1900401d40503948154a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328776978 1106 328775872 328775891
    0xc0303080606090306090f190b0a050601051306091e0303051204050102131e0806010b07060218090103060b0306060907020d05030a1b0c0c0503030a0c0602030a 70
    0x1800c11904544821010032070720300424190b1900f5203c0c41062021aa1002070941c1c155100607080741c006201032501c5030030310082c0800007844e60340880c01168082d000d80c0c00c000e034440c9040c034204d410140c0300941166411429030107480071034070381003050065451120001c00110141d41402034514903540e0020010b10845108600c0c19800d0b002140400a007901280c240da59103d112989058580840301408440c1041c48000c240340d0084c00105505c002c24058100d0b5992511241848460b03107501d00070354440d52240304a243c001c4600c00c010394400203414083d60055200103600b04d0701009040c981000580b095200b0064003003003115007a40014850603901ca113160881d02d944951040902404d06030807a02041e080b00100503da5030b500403040035a03d8041d442c0c801e0841c0d1b40e00c003030580f28840d02002c040050080801c0700041055500110b41203036415000191070f10340c = true := by decide +kernel

theorem cover : BRFrame.Cov 328597122 328776978 := by
  have h0 := BRFrame.cov_init 328597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328597122 ≤ n) (h2 : n < 328776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
