-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:51:35.859728+00:00
-- url     : https://prove2.me/submissions/4ee129c3-36f9-4ba7-a7a7-88fbf1abfacc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 220323741 ≤ n < 220503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 220324991 1250 220323741 220323743
    0x405100b0d0905150412050403050c011d090a05070e04290103140103030207050102150903070f05030405100305060a090c21111605010c0509060703080604060e090601090c02060f04 79
    0x5080080c01ca07444100c190005610980c0190946032000b620516105440781e0885040f203d0508040030441b000d80140c041d070b410389401034014116081e0400064406d40760482c1c860501c4d003c034440c1c00409030b40c0c07080c0f45442402d201c0c1001c00c0c00d00700214003500d040e0b185c400c1c1e10710881c185040c4100810f64600841d0f00d42000d81c52a00d050620031005800501d4010480c1401c0100e14001000341038000641200701d800c02e0b07080b034140d1000c0c02414400c429040d00c90740a1074004101000c0406c03842c0d80150325442c0540140c91801c0c1c1e54100103101032070701003600340210b6101c808110440c51f15010176801003500c10420301c00702440a1005090b200c49107001c1c03403d20f018000292100c1041d51040c54101113181120360340300d40102100548205114088400758280411040302521400544004500c0505910b0515503283d4042d5403410300102480c0e0040d6075070f9000121001403401080c051042070b00907040c00d5043c8202d0406036500c82e00040d055502c25001d0149141005a040381c1c06 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 220326241 1250 220324991 220325009
    0x60219030e0a030f050f160f05090601020f071511010c0207060809100c05120702070501120c030e0a0602190c0c1802090927190605091f0605010e040510 67
    0x340480000b826402c2581c1010b00500c0085400e0802c111001035801031880d5503204481003602e010741301504084250080c103111510216007000941844012031307812610500582310b8034946401980e240900c2503118400100d6030000c0780c00f0782a0840f0200c2c00d6030b0003c0303009110404c00880080e6441415102c0c20342007007074060008048920502412400d007404a030240003151011000500e60307040320864050015025022440d071900006802007200c2d01038646110740d0500d800d85000600c1030110002c20305490b00081c0741c00c04824441640c0395449140010303203815910716015401d500d0b101d210300038080c106020501040b14001003504881c13031004200001e2510b005484003a000b00852150040231550038800c0c01c0c0c40c515484c00240074410481d041c54420301000503a1441303400403c0030041c0016810b800403d25a4000c5030f8014400000c40741e076401d850071400020124625091083d42d69164180800c0da03009094504101d01110300f03000c1c038117101c0a50240b241e130a114043c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 220327491 1250 220326241 220326257
    0x1415011115220b0703050c030f06040b130615021606090b0f0c010f0b091321020c09010902070302060f01231903051b1807030b0102100507030e0706021903 68
    0x2a080d80b50326118003203511910580c03035084551070202d801040c00d840701c1e4003190034100001d078980c0094064034070580706018107050684544050000800304c03000450b070003850400b104454000c003070040e00c2c02449101c00b81031003031898142c001c2c145500005004010240780500b0011603030720601d4030083e294400d1115a441e240c0640214242c482c0f0401c5034540d50031304945082c40e903d1a03100c0c01051409440300003103036552601c10b0048000e5110010880121140181f9440008000d1031182d1403150046034a02c42c40000060a43c1500740e00410b040b0303400003416010150305006440d04960780c45075043c10341d41040d152040750250360800000760031140101124a5841d1358040113140250106880c0468682c200b282c0c8400001240c640f5280c80001640d40c2400c0004ca1048100400d000f90382c09516010411001762000000345411485001482100403000c0c0c800c55018071a1620002845000c6a040f1400c2081d146c2c4140190b41003011a00c510720f14003440311460582c5817405841c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 220328741 1250 220327491 220327501
    0x10e0a020c3f0304030315230f090c0309010f1406100207050405090304080c06040f17012903061005090106030c031107050607021b030309060c030705011415011115 72
    0x8810000070354042c14000c1044500c40003600e580010341c0202d00994050150315010390300a00c0f00344451160a02d185102c0d0080f03c0c0c3d60030314410000f0800e60040001c03048508140000300c0e6100d003616101c031026400014000803000034810703964402108013007030003540c1c0c0899401d030860308010541d9004a03107101114050078800c1c410103028040041042089085c05145640e5039002802000914401d0000551061074000e059074211411940c070314000038108105602103070745144a0528640d210102500c4c90f400000c942100781c0c0051074101c0c8049180001c0502c2c00d84080d00040e840441c0e10018449502c80b044464103540c5642000300703a0031507c110480081403580032403070200c200401c00204201020507420f02500312542103500112050b040418240d410403144c2d680750303108121008036424441c015090350907200701a2414a4855100c1c1403d545524513007070882c11075003042001c5510300480d5010741030000e281240d21070f54006401d5903070358180ea440003000700100f00021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 220329991 1250 220328741 220328803
    0x2010903020f01170411130614040e0f060a090b010b0a0806210f01050106090b03070e091003020d050c01110c030304140d080a03020405130e0c04150518010e0a020c 72
    0x290201e1030074004c1311a2a1504010320740301d180016403480b0302c1000c01e003d030b100d00c4c2501801d0180c0703043c1c2c000b240e00c000c3ca80e8100402440b600600d4140d5004d521003004100100b4400f86102d5502c600740414080e926280041034424143c203c52818a030600c12421000d6120905a80c401d90940b9103840c0b040341392400c20585e000507020a07a0b1882440d07805500e032941900103034102e039440e454071941552942d00d80042c42c0003c46030700000814206031010603203000c2d02c0c280c0d04455881d0004022075200d07004075030a440d02d000c00380c0e42980210320040340765a0003021421611080b401030201d4903a220b000948a1045d4402c00c24400220300520226a443d1040385440d01d90200115607285501a0064040d4015201d61489000841802c001c2d03401540220140503407220003030001c4d46119402c000c018903a0080044031a000e13010045016151a14041c003080703140d1a0859966240010000c1e0320b24000702112031282c0144460041c1000c0040c1010f0031403a0a13000d9400300400c1c540b48 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 220331241 1250 220329991 220330007
    0xf0c02151801021b0c040e0a06020f0412030302090f0303130504110c01240e0403140310090c05090306060402120714090301090f02030c0111030406031104030609032a02010903020f01 80
    0x191400d0b520028072442035040910100c601c0c081c002040c0c0e40c07040703808003c100494011400300754480d00321141d107000081c4258001d005065803889060704058a4407030b0440701d03010b0080114082035001071861210b01d48499888840030085004519185400042030005103852160f90b0165407510000f101c3e814041056480604422000700140b0040c1c01e40c2e50414903000150200c0300c1c0b00090302041407801c10764500c0c425505a19001c800914050301c1426913440282101c016210004010500c6203d6001c0e1100001140d52150307100c151a600b054240f43c00a80403a100d07034410400d503c90030020401a96001006060607080381da070541c106104c130701c5912030155041d4a05240b05c01004a14030700c0080860081c0d040741e0b061142d0b4401135076895500c0103551810703071040c0401c00a29200360414103448614811260a00d9034940d80c02c010342c0c2c450039003280880c03595400c0d40b12500c0810622170014405003107a29415a42d9000038204189500019000e610701701010200c80c0d000d0950 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 220332491 1250 220331241 220331281
    0x105190c0215090a080d0806060a02011401030c0f050603010f0302040b0118090c0e01210b030f06091e031206090618090706110706080f060d1e05010f0c0215 69
    0x1d240e00640701e90302c40c0b070304039407100c1a0300b0711555001c0c002142c074020003d04841c04401a454010564403024100126608040180340841d074943c806850200c0c601083d40d4001c501c50350b1080728190810310b45005598141d003000f80180001d100400c448000088010300310b1340c0555000075504c060b400102d03030b401d104040c0b107c5458600980025400f0700c6a01c015400d101d1503644a6410414500455155448030510750f0940001d00c80c1988240d940d500610346040300a0455149000e0154110f040c08401c541c01000c1e40c000c940c44041c1c84044a03880c0080a0403403025500d00084000042d0700036501400090040c000d400c00545142c60304001c10f0f0049001055208403850b05224041e81c13140b2500841c00002c099450f00300000c600050700303400f510100d450b080301035a1603460300b01c1d1811008208a40c0013008680362408140b8400c00d200101808443e044e00c03040081c1407550941c1c1403400d500c1c0180d4a40f07003040c030300c07190f000c80c44440440340c40132584041e84840b00c000c110072483e00d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 220333741 1250 220332491 220332499
    0x3060402031f0311091506091306090c0305010311090903031902070204180c0f050d14030d090c0609080a12050d0e190311150402091008070608180c0105190c02 70
    0xc0c00720030304c00001c0081d480e8aa0850b8050b0080d616001d40081d011081400c140e00004148100410f92500703042120207050903000c005440d81d034820003201a03034030351004607001c01c0c0d5440c0140203010000c00039108541f0103681406c1e942c20107192072a941d1000030016a8484182220b00ca908040360301129060f94000b0001c0c4006090010b8141e070032204140c0c1128800224400069000381c0e00038944200c6500030a4494143d0b0303682c450190f10710f1103445d8003800d80070030485000590002d22031404070902034010240650301b0010050681c882a4000072040d41c40a003201c1c00003034100242e00c240d4061480d0843d29a4490404000034000140e400c51050241480d2412072002d494070081c901c83c029a0b50702480118400070507200e2200c4090410a40040000200941031100e1819001039003118006d401541e680700c0a81820383e944c000f00d000070f05070b4092155401c1e4141036409402d480c0400b8000081c00200082d04074400c62403040c146800700104201c86030f001d54200c4845940140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 220334991 1250 220333741 220333801
    0x12020109080a1d09041e0204020d051003020a0b0c033109050a2d020901120f050f0a05060901061b05120a021204080304060e06070203011404050f01110306040203 71
    0x240c005080029800300262000c0e269a10004440c500000c0302c4d13000e00d4004060700400c140e5600100c11000444406a03045902000842c5035070380c0da441454410344c0100421100b041c1540704104c01e000c0242d0261440e032409000c10500c10b6008070840300554580382c84121040606d02c2401a8260703500c5003000c0400744200b000400000540050703100f210251020004400d80c2c04064520541d040d0006014801c0b443c0b0010001c0c2c1c50740c1c0100543e4605042c2a50192180380e6840140c0750304001c240c420a803501d050224040540300c009410200000c1d00340030070f19044000c11b4428505110300810441450640b0781005801c8800504054000b01030707802541d6a50300042d011b6010a002c1e02c01446400324146a01c54498261800d03244500044c510301131412900300e070390881103920b00340e10407010800200140c0d402d02c542c60160800d541c1c0303041a45407505040e4104400304d00d0325240d41e410300540c1c1e00306001100885e0303448102100c0040c2c494540048140a00b510500c0201003003401c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 220336241 1250 220334991 220335007
    0x22a0109081005041704030510051008030712032306040506011103070b01030b060a1a070206040b0a030507110105090d1209290a020f040605071a1008010e0c0d1202010908 75
    0x10f600058407a80c0508080c07115507402d5400b891040c41a0310001d0450b0304004061038005d04c83e500f00b103410041e1550601c442648814240b4115030100c00c003107070006000340c404008260140154848404400710314003401640480c6601e0351b40b8028050f620850303443c0002040d90303008584030760041c24014103d03070325111140350031500320f5000c0c04182c904c100c840000600c24a02000c91030242c5000400540f2191045469003600c0d81081d0000c0ba80310005110100d40c0c4610180506803084590740c0101d194103101d00d014206100c070600c4031099174186810401c0b0700300c0020b881c40581102e46040c40030030380210360000c009c01450500038010465221100c0d26001e00d07200c511422905440204e80540321200d80a0892103030036030001e11075600340b000700412030141020384010750060603c8160060201c9600705114011510203107903403803081c000c0c8070100b000d20034100102c8850005110502c41a00080c4259514950003041d280c0301c2900d900c03825200303411100c02c480e4098074031a117800740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 220337491 1250 220336241 220336273
    0x1801051c05010906060e090705120c1603171308030105153a05130305030a3c0203040b1f090501060527100518060f0a0906022a010908 59
    0x42e171007140c0000380c0b103801c6c036061803a002c5c480500a6030780f0340b10145828444081c074182114010440644880180600907102c440d01d200c00b4280c81c4a541d0b1200303601d0248440b50305048c0b01814000071030110502c440300095080048a054540407240c1c18040c00f0360f007a64005502c078500c1c003d8800404103022070030310120f03480444145c1d0b01041c2000c816050907644030048400444030034613943c0170740082ca00841e0089000f190084c51403a03000c2034080c0500c1d0411410309003071021030b901c4070000710001100000411182155a2032440661440c03c07e500c03080b40240b005800482c40b580440c122428074595400b048000300400c2400b4440380da501c001c041e240b03401c1260360340e5042102ca05800030394840c0c1070818100700b80081c00665650500340301280d09030865000d5483e400c0c0940e4407409640e0364080a45003481000d4906692408403060050807042141d00100640d400440510303030400d003006204500801c00c490803080d0407036402c0100c0e124651680b1013081d90148540d016403400c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 220338741 1250 220337491 220337501
    0x30903090a091a0613030f02150a0e09060607200f03100603020406050405090a06090326040c0602060702070b07110402070f020901050f06090105070606050a1d010801021801051c050109 81
    0x101c4074406004400d070020f001840c82001e110000b500e03005c100a000007a420901000310b5800a00801d28411001e000242c2d00d81c4800e03d142e01080245045020a2600c011a55800441a900c175810200ca070740d0f61400c1c110340d2010302081408240230740045510b94920303da80102c40182121010400180d00c00d005241502042c1c0c000d5080810204003402e182c0501c41c003c0c46040c00900010100b03490b1140101741182c0124104102c0342c40c2c50704006041d0380440804d080d980002c80c502d04003482d00780d0001c003240e8000425074200c0c1080085c684e0700030420383e00b2240d00380e004550340d007500e00e00702002c910025841c40c1d2051021640ca014030050380c0344070f0009442903030b82410316601d94040081c800d084403003055002408202140c8203521450151001c1441080c0202c0c41548800004000e082d981d0003019040d02200240949461a9449c00f0700400c6224021803402051aa01e03610194104040a05200780050400c1468000d128031040c0c89035a58400c0002e542c680398000c000d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 220339991 1250 220338741 220338761
    0xe0702060c090a150c0203010c020706182103020304090212010302010e03011109010c0f060e0c1c0809040923030a030c02070f0509071b050c1203030603070b030903090a09 75
    0x1100c0d00340040c08045180741121031980000304042003080c13134402154400d8011081100c2003004c11401103006031001d0060820086040d00a800b003c2d0a02744002c0c28605c01c404403541d0200d001c0d0f0200200440b502001142000390988032020310090b0400b03900d584520b42c00111164400150120440a1641001d068a201741e0340d68141281540c10503080e100741c4c0e004c4541d500420000c80704150702440010401a10500c2d41a110141540354030040ba81c0003003e250607500070007440302d00e51401400814500046001000c0d51400343d031101c0f4428018110858065503441342c0c001c06200e81309203d80d0700f030050f412501c41c3d401ea07590442a1a131300010100000700381001c8103013685900210740c0310103564038041d404400600d04400c10100d02d8010300400305016081644101d100d04410111341c07090300440042c8800145502400308103624242d050555410500a0000595000c00e5900c04c03502c4191400d82c41c0c1e02c41c180d800c0d040d407044180300c1c0d5105141c0300380065940c509c0d4001c3c00300c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 220341241 1250 220339991 220339993
    0x307050705100309030e01030b0d0213020301090b0909030f030a1b0207030507060203040503100b0d0b0a02180f010c111c05061005010516032f03090301060b09010c020120070e0702 79
    0x100742d504500f5004e07112441c400a0104240038141d8075a54070940c030800c000d09000b40802c2041c1184d40201b2031046011000c1310003140c0000050103144ca11780288110448141d03045041440c02e1209a034882c05801c030100034000c0c002011800e0948103400080c12020400800300705034500c0311005e07550301c0a900c0100c84601035007070000741e4280084256421a00040d0107880c030480480d031020018100c0341002540445c400c4111030100e00340c4080544252002c4000503500c3e1a0410802c0300054500d8185214038401d100080403031364020720010794103500c0b062541a08450b4000a0700342c0c400c1d011011101200b03c600d080c240000000c0080c02034521007403800c111900d52004454070704c550201800151035010146001921500c0020000841406c903e10341c001c00c00c951000030251030a642200354000720b0044501d03d020320502009142041c1404e00d00700d05d0b440041c0102c07810440c00780c1407110004814980c076074008101181102d6500542d014152100c03140e40a40700203940103401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 220342491 1250 220341241 220341259
    0x2a0f080f0105030d050d0f0c110c031c08270c041409030304030804050c0402040902090108060328080c0a0b041a0105090a0c0203070213020a020c04150302010309140307050705 77
    0x1035410360803161410380c1e001901a001154007524140c8241d40b0441d621803140d56a088401c90380300c03a920809244a010366204c182c0e01180c0000645011605491b40e482504201265442c240202c82c060406c0c02c458103042005640711403019011464600841d01b00c403012040542c00c1d03d1021458160300c40303046a00700000ca00c0301d440401d49100c01c4a0300c2030780360700030408140405d004108856200b4030903c102d40c0c4064116000c20166082640b040c49941e4001c03e0703d032595a0010348403980824150b00409964844d000c0d0342c0054032440f020b00c089842080a6041407140306011503810072a400100c506048642c41d001e10740c0d0308100c41c140c9a41c401402d20311403003590184410304a81c0014501542c548805080d41e0003010b07840d40c5041940320030001040183c5814107280c0108902d901e0068803042c010b1030190412500070000c034416407603c030f222100501c04802c0d1409698080c40c000419404070b2030000140b00c0c586900514520021498101300040014804103a601c16078060070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 220343741 1250 220342491 220342501
    0x9060f0e010510210b04140d08061201020a08010b090d060911040605090702030d0f06080a0b040c0512030f0f0f0d1e0e0606010e0307090f021e04182a0f08 68
    0x2205a800c580c280d21940800c030440c0b001c1241c41035019040b50249030520b10312017106803050308d441e15015100340030503100f20400c2b5940ca04180401c0c0040c250100030761910314a01307002000c00005003e02c1e098207402081f010807540f51600c0c3c5d8100e0981c4150100300e510001d04011059024000d50b00740328504100d00418a800e108071110b00649c1140c0041d4102140c62001c4000340c11484140000266200c00001d0001420401504003038080c000482c03180c1494140000491070681049015004003102c183c01010008225626370031a81401034075403281540841c2e1902c14901c9242c82001d000c209040b040709292722504100c026541d88840c4410496205401c0d10a49205810250002c000050055000304544043c280008003950b151540718084041100e801e588002002c039408102203180d4251944c0b07180310344206100c0c15050034034001005540c668005c0000c15000e448001044801c202109000c0d01ca28052880389895540d5460003000360880034941c2c8001101400860 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 220344991 1250 220343741 220343759
    0xd06080114010b0f070206180103060504053706062604080714010902060307090f050607230f070b03042f0103020a02030d0e070e160f0309060f0e010510 67
    0xe664400c10000c050602d0707191444500e11504140d154040040f010403000300181e41d44001040300c0c04110800d1100e082c40200014102d40f001e4004d6130055140c00203000c079115840040d00d690243c9001740c090325042c2c11041445000c40c4615070809a81000070100c0c0451300030324040311100c94506040e100b541807202d1844000c9d02170350007400c401c1d030401c00c01c400f00b2001c1c0460405107001500119030500c40340d021480d1644116091800185101c20501c5520441c42c00b05000300b10480e505800c00c812511240002c01b0744241700c26076080c05650b0201241400d0000f410100b034980291400280e682402a04a40c001c56045811a01c049801038041354240402d130044802182d01d1080400c481c80150029803103054075900394401400700000310300d5240034159641c181003000c0d11501c0e240984003280c60380f0242c504c1014811f05031103001030075480b401401c1700100c545808500303450681031000041001d22009240c45007002030600510034150440f0307005402689819900640e240c12070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 220346241 1250 220344991 220345001
    0x11d040e15191401050411073306080c0402030717010803070c080d0f08060105120a0c020601080316120909021b0f03041413140412021605100c0501110c01020d060801 73
    0x12020000714403005210303500b0309500aa000319241c1407c5854011191230304916140c022096210604901c202c4011707d6050301c0c003c401131000c43c00c0c00d00415042100c80c58440489103074a6004070790200020704001d200700060038940c212102407200a50f1a102c00903180c1d40312403000d488078800b03a400012040400540720022440039950443c00905101c8112541c000207011a41009810b1001c080b00754404ce200c1c500910031400700080d041034440340681041c0c0142d0150304607400500c850045500612030220206500c4408a00b803800d0505060314040c0540e04000c0c015840481c1c800318a0240078110800b22407181c2c11903a03c17205c050b80141c1e49110b00d0054448040035444118054200956002181610400b0225400d03070340202c40981c5442c21501541d60340c0c05000d00e881540d4042c0074100000014107034203042c050606010070300c10b0102c0115901080f07521102181031000070750102134901a18411b0598481e1350060781400f0b9002031072040000c07851b040740000e40f20414071072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 220347491 1250 220346241 220346261
    0x120114010303031b0e0102100504140d110706080105060301142b03030e0d0c1b121b050d0210080a090b01150e030102030f0c0703020a08031014030a02011d040e1519 72
    0x200040507501843c1406040302400441e02d42f00900d20100350a10107100070355075000070741c3d1400d418109540c9550300d003e03034980c032110500200c030005120f561a8003040780d056131a02118042d41680d44004600440c001c010fa0355591850060100080bd03001210344206500a5809000c24040e65030655140c8100242480109000c03456000006042c6040108428407030080c4140440e560644446a40107030070048460b40c8120303101417003400d406900000075110503102c042041c0c45940c04201d0904140007944c06211144002503064421900840b011551054450130340303580d03d1b100e0517282c2c800038411002264101c0703090503443c1014400e4078840c0e20030520400843e120890444150340c4807040940441c0292080c44021a6500008600400120003002d0b456841c1c00c904080d50590354110034441e0700010780172030260707074090b940e40c0780c2c0c440d00414102124080320003d4010f081260a1080b40c4c01040807000c24a180022140d11034000d07071411300e10011b8096294002c80e1010a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 220348741 1250 220347491 220347493
    0x204150e16020c0316061106010303050901030906021303110109080a0b160207030c03051b271e0117060c0a140a1101050907060207081605120114010303031b0e0102 72
    0x40060080781d00811030824824090059035541c091032804a802c11416032244504401c50207000c1200d164060700c0b007411a21224003524040d411950300410901c6039401140c10103403a0010391701407155650441c0d03078803905030000c0204e6658a01d080713540c100031109090701064140c6000618201c0c007240c0c176502654880300a00490b07452610145500780411031032405c41c40307030060200004040403079031805035000b03400905a21010b82c0010301f1380301200c03081c940119004000350103150100500e0b22a85a02c80c84000c8041d035907030034020044003101740020103030704000c400019101c1030321248010016481050707410540d04d91a501c041803060b032940c4070002e001052035050003034645014010815442c6001008801e080b218207013503c0c0c1c141c800d0181c03900260010040e2580400c0000c008141140241034450584034889400840c2803040300d00440414520f602ea940c003c1d80301c54451204195002c41c41e50312800c0007002019030b00340e494401c10b074803240343c0724032405403005844d0000168 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 220349991 1250 220348741 220348769
    0x30209060403060906060302031e01051303080f06040219031401120f060f020708180109050102011b050d0902100f110114060d0201030e0d120f02040b091e06070f020415 74
    0x540c0d4600282130311282900d4640c0e6502e0302000596003032100a02110401401681c5000445600d608407540a0103121458100840140c0025002034403141c0c0001c84080c612850364031003020074081d21440e40e814442c21090700c01800069003561081d43c40700302c0d1002072101341c4e03224007104030074040091020380700b030452408590028140b900303c1030050f1220343d405800c1c5411035a43e85065006580c0c01e03100ca0f015106040380d1941d0004441c0d005007802d200030301ca050b600001c45400d54900b03015000c108480080c0b0b62010800c90f03000654016405010b540f20358826200040280c001100310310001a0f180fa207403107002505016400041107002d000002d6625440700700480341503c0d0100301d05054580411044800d4144000c071015815501c0340c1000c003001513050004c94000351401d440252040c8002d10108600e481526064201034802c01c400c8108407000e50f000c49440002d0941c0701030f00050341004c0042c101410602c81e4400d072002c0c03040050301079104103045568041c0602c1c4182203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 220351241 1250 220349991 220349993
    0x1501030809090702030f0304141c050d090215070b012105060c03070c0501050103030806010f0206010806130f0501050106050405040b030604030f031a0a0b030403080601300f0f06090507030209060403 87
    0x4019183e006681e42c01120301d060003c842c1a20389070011070342a141a11f1007595080e038410188001807441c41600454651907852100c06003060042e000e20301240c6070b6511101c8115142d5246902a170749079407406588540680c90030000030b041c240900d06c640d01e04002c0180502546079103a101c12640400606400c0e0303209150b02c20540c000034114001c00160000d40c0020030800e1041d58041c0d4025602c06003203240800024101c0c43c1d481c01c0000456020784010010790b0000f250381d9800c00325217251082c02c10310a06090450000004c03002d001c035460180000b80054201000300111502a2000d1081c40301386c004142d210303282110040c01017800045d8580c0781c284a5800701b0200320f0400d442c0144030b0010380101d4041043c0b82c008544440000090200f0306403c103004640c0903509103021803000310311903201200c200900e90740f807c90400058140c04c5c1038807160088030b034045520b07108100c42c00c9120720281c090035040c030a11200074a00340101d000f4030311a001b00c0c0c01c8200d0140c0f549240c1491 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 220352491 1250 220351241 220351249
    0x1180c05032a13020703020703030201060518041205070506010f140a06200f01060e040b06060406020a030302030402010915020604030f02030406020a030c060f0903091502210a0c1407081501030809 86
    0x100780c60507600100c04012003d4461040c8090400720b0300036070040c02868190716002e802c542260700840c0c46100e840d00c8884040403040c0c2d00a61250740b10a1521a24030584c400ba1024090b000000f0114054040042001c1e004420a001140c500001240766410004180005900340740240706c001030142d9404581501d0b07900c01902c010a03200c080b070316020541c245640c210b4201d500103a040c1503c0e0402c0c04244110040080d400100445503189060b1414401a5464074045801428160080000f4055a0090001a0007072040b03410007411500030140003074031400211011000700342c003103940021480c0b00101351015a0b1a41c0c0040141a40549007610414440d2030100e41981d201c80300411014020b0268032007a511a444030300c109030800e00d2184403400c0d101c0c0c3e03960840d40040c1e40e02c0c00d220040040d0441e0f2035011340209a43e218091400c0350311918018015000c681c000780a44070100c00010200221101c032425142c03c0300410b4111050402c080c480646084410300c0b0480d650b1030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 220353741 1250 220352491 220352563
    0x60909040f02090114041109060910051306030504050d03140612071a1306020309060417010914030d06170d030e03040e0103050a1203051009020a050c01180c0503 71
    0x102a031074000c00d15000d40d0004003284426007040f6030702c9007220a001c4c16070906e4042c2c044000d059030922810105128082441802990360703003481044049600c011860040c0c0232250a0740d0441c4400074003c0e01c400c40900a444140c5040356148203001d9410708051291040e82c0c11403496815051243c0c0f110030802c04507800003e120741c090b0081e0707080002c81000e40750650078490501e01901d40c0714081c200341142e01c2d55455100d0425508100660042075540c0c0080384c0075078140040390800b46801c0891365005045803030009190000ca03191101f9002c4d40000036041925400c54113010f0369032141c0d0341842c421400c071300000321030f031055518620060090700919020a030340401c4a080603507540050400b6031003a8030644140d0404c0c00c000046c80310130018842c07648440d040600071824500350010b4039406c14441e800000b60301148102142d841601120092200c88000b40240000c4503080944003055a00403a00b26440d8100040d00b41008620420303102107500b2000340201c4550171101d1048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 220354991 1250 220353741 220353743
    0x12011701022106030606030a0510110d05100906052209020105070506011503110c1e010b0604091407020c060f130b030703050a0c020c0f0d0c030f2f06090904 69
    0x5502032060202c016004200c1c50303101e1a000c11a520141000c80900d4100380020340b40a01039003048903c07001181d40040c101c880542070f403038002840c000c0c0c200ca41900f406503074100311030f5604000c14050101080342d43c80003072f074050710010010642d86a0801000110443c881c50000001450303040e0344400079845800d8107070040c1061031900702c183c0d07591030800400f40c00001c0d1045a0540e0a080c0c6036252090000082150005a140c414040e4a150b075a08040a00f16100c5140d011500b1041e0780c29040314011791405040c10352078a4171441c400c80941500c040300001c13240301c03d001804180c400507110201d01005031916140c149210711132681640000d822142580d00140e000034000400c0000310310079280d0350f400050908220580409450103c0c8041c1c0840d84503c0c0b038094165102803601c0c60014081380c20f6000c0c0503040c6045200d0610307035440517040b4810002240d081c02105401d080e960389400507a1030a500d030010201901d40340700038446410034018090841c00f8103000704459042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 220356241 1250 220354991 220354993
    0x70302180906060c0a0819020c0109151205090c19050a03081e07030c03020114070504090207150c050415080106120c0e120c100c0f0b06150705060f06010302120117 72
    0x401045984c0d04d00e00390029504544110001401c240400010490754404020601c0644454051a00000c002400e1350050041c02003c2c09403d0807454045c144240c01850200403d01140c038080c0300b495101c034852001103000314007111400940c0d9001101120558a004160401d02421030f222488241c0000303003c92114002160140c6903017040c1405818114425500c62464100915000b130035650500b01180c040c100344014040d00d10f030884141c6d400c0d41c0e00c075500161944202e007020445a50131040d6000c0c030902c0d00d40c1400103607621500410654011000100b10180c000b101112450002d109070000074400d5000c401c1800080d80180c0b04c004100e02e4008503a6801400180548203d00606d088a80c08079000200c00d00b0603141c1d280040c1c910f4100010030074482d850b003050040d07440070014801481c030800515140c3da05000340700c851450003d0103841c0e842a103811503444206441981061500f600003174200d600c40e0003150008032581c10322800d00d910b441e449291505001c02e40f1012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 220357491 1250 220356241 220356247
    0x10050c0d05190603050a020a0902030609071101020909010330080402010f050d02160c0902070302061609030b09030a0914030d0f03110f04050a0927021801060f030507030218090606 79
    0x940390b00e60150301e000d540a039014080c050090f01c1006402e4009a000c928168010300800c03003641da8601c0c80507403100301810040c0d1801d2707090142c98020310804542503403004c0f082c0008003c3c0030350042c40c1840751200000500005407800144000b45802480c5c80001a0306140010019403050f08000c68a003207a00388141070500c0304445405030f0300b0010101808820004100d0140410981c60300014014140d085181c44541e85009440b003100504107024098a181c2c0d43c2959845051580015900008030310068204a1001d548940c00308400034000b0b09120380104000440c80038110030094010b00802460010902c20740308010b1150705141030594440c0c59883c1d02d802c0d500148160400c0e554150787e40c40c2410100070328082241c1003404290304e4001c80242c007612100138400038884000c400400030700c5910014100551307844c01d030f503540182c1d01c000050700c0d030308003c00c40308034112528107100c5603680c00821400c9005403507042080460000000401f07060580141d5000100501f605203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 220358741 1250 220357491 220357531
    0x30513030b0a09110604050102120310030b010816091104090c02010f0204080f150f0105091b0f0405010206070809030307050c07030f080702090a0902030309090a020c010608010e10050c0d05 83
    0x4140701141c101c0540b0381c441450404101c00c1d0a01000e40f9007003103801a040506000c0000c0d070350360a0b00404484020004080707001141401d650780c0065074040a1034003a5038468242c162100701da10300440d090550840041503e080b54060711000400640001d410301c1d02c0d020515002d00060103c1d202555031707400c031680c620303d032a000600182c480c920061020003200362020b860f0000356002107aa07064140140008402048451811030310101c2e0883d030b41707484550324401c550b680741e5107507c03070100c1c00190320a00356112000360040310805d03025a08140e48144003a2080c02c001c0780c901c03016800400c0025507403030084000d80004030b4a0b008580c06107480c0d954542500105000c1a10886000700d41d940440c030f454100103500240d14036051110922980c0481c0d80c9024100c41203104d0008c0c030001444204e40b0303030f050b00e0040500c1e10081c010603a54400f42c40c020a5800c0307403540311340a089448107282e4110300526020303040c010419468101c040300000024100035040c1e6020f440080c01d004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220359991 1250 220358741 220358753
    0x1e07050601260115060c0507090501183b010605061204140d020a03050a1b0f0b0a09020904140703050d0801050306100b0315011116180b0d03051303 65
    0xa001e031030507600d00b00c4007101842c49003007403140303402c481140ea0303041480016031514030b00c03403031030840d070107410481e10b141c0e810300d0300a041440b5500180029440d00000140c0c804003064070354000010860104115410078141c0150224120351500780d19000c54600704c50100010002c00c9000c090000000311b01b500c0d040001c000754010782111708cc001405e414081070001c0d400c0c203c880e0500d070130007c009001c1c00c9136020b504e440e034004019050013008129040e007203004519441641c8191710004228a1403403070f00840d4015259000d41d409540b807070010782c0c22110307481003664080d0020b0405950303a580340d4811107829104030402e415805005000000540200020310f01407040d510356000940c1414107251600c000203104509581051a04220000002c000c50f6000940701d51301c5260190f11000603a105114540324035514483c0da43e1000d0100b00000100c0705496682c00e0030380d110b0202880303c4041e01d0807055040d9112404589402c0002c0c0541c0092a1006154a000e4440e075565150341d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220361241 1250 220359991 220360003
    0x8070e0910051c0501060602010504020306070f030b090106020a03030b011b060e0f0f030409050601050405060403120e030712050601050d0503090d0f0b0a051e040b010b0906040504050a091b06051e0705 88
    0x280043d820b02000321030810100380034020191505100801980c81c01e81c000036603074400a0211424410100e64500d40d00d40320b50009510901d01800429140d43d46080096503505604070130b400182c80c01e0a00c004640c0f040d00c2c1136600006c00400b408001c00103840e610018210b100075003001d0301c159004e84001b01d006005c8100c00146100180da1650324040c000c0040d26030080c001810408200320030b0148ad51a08155025030303801c4428500030028220301504e01520301e000d000d41c14801c1e00c000040310410140311102445c4640d05440d07540e41e86405020125100c80402045500f00380b2121946081c4031900b21041805420703210f142400ca6142d030000ca12050783d5907100c2d1500d40c820048504002e44814441455440760348104e49800d8942031050350040c042e008807000c0019803000385544a20943d00607100045c000c02140c149005104010010704400f2a03007040d0841d824403030350040200403000c540490716414940440881c0c2410754861107402c2031031200081c010040410010016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220362491 1250 220361241 220361269
    0x7051803240618010e0a230c1b011802090c0d06140901060e01020a03180e0f0a050606040806070f0309060903081f050a120203010615021b0108070e091005 68
    0x1e09107042101c14401540e10075002a00c00d8400e240c010840300292404013603201a40e100b000541659850200c40201400180c0c1c0c3c514000800510a1000001008001c0e07030309245421481e00d90490120750a030fa0071100e858070341ca542040c0c2d08000d42001c2801e15806a100c4e0240c510705045101848101c8d46103401c0080d03005288030381e5a180b400c040203071a0140983d070801900fa00d0403a00002d68410018000500b041000c100e80705841800103c104050910300700f100509151a8503c208026000c507481003100d400c00c00130a40f1410088100c0b42a0f5101802070905076a488100342c41d0390010ba1925010950380741c2d001c1c8082855072040f0700e0313814400d942d042c0c10350501900d014100100303800000300540c00c40c4820005951450349200072103411344105c20345481d4600000c0d0050506a005507048409000600280340c2d001c0340f80400130001d5120720032812118030044440c1e00d000c503260400b0072194410000207250040c45c00d070b4030494000f000c00d80c6c241c4030300c00b0075040000301c44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220363741 1250 220362491 220362553
    0x703060807090615050f030a090305090d050a120512010b090310021204021009080307020103090204020f04060917030a1416050313060908060403090e090705040c120e0607051803 78
    0xa401e0164801120400b42000d15514040c1e045c1211444071b40c483c2e11003d000382c00d0b07a03541d40d1f84050806d0b008000740c400c0d030540101807605805080c1445a00c032404184101c480d46a24020f94942e07131300078410b50754090034018408503a60f003025003449003980143c603920361602c210380700c5003411103a42c0010603c4c1441102104290704080c8103000d9101c00400c1482c1c207002650105111182c00001501c507001e809183c081091881400030070024403030f030003059030000b90000d8085050741d042800c00040715581500b10b14504d07001d0200b15180e02864011f140081c0314641018240fa41c0c05000e484152009044a5086045990703014134550000f100e4400742d00b0020b004201054005101e200105018405032281d441d16070340085c42202a070040c110404019030108030500000c11610000e000c014204000300b05040710701070940e036088a00d0040060410702d41400407080822024007030480b980350b40382001e042d00e040714103100a00c40b0950705845448500703011007002800504810398540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220364991 1250 220363741 220363751
    0x7080a1404061e0b010e10030603170c0d020105090d08071206140103061d1b1b0717161a0c01020d020415050412030810090207060b0123030609070306080709 69
    0x500001d09280582e4403d226070b0b0f183c40346a01c80e40c0d0300107111000f444000c440e0309050b26400c200c10703001440f241d040600b608800c12404001f08c01481e00074815058400112a01880d2000d422401c3e0340084800c40c80d1030b0003505003070184500500040e50024900c2c100f000036554020310480c12030300254015a100600f4075171290447d40c043c814070001d01000b4421f0a18a40b4000303d80c0322608000d01100340c000801481940c0d0248a842aa44104484807410484a1440014035620082409030794030500c1307420000d44008800040c2d40c14980700e030b032144000041c5040e400c410308818a01c1780e00c83c140710400c00f121240c2401c3c1700905c802500c25400503180c0e070820160b40606441d1240c0c1d041480400c20091001e5076012035580361040d418a404003240d500c02d02000d00b146c046a0002c0002800420500204007454014941c42242a81d40410001e8001d090b070a14544030f410501c1000d00420100d0003d00b40f46c1200d5a001002d0709010503104d668040c15441c1030200d50191a04583d15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220366241 1250 220364991 220365011
    0x804030305060105070503040e0612150a0f141302060f0c0a0b060103060f0b03060307030b040b0402010e09070c0f061b05040f090606050a1b020402030703021209010c0807080a140406 80
    0x103101c1e00d60010802e01c0c1c054100101e13959456643c0c07080c1d018901a0412a00c001095651000c0307840441121140640d0403c4103842c00150703001c041940c004088600b4182c8411055040340308205038a01448511101903c0e6071520f0400062a114142c1c0c1204080041035444c00100c402401501826002800b80c0100c42c00c16181c0b9000150505040504001d41044980200344c203600035194810032842c2d8030f4070b841002a1a0a0040c0e100404c0034101d80100710034025000c040510840c000c2e2248090308000e1010009000c40c1140e00c5004140ba4031103860111346080c0007416198861000091500c1150b1308407180480200c100e03e00041f80068240545641260250000d10109500b4042241070030700240090040262400411044400482c402502e8241a6407010b030041e00855a0f4101a10010007075031024010704080c0842c400846c8034240b05102e00038926942c0c0c0c0e0350120a45034414121540c52000d4145080181c0f540140342c140700c1158541c0340901d214080003d80c0c4041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220367491 1250 220366241 220366247
    0xf0b210f16031b05100905041b021b0114130513090506010b030a090c0618170705040207051c0c03081806010306020f16080c0106051005070204200a080403 68
    0x5212a80c181580140803900000100300e00746000b5a030b8041c44003901d03090305207019100003c081d40000c1e4450361450524080541142d000000d030303101510107210010224064080002c0008444001648041411041c000c200a60f0038910703001450020200901c0707000c0c240c4650040c1c6100000d145604404000310310b8510b40c0900e000803154002d109200258442d80d44031031052040038500080000002e0f40c181156100f05240b662040e1800c3c10103840b4040105030483c00c03160740035500d909c140c010804200f200041900d080c0c10000034190241003206000203500720040841e00c610800e042059010600301031806030380425a5021a8004142002012044040e01540c0d1444a001181e20003150200d542d505607600b1090150703a46071160b065030510320503640072000da030115031400410001c01c100100684840c120003803000e552501c0400840c0d01e40810240c0104008019070720050600b50041cbe1080340e41d000100308845891011701e8416403000007540300003892801000f0070190 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220368741 1250 220367491 220367503
    0x2071e030807080c0d180b0706090206030702010c0e040603080f0703030b0a120611040e060d0305220302030607020705030307030e010c062310060507031107031a0a06080c01090302040f0b21 83
    0x2205d8605000b86032400c4111022440440c083c06801050000d500e2041c0051501b0009000e940507009656a24201400a000f000c4001a2a000821030210000c2d071b4603140c06804103583d0401000f501d4191a40e2050800d80e12400040302450380f612001d480b2561002400002019131000004e456107143ca01075044135000ba000024904041c0070510102c40c0050307551791720280a039015509084135040c02e07111340c0a5807400640d01c000c024550b00141b0040b03041070045038400d4040751100c1d1500141079031104c3c014019550140c1c024018000400d1045480d110481410b0602074924501d03034032070105850f1140d29203022b40102c04003407064078074405103865010400f03c40410703403c2c5c240b00c0000c0041c0724044000e0204a240e002c84e444039842402000000c5601c1504902d8501403030024000b00b503c100c60340e080007860701900207401440400d07600780c001e405075652110315003141d081000500082100c0d52440b56210f034000c5040e20340d03c01300300d0599140c00f400c840c03080183d803c49181003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220369991 1250 220368741 220368763
    0x30301060210060816062007120b0c07120f0908062706010b0313081204050604031d01080f090f010e070807230f0d0f06020403020a1502071e030807080c 67
    0x5803003903101030011001c02e17012030281c4900c2e280600b41e041b0250465514045541c40d80b51250184000000341005a0310303080c0f188922610f80d81440c0d50720b08103200c6480c0030b0980050321948144620812842c8a0020b0840800440c18400c4040c0e40b9210820300d0440121140110031754081601852130101501c0c0c2280c00d440b40b07006208560402d110308090f400054416200038071351200701c50810440317500b07503842d0800100ca0a4181d2420303061195841d002030710140c0c04107502c40c02134000d840c2a20071100c03140750180c40b10099600e44146c940803014008200000034000d440a803840c1c00c81c207000700c000281800c8020003865003065a075500b0100d9a40c4821030041044009a6030028000c01d400d00c504011610010b50f07d9910020035800130366854028450302d00111400100004c3e0b40c0640150b038000d03111688800d4503201108620480300c04c032100075910206c010000c0031007a01c214518103c4e202c08210905a4a075111700c01500100700c220b40201e00441d207602c50030001c1008101c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220371241 1250 220369991 220369993
    0x906080c07030e0111010e06090304172107030c021020071211010905030307200108041a090f07090e0606060304020d08090a0b0f09090601050306030c010c0f050303010602100608 78
    0x260352550050032900f01c1d1900c0c981070000702d80c50b10510480a50025026411080650f02e0501c1c1448409440307a016025403240c030700766055002105400000c030f03c1aa8480d4180300310052035681c09208454200210450070010417681d02401619818118684c2e540303a91185941501088a0b07001c401e005410b103441e01307a00603207040140f441c014803000106038012036210985044a001211061a01d4208a0f0544400640c035020801d2500f0340c03044002100500d145003140107001158504810344d000780541c10303000e00403d0700c10740d20180c203a004281e0301c049800707035202284c01a0401d10140e02180c01242d4908012180724018000c0302d0b40104202c4045146240c00d0740065020b070003403400a04101c901040b01e0650b5201d40203502d0142146203409a2580b480b1240c1c01c0480c0d1000e010740d80200f80c040701082141d40030b0000c1e80d000e40702c020080e1500d09910001140c03400c001c200c003a203020320081104030120700c00380002c0d030103088150b02030250100c5001a501c1503901a607c1644070b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220372491 1250 220371241 220371247
    0x40b0c100509280b01150f021209281206060e07050f180d0f0210030501030809190302090c0a0f0905090c0307030e0708010507030b0402040506030105040216120906080c 74
    0x10b28200410444014074840e656400d0410914640403849071600300f0040000c4900d000100390450858544074503c0c8141d6600500c08490000481e01e50031042e2800d650b2000030300021005280c90240201c42c5929280d82100f042590002d1346071281480c4c0c030000bd122450014142840010b000d03080c00303044491682c80a0b0b08044100900c28490061942d01360507000c00c000c4000001c00e2402c510784e105c024100711402109007003145580300700b50022803041d224055210030080c02030003454100d039007004180341030030b20071003c2c85068085052a540c0442501d4030110047ea02e554040c2c5c040c03c1d0079403400d5260440030350301500480d690300c941e506010807000304100b40e548007621940d00008080c9096101d84440005602410386840d0030030145c020340388003044110056002a1040180b40d03418005500580240b00c100c0c452070051039000705041006100306c0c10180c00805055020111004130300115880301030b0400d50082158002079201c0b0b8040000d0b0341d0003110141c08c41d00d050748140c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220373741 1250 220372491 220372501
    0x90b0c0d030209031c080613050601121e06090911010504030f0206182106060a03020f09041b0308070201080c0a0e090907120506060901061707030207080906040b0c1005 74
    0x155884140c0034080c1010703000122002652800e20554141c041d0558a020ba442e41c070860180070343d541203e038240030b68000340210b441d516040c0942c6001c0c402c10303114031080d198604d01c004068104000c00703104140c00c1c0502c81100c2003051041e13100500c41d030440000c20126619101c840b00d030110100c181000750900c410b0002c070381c58500104c09030b9411104a643c0d80c5010801801c0d40b00c0c03540c901e90344030021202070b42109c03c194120f01e8124810105803082a038641c0200144480e081c08042d40051842001c03a0f954209640010303001401240b6004107198841c00c1c0642e003610540085a4403e00480ca030f0003156040305a0a4100008105260405495403002815805a54002841000c4c180007181e086142440007a02509104a03890241c88150030801e40d0f600c000ea500300d0080a00303034000650180f084000d0920002c3c061082101500ca0300e900324065042070a040d03600720b104120010302c030381d0b420000f080100b01d03249c0c4446d200c41d000660b0b1824401d44801d074410032814402004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220374991 1250 220373741 220373743
    0x6080f09070b18040e03032403070b04330903030804050705150715020306090c1e0d0605010207051005041502071d04020f0916051e0301090b09090d140d0e01060e07090b0c 75
    0x8400180c08e44054403100c0002400285440c481c2c0c4d0090110f8440024080f40b5081d01c00e0b0300c14412084c131450590f40090700340321003a1900388010540d000451541c81400021321650840b604640100122440e150b11480094180044400280e0409031b00148900c200491003e880c500d02c00c001008504503d82a0045490081c0c024200d1250850000341418885800900c966044094a910729100c01008920350018060350048070b000d88107840c0002275034034146401304170141140c1c0d0340506080c80c204005100c50102c011080a501404070f000c103455120142c841c81100c62001d1100c168100350051226204e00c104007280a420010104080907106203402c0700d51070950314281d541c1c2e070580a03104d100840700e41d8541d846039a00100001d5644032a800c2401c510804503010080ca85034040050340d1030b45a4071008000c19550404945a0040500a0b06015004a101082c0c201810301d10b00c0c2144d1064000310b10000213801888042030f8001c21880203850781207080c07450400070034811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220376241 1250 220374991 220375021
    0xf0a0e030315040f0c050c10050402030d081305030c21270a05040204081005181011211006020d080a1508120901021002030106080f09070b18040e0303 66
    0x212210007061090b1454548640d4044150003900344410004001008002030140e4007610346180030788680003c8014400c0d06104090140b41d005000740443c1080240c01d688000004054035070000018079400702180c414001001c5024200029000010004155003904041d00358003c102c03820034030030740481080d507000d1000305218401011810b0702c00003000401c0c220058101c81d8125002240c0013407446000100c080480319104070a20043d9a4452541c60b50582c030004060030f070303102c5011454020f01560001008520346a040c2e0714081c1d000741d2080d5454000408030070203070020003c0155503030401103040d0142c015072000d019407285814005001c8400130300b80801c0c180e5120781700712180b076151248800a001040a0b6104007541d01c43c142020b4200c000c0b41400b50141100305410303072645100b1a4140c94203038490070401d42b0307507400d50090148014054641d40c890300102203011401b102c090f0411407100800e10b0b0483c030202c07060205803940e544038548a03034802d00900c00d20380100400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220377491 1250 220376241 220376251
    0x114010c020130090209093d0c0f08061f11030702030d02070e01211211060115020c1e01080406060b0301060518120607050c01091a0f0a0e0303 63
    0x1052911070b00b101542003441d0f00d4803032400c584082400c2022060781c0c09802824946000329001240355481d9000c580e140c4050140c03400180080c075540107615503110f0718841d28401248041445001d620185404070b903146a030714404a14045052111a0382c80303442c20b9402001965461040308d081c585a0b0480c55019000e07405108101c9440414014100145c0d079406130010111500d1080364100a522252540149041000000008603888004c1179825102842d42415590782e4403103529001e40b220010039054080000c180101c1e4149030003082990b01078501c6442c7c2c0301035a41d01d4100039181c614070521260045400d4000803042c200ca801c500f08100b0400e0801c40e5443c0c0d01d9242400003031030a40c0041090380b40110010440c2a8820060445e41050103021601d1002440030011003050f00441070240354820030005005910900c0074111604400c000400c00d56440d0b660504107909920f181600307642c01108000c1c000fa00541040d0f04071109240800808401c50440c1c2d480740300042c1b03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220378741 1250 220377491 220377497
    0x5061e010c0f05070306050f01090b01020703031110060b13270c021e16270b01030212150414011a2b0b0f1002060114040e060a0906050114010c0201 65
    0x9074503050100d07140b0480101940601500e940c103460b4a00034005103000e4800352003645c0700000128030380c4201c0c42040ca4810f0141c00400308680307140c4e001c9070400a1423080100b14041c0d070b42a034a05088500804014012001d00341d40c6811004c401e45282008507030016842044149007628801201101c07842c900480e0301d40814141200ca0007071f40340c054485010120424003407054401d100d000f0800f4103003880c1410710100504d5039440880303041c0340c40e1400d02d600703051001c200380c0b03185559501203840303801e0604015051500c000ca00550940d01280c5018190f0440b0a5440d0b1600d414842d10300c0b0070800e50b40a0901e541060b24900104100980058648400150903040420392507d12031010f400b0001c07504011404082c040080d014141510780a6844080b4011740d07450445103001e6003c1055005025a070310301400d4100d6628031982564105075203d44250f201d0701c0078482e5503c51564070201180c4500146054000c940b0b050780500390801030741d0104903840e07a10486800420b90240307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220379991 1250 220378741 220378757
    0x80d050702031209010501140a0308031504061503050103170f030406020c030702040f0b0315090c1903060903021b06030606220816030c08010c0503011205010f090809030105061e01 79
    0x28a0581c0b035403041d02c900120840c001820016142d0054010b41c0c1a1001c3c02c02035039541110005220300044180001001054140002110a05084442450381c64002d0021441c19a00c00c02020003c04001c44070000a8a0b1b000500a00000368190040c00c2d21010415240460050b0280c246010191006005640000703104104610405c1520511900140b04000c1941100c0f9880000c0c00c1114009009020300607809600100402895101d00d180c000070b8440c1282180c10800a14a481540c2c010010030002c04000f0441910454144c18402d4005040840c0c8105501c6240842150050b1141504000300aa140c95080039180643c08540d070707070007989441c040030142001d9103800c9500c1502c141601c1600c0d201c0c1c0405c3d818202c034010300010b00010384845d059804c1e542e0701e07880400821420401040b11008103000303402d8080c001c000011350601c2a100c6141500d0320381d00305030750554021036405018074003072040c0c0f07400a400300d50b40480703031400b007041c13041c020000d84039141400801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220381241 1250 220379991 220380001
    0x50406050d06030804090e0606030c0307050d020321040f12050c04020703052118010b090117030f0a020d200c01082701090506130506062209150b03010207080d05 71
    0x20340c0200c070203154040300340760701d40380c5070741c06c140042c400041d0715895031241c0d1001c0744042c100403034591004007025000c3c00200d41050244841601c2920040341c252003400100140d41001c131a02c3c40100310007541843d42d031868030321882009002600100d4038041d901c08030b4000101c00080341c510145c3c0a80b405a111115400d066516019203030b1242d1010780c1407084c641c828400145140d1040c0460b03911280070b1114000340e070b07088500d10a1001e4011035160014860841c0b0300e440d100004c41e07002c08403482c100d0403c1e070710070140d007040ea1144007580c403090700034001c5a001062030954401800b0418014400340c4d040541d1114030b018a281444041e801159050010740000c401c074507014044003410001030080c003802409140010784080c0036500200313031255084010301c18129000300c0284400c0d02c0d80810083c0c140b525101d82c400d124140f0801c13402083c024012005078034020714100c181655103001e402c082d60110903003184203034810408d007800030f1542416601e81c0301c500c202c001001e0303640e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220382491 1250 220381241 220381267
    0x1140108030301151419030f020909063106150c03020c040c050f0c032203330504050a0b100f091d060408180105030c03150f12010e0f03090105040605 66
    0x4180030310b2000440014001c10100301c1b04580c90040300321507030100021100d13103100208a00540c1480c9500c280b80d003000c1001890001000c80d0280e00c010b0310041e20354145020030512416182c00425015114a01006000c194010101032003100707041503850f001d0145c0d00252a420904501403249586408290200c1e100e0421b0328001d500101000f552021181001d03030341c03600b1032580c1d030b0210141e40c01101000c121245174041181e85c003800b00c4405e03008445510743c507258050602c1c600040d1801521400f410280034581c011348c000d00c09411803210504044684020080501010030b0600c502085034903a00307100c8400302c0c0da013040000303110110203201010410305e00e0100b03922442240240000d02c80b0100040c555414100106400134546000648050008071501405c1660034400200080c5000c540c441450320003c1408001c8407001c07001644203041000b06460780d039992030401074034003010032440c40801d2a61008606100c201c03030000b0707d58491030054a0401034007203041040f040d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220383741 1250 220382491 220382507
    0x20d08070305151302040f0506040303050301061214070c02030d030507020715030f1a03100b03032a01091103070602161712070515010501030507171b07140114010803030115 76
    0x40000e126044005104041341d002c1e410600510b00c80400c1c40c140000c1c0c40c40c0c4601190101ea130b0685819045030300e072104c259040035052894850f8a45c035110301e10510036084c0600d07072051025448a20b404025401854509a04480c414040c18644814081c2d060340000b040780440301c4080d18503892a44285040b80a005010030420b4883d0804810105200c0300c80c01d050b04440d41502100c1005400b421345c1c0041c1d40e100b03203c0c039030903810400020301802d5010801e00050303a6003a014070580005101c1072801c4500c024020b41d2900c11088900e4614601407000300000e02061000b01210b41400034480d240f140180f262500d0044e502071000303140384050010000342c001b22182d094640c00c1c3e42c101591990310908000021210030000450300358028840c49025032401d40d82c058006c1601c0243c0803101070301a000c1410354801d80c1d4070f00465040c0000406285120b1004405a004d03600e02341401d441d130303015410656120201c010b01800d28000b041e80e044036101181200040410039060b59048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220384991 1250 220383741 220383781
    0x32a0509090f06011115060409030509030a0b0a0608030906040b0702030c1509090123040e0111070305091314040305070c1a0315010f120e0309090412030c020d08070305 74
    0x41420200b201c1e100021814501c2101c0a1300c4018441881a20b0951600540400040107481100116440c0d0809a001440f210f01c01e0501f40e182c45440c000203450b00a0001048032014101001c0050740c104070f004442c004c2590b035000b542041c055000180341801030b03000d1a03285600100300d000c1595820090303141ca41d2400f4010410052020000d940e1907805078160b02d008035000000010303000300b09500707c01440c1850a0510042c03000a081001410622100b50303180d41d00e03802443e0266407103a00030050720744a5105c50756903544540c00d1041c400c103010100a070491608074400490805e85000c603a210f903040c60410380d2042203241903030a6000c160041e41b170400e80f5020007484501c00340e0066000d07102c003c072801c6a68a80341c00450b10020b42c40001c90024000d581c1801042042c0d4120111954441059a0a12040002050301e10100320b80c103440384078030b6440056601c0e030035215014580941d40701502003041c402030040d04811001e010344e408c2664a00c0025840e0310300480f400080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220386241 1250 220384991 220384999
    0x31709040903080a0b030309180403030f0c0f11010513150204091a011107050109050103020a1707020d09080303070917010f0903020303060a050117070503090a150207060c032a0509 79
    0x9001c603060040c1001021201c5102d03d44c83c015841920b89000002d441801d03034010040725000c0716003e814200700070054811418103484400c51907004100340142c885960003680c0341d940d01c841d0140300400080c030078885400d050341b605050100c0d0f44062100d0582c4c448d08021103c3c01824108a024002d200d55071020b102c0c0d618003241c2c040b000c0441d00721450000e40c02d9071000481910419115160101c911486000c610030210412807540240c01030900840c15003081d4046a00306403813880c08540071030f070040068100400400c06607400051602c040c1002d0401142107150054000e010403e260003031060003440c0c0c132106068000c0075041009854003034201480844c40c60728002e5070b13940003511403a201d0481950003251552148050f025074809030440318a16444d503402c242e03070a50001d030110403940511408a00070501000901215801c035801c01603560b6403a0810900300d1b22180c000b941010300b0101c20241b841c8007032203c070030040c440550000c000c550701c100942705442444a59604 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220387491 1250 220386241 220386251
    0xd09081b01091502060615090904031101060302120a0b100e06150c160503060a09051c110d080f0604061508070315090e0d020102090a0608040c0f0e07030609021303170904 75
    0x483c3d901003043ca004400c02c0c1c46504003241021b10355001d9004180919410540040009002c070344a180000d00200440c0300000d1044d80303076000310303045610340c00c0c4500484d03018075602ca00700b100c03a203005580800d5103101084142c0c1030071244040804050a114480c01c0d0704c02c14a4000801842101e0001c1c0a5104840e002c0c0030001c0307907070311068052007480e1103409803200050030300615000313a1080aa1100140203908480f641c032a545a0143c800300082040b1450759a00000003080200342681d0143c4600d0020b00d00101d410250b1200203111a01660512500f08020f480500d01070003001510b00b0000741030340e91f02900320000d0042e680d05d0310440141000000380710721154050100660414241d881b441c0322000244c4c240d10074001c460740c000618020030410f03d44140b905681183c490b40040c5242580c4544050301da20403600329000050b0310a0900440e2501403195800a000c04103055081101d00c1c0ca12060a200301e1001622141080f040301b600940c80408807601c0703ca0041c01044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220388741 1250 220387491 220387529
    0x150618170a1103120a05031302060a120f09021011010b270f070c0b0403090503061528140301020d060e011d040210030209130f0c020d09081b0109 64
    0x95a9220780300203544180d0645140c520500b4003144529a0303056500c0007601d820016002281d00341d0008140b82c005510300703094600103907101c000a012080381666040003c440c08100501200c6c0c01d405540170803413074681c0c1000140c4400a02c1e02c10340150341031000305400e504660300d0144c015000341c140c0c4072000e4400d0302c00000e14049041d040d62091012800d45594011015003001803e80e03408012410061414000404000701c00b0343c040d209107405d1400790764440100b881c3c48070680d44440300e039003001c1400e120750910348610142100d400049070020605244003c0d00c0c19241c5c0119a0701a08001e40030005403000d4045070010750707903840104070141e91000c41c012004802e02070311914210700c1c0c0c402d00c000c1c124003400602036a0014802c0000080030b00050b002903104000590304181002d00c1501c001c4214441c042c0c032012501000f18440b40400002800c0850170002c000c24482660018415081c0000713080c01c80300c00e400c0440300d049502e0030058880184135805a0340008030720740051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220389991 1250 220388741 220388743
    0xf0f0306160210050c030c07030c05060a06090f0207020108060103020d14041a0708070e0405040606030f12111204050f120d0207080606040207050a02010e010e0612160315061817 78
    0x1070a12405a0700381d450100030310001c0004c1d100c09072540e15050710240085040b89881100130b043ca24401c0c00c0c940e0030ba0f0f00030343d1040d003040000c03510020000e03500e0b10100040d00d118041d084c809481314030214500801c50340003900c0030f10301806607410554042078113400007034070764403980d00d101e01115403501c41d282c58a800c20158510148607120054800041000a8040c0c500d0b0782c0540c000340ca6403610410345009120080100030720a5480903101c581c0040813a071003462065007140945020b85d1201a0f841002c2c2c10b140425841001d82d80c4018140e4688c08248000c2d14107840d0110350b41d101c2440194005907510300b954842244901410b0503130382e0515000100c030b804488925040c0c0c0c1032560b840b000c0208900075210080e01d150402c0c07501e080150702c5008072011260050403d04940139001c3d01141c03280d008aa040003031010414140440101d244090b0000c0c00424602440107041d06106c01e0043c1c0c0c40d5100d002c0601c41d5030f84030a41c3c085d00c1001c48002804204060032880044c6407012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220391241 1250 220389991 220390021
    0x30a0f0203070512030a03150e0c12060f1806060904240f0e04060203100803040b071109010f26030d0506210309010e011b1101110607020703020f0f0306 67
    0x2244a48901d401c00905401c0c0840400c1303e115071030025506120740a28107501410703102c02c00a204c03144c0c48038042160300c0c212140314021030040c0022500c402c01c040e40c00c6c8990101500c06442501c003030b14204896502d19032004209605002e00440c1d503100d14000c28014003585c0002c03544542030841003412642624103014049101c11144184556a1a8001c584c1a80e43c06901a40c41043d0b0000b00400d2558005641207255039200090342c0c1d68400015085030041d8005510040c00087c014060100d001c4407903101020481d4161a00d514040040880b00450310401e4046001968141c480c1003400040d001c1c9040e814043c0c81c0c0d129880c41a81c4000e1004488440c42401140084502e40021020540c0c40c0c0d41c002004500e421300180055602c0c1011400b65030402490034000000780034a10320300102c2c40c1c0301c1d004900c0e01c0f0010000142c690002a0551121a80024108103000d5030004000d02140c0e01a10724a080c404c820022520800d481c00c1050780505c5078600740000d030002d104903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220392491 1250 220391241 220391243
    0xa021003140112051b370801020f04061b0b0a140a0e150606040506131a180603100803030412030e150f0703021e0310090b1c060b030a0f 60
    0x41c801c0940e895540c89103440011282c0a4000c0c1d103d50040340c0200c0803a080718034007100041201c2d000786c100f445519031000c6010702e4105402c1d44c510250f4191091425081e010303100041c001d60401c68412000b00040c00b45201e000c0c00c01401d810300c03800e0345400d4580c0400107a08190322038914940044040c0c00b0700380020050410700040b0001451300701c80340c8540d82c0028400009480d950a403c0d8404000c030001404107079010b4401c100c001555983c02c002814280480034060300b08516100e071089004100b00031500000c08100070404144040030325034214008129051030b100d031146401040000990340080001d40b20003c24030040c454107481400b10402d595400b807007501c0c2414949515405604180e16400c41e20401040b20300c0850600b25a2101a901e00141441801d070f00041c0d0380a185800d09070b01207800018040e00320560304186000d4003034202e09104c1820600d011404c0c0850411824822080a071104010049160810440c0400080442d0042005420101021200c0c944 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220393741 1250 220392491 220392521
    0x50d02040903050f0c250308120a23090d0206131509020d050a02030706050c0c06030408071209080c100f030906090503030a021804050103080301030213020903070b0403050d0806030601050d050a021003 88
    0xe0b17240c1b064000441003070700d034015541030805a881c140d50710320702d601274102d0601c6038940026400d9418005442c8105c901c0c1101c00f0030188c2400c40c0203038148080e051006045400030b00c10482e04010082c0b100a01650050580c201d149842c0b00040c010a81c0004c02036008030103000c6170091210000d01800e8142c000c50a8502c1d460391540181c40610035480000007a4000300d5020708035181c510003840c0d20601070310341c0a1074140181e40b50480c0f852064640c002040032260107001c2c07103008100165401106860580282381d60400103010075401c0342c5100c08058842a03801c040003559004514110340c4141200d403a0f0509100150281d0040800407001c441c0e9403855241a141030700846049a4000340507610390b909680034050280d41041e4003000640e002c0140800c1c42e102004120000d00c004002c143c0c4450840c50702c24100500000000304100c1c0d001c050084503a8041400c0f411550101c1d0f4952041585140c03260a05085400c084d5114910203024002c3c20707099000682c94840d0b010b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220394991 1250 220393741 220393783
    0x1005031207030c051c081f0504020906040b07050d080f07080f070c050a030806011b02090c071b06030501060e060702100f03060911040602150403080f0402040605032b09050d02040903050f0c 83
    0x41d0300c54440304000690187d102036010b400c01190501d0f50040501102c09090f540c900360301da403002542d030381c049401200c044d07001281c0ca440c0c0e2035000b0240380d003102c101281480581024000200041c2c000703491030101181020100d50698080e1001400169102098900711480c1e03007400341144000b12a0640442c518180c01d41c0c03010746144410800e194000d20610140d12030303082c0c900c03040d041001c04071030a84142c03041d0840540c0b9031000400600240da0301082c60740c101a0024603a12411085500640c0240010401a80d071581041305c01800c1386408443c2d2681c00d1402c030003801b07580d403040441c0c0340b5201d00c0c50360300301540e00204151003554003100c0900c2ca4149c032201054030106c60203400a1020004180c549a10a4401ba003040c0020800f142c03241e15500080e05016280b103640c5002d40fa050781e000c8104031190124a4100e0081c03c102170090301c0e1501148002e60f40c02e200034803641d0380d584030b2070400d4014420742d643c88213000c0381036031512042d1f002995a8004141d910250356425 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220396241 1250 220394991 220395001
    0x40e0907150c050a0b1b0d0902030120120705160f110603010e01090207050a0804120b091b0d0606090c08041401050c07150609051e1005031207030c051c08 68
    0xc0b0101a40598408000d10712400140c68074040018060800424031403c014170080c080142e1001e401100c00600c2c00045510482c410982114240540300001400350042d030b40d00c005d200d0050302c1c10f0300102c1005503019915100100c4032031090185410051000140220501001101a0704254460200808a03500c0b241c1048100e000034890030281250b414014411170001c0e401600c0324034442d1003203030440c030b8080d0380715400c9401540110303c8038041008860f007800710450740160002c04202c0609020114260214000c00c075500b2101c0c010382c040c94045c2c041019079444400100b44e000070401c444c0c039a0020007402420140d6065440762220104984d07461018071942d4010440e000c005460069207945503105c043d80700090111269031210000341d650320b07901a0324840c102e001c207a140307043c503003060484950501034004401500214070034030150300c001841010001c2d1885c0b6140c1c486a5a1174220f030310000710703907009049008002d1090001700e0a50044003000000d9104c211481d9a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220397491 1250 220396241 220396247
    0x8030903060109020f220b07030305090607090b04120f060906020901020f0706081501030e060c091206060f0111160303050a030c03140a020c01060902131e0623040e090715 75
    0xe140214404080070400444c1702840e41e40e200c01c80c0b10a60b0028203a00d503940040f07d4a40d0040f84007600402d172100200001c205061000d50340c02949820500200e504040e05462a80183e00480ca40e03101b11b18503007410b1200c0580240e0403198403030414400d900b41813605030081c0d04403058040c0035109021208003224804101d0070b040d5901039032403c0c05030391005000e103044140014424141685d89019500c841401e128191084928011b19551403108009202a5012070468641c0a810000601a00e03944841c03020b180300b542443c000004800d040406070802c0160381480a107136160000000c00c050b0050040c001444485d101000541003285098040e181c070f03189150200c00201001403903c421540c082d2844000002c00010066240c55403001242d0000003844142d01149070204045c0340e010940000019110071030381089480c0400c0a081940044003800025203500c102e0005050b8020a03a4024152860081540d041030304000d40c90b01460f025111403c20042e5582c3c00f10344c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220398741 1250 220397491 220397497
    0x101b0311040311090a091509020a08120f09060910030605010909090f030f0216030c08010e1c0e2704120201020c42090c01020c0a140301090209010803090306010902 72
    0x1410403d2903580041c444100894000d0080212565654880c10080441c1d04084901702c2c81407c0340c80064010042c0c0104200480d01d507012140030707440990422416807805041d581610150741310740351031700d4418000410030b0181040c1c0f90f400c0f86403040c0203070354540d15030490303001c03030720b086e00e40707590702c6482394050f01c00e4074000c4401502030700721003003144000303442151030345d00209072803043c0c1d2420000500c10981020865109a4642e01c00107820300c0301348000e20031810300c241c0002c0100000c900c3c82e9007000755550a4590350080c03006014441c0030701e8a039507100300f0900c041d8412414110364070014403916508151070948404100151191801e030052080750403032040c2600410081c2400c3e0350000180c3c280d20f0400003100c000351103c0c5000c0e10525091892441074840c450745a24003208090310300f102032208603045600150910419484000c2000c06481030b481c8007804030026503001c00e01410750341c0002500400408000528070070044050304158034110141d4010703036170b03070f180303c1050380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220399991 1250 220398741 220398743
    0x120a090201090312030605040f0f0510120b0403031b030c0e0f130b0a05040c031d0705130e1504060b0f09041707050f01050f040614040f14101b03110403 67
    0x600e802c200303101140d98103544586018452a000c04c40d01e0b210000301e821703986207000818600f51a41105690104280070702d903804020049481c14aa1400c20480c1040f4180e460243c1003503a040003060134944650040703510301880c0200880d0103c0769150042c02404040d00e40c000095006143c500e80c0c0c0341c0700745035041c0c080c0004c01c0e044500c0111480b2000820381c9a85856001d09005d030300148685840c02411f40558a42e18005510245c0210f40c161103540c00c1805240c0c0e030090001407102e584c800180d00783c01c691a0b000010064440e100080c0381681a1403e04802d44c548400c100070040d058114180080c03003078416640c01c50500007400a01402a10014208444085043d407456199800f420b0721500030400c071016a00b003001003508446c0c0983d032103811000004100010301106002c0d106c0c40d0000da00c02c104c0700f460315845202466101030340007010307503204000403240c2c6e600c100082c2d801401f078450100219600c00c4420955070084140386070200e42000c0c0d60801c1180c81a003603070116 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220401241 1250 220399991 220399997
    0x1107061503032601091805070b2a030703030f0f0905070906150e1306120b2406030406050601030605221407170c070804080c01020c030319080402030a080f120a090201 73
    0x743c0d09040c844406006c0c200d002019000c40201044081003080103103000408400502c103664001c1d82a02c6041c0c84d858039004504103281d0005500b8402000003103860031074041c9000200751040400e25800b8044c0a00405051824103001c0740038014041102001c81e4000d400800c02e20b0741ea207079110030300710a580601010609207007110355a81003d0405145642e04041d000844035103805d00004d02c940b110340c3c02e0b9a14281c160030045002c0507000002c1240e1100001501c00c2003001c8005100c4e4070005000a090541b140301040060340039400134170103040020f0000c4012500e0703010002205000b081c5c40b503c02da0071710704240440c0c2401c00f280c5001c0c42d0302d90b5481108602903810441d82401c090b0003a0312244042148501103240003000c1c0000d45034400282c0030664698000900c0e006240c02c91512036002041030750b8101240341c922608070301c01800c01004c0799949000090a02d480510054200d1000180c0c000003d03c0d1040180700b0007480840b40a01a00c0341800801265203102c07009000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220402491 1250 220401241 220401317
    0x9160303080612010c0c051207020d06091403030106050d0f0903050403031d0604030c0321051602030322030203120703051806070c17070603091104110706150303 71
    0xca8881c0c4003456004602901c0d0a0115291a081d40c0c2110030722003071071000805505841080000510070780c4280701e032010006041164940000e0701b543c0606d40020490b50355040c500d000c00c140154410403092254040e241ca03503940e84400385c40c3d0392100c0003143e15985080818150f4142611030103620581503030b5228141403d55070f013561000704200c21041d007020784010440450b661b8038000d0000d540f0641c4071401c1a4074600e00f410000052240710341d1040b820320383d00c0e100c4c075a010041d1088005001002c07640d1540600201c1c0c114441e5034082d44400140001c0b24144210036000070040b680f007a41103c09012031a9180341d028012031900800142d41042424144034204403c902c0407900204030324508100c83c0c0d2658003d0070b50b50300c44404946a900c1c0d0000c0c840080c0250401080380d03003000c0c4450b24440c1d4440b4400d070410b038031143c400c0c3e648603240019071080324255030f86298806000c0150240c0d40c1040914150144811030028200d0907410001100c1006202d4802c2d04040700900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220403741 1250 220402491 220402493
    0x5060c100606080717150d02030717031308030c060a0c09050301050c180108090c2b05010c0917030405130212040819032a051603120608010c080a050703090c03110306091603 76
    0x3461f021040c043e0b0b4140b08803480810000d00048004030298022001981d0307030700000c66107203041d0005034400704542d0030600030014540804280a907200954410028050328051000e481516a50b0003258041d80f9102c03c01c0840000b0780024200c40341c1491281e113040b0780d80c9004440021040319028080d400215105082e818900a6803040e4400119034403203c881800c058142030b00d0811080d16669110048144050307000038020380036054503050314070303281c105403a542d03503d21592141900900803410b00c625003003100d42c180c0740c0541c007500d444003ca090034200030305240c100030b0b558610744e170740c0b8003510030034500a20480c400f20440c07180d03400000c0503013549150703941e031202450014020b0400080292540d0007900c40c1503a88203458144e818004002c00d401140c2448d000714655a00d0610000f01107074021170101e9002500c00701c04aa141d440c1c2c14100c0140c03e03041f01c01040980c01400c084104050b00081540c0010291708589681e62035100715035540c2111056101503950140d8144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220404991 1250 220403741 220403749
    0xb03160303030509120f130e0615031e13120e09010b0a0909020307021e0a021f090b040b0d0f05010b0301050d0303090807050a1401020705030405060c10060608071715 73
    0x16031250030001540c2503002011011812a1b0184203000d00400c0e001601c43c0700701e501c00840c40054519021070125070b1400c034012400b0058241c810f8113040002200144443e020201d040224103c201c41100301c0342010b8414100000750b101084170314103911b0320703031141d002d104100510f8034040c001e080140c01e918000c2a42e9042e800703035150308200601d0040201f003240ca640000c60260030301e9401401d08540030084c08000310f041d8202d42d44207402007031807000982d40300c0700c5a00b00303d030078405401c0c50310407103010544001140b41e21690f10403001141c0050b00c80030010207421107400c40340042c4003000304061103c044600034002c2d0741c0411010300c014042420010320f1012114424140000c0340d00740c544a000c425003040c0005c4841c1c0e4015107110041102405040d17850b40d82d800025803d24580355100c035103d0007103004440c001c5602140c0100f10900402c11140d180002600804c450398442c0300062160000f10790300e50110720460701543c2c0060a0300110f91054000c111400c5040280c07400300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220406241 1250 220404991 220405001
    0xe092506050f09090103081b01020c1002090a0e07020105040605090303241c2003030a090501081306090302060601091a0403080f040503150f0c04030f020d050709020f040503010b0316030303 83
    0x8490480d02444010b0413600d40c4c410380c1d806540200d0401c2e40303400000034841101c501d501d000c10346a1740103205640c00c039000003c648202c41c0000d0400b585601060006c500c64691503030207104c0d189402024407503492340640c00a40182d00612003880540d45582c2c3c0036aaa1005455404006030f0b10341080c0c140f5601c071620050b000340020301c00c40c82120580c1071625151410381d0f090b03850504040c15802c8405c2000708007100340a00764050341c00c129004002524080b004d00c00d490601401000041040d803102c0600e4401d154070071400c01030011507040c029500c03501280c5c0140031807501040411480c00310342c922445400c0074920645031600f560366420315a00541000c100f02103050101080568017032000c103003e03080040076059185400709085c080854082c03d5000c0c2c4120400040c80401c003444e07002c40c0460340503201c1001003851403038918504183e5900000c1c90758804100c180401210000030021118118024410201c1e40303030070561036144064130700c43d54a0343c280381040020301076005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220407491 1250 220406241 220406257
    0xc0b16021006170f0105130602090a030204140406141b0912070b030f0703110304020907210b03070902191101060807060e01030f0b1e0d0c0e09250605 66
    0x1500c0300c40c1400407503982036580381d41082c2c41660f01c0380700c0b00040c0e0030200465185007411000034004c90420000c0041400340980e8050314150700068902d40303d1b102c02c1200c5004581c00342082240f100c40b1001c600b03015030203440845480f4106502e03607191500c0c480d00305004a410389080c0510803200c8400072001e0340301200c1c646d0030403802200e0090f00d04090210400500c80982e26940e41d00d0300c00d2141c0110000201130030145071400d00c8010184d403410050701d610560544001c0655110690f042d5034844202e441c080b95400d4850b000c4448200340d410402c6c1c2c03400258210341d442d0f40c1700e40c1007805a0080704031004000820b106d04800940c82383d66010f02d5000d030800000368203921182240c0c14a88035400c080049541c4a00009181d40d061081d0210450315900801015001d880010101480a02c40c0d891405d00304010072065620b100801e0001136010710142d2074141d82e078121881043d0304540c0d00044c0d0007800314804a0043c510041410040c0c2075003080181070603c1c42c150f80e203410001d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220408741 1250 220407491 220407493
    0x105090a020c07030b04050a0b01170d030513061a120a05030a0c020604030f0302070f05010c030f120b0306040c170304030f0803100e13060e010e03030604020313020306070c030905010c0b1602 84
    0x180000410170f000c01c843d000d01d0040010308038141e1a42810a040001070b03108041200d000f1641a9514001040d40301103031055240114043c0c6139200087c0580514a40180440303140400c465402004544102c040725400d4a4021526052a05da24ac03074149640011745550410425503140391700c18044038440c02c0c801480241490b441c1d458602100c080042c00304c000da408038034103100c6070030b040140c07000a000900c0d0402d81080c1c9660001c0c0310585041001003030003012103040f40300c1522900219100c0d48050100c0b00c0c5841c00b4100121244d555201e002c01034061400444c0c2161004001c0381c00f940c0e00410a500003920036640c525160b407000703161015010303e0395000b160440000300100e0041482d510000c0080f1190704054003110110800403016070b14110484840c0a004000d403a072103034040360f006031613640e451152a000180800001e40c50301514040001c40303030304075040503801e42c003d40e01c0075811a143c50045d501100030140c0682249038400001e0034070000d05886646040c01c901c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220409991 1250 220408741 220408753
    0x80a1107050607080702070b1612030b0618040c050f040b030408090a06020a0b07052104050307021c170a08010302061309110a02010e030a0f1b051009020907080105090a020c 76
    0x78440d5410060280c404100061040e01880500c0303034100300c6000600034000d8120301d40401b07002d4601d92580c2e0f2503401086560329509244400d80243c1c82451118030150000341e0b5011800c0ca4482501c260240c0c89200d00d141125406001d0701c200240c41c030b20380055806d40d28050400c00f014443c2d80000740121190b00c410032881d4180d40310304110030700800054000302070b004501d18210610302d400600c210100034090051200c580ca581c0050018041e43c014042c0d202c3c1c445041650a610854202075007085440307194080490342c0800020010703004000c0c0c51001220010180404d1056082c442e000450035801800540b07000d0300245000d40d0405c030440308540da1861050f042d10507803403034090056008141d10000b00d4081c0540c0c0c01d141d2650b006907181148100d0064002c401c03040d2039100b00f100d103040300c84000302a00500380b1065005411076040040c0c1c4c241c0040a010030240490048441e8000325643e5409001024140c0d20000d01000744c076a40c01c01c5d484020b401c1840d0314695845a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220411241 1250 220409991 220409993
    0x10030b1b0f0a030b040c0e010309030507050604050313060c03140a03020904060905011503020306031209190905070e1f14210708100b0406180e0901091110080a1107 72
    0xc800500d08031800340615501c032140b00c03902030200c0c0c0040c41528003850400d060144582c1d070211010031010305c01d00700020340110034201110103004081c1c0c01801841000240401e00500002034824100707896268412142c42c1d079000c5032071001480005000c1051324042e10326070040c540103000680c403146401818911270780002825030301945c1c4403030f210f0fa648800501449070019040c0708100780324181940355041180110740d0302e01d176032107d45000311004034425103555030700c00c0f90302000c1e000700021182143e150b003180b100034039065503100046040132141c0810b60034003410f17114040c20420100ba007600b00420f02554080b4040e117640c43e4600c030400213201380403542005c082e0004c0b19150080402d190200c00500a180040c151042d01e0400e960b0400404e508181110180d030b120745404025203034240440c48180c15180c202400c60384e024020841200c405501003e0814010303402e500030812220203020412401044000c002940d03080020704030380b085d40240d2019803090050701c0c40c00d80c0e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220412491 1250 220411241 220411291
    0x118090507050918090607030b0d3305010501231209071203050909090601030203030d02090609100e0910061b020d0b010620070b070f02040902030f0a14030310030b 72
    0x56000400b40703805003c041c8900c01070200714040e4084108e0070104a1522030000261030190070810040c0719040720350103426200d0b24800103922021909001165126074020140c010f06001d024460004052100c01c21170001c800481d042c8500f0f501a4aa01c0c2c50440380b180003140100074507841491080c03c0300003940300740071880d0100e210b00903620749480350101020440c001c030020b0300c460420742c44500127001580c1c0c080100c43c1c13500105100140e5400c0437002140b901c0c010194100d40c8104d080300c00c0c0414075080400302c00041c03421900100c9950f26400341c0d0302214820701842000400100310202d50011805003651010f0001b406080e45010a650b20124903409820450005a10110f41e01041c00d4030400f140c0080b4610010701b90081c103050304205203000e414400340840840072950340031f5448590011203400d40250645402c01d5a8a22466564070303078034411a080140300401012056010040c0d078090814000b503542d80d03501d5a150000c04041c060450a2030032100442c0ca056204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220413741 1250 220412491 220412509
    0x80c0607120b130b21010209030f010b060301061b230c030a0308070c030302120c040503070603270602090901150215060a0501030c17010f0317161e0203150105040b01180905070509 79
    0x3e240000940d841523a90241b44c200b200303d440801c026030500c1c0707103100720b50740c0ca070241ca05480191070b1141401c40c4100302c05074140c8400b01c000d40003d00809180603000c0512070701c0020f0210744002c032081c520241080c1a5602da10120140005012001042e1154072600d080420703140640780150808200540f03403c1c0103881582d00d01003c0380d00040810960506000000051000742800c0121681c86a4802d50840108084400e0102c03904000c0c41000034a50603184001d0780039010b000c036982c40380140c098500b801c442001c05481980100f01040c41502c500d24271404002c3d00d0306448034a024015000b4000d80302000003404946250442d001000301c0d0760b103009050010607000b400d880e50070442c01c00003c400c5403d2209104114210300074424258003c2410b42c0301d00e0151840407428031500313603888005c80082d89405030f120b1501111402442c0241070380e0003201d040022506610054442c241c518074015100e0720054410003800071580c2c00740794001010300300030303141200c00000944640c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220414991 1250 220413741 220413799
    0x41101270e0906010501050301060813020114070b060415050109150219080403170a1e0504050303070803040209160c0f1b06030510080609030711060403080c0607120b130b 75
    0xc03074014108005401c00300302c064010002801c119140d54140300d402044420014011001900313445903003400c59215600340700c0c140000a00f4070741c0754580391802402c04007003910b4040c0302e42e0074660000b03100c0c8140c10040040f43d505840710307110b02c3c0c500988600001c0c0c03040c03e99025801031f0140d094100042040c500c035158441c0c01510b5642e8194070b042c0300503812a040004c500c3c20280300a580158109400072109541d0360141650120b06000884813441950005030300360102051500c1001015400b65000318421900180385a841180100303041e40d90040c4a40040d407207501304008280a10b140d017010700c4c000c46140543c018500b1510014900680c03000f40040daa500820100600c40e000310800b420286005c0e000c01e0a041403c169240124070020b03000c0c15900040075441d079550801c50b8003c3da4004a4a602d56104c204901c0d100d0030201c42a002162131070903032000d4000f89100e1801d1040001380400825003035625020020200b151000c1d40218010a91482220403038068032004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220416241 1250 220414991 220415009
    0x209032e0f0f0903020a050d0302070f020108091e0a02181018110a0e03010506032b050d06060309050d0f0804110f0d08090f010e0a1401021212010905070804110127 72
    0x1b074221440c1841c0f500c034070040103004151050007620001007045102c02c204980901e0aa526520b8030503085091810820324070302421814100041c00020110b1580410340c000c40302c4c000c034049040000304103c01d00b1111000e45154a48007800f018050900d007132201c2003206030000d9080903100302e043c580e40c8800c0580000c56480200340ba118a000d0044ad42e200c1c2c01900541004280c01c90901c0c42c2d680615100c89888001184d4400628030410a41d40301e080c0035482440019914a0f01400400f104c0c041543d05008094030442a18010024001012803550b03030715510f503845448100d0800b00a41403564001c06034641148642d44090328000650300031940300c3e0b07441404a0401c050f50042c00b880d541070140c0b1840035030080e501e04044008540d01901c15020402217013004038288811002c0c4208084404a005c0030000141020a03058400505041020791030300c090030ba924003800c0710010700003003c07940c1c0880654455003054001c0c0004400202c0130a03517100341760010b24903e410545003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220417491 1250 220416241 220416253
    0x304030501050f180312040b060d06051003030206010b0316030902060903031c06052b03031401030b0103120504141021050402040501120b011401120f0209032e0f0f090302 75
    0x21001800076415020441c00082d1b2420740c00300b0900182c4600100007400e2044004001007030340d10307003440543c820740c2c1c000c40030803542c94403100408804e002030000758014411400046a042d035948200e80c041c43c1902c001803d00c107108201103000d40811382e07040341c1040051080100d01e4a040006c0e101c0d072410080e448842d045c400b0341002c01c4039a2940800d2140c52048200600700d4504052030300d440c80101c030bc070f09080c88141420303000b40501c01d030724240400546d00000140800349000e141030700c1c414402070350207031541b85c8200e9040c0214060750700c5103000c0704140315040c03401490760000e0800034180305c81c6507090301c840c001c0301540d01c05802c800141c0310700801c03045281c60712640c2d02501c10342100c0e00135581075444050447c1014054902c5e03141d08048421120b0b070080b100b110100071420800e00c81c152054600b800a900b05015941c000e02c01e056000d41000000340a10b00c1354001507110350010b8100764045030280c41080f04501046544044102d1507440303078003443d54042e0007134008041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220418741 1250 220417491 220417501
    0x509010e030a1704050a0b0f1e06012709020309030a090e07080c0f040e15030607020c10030c0e0310060f0e011401050a022d070512030901030c020304030501050f 71
    0x109441064503403010340d4104014040b080c942100e1014104000810101e1195031940341440ca084076102d0040d105108000400610f64805010307548251060090303614807880303420030b00c200707408103450103404617109144402c002c80411101c00c602205010f4910801030392541181d00326403060714100141d030400100c1e071600c140c20600c2c4000400d443c0400d01800c0c50701d000c1c010321000e070140c92402581000036500881841100555000d1b080d424011511428480c01d2400044010039000e0b0181c0104800251550700100d00c4c510011000341080034400b50040301280103261348404001032120548102e44076403401c00c40280491009880007842d141000b0f03250f00454000c1d8040307180501c940c4c00501680b030b6203458140b4480744c02e081c02034551a40502c107a04004e52280c05a200ba40b025080c2c1003030002103580300c03204140394410703107521316210010311410b000140c113a17030350aa0003005006000c0d40320381d20500191895105480c207003522503035078501750b40d81a5450300300c44400f4002c0c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220419991 1250 220418741 220418743
    0x60706050414010e03031911042705060d03121503050a0f03020114040c03020f040906021603030b06120114030f10021c0b011710080102040807091508060f0604090606090509 76
    0x131449076089030045080d03282404030f6034840300c48101d1001d0b4560b00d507081c0a40b0300742100c0507240504584220100c5802041d542d64482c0c1512041920415061001003003540c18160710701c1419a81503903a298080c14100c03c820301a000400a040380e8660074a00040419401e010030031120344179640000c1c8030121400d0013400d5032910341c540e07900201c2c01c0d000c0c03000194002685004032581900c82c40e050110b42c900240050541803800350119000140c0c8404000404000301180d0313110752001c1207030101c440c0600080e402010407c450003000c410040c03080d0b988400444030404801030481d040702144c540010f04140004004501c0c85801287d40d10915041d0b60204480c2280c1c01c00c10000071003440d00003400410109000c00c064080007020031030483d40104000058800308000355646d956408482e0350385e000354820340c51414984840c003c904c1031a100700c03c04698140f8000c1800ea240d42c80200840a00a04104d6000b6030303440d0120001400c1d4041e01008000103040041c651400b200e1035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220421241 1250 220419991 220420001
    0x30b030f12032a04030b041502210c040b04180905030712110c01080a020c0a020a08071805091515090f010e090f030d020708160501060519060e090606070605041401 72
    0x1100b800220003d0f0400d000118000c0c0c4048170340250350180d0070b40725070a15052890185080d03103074850000032040c0a0030000d41039269450741828054005503500244410326004038000ca03e9561010001008442c000e011040b8250144000c00102c1042c0c6545031450740c0e00070503045a1201d40404070312052600040d08409080c000800707000c50002070301c0000c0114000070b00900701d0960200d107010f520b000c10030462068640c09007905500f5a00c452550395508600c2c412500180510600350040d035989024480c05050501c00030a2505041c0040d80c0d80b10500030060827032030025034602ca51a9492a45882c0282d0801e0405141541400c01d142d00000c80189441c5090344840d5900041850020449070f04c0101034000503116141890120305a10800d55603a903010090600001809011340c03001d002c0f01c004a131040e6190214108507402c28040b4480c00700481c140710201c3c10b15081c98881e266101000402c90b40c5000b08603035070708040300c900362801e450040c4651403200300d080b424418 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220422491 1250 220421241 220421281
    0x5030607030204120b040f0b0c0309010f020c0a08070201021204180c11150613090803060a06110d0305270f060a06211406012702160201030b030f1203 66
    0x150303d020b0800e00c0000c1c024070328040040141c003140740043e05000c04800002d00d040d40c0070b0b42203c11804c02c0c03420080030f41c0007654a25010751a003880c10340d10501c3c1c1d200722091141064050210384849031120074254104c0f000c240d0540c010948000403224000b4020000341980203990079030014114580011505401d00d44010f1084001c5964075a2034000b0310317050030070300640f0028030941d1840d010856043d900c031028151a07090486c0c2004018100014500c519803d03202808000e64818003200c3d40303420000f1418840d00080e5210504910030b0308404e5000980540d02c401746810100e036840c070441c0e1018a01c11075009200000300030381040c80b8a44d080848034006005d114100650040c80030400030b0b0031404d0303006961001041040d000b00002c0c01300c0780c00d001d603200c56a4481c071040c00b003100c03d4494032141e04440412080c00c080340c4240d5900c01d9403054642c3c0107680980c0194020b04020f015154144a0340002c0d6500c00d0080002d00700c0fa039562403520fa02d90400840c0f9040300703004448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220423741 1250 220422491 220422497
    0x150207030303052211150c010f0b030307030507060b0103200915030c0d0e0c030105071e090b040909020307030b0903070605090304291908190608060a02090301020c011505030607 78
    0x4040080d4184070024803000359007003170340b0b2140c6418803000a101d9840e404042d141116010491040045065100818002d140764044c4400350540c002c047c0c9a11500c10002d010450a0005002040d81b1764450303034030400c0606001071501c0700d9000b05c2d00020b030481220400444001100e140e6070070003002c0c0d07040c80000482000d055080c10540d0035444d00822003450740c6140c1d120040c100500b800c0100107161107014000300000e0600c5070008000d02e04484208804140041d96203001500c03600b40d28082310b50000640d400c060501c500100500b11042c8140c0c0e16128040300030000c50304040c0ca0b18007554100c0c0085588051628014083c0d50005280c03070340640091000300402090681f40c2c00e2400012840d0744a100f58425655030980a0400101c0c00d504151402007000e5410500350390203001740c000010003d10450300c040301592110300655402d500001c000c2854061560090400b01000800260400d002000914210741d614142c1c0c144040051404028505090101c1e5401c0b1800d0300d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220424991 1250 220423741 220423771
    0x90f10061805040203100c030b0405010801050f010e07080f2706152b030507060e010207020108090d0f081e15041b0801050603040204060b07030e03010b010c020f100915020703030305 80
    0x20700001e03107441c620480601616161f106030842244a907201001c2d101d00100200f2079940c50344540390092000312400581030b4043c50010901a000c101c42510a00722643c0c0d8035981e91300c84400f0030307407500050082c450a4506200b01f42c07840030110901030403031800c0c9004010038606540410800070f0b10001e0980106510301c5043d65181c1030341d41c0d03008191415142d20006c1000d81c41e084510380300e1014054a014a4100003140e0300d04190018031046000340c1c0c552500303032103c200694440308040203190228140c10360409080e070050140d02e40c00313001802c04400b000e000c05140341c0b20240840d011135021405610184071803038640b040740310302c40301d044484881c0e00207484040d02005060007124030840c0080b000408566070b40e0006809003040b003c8180e1030309081d03c0c01405400448560b0341c070031f50a180003140c0f41c0d44960490200e454006000044962523803043c014100c2101d001001042a81c5001051905014985107003000c00c9034020200c0d1444d5050050807240007601c90304400e1060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220426241 1250 220424991 220424993
    0x5010b19050a0b090f061201080601050f0f090601050c03040e0603120a080c13090204030506060a080c0a18020c1203100b090f060c0a060606170c03010302030312090f1006180504 78
    0x110b1800c02c01d5031070600360241c1e1194884001048a4100405c4662084001480100d07c000c0822894100c2e24581d00300d900690b29403040000320f48034800b403a50041d144101c1e211881c42c103440790030780100b418146145009409070000d03080d540b00780c0101a410320603505222031402c0401808140d9140044802d08054000350000c19005002d00a46502a00810201040345c2d40c1001000144015003046548030303903d1074055244c242c2144c1c55442240b00c2100016000c9012403a0304005500800495a041c03c02244056940031828070382c0e64280c1c248030384c42002c801006882c2410015000c160348a1824000c03d400d0000c2542045500342d02c14051542d01c0c0d1110780c2d8004c4804002c403186902c6410104100d40b60203a9014060140d074203064000a05c40d402102d402e5221408a000d140d150342c80c6495044548028400250198800c0003071180003403994a10740e4100d80303d41c0654112004c0a814a4a49400180204c0c98140d4a000400c202c0c00c0c0418005402c040c4080248054a42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220427491 1250 220426241 220426249
    0x20f030703090e090f0307150c09050112090f020d0b042a0b030406090501290303180d150f020d050f0412050c010b041b020d020a0f0615080a05010b1905 67
    0xb143c031960652880e06008948010001e04c80b101e0b0102c440307030450340c40b0302d4181850810380c000c004148503803a190016000559105064070402c2c1c901c183c503030040c4008642803030801422640000d440b0f1036000168080165102100b0100e52801884680c2983c05d203420444400f0300e01c80c0400300700400200b0390b01c50828152a0003410dd8200080d0603480795154140b40025011071000102a540390000f01d0301040381203075003d000c46120b8003004030b844034800305240c0d49204042e0300010000c0d9040101b28207103001020400d0413449a072807542c0050039045640c007956900c002e148420341d00410950840310491294a601100b080000000c0b81010707114202c3d44141f070318170082009400584d141d0010400d4009505111010708204011003540f80c090411000c0c5d60141e10040c020440c8080c60340780700143d850040ca400400d5118a40071655130303100240210044858615051140001c001105000346d003003050040300085000b01919040101307448054a9050304000f03900000d12060311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220428741 1250 220427491 220427507
    0xe0c0f1c0b2b060209030a1a011a030a09060207050d0203071a0609070e031c09050a170304060e010c08041d0601140a0305091501080a061a220f06090c020f030703 71
    0x212601c0942e4161185041c280041d124920000ba014415068014108001e84103146030f51040801034500603622200201a440d45013070b6070341442d20003440450540441ea0b07100052403441500c0040c07074103141d81d07130381e50400003c0c00810b000350300080792000521840c000722886642060801c0e00f554680240014041d07240a0820401c110300c20301442030646040254074000040c1880d003003020120908002c1c641e91082c05014040c07014828001440b0040c4061002183c070718402850509042c142c0032107001a07034400e0241000040c1151802181e5904000d002519910f60590044014155442c90f440c0014107440d04100107107040c61084a03911056500201c01c0b03240103d655119a09542c1c6084c20442840c801602020b000180d0f403000042d400314854400e04041c801c0091800300b404840302c20140e90341d00a2003030841d0b0304102d0306401d1294580c441d1107000082e808400c803190021980c0d00e4002840d06561000c8280710140c0402414410300d1b440c000440c50030070290340c020100d81c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220429991 1250 220428741 220428799
    0x1e1809080304110d06050108070501111b061608030f01080d0c050601120501020423010f0309170304060e06010602011a0409080706020313050604050a030905010809070e0c0f1c0b 78
    0x180b9400e5000f03850780c1c0c40440d003640c02c0b50070980a104c1d558541d0b0b10262517440b00e10442340800c40c1551209070b034403c04a51100d0180e82000811301c0c046c1d206090042d241e02521502e402e0302151524080001c501d20007450148008500b17100c01903040c07091092034400e2400046051080b00c8600000003180080c015056034007644d403420301d032055860b150b40680659041a20458000f01501c4011600c290007a00c1501090343d40850806e002a4107400b140c4200070040d00b03149500d802c0c01c500d400d90400035500584174000c0011a0116041500d04000c2c2c2a001080184d465090440e00ca810341d105461203003104540030000c002c145d03940e00b141880b4080d001825070303801000084902d6102c84d540240a038101050ba200c9203050300e051a180c1e550701000b140402c40300e00010540e94440d001d4244180c12400052401904108454901601c0207006103619481004152840d9950354080c191002c4601c000c40341001c147c4501c5020740700740301d40d00c0d8080c42030081645401c07080550107407040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220431241 1250 220429991 220430003
    0x8070605040309081b0f03010e060c07060b1c080715090302070302010201051f12110310060e13020d0201031512080301090606050a050f03090c1503060909010203060109060e0a1e1809080304 83
    0x40d1b13804e000403030302402010601100354080d40c000c01100301e072460b004041e22031080b40c08000c02c00d60401000803140d9102c26810282d60041080400942d9243c024002280034a070341c1b02c254071225800905403104c0303150450043c1c01042041046503024007990307030003124555081c8550002c01141ca443d00c6411702c5003100d074420742487d40e8207008100040b04030401c0b000e41034136076066a04050320050502c6111b0404181d8101d400506940340c45500392404a5000389004640303c0960011400342c400d83c503a00901628403003001030383d03005610160240611440900351651315122030710080307030382e998002400c0c400c00708006416554083d04548241c0c0129200740d07100c3e00d411501c1490510781203100f5401290102c01c201864010102031072090390f0071a00c041d015915440068280d000656559000c51469101070205da0b0107490440f050010192040e04581d60305c0c07004110b130600c1640c5204d0114240380307050040150301c8072020400c0f06048020310440320f05980b6500d0900c00203001400f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220432491 1250 220431241 220431259
    0xb12010e0d080a1506200703020603060d021503150901050a0305070506180604060c060515130b1f030912020601030c06050313020a030c140108010f0e06060708070605040309081b 78
    0x289034240c0c0e015100c404844110040420313210600a003072900000c8074141d00c0c0c20403c01c6d0244080d030018000040daa8041c01080c1540c480c4014042419038291080340c2c0801103408428048218402440c440c0b5a2003011142c800030401c180700500300c068001c240140c900e21003d0011600010f02401242c034103440b126503421805002c1480c0e07041d025209030780001d0001d00020500d40c06480c0900c80c5024032420080ca407034044640011003940654290004034101140e4580c1d900c0358011005408041c000300d042850074091a4008411034070184082035460448000b84125420194038018850005201030350554541d21111541c520440081000c000002010000c07048102e10405a0140c03512540316180c1c604046031004a000d40d17031081d13051800c800b000c0d42c45110024126111510040646414140000d12040005211070f4122408026102c000391f002401051024090000001c407030802d1300e001000c441702940305480a03400aa81c821000c400d80d0131102c10000c0443d030b0080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220433741 1250 220432491 220432501
    0x27010b0c030714100606020d0909020c030c0601030b040c0e010b0304020d030e0315011a04030804090504020402120108010b03010c030e03160312061d060103090c09091a0106030b12010e0d08 83
    0x71540c420001c00500d10080018030304034410340058a910704a1814a0610880e41c54510881e40c4a40c4030b0070450000740d45417800c12482a4a034010300c400e54008056910741880012101e207030a03400ea01c22203240404600300014444101e001d0300c007909007118140e01a524003d403104107400042c1c40030384150b43d05d8045800701400382c1d1030805001c0f8040c0a4076080541e01c00f1000982340709105d07000421103401c2c94008400e620b58111015039620801150403d400d06600030b004000041049070895404c00801c024001c1e080000c40c02050000008038500b04aa000d040c01e490061240303c0c180f41c241101d00701d0f80c21002c0151401480440256102229242000c44500c0700881101c4001d0303142039404140d00030390340c001d1403620003240710200854a42e280110203c2d04c02840140c0620b1041109000340c20320b603082600400d01421020803400c003900000c503070084003a071040002c82d070341e605220a0ba080c015010482c44070307000000c00949581300c80f044c0e03c42c1030005a560401401200043c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220434991 1250 220433741 220433743
    0xe0c1806090f0a02160308060f0306060102070b0f040f17010608031309020706110a0c0318120b130606090603052a0d0201031104030609150203040809100e0301050c040527010b0c 78
    0x30021070401c51801701981c80c030304001e810046c01703030740c1280540f202d00d84861341801d00080c050b00800c0180d005050a0349000d0442460341c00c040d107000e101c030804020000d0001c4000c40380c140034001e110648000803405001690846005512200840e001803101a1403a50551041000c5856140001d0b0342c807011031420304010f203e5941040d051020100e81034a005610036000000c807803080d113603240f543c9011700b40100c06018610600342142c8001e03541500040070040b20f550802e402280b2551004d84070760304d000a441494101603246c682e00c00e410018048100071380300c010b8a0503440720141145040c04034444c072410904c03150150ba039030f1054400b164820707130006c2107440400103955200d83e241e18060300138120544080d42d070880c81c002c1c4140108214400c0368001c0d503002d00c80302e280c8020801885404201e065402c0c041c0000d800200b8040e84082c0030b01032041c603204113820f945a0400d010010125100e00002022961410750441c822140d07441040c103450040d0140703a25004181d040c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220436241 1250 220434991 220434997
    0x1a070f1118180102072a1505120117100c020c122113060c0f0602031008061302221b0203072f130608010e0c1806090f0a02 54
    0x41a0040110207110703081203818640306016480740620640c1903104111031030b0030703401203801c00742c10340d04124851310b8a000909050a0060044200c464816517500703203d03d420403801780c0010120b03070000360f1441140303c20f00c2c0c0c050141600c00d5801a04007465040c26540341074440518241c103560303403000c48c1c805000b0026420001c000038000b034841d0303054030030890302c80c05c1168015840041c00e405000a10b040f0382c090ba003155640d10506000186800002c9400b40d01901c0b003594020b466850390408201c840c00218400c50b15110000c1c4101e01d05021240342c0040180110021815403a01e0310043e580d111151f00700845100c2c400c48088032402a001c014065401c40501c0c3c0d01303220550142954022000e0701d41103002d00500c0d030038520307400200e001c09400144c0382480c01117030024004551519186100e040c1c2118000001d029813550895402c6034a0302920442d1076110490880e22441c0c0a0b80c1c2e9200b110750415004082e00f042c40200d400c0c10303000380c03a0361b44107031403400041d80f6600142c0c16 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220437491 1250 220436241 220436273
    0x120a12062108041a0c0c0a0617101503050907170a03120609020703020a1101091203230406020c0f0a060e010c06020c10021c05060603010501051c05011403071a070f 72
    0xc111084021384240010765806580382d4040350140201c94003092500b143c04008a50712900c17804003000c030714150010745007070080c440f8070f60100c1d4904c0403031426038590f6054803212040d14000780303c0c1004c00855190240c07940c800d11000c07040c00743c2501c51600c0496072000082d81818081c180740c1000255801030200c5400c444062440403407030f001030513400280c548000b8005c03641104444104801104d854000307005030b95070315800050510000e4892208000d441d602003030500f1514200c000404800d5125500074401640943d172002610301e4000400034144200b2211903d02e00d1900d2000740030141c14240380b03414022000b44c1d100c00d0020030b4040725003002114081c1c40070032440c00b240704000d4110100c114a52540040b4904410805104050041500070180c60444e0f2a060045034541d002e512601c0c0b41d20f8900d031150109a001703008103806040e8808101e100358102d24285880c004190340220150b1040d0f403440b01500310180c0c215011140c00c0800303052801d0507400d00131800f200c8110b03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220438741 1250 220437491 220437509
    0x403080415200d2a080708010f12020118030c06030e01090b04060504051c080f16020c06090604170307030305130b060f01030228120209010905060304060b03120a1206210804 76
    0x38148070110605843c10707904503103440d0040240c0312446c0440d144402401004c461071408a41488001043d1000e095003030301c14034003015030318030703120380c11080030b41c075500449070ba14031242c060240a230540154010400301400030000c050054075544904400540082c1120307035210041401d01109011004004042550007d402204102c00414a4004890390850560031002080c0b0702440c141d05d141c400103d56000b0a0101e540c60200500d40d4092414a540400c040000046018a0848501d03404c0d40da0b4000d9526000c45060143c1502c1000701000481c604d004611400103103400b541980001013600c0801c030303403040d041c0142c00a210728410401c1203021680c0007001080d00101450b011042a621803106103405100d11080e4024038001c86d0200d02e60f00c000780145d0404c0c2c0c0107580e015000d0701000c1040d02464000c03c1c10011000340400c0c0c0b54600040411106400c02901c0781280c1d02e0403400c002c0c5a140900d01d0742c1010718035040c02101800d032003190080c0031f1a80d054801a03e4100d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220439991 1250 220438741 220438781
    0xf0309030515060a0e07120c2606101419030f02070b071106011404091b0b042d0504020702010903051609060f0501020601030210030e060403080415200d 67
    0x207000d10480c4042200c00510801c4da804001ca003615444541c00c1c003c2e2005d0300c9003080c540c00080344c00c018003d00c1d2520401c004801c000b40d40e400448000d070f5254150705104003c03103810725100340218200410686001d00ca55030406855000044088822f01400324401d5000d680700716800b1000780a52501c180300580c0081401c20074030410b052010b000391000d07207030386848044e401029502c8450074480c82043c000b109143e05220305203a040810464414201c4040720044141c90b4410301a1a4012051012011400b480002c00312040404d540751380c002d0915001884841d081c1d03801409000d04c4e802140c0116800c1e046900580303071540135681c094280c501000c41800d0074140c00c011031187c1a01c2c20308100c1c00280841481041005903a01030340901016030a54080c0710303100c03940d003250504140c0d0301c068101104505002c010b016502c80d0341c900c0d10a0409040c40360364040484c100d420f590385444e1581d03030b801c0364600c0b002c19190402e10031107844400101700e04004000340c03403171503a00c0110a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220441241 1250 220439991 220440013
    0x30f021f05010512060c0307030902121b03060903070503040317120a05071b0f12021f09020a14030a060e070905010e0402100801140904110d0c05090912070f03090305 73
    0x3904403605840040e40c6405401c030b60b01413000d540351001e5800038a0540d0410104055a1080d042903e170580043c10203a03020064a1106241c000a0151405503408075518005603141c140200f680084042009500344862030711132940740c1c072491100800840400d0303415844202e480040c0d802c445901084081c041c50a01e44001c040e0404440d4400007410b480955180c0903070b0180341d134140340d0b000180805900f100303035030720303031754003140f24142d4055224856144c2c02080400c4100c02085c416020081103e50b4184141701000b0300ca030300126928400e4040c840c855480c000b4801405d982c0010010440d041c01c062542d0030b01100342c0240c1c05940c200030002c1041e5420001450040748207469822100d900e20104440b0343c076082c09696418601c100c5801c00078900081741d2a0850b004030f1111101c1c100503000541400f01d0351904582d0080070040c1002145851426140d210814401900c1c004201c1800386e00503101d0010001d004c0301841d8041400d0601c151108005164800100d940c8142e00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220442491 1250 220441241 220441303
    0x702031c0b041e060305121315020309030a0c050906090906240a03050601031106120c0a03061221080903070305540f04020d1e0e1203060d030f02 64
    0x140010b6403a84160307c803840003000310300d046400314010740042e00515030500b00700000303414140301d42104601c0280070140c0c1b150703020700c00040f09a1207880c092491034a444148503244034020b00b2144103070741107000c2101c4036030041038250b4401c0c420b40c1014403200006000c03400320700014152079007144c606840030040040c00200203040e207004501043c0c0c0705c140c000c1003003030911034646e8040404c0307504008140b00b601000058a0341c240d090901043c16502c1c0d03030300d590090f213054a05680541e049840901c1003d1580e2549a65089030714000c803082c41c040020660740d200e80000101046400203040b900c010244071400c030707900f20f407904c01d0b18441d484418040c103102c25140d501034000461290a00c10107040030340b291900c1405481c04100c3c02008080000a40101107901c078060b0b10340b0071800040c0c5602048075980480e1103800507a000048150030714044442c2c0000b4442003040080c8103a43e42d46050121002d50300d03151041004e0b8035a24101d0a041c0d1545908030a5401580d200840c940 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220443741 1250 220442491 220442501
    0xf070e0f130e0c041508030403020d1a070f0f080402032503060f020c100c0f0809010e3903030d0c140c1c03021303021903050f010c080702031c0b041e 66
    0x3c0310b085c000d096106540c09092811881607540caa4400c000030001030505910b180b00c1c80f1300a060001d8404014684041d00d142d049a0b0a0000f9000f04506112150010b248000c1481c207490301700c4030b518041d804603a031440050204613042c0800c181c5814019801a07401001c0c503880b13a01030001000e08020000a9085021a0701d802d008100d883c81604040384110900c075502d503522052621908001524410405414081d440d520f4124604908804010003c48800c02d8002d806209400c5001401c0d103101103901c3c00c100390f85c220801d90031580d00005030b901545811800113030000e0940e40648155001c503801d48a040170100300b1003508000800d206051800704001071955030300440c0300714202d20850582c1c00c0601d10010b024005401c100e003205040802074071110340c44a031a034a5041c500707d2921821031082c0e440f641d01c09080350744509110380040c160300095042549000e035002c080c0716000f00c40201d2030b40c1d503039441440b85c2e0b1300e41020310319201041b045000d01c3c01d4004141d000d40b07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220444991 1250 220443741 220443763
    0x10e090d0522090917030411010f050d0c180f2603160f0b070306080307060e121204050f0703051e160b0a080106080903071401020909010803030a050f070e0f130e 71
    0x6841c5c00174800d140b415404903842160700200300e007d01c00c041c1d40150b036007009814014040003000e11036146c50300507511134210031313a9040d140c2c2074a040720002ca6080c84110b940142d100d00401c0201000148444102405450700b0580c1070b10404402c1c400f82451030181441d41c02607e200d2174180c41c140600f4040c68590700e070003000e07072025070340e00c03500309906882c010b02c039103861a44100402400700b8403135800b8001d860044015205880c03491354503000b00390000c0c2801c0300070311a1001808100101080040b46544541c8040d00955155445841e00c030007011018a501600341138440c450428148105c20710500d11a00c0c1d0140d49441e0700c41000560400b91010700421000e030004120700d80215011803040c54004010752510403241d8038541d50100e61801d05a05640030312100c41c245e0303104c5400764060701400c0001d40c0c691030880c11080a440c0040e14a445612100c0d081c001020360080c1d42020890055503481e00b11100030000c98000031040101c800140d241001010300d009001c60056102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220446241 1250 220444991 220445003
    0x3010e0f010e040f15020c0102090f0f0f0910050312072003030f07080f031609060f08060d030215040305030603010b0303160641010e090d05220909 65
    0x140c0d80c0a0688001840038065032010010030800980010401d102100c54a4840c448a400780d106991201c4282d802001c0307074032001e07500030030050303017a04210301c090144071022030720010031150301b0300030800404034052014058400341c030010341c640701d2011094004044c0a0203c0e6000043e0f88092a429008160119825105807000d11600030701200c000000c0f1130000c0185240c03c40400360f42426904c201c408940e4024140014500d807520b10014612640881c1d4040704c43c01c1d10f5071801455115560800814807503003e4150040c0d0740c2c480701c6154005000d9680c040c402c80e00c2d0400f41c0c039001c4078009800c051101102040205a8014051401070b0000d500034445103c01004254503801540d82442945803210883c10100301507822418402001194101c2d0f0f82c0449158507555203c40c03014003942161002c54030071081c0606030200d00400c00950b0a00c03440c00d00c1861315444410150250082000104103409203c0308800c0201c071007802c40303e01c108529660608030001c2c10700008141c40d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220447491 1250 220446241 220446269
    0xb010c0503030103032303060a0501030b0109080f10060b0406052b050a0b03060c0903030304060b04110a080106091403151504090b060f01050703020604061107080d1505010201180305070f02150301 86
    0x34006c031001350380c0180c10080c168a48681400d0044000b0b1a4100c841030410085540c0010020001d101d040740c0c1821a6019104500003100f0000544089910122101004010030814a03900030260340e070b0b841c001c1c1e85510000c40d45140d00e00c03804000c0740380310682c6880d2405010001c08035522403103844000ba010b03505560350348100010140600070700e603905600101f00240000324540d11000c003404009000203009004160b511066400c11940384011800703d10041c010780750418004001821080d007204014190100403d445031040c0c4211146600e0400215081e03040003030004004841c040c00410074204641400c218101060390240d0042c05400e5050b0310551040e0101c074011a09500280302646441e69114001c01c426000824426000d1181c04009044070005004d11101c4580108048004204403000304229038007c0e415a8909090300d0b0076034880700103e2030b070f054050500700e45a014a041100402c411190700940c003082104400d120001c050b401b0b0b506030f800b2000c1d075005c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220448741 1250 220447491 220447547
    0x21021614011106011508041a0108160e010f0312091502100501050406060519120f02091c0309270903020601030c0911040b092106150108010e0601030b010c050303010303 74
    0x6103e100a0144c80b01c4202a601480f040b03a015900242d0071620420701403407942039400d070303001d0700c0442a0410b140b1500050007100070001c46403044405407082c044120340a52400320340810140b400c1c030000304410140c5014a8000340108854002094844480c00c03801c407410307038004c6d103522030710342d0054803949008000705050030184503000c02c0c1c41080e00ca081c60520144c04081c0040e941008000811481010790a2814418002c09c0c1c040168098090380b0f61007894204032034040c100d541640350050341c80200c40880d900003940f10813a14042000c1201d0141c40300a0301100c21001d801c16496810082000201a40041c003d41240d009040001d00380d03480300404000e4a401c000c2e61940100c0c1803200b0b004800c2d102c801001590401400000684580c0c103620405641c10320104029070009010000202a405c3d070913100010700f40b800045960410346d0480d031510015203a58101607071204007504070307409a003640b00c6443d0030400f120b842e5a0740303250041998854800341c1d4000c0c450414204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220449991 1250 220448741 220448743
    0x90c03020306090705070f080f03040c140306180a021203070b090a0c0608060402161b0515030412020c060301090b150703020a200415030506060d210216140111 70
    0x900a800c0180a60f5080d215100111000d8100490075540f002c014408800003440040080042c00c41d81051542c0b04d141600b44581d10348026404074070481420055400b19507008a4800c0e40880ca458003078000c194a0388210f4640303942e2500003504074014075960964100004081c0680510a5040720401e0342c2b0181000d480d1500c0c002c0040000480000c14401c9600a009035584804050401401c003001c0302c2100342135556003030041d5a45107100f68490742000c0c11180c100050007041d204858035425110420425101c000c00140101c04403d001c24070703882c401e101c1c541c04200000e203e00c2d160b50311813020000600e800400c00388a02c0702502c2580000d80c403002601da40b00d130541c010f4180302445846112030059100141c0007034072403240d00c01d83d00d07982c2c92007810701e10007046c0d84d031000c2d840c03c61514600c0c010700030345001d1160f81c00500301e00020341000c036001c062a541100704101c52050b03000a03480c0c84400760010824100807a0041907000040300c200c080070b1003d0703031035401403042c91000c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220451241 1250 220449991 220449997
    0xb0a1128020f0d0828090213020405060904021303050a030f0314010f1401031d030a080c0c070b07060b030102040e04050d0f081308040b0c160e0c1b101401090c0302 72
    0x92416001846403850090090740d01035030041098191080c0c0e0f09501c000f4001468100c0c85e0000c2240d5101d03d000190308004404000c00d842100085242074107142c0040c0d10703400b039401c0e0940f0903500050352060301c6001006001c0119400401c8401c084c4451402400103649100844002454640d100009800b1000228104c0703041801c0b5030320050401a900d0341070120800c640741415150101c05404080d0b00c1e0b0484d008401c0d02020b15211400c1280003400c1d40405410110a40014050ba122034000402c82800303e07814901c1c8070f0f64230915840c000001d031052008041d40f55101203000607401c41ca05e000c040c03140d40f16405840d0045a40c0c2d805803819000ca03442d6000113042d0b6000140c1e001c0c02c0c3c032080118940109078141c140780e500c0c0e07244042e0764000440c030100e607080003022000300302610310200b029080e000340c80001031401c0041c0d07485074050000d01c51800000d0400d071516141e0140103440441c0f101c0f2409029204100500640c007036020b204148202d890681078408a92184c400c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220452491 1250 220451241 220451263
    0x9010501050f010f030b18010f084b01050117010207030903030f090803180301050603030c0d080c0d090c03150c091415030a0e0111070503070b0a112802 67
    0x32030944404081c01103646115103060301c4e05050392201562660780c1c4080c030601c582d1000c498241003940c100726046189204580c004052548061030244404414400da08091440d0641c0820754030024651880310810900c03030011101070300d8a581042031019040107050310102d402131140800c0103581b003400c0b441500170240000b180f9150070300c0000c1c03003000740e048090740e2407511400c3c40b911103000754195482440c60000030406554501101e05003030258560001044016509204c040e00c5115120192020ba0408003d00306000400b1080c0394015a114494165800c10042580c1d00e4004405426804280c52203411a0000007900c05c003406140500c0c7e44d150783d10591280f900084000c0d40403164082079015030345c0201200042007a90103144a81c00389400400c091180b81d00150849020201c100c00d4854104114004502c0000803070b20059802202c07a00c2d0348e036070b03060401d0003083c1400c0b00b00c11614001419041007031080b80d9070a48841d0341e14901500c0c420340c250030390750b40d919144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220453741 1250 220452491 220452499
    0x1e06050403030e040c0e040e2d06150105040f0803070c0f0b0711040e01051018140106120f06060306050103050c0415110a020d0b01061707020606100509100806090901050105 76
    0x2180f0b600340d00f4150400310545149080c481031300e01c0c0e09000502501d482c065080c009034011040651000b0921110340c0000d2100c22081d0b1240b9182e07a5519107484000300194000c151101401c00305902c1101103c005100808282400944480e0380c55201d40c0840d80a40300007203110404260301851145407400c0340d2810141d5881d103071050391040769001841e408540e10507500e482d240b280f46001c2c040c031845409248407a5005608003d55020340c40800c6040b0300b00980f030041004864200007500c181520140c0c1080c21349540210642c001819102190903c1c9a00b0148005201d80d010781214058401c02d032400c1c0b01683d101c0c8a08000740c0507600c51307018100c4100c03000040d502d006141185483c01d415050300c0912410f80c010500452480303100711802700c1c2c2034004001590303101341030041c020103001c80104c01d0f00b0006402940d40d45c01030b03da2403103828400100c102460095040342d401d4080a0a2400110425a00034200b4a42220f00b14003130030b111400200e02001c1880780c41e0507110024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220454991 1250 220453741 220453757
    0x31209120a09030308061f14040e090703030f0201090201020c0405091c0908010605010507020a03020d02012304051f0206010e0601020703050609011d030309030409090206120414010b010f0203030a050705040506041e0605040303 99
    0x80c87c02c40d41c81c0e0500d0382d0030884440030840400d40940b11082c444c0b191030418002c2c440240740d460000c0c10f42d4004440c4c4402c5901d001c02c1c03080180e82c080355103d00e05030111404105516404680c0c1c0c100200701788000a81824801c400d0718040d000785608040300c0480c1c008119842e030b5040152500d11400e80000d52149d95400300b40700621307120003104440e6006250004502445100a40158500c0d2011301104d01002c203003040689015007480d030440a1486060710401d00c8240003968a00701801078840d952280740005070503910800c1013030000e64001c811503d041c00e00d8500030340201035007888505080c254540c10703180c4241c0042102d008640d800d004501c0c003032a0400c0900285094001260302410030044841001201440f180c084e5010300040700c0c40c07240700111942110141c000050600c0002803450b40490f4020090700e86c004252007000c110341d625410211901c0c4103a0f0415a0722140100d030114000082090fa448892050800018000e803206e00070303110fa004610006000034410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220456241 1250 220454991 220455049
    0x180506101b06020c160303050c070902181002013909080d120f020a02060f060406142209080304050d080f040206070201090513091a09031209120a0903030806 69
    0x65401000d005400c1030a440610420f011035162408040c0d00641c0088d2021807490420241030101c80e0007807407034540c1140782204513690010520304680007144210043d24031541818000c0d04512901900d1142c000c010480c1c070201e0301034020003001400046041240d0200109000340550300c20780d00000001e001c6100c0d1007808940f1007a901c1c256400241d200c14114125000c203001504408140b40c001e0300080c608181550060540100a18403403400e1050801c502c003005140c20342001e4060340c0d001240101c914440b0b00740c0c1500450309031001d00d400001e00521020724007035030050344980700740c6800d0000250704541d01c150640c1c41015051141c00403d00500e0310200400d07a80344107040101b541a5070314001038040e203480070368051298076044540c08018101050501210b59400141011b0801615990341c1340a00d030460500d9541c03210100d421440100700240032030b50b107441141c0d500c07200759400501c04441c44c070085021414280100700c1d2403034152400c030100030020741075400d20300c84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220457491 1250 220456241 220456253
    0x90b010e04050f0109030f11010606050307030f0b12060106082a0c0a060e01060602070503060c070609050f0a03020a0c090516030515121b0303041a03060406180506101b 74
    0x4040c01c00c0302d540c40b503502e51041006013801075000460007a264807403058506e10001d001240030b1070681e14a80d24041041c05081e8014081e2508036074a4580090101e850401000040850001283c1d100c070380b512140c0d004200000718503040c1c03249691120300350b40741d03040c07940071a59003540c0e800c03590b082c0700d0300e40c80101e0804009071100e0030b8480c08450021032030b80c50304070450340d20520700803559444600070300641d030b0100f003101d000f0f28044d0001c01640c03030141100446400740c15401001143c80340c614000b0300004002d210840c01c1c02d901580c0c80510070340341c065500d0181104c2217448090000e800200380501e4821140b05801001c4096802c450280049008200003455541d8200c00803032412081e03100c4420800112100000a0840d1151074049440c481d0304030408610030b41c0300b00400c0c070280303002c6041887c4040184210b03d44a498036800a0098a82904020380c00084400b0354008050150095401854203a5030b041008443c0e160850300d0341502483c0c2d5903c4110010710300000750b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220458741 1250 220457491 220457519
    0xe010311040b0d05010506010933140d06051903120f110a0b040501051612020705010209060a18080102090d03200d05030f1501270504060f0612090b01 66
    0x240100002603041c6842c0010301c04074001c00c01510180e542d1020000b40b560840038000141088080b00d01020444a02d08101c801c0400c1001001038060003194065a02075440542d4003480201807580750b10840709014000c1020303100c3c1511404004040990340860b140352601502d4000f203035140c482c50013081c140d80007000321603840200b040e07240941400800600040d819544940015038060134541026800c4d00e40107080c0082d0804001964407d441d00184c060500300c15050700503032a2049030401500902514580642001c0d0010741d03205a00e03400442d42610018000c1c40030039080c0c9030007080c0c3c01c0340100c000481c0c004001110b500301090041102111207140480f004404402a002503400d0015040c1c040002c12004001d00243c5841d1200306075000780e1001c110903d51080400092400812810709803040744058420400c024902ea0702e0340c05000090014081299241207070440d81c0d0b601e1046c580040d881440440d411102801064a025000402d0b003200c1d9003841000c521803c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220459991 1250 220458741 220458773
    0x30d050106140a051305060a0e0411160210051c061d0c0d1104050406241b0201081503160815010b0409020a0207030614010501090e0708010918060e21040e0103 70
    0x3000c00c85c07001945070703500b40c01001c1800045c0d03a40d1809854074014001130780c41040c040a9844028402c2444809030f040c150860680c0403218900f010200103030694813840303040c0c007000d025603041c5a03030580f004180c0c005c0c0c0c0480c4e100220b00ea203080140110030703860039007e03100b84203c54003c1000300d005589035041005915489410a40b07410f43e1100080c0c1140c0140d48040051403000303175544c00018601e031a5694100032400e010282000e011420103140c4014038009050101540115802e5103102400405010780075041741c0030030300c200111001c1907100780f08400140c4600c9131214010240407550070b04a6030b80d496514201800d26191001a4000c02016800c500c900f18000010071128042da51269071031500303010071541000001442005160004010081c17081c0500201c81d5002c402141101d4441000140c440441d01500f10380401c040030240c07109082c030782002118140891014014090303480f00780d203032018030011080c0074080c520603241e2030140e40d0010008901400424007a0ba = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 220461241 1250 220459991 220460017
    0x304030927020304050705010e220513050f070305120a0c0204090812040c0510050307050304020d11030f0313050406031e0204060902030f04030f080c073002030d050106140a05 77
    0x110080c240820481c0c2081340c0c2510113521204042059523041000d5600c00032041d160110054601045100a12940b00480241d60380c1d4000281080036204284003450740e010060700c1050144514090355815140000c1ea0580203170802c000000340e1602c1120383c000101d0b1505500c0c000307190204402816600b0081d1803c0030100000d00c8070060640c10640701d0f82c41915082581400c01d418444040015940c241c2841410418048240c0d00482039a81c495412120440380340303824a031030249000007052003a0140b203820395030703000c2c900088040c01c4403101c0c800401e9401a5200104070541d40103100207010a000111540144581c0b4a0805883c2d4006400820030642d074203003c6040340d01c00c94480c0420440c02042c4010503503c00340c01c5400c5600d914021659040c106145911480351240080243c18a0340400c2c2680c04060b030304000c0250081200d201c0c1c1c66450902a41703a038803102200340b616240a0000c80c85900a144822810444014060400900c0d4009807000d41c4010045049 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 220462491 1250 220461241 220461299
    0x1e0304030b0f0103050c0d0f06230a09051b0d1203020c0313050f0d0c0909060e030310030c06090b03180a0c080102040504062301200105010602010903110303040309 72
    0x3152416420502520b030401d07280800d907255007025030600a004d80103500c0344040d491490040f414a80300b0f07541c4213030803410015440112060705846031054642c022010b820b110100300405090b5808120b4141c02031050b03801e22002e00c012281000d0a0006059006103c00f6900010508480784c40c0501041c9040041c0b40c09a044191841e50300080840d12944c0c54081083c4050b003400441005008015210f010120203150f807030304a400e00034000c03040002d07550000e40d41408825001b1040d0601180c0550f40c0d00d08000c01c05513154003403400143d0702092000d0000988070303c43d00d010021581942c00f142d04648910a40c0003100b440007484801510801c070300c420100f04200d005c0070051030200001070b5035615140500003503501d140d202e03c050440080c2c51900d035081032110004038142c01d10b0141c447c115a00440140a90425040c10042d03203804000300d911601588002403035070003600d0301c1d000505804802583c1c0d1200302c070002d002031801c0404014030310042007c01044807841d030140031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 220463741 1250 220462491 220462493
    0x30304030b250509010c081e071b1d0402010f0e0603070807020c0a080c0904020a170f0c220b120a05150c040501053114040506030706021e030403 64
    0x48108000c0ea00c6503440100c440d00101c000c0c0c0a00400c00100d1081c0c10f02504001c0c00800181c03c404e054070000d003080d000020840c102180040901c404500c0d1071a40740d0702c460240c103001ca0507020200011540303041d410b2001c242c5c0a07134101131820014180e042d413841c0d60396030b6004581740300c0783c1c8115500388207030303034861302d030643c2d83e08026600c80c221a03503541c3c0d5240703442c1d400240340511410185004000d10507007031100c00004609017100000a0b40d041c41d254840d071010030000f22255202e0555188201c02004100700d0124000c41d11900d68401c4456244501c030820076105a10085003201240030001d191b41a0340d103401c107401c2c5a0004004e030181c820102c10203820102a40b600310760540098101411702c1e400020030b150010712a1421500b4030382031400181003441282e18001922400e1500782c3d01c101080044d840703d00c060b645a410700241c0d54060280000c100340d841501c118140000124103041c00640d02080794160f900521076050361150340351800925021550f0103000400002c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 220464991 1250 220463741 220463753
    0x60118140901020705071a0702091e0108100c032c0a1205040e0c0f0a050c1f06060e01080c16030c1202060f010801060b03241002030d18020a03060b03030403 69
    0x90301c5036200d01c00141c0e40311800d241103424159160403080300015100070720b9203441c00072001d85001c980d040e640350700301e61074403d221948016152030784078100500000106042c003000c180b20420480e00c0c4c509001030700c1c6418003503003515000c0300011124441f61440951400320b458200e2031929500c420f0b580120301684501580c0303940002c00c6030100d48005000c10030554800d04d026444846404468100042407620810510414048008022021079004080b61003482929011051980303e500e014154010b410081c04c7d061041d4008910004449481940146030961051029200080c6020300c29a070301105000b0410054040210408000001407200c510b800c2406109030020a04e900d03061081105810058010618a034100001040140396050589410900100c0c0941500082c921156150603072940125880114000f1060049801100a000c00707c0a0342080c4040290b07c188a5045082a007000f07401107103d06080002ca411036020240d0102c0c02401d90785415502d4843d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 220466241 1250 220464991 220465031
    0xa020906090312031009090b04060c09150306140301020309070504050c1c0f0c050f040303030b06070515010e070e010806040c0306170c0f040c0804120203040f0b040f090b03060118 79
    0x1242d00b02900009000280305d00e03604010003010742c001c0c00e1190503425031b0f413040c0c03602000d400100030035190030120318050301070700848000d09011403001c0405403803150000c01030b20b00b520811151001d813101c0d1212909040c0206c1c1d114003038000080451616200900c001010000c1c40c09603624014014400c1e2000c19020451000c0620280404c0340e1003000246001ca034480a01d5000380071040080c40c0100d43c04000780c40c1240d0701030500160061109002c58414410610018001d001d00040761012081044982d8140c480c6500b22034403540d60748400342c1e0b055925001280c00314854034002000d5242c80d42000c0c001107421b2034017181c400d03541ea5034071000103465282d02a9a4009021024080c2041040240311050403101401f001010f040c000d020001302500141000000502545050703000300110f80003800328070401e28000307036903400c54020744d00640151210b0902402c0001a0010f0500803024000402805060340385d1a080035681c1071400d0b4041c1c19001038076265401c2c0c02000f44824 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 220467491 1250 220466241 220466263
    0x4090804030605070801030b0a0509120a1814010909020d0605120f061f060c020301150f08060115140d0f0207080301050906030718240f0302090c120a0209060903 71
    0xa020349450540c50305100340c2c2d00041600c020070500a00410204201c110100d4100e48501800249a16074201c20b6040c89043c5c0b01810500000054900002c0e0348030125405c95601d01c3d0f18543c4040e00c2d00304958a5a585042041c001859288213000d260400c0d801000010380702c0000190150341c41d00030031420080021500201c0e00941403081d051582804880e501800b9861140c5030900b4111209040c0c8801d4000c510801c0101c582201c21918250302402a501000c680700c0c2c01da581e030b00440c040340c1005001b1104580548000040d42c04000d402e284d150320019202e4065428141020384155006140400501c075140e029100038100c81c0d20041c1510382c060440142d40358144001d00c0010000600954000e6104480410100300700c08020603455a03888004107410410f0fa05034010441000b5600440b070040c0040025a4950702420000312803094460a9507560388880c01c82c440c0c011810608281080040090761041c0507500a1880104c010501407c0c1440030b40403901e84032010031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 220468741 1250 220467491 220467503
    0x90f0c030b0a060b0a1101240f08010b0a0605070f0f0510110f161505070201050a0605030d0807260115020d0503090a0305090406181d0a111e060c1b0405042f0409 71
    0x740a0241d0310455043c130f004ac01042d0001c0c0010b0180c1404a85210018441c101c2007020105030301d410400021900352103150840640c40c079411090409a890300b07131204034071400d240b40002c03030b640c81d4211100f40e43d000352900200071700f440341e42d002c080c080d5100c20904440c51481e07812201e07103500b2184912130007800d03180e000080c58a00342451104441d03090304024400d030f1051000301400780d03102c8402980300810780307400d41e400c0c0305170413032400920b107020f4003d040182c805002007003072200c580c80c02038401525407c613116280303d2507080d40c40384801d89404070103800c0203840700d000c00d0003000203201c01c540240001444650310b400b000d400c104040c004621190b01c603200c15107503d03450030003452003128a1002c1d20846000f65100d0891501140c2c1035400751a2207688005002d48003c1f180b060b0600140010760384815a40805407a20030080d0801d001d540450002c0070341e030400d88145846503902c80311103100c2c0b1100039100241c7d001d02d000d0345516075228080c00c0d82551158014846003600c140c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 220469991 1250 220468741 220468811
    0x207080f030a29060a0e01140703050c07120c2d0305011b0207080c0108090c04050702030703110304150e0a081207051b09061201090f0c030b0a060b0a1101 68
    0xa0036103c0504442144400300c0b258001c02e0074440c1c0d80c00b0b04a4403d54403905011045c240e4440050780c15401108004501d8580840d01c1360905070060007c1c805199120f06846031180c0742da484003c292503612001d480d01c909400140704d902420141c0041401140342c080148030810400c1c0da2410103ea0411280c907512484e202803640800f0107040400340990020300401401c1400d80386e038031090711800c1b031704020090000c900070000501001042140180c810b100030300d0b0540340a035584c0e0029074204d00180042034150b00c17001c03000c420f0340c0983e210941982090864400c045403101c0f41140f00a038009034061001450705406c00110810400701400d0b42c1e251b1f805c46c10082c0c1428441d20f5501040740c0d281c501c95004da03a0b200203450b4030040446007180341039001c11202e0f00619038060020070508d010b007443c2c1c040c040b48102c0c980450384607182441d0255213501c00c42058030b00701d110b43c4042030320601041103040c1c01090090304203da0400002100840740b036900b502c0a1505054500c256110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 220471241 1250 220469991 220470011
    0x140115020d030b010e1c051002031b04030c060807050c060411041d1908071406100602010b030705041a0301050103140c09010303020304030305211905060a03030804060207080f030a 79
    0x40c85411041c0e45241000c001071000d200000c1e12042d880e903c61441b59800c40c1c100611030f44041c140d00c00c0142c00608507050060840c076004029403054958034030203800300a2105c00310500303108441c2034076031010fa00c1c400c891a000c0156202c610141081c8144081400400302d01c030400c000c021322035805100318840005605050004507a4001d80040b405206100602018000002d01d20142c20046400254000040c20880c0701c601807900c009007016132105001d034070303100b00103502406003010450fa40c031101c2d80e8400c107900329207080c109a605904015402c201790f14245c0e100d51301651504a140c0c004070041c0340002d0840300242c004844c00382e40010000362540040002d21816042903903000d48030750542e10080c0d524002e62000404104e00040c1100c4010424009010041d0403210102501e042011100a045041a0b0b0150001d4075140004800749401106038084030b07016180c10074103449589410020350710080094410500070040e540007424130030021881135020900c005000698 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 220472491 1250 220471241 220471243
    0x51605040b0a03020303040b03040201020313061e030504031b38010806010305150a0b09010305100c020616051305030d11060a1b030b01110708070303030b0a08031b0114011502 77
    0x1901c0701c65019845112003440161000000c40301528040c011540d06c0750340340c1c40100c1c40c510422941c20000c2c0e401940000301030342c20038002400700104e9800000c8a01c490300d4220111901100d0160004442c6001c003205a900d107060000424003a0201100c0305090407259080f0f00a130b01ca01c003c9480c025198407000b0440408aa400b4000182c042c100551464490690341c441e1003100c3ca484c04140c1e404034044015660128100d64405032510340f80350f0796410b01c1a11524071819210002d41000000706100d8030100f1144d100381f604d800c001d003416031100d0084030070b03420440e41041c0560280c0008202540c04000c0000083c1d880d689603102d18182c864403d090480240204a60303505103000305e0002d1101310100041d0742441e180004d4540c000d100102c0e04880c02e4248142d041c040c00c0d0f800301d40b506000c00c010040d0fa000362814003c4800314030034492184070034450148160030038072048800680545c500c0401c03803400720011603010030030700010a00510030f903c2441e01c00304c0b003030510a1844d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 220473741 1250 220472491 220472501
    0x907090e030a0c02011b06110307030b0d020a06110a0510020a09060816080919082a06040204020f0f04060903020a060c0f32030307080115090e100305160504 69
    0x2054000c1e5007010300d10075000d0800880050300a0601548810b0951190340c1d1182c3d5125080e0400300030710003c42003004880d11580f054401900003400c1c001040500d00300600c101c0d01555001c0c0100c082c882c5824000c541c50840c0d55403081d054007801940e803003c940d00b08090003803500580e40040c0c0d225000c400152010b1115030282052200d01310070054050402c503c40045403c0900300903031566118007909090440800c0c00c02d5985c41ca070036500b414040340c0e0001d002c48003c80001c000031034001140c1d20400c9801e04030894035550065001400504268010300b5080e0071070400c25003001021700404105805c142c00400000c0c1c0072000030015450080b0000c0018501030802c1c0d10f81800584488000802806010342280c0150150314803401101c0140c0e000d0107407602c100e14501600c240242d899500030b03180307030001482d8003001040c40c1129099141401c0d1071619442a40ca06d40500480040e10062003140c56414290000002c520b0500c0480f290112420302d01c91501c0c180400c11080350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 220474991 1250 220473741 220473761
    0x8250e061305010f080415020702180702060a0b0301060b0d0f0b03151e1302010c05070b040b0717030601120506010c12110709020c0a0f051002070c090f050c0406180806090709 77
    0xd18050001145c1015000090707e0312130840540e9905060011075891000407800b11359a43d403a803300a0034076400b08407940910b82c003001c2801410303200b0007014240c407494054440504010444856145000d500c1034030120100c807008100400c00100090800700f100300200c4001c40c00d4810030910481034520510300700c544402d089543d09100c050198025001500281840525820700040c08400c1082c1001859030300700b41562242c8a944682c19500103d02c2160741c2020703041d002c041151104150303442110180e40380ea000701400310007000600000b174070050600800101013400308200000c0c4030381d6140c1ea900d40703201c0d071013858258502d05196507100710406407060080d80c3d09c2000205a11503841e401c02c02d0004a0382c5c6a061503030500f4248031004416600c000f41c08400c208032405031904588079004104460003000c20103505079803044801001080c3c00700006c0c03260303a0042c58944045102d0100038942039480d4400185425026207013100c096200d044100540030860141d21422 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 220476241 1250 220474991 220474997
    0x10803030702102007030917071a070b061513030809090a0b06091314070e091b09040f0207020411180303040305280c030c03020a0608250e061305010f 66
    0x2185411060003200c076030244c541544c4030005021083c9803080c85200c0280030313901e0621282c0d603e40380d8810781c0c1f00c84902c86d40554440c0043c200480d564a40140e840316034005111103500c0e907880042040300716004203244204281400034a007a8189002c140000d9840f80301443d40d034850101c200000e10000403d40d504490510180100f240c682e08140d403003842d8140c413480c44a820154185000e0440c0d010201ba45e1420641080303200c903801031010030310780b505442c1000c441c0c844400307030358101c05100002d000d499030820191001d403c00783c1c0207500071018000014180500344d4006800d6501c2000218003010300441c10744221000382110140307045048000b03500c0c251866480310746a0a21010780e01074403080c6203c071540001903035a10304025034028071030a08c5a449191110f24002c0c9808280c1c01024090000301d0198003d52025000700d40c4003c18540070051654510001803040c0202c804118090007224495158040585580c40c401c51040110a080000052420700140308807410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 220477491 1250 220476241 220476251
    0x301120c14100807030e01110d051014010e0d02030607030b030715140705010603121706040606051b03130801060302090c07020a03060e15010308090102060702160504150e01080303070210 82
    0x101da69841581504075210f00380102c055560b02c006500410280840300915402c2c1000031a0405c0b0000c01015059001c030030401a5480f401840f81c0451198058803148440b48482d40309158084c2a0b0f0b00c0040900406100305c618150740403d0a0103c280c41100209881c1c4400c1c80280c0f40c14840e800181149070303250383c88100400750090a03041c40c4641d500200c3d500090303c1c82800320a400460266804c46d0364245d0356030700c44400500c00880111480000f00d4103c01003640b0b440c00d030003408112401a921203040040072000d6101c4562200750010380e500c030801200c0003400b6800340005c0180340740d00002951525600510555001c01015252030301810846200140d03500c071201c6040d1394000000040342d0030085c004518000d5070b0846c0c2400616000000010080454003c0010a5081c0d090790304941302c5120507a81c45051990700c025210381b01d0b00a1041e410142e100d01e0f420032078a92810192a80c54003421816402a045011250030000030005110340410411000e20400042001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 220478741 1250 220477491 220477529
    0x415030b01050a0c021207031410060609060e0112061e030524010e101d0103060e1c051c1b0906050c060112060207151d030309030906030402150301120c 67
    0x7103190100d500086c4101e402480e07021031901c00700318420165a11008202141c0309002c09540d0742c1c0300d010801450b150400c00081100c6110f101d0a200720784079602c840c801c3c148102c0041d03d60301c180f2641401c0d811740d680e60010780455080504c0c412080081c104444103410742c01d140f410a00c0e44a4098105903904000881c403461078124a411600164400344560301c2c1c0f1694002101c456900601e410b0441241f00a41c1518481e0118103d0348a08800c00160105025080d100c0c0215040394103011602c110f50910180a50002c0c07007081050207660b101d010460041d58200c038049d2040941400000040060aa030001d40c101d024066038104141003408012009940d000140214849d805111400c2400c008060301541c010030760058856902002c903c1e540402480c030398541d078000b903840303841880c072200001c02124022a9054065440e00b4583c0d01440070a9202910407600312960352510f004403103190010314040c241d501904144048107041480d0208041d40020600f025246011a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 220479991 1250 220478741 220478747
    0xb07080106030c020115050114160308150102010515010807020118060e120f07030311070b0406050f13030914030703140303060112020c1507030b03031308011508060112060906020415030b01050a 85
    0x101120070034a01048031140c00b002708507090046244074102c107034406904404054000c0b200c1d80c4100d411078502070300d51038440012800c0e25030a4034810801c941034454080e00f0f5204902041d804511800040f506518a00600b00c02c181091410355a0b2550f81c1d82d103880206e07051106c0700e045260180f0355410581691300f103000c244180c203401400c0c1aa40d0781d925102021040c00e0711031250b081644102c0515050408401800c4200d58450b180c1c50305900040150520006010801d038055030b450140b07a040010341882e4010a5601513814810103800100040a02003060340e0151000c2c0916141e041c14800900312107102c042c2c0310700b154018003601031500c400040f8400d641c111310503501100e41700d1600a60050921004081d018040000c001085c40080d0500300100e50448000304070b01005414440d42100842c000d032403041d007000c0010050324031180035440070540221400603a40780701c2e9544104907441035100116124014500246154241c803c1459580c0d00b03007401440e00ca40e0850003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 220481241 1250 220479991 220480031
    0x102120318070f120b10120209040c05040903020706090b030105090a0b1201020a211814010e07151b05070b0f04030c0803090910080a0215070b07080106030c0201 71
    0xc0c040c54100c0c00d4540d210100100442c000078040d50f04004071040c0c0360783c1400e5030488030a40c291084007035003002c21281a00e4040070011100c14107640d200b045940d80c20005000400b03401640c1c0c3c0301c400600821103607035174800d4051240c4a60020a100c030328000d40900b45042683c0040c40009003440108455200c00c8450b80c0c0c0000500000141c0301002c1000903850007d0884450070342d840031039020081303504000803101065007900070104072280e28070f0360b009642c603044900340c14010015207000058210055103680d441500008509840440040c070f10341180c40e031242191146104020f0a240d0b00902d0789a42c412201044030580740321a102d543d40c509051003400402c1900081c0d01100311520310035a8007640c0e00848628500e81d03a24400356603900f11600041c4105c0914000c00c0c41d200b101c5080d0b00840e1070220103429005007035001c00c1003400240080c0c085c60b44080205100296807200610311515403038481803000e5040120041c110390350880e6034400d582c54003a0041081644d1480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 220482491 1250 220481241 220481251
    0x1a04030210080916030b090705030106083315131812050d1103071e080a0906060306090c08010e1506060f0f0315031b060a2a03030e010b01021203 64
    0xb0100c40d00da450710145002903103d14072842407114180802040304040c50280034114590445d00caa948030402c2500300c50043c031407005c00342d00031082c00c080c21501102220451410b4600c0406200c0090342c01592490201d07010b40c0c40240101281c040e0b0700c0e10301116a10161440c030200480c0c40101e5000300b24846024000d07010010020007806228443d20480e2130b0b20003032010a101c44540328070340c0303001d0b0b40055030203401140d520001c604054035100031040d0880c800c0e503100d080503260312034880d0041501042c182c8107c3e88440021000c40c42c40e01419540758442c080e208000c500c2d1103050b07800c43d8042c03283d0a003240c0162000840781d40c4c2c06007001ea00a041200c05d00d035103551888000c145445003003880250b140c004002c0041d12640300c84400a66103098007618074040c0c1240c00c0c0c003400004c0055a40e40b00700281708504580d441228801082048180c559510701c0702a0049034004050b02e008500080e100c0e158100325032801c3c010030900c003000b030000b0031102d550808108064040205 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 220483741 1250 220482491 220482497
    0xe03040302121c090503060c091e06090d0b06030105090a0503030a150b0406111b060703211514041e0e0705040f061a090a030803040c090501030305030610020f0c0d030309060c091a04030210 83
    0x2100205d24be0ba03d07411220740040c0100b80000e040410f24111220a804858a5102e54600346c0024402d240100d505002c1e29400000740d4650f640e1031841c40000c06040400421a400b94503000c80d200075030100520181c841515091034110300c0780080c1d403821243c11281e81c000c400010840c030464030703050240d50059038075017082c00c07c017a4015520003035034076005182540d2034285090303040c1410704091880182e0f0500c0c1c4004006030119018401928402c032102045400c61411194165035280d1010111190740d00c00d44048682e034000240c103603200701e40c0c1d500300300399241020820b6100c45943e00c1240385003812200d00700400d450000707240f00b00500c000303403001400000280c1008403401c02200503068414080015503140c0c00c0052058000b141c4c26800b45080ca54a200c0081c0001090b0704c0c200c0742e21008014140c90081448214203421030200c080c9501c1e03910050000d5040d0061211031104c1ea07450405144c5420401d02100c011403814544d008030800007440940c03150160400ba41046007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 220484991 1250 220483741 220483789
    0x106180e01090c12030801120309060305070c05070b09041503021005130b040306050411010c05120c012003060103061514031302060c0f0d030e03040302121c090503060c09 75
    0x1034591805402964002800380c0f404900101d256544200a0881603009580c4c01c0b03096a2142044104061230f602c007d40403450700601042001d201c0d03004140e02564529161902e00940d682d07003850720380942c0001d6644180403078440100d0800d03124443c3e06402003036044055034610b40200d110550488801410440005104e80700340d03481c2d80072540181000c0d10002d5807983e403401e081004020903030b800c954054200d50b4407909507106261255005030060017812018490341844801903000f441d115407155210341c1d010800108440c1148116020f1158043d50b03890404001000c070348640e0040800e828519001c0c4002684c4640175414580520460540e29210714900f0301840c0c810b018000d601c8000081ca482080d400480d03a0700d81461008211044000031318000e07419503000d40c1c2491141e038010b100c10000361801c440e040d01c1044540c0103070303a099240300c5e16107540e002d004e8000501040c021601013106080400c0700d15400780e48604078034140095440022044d146c40c40d42d02030f220050b1303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 220486241 1250 220484991 220485011
    0x308030c070f12090506090303030711010e15010515030c160201120e030909090601080c0126010e040b07021501060f02010b040f0e120301050913051213080d02010618 73
    0x10048030480742d0010700c1c1c440c4020359850140f00d4900252030103400520380840c0003610341425425101d000c00010059801c6944501c0201c0e000c4040c411081c840c0d40d215194009081c90a02c56281481e45c0c58003110031640c100300502000c0743d8500341c9450b03440380030402c02040305007550030b9901038201503000c181d0340d0140340012911050303c00600c01109180c11f03500010181f00000406440e407054408404c60b40c1c0702c0364841e031505024403806809401a0461803203130f611075240006a980002c5448102951030103055600e41e03000d800c54a06912410b003840180151142d0303855020350b8510040084842542481c0b00d0200c041c4074400038841501840d5020318000c3d0001000141c000d00f08100101e07100c540c200207000c0c1c0c800c8504003400340d1a03807030030018842003c0300d059550250048000c1d40b52501e114800f601501c105480038020742581c0420ba80d42000248184104d0b440300740d80c02400c103c01075007010140022071056a1402030104118404900d02c0340031410782c1e84001482d2581 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 220487491 1250 220486241 220486261
    0xc09040c0635010602190302030406032004030302010209011409010905011b0b07021c03050108060106050c0a0b010612060504180204021305031e010c020a0b060d03090918060b01090b04030803 84
    0x750128000c250510040200001401c0b506210704858184c0e00b11211941d112020780c12403031581402600603041003106118040c0650084180e007602000c4440200613088131915070713500a5041100142d400140c1c06515682c4400d14480c2ca140441103035140c000d1100019004c04614483c1506022141c09010080442d0700c04339004181c01000d25400da00d00f03404001d4507403141243c216a40c50510f04503041c40c910a11986040e40c481800906081e403e20106451903000020001081d03c1010135074030010348684100c500030602521800100040954001d09445058020901683c5032003580442450030855006660b41c0503a0010390300d22120000340d000e100c90340c0084c0c1c0c0620401c141c0203200c40300203030744010311807081f0003c100f644a224012603d40020042c064038880015011418614180c40500603680c86070400c2c900c800d58038a00382050b185880c0007074103c45601400c010910109011700590101d00f460214205400d001c185001c3d4000c0703010203083d407440800021350f4408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 220488741 1250 220487491 220487537
    0x80316030e060304030c030908010e06180313030302060403200d030b010905030d05090910060507060c120507080603010606051e03041a09060405010b04021c020c2a030c09040c06 78
    0x1c054040360b0740e4a031a09016205c080103003c101c0004041c00c01c009410803040c070800380c0342c110001c05481c03d91640c0401400246001100e000d50f800200324588101c40341a0802c802107109401230600c2d40303040c0c01c001e0310711041c000701c1000b00c24513818040c0c18404041180c1100203824140003072880a40c100480c0c07040403e07004a50180301c1c4000a001c4190000054044e1000031a0284e115a0f500f07210841030982500c1000003140c014844240082d01a401400840c580782c545204007000c40100722059030f2007528941d001c2100343e01448040c1c202801002e015000b1420510b1034481040010312030244c040f2805c281c18000407011600300050001d120100561102001d8002d0501c602016252081138404440c29841c11407818201c0c1042c0c025568102240c5c41c6840b0034136904040403001e540704054200c0140584840d180e10307025050364500003150b015040c5555400c0142c181483e040d10030401d188134000c0070040000142c3c6800b40310b4250ba013603107041721119040040140c200d82e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 220489991 1250 220488741 220488767
    0x4030206180a060309060f02070201090b070f08041401031d060c0c0102040905010b1209010b01050a0309050c130f060603050f0615070b0a0c0e060921030904020d060f0b0408031603 79
    0x380b02c5076000119241c2c56040701c0b1501d030007004100500c09400c3c407040304a11540100a01040c0e070740808010031110702c03014154180c0124038034051a40d03145c1d07030b0405550140c0c0200d00001190400402103507454070a190500c007151040e00c1030302c0c02c00c036105035450600420a0b40b22100c0000c0610b40c203142901620010004808280410b503112051801607400c10340955049400020020341d280a05010f40161824103841d9113140449944040b80544041c020990b080d02c27500e008181d454468400c0514034003041d00c4c00080d09080d0310b503540155151540b0002c201401c05080c071108010469299411a108075035150610030001c0f0303c40388a00594101419494445e010000b01c140c1e1038101c0d120009040d030382e41401c020000204110780c0160110075070090b03170841c042c2d280c030300011000c8100d23580d000e01100e041c0340b20034000809030390020403074809030398641c10108800b802c02180c0d1009080310304100ca0415003815905e503664012480131030300c2c100c0001502010b00d805400c01007800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 220491241 1250 220489991 220489999
    0xc03090a080102030601030e0303100b13080f0a0302011b09050609030106030803040b0912070305090907090807061e03061805040215030a0e15090a0f0218012907080403020618 77
    0x42941e0300d141c64000d40003200c03800c0c0800c2c01e080c2004141c04020049030b1040003500b100c1c03180c040c20280c03120301d40d4001a41103640c01c0c22402010030189810000302001c04000c1000f803041c2291450000e09480d52510b800c50000e4014a40314001900140c2c5042501c60a070b901c1c40d00c079090340000902410950340046c00941c070001c00d01c802c0c0004400c94600c6090b00108940d816605d40c2c21281c0e0a1082c0390700580000d0080c400d00d1a189021041c09421585900d44000c000761613028080c10140e05602c07031000715194601c039140c0c8070300c0c010054030208414181080001d00e0250311150a0b000003242c5c0d810749a55200080c01c40d900c2028500001880c4512a922460801204001800e1681c400441071003219407244056010141482c410b00600002d000400196501d80700343c80c04000f012680513100c00401141c080c0c00d02840c42c0240003000ca10701c4960600d00195080c03011054421840d41820003202022907150b80c12581203a40c191241c543d04e0304007098184a544180c50002c1d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 220492491 1250 220491241 220491259
    0x120603080a080a180f0b0406090c120606090b011e03021c0603150c0e120f030a0314090f0304030b062107080d0503130204090302100219090803070b0109020c0309 71
    0x341c00c0d4001c90715441800c40c07000c200b04815031843c02c0e07034034039501070801001e40b181e00001c1300002c0d400b860419001880355a0200303012407143d5402160105580020b0000b000f2403018205010260080c2801003503030840802c103541031740c03000901c681d0510024181c1c0302c03400c06140304111320170360480d500c80008003080c00c81c2e01c1e41c01c02c6032009001140300c01d82da0010b078034580c80130442241c4540024400e06403107240541c4c004030103001d20ba150755003560b0460302585145800c03d110034001003050780002e50b00007d400305404464100b60354003a180c031205a0124051070145da200004503019a900070810202a0381d071078002804d00d641900d50344100d0140300f140c0c02540c103800580c1e00152902981070350300c80c1e007410b81c0445090108851000d44172035403064060150500742e1150400c0ba000c0c0c81560581c40c0c5441c0e2060907a84646524966001d40c0c54007114540e9000e0030784070181038004003071880c00c92107841d081000f01040c0105241a41c0c00502d8401000c81007007202c60300a4080c040c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 220493741 1250 220492491 220492507
    0x306150b0f070b041e0c050907020105101509050303040308030a05071706210d03050a0c030908040e1003020603010b040612050903030a0b03161d01060e100c0224030a0b01180612060308 81
    0x46200040c45250302a007404402702c0d00850040c0aa94410a10015007540071031620f650f80304041000c040d11030600440e03500c08241a10240024000b86000700c40c4103541c2e040950b410300c100c8600400807800c100c0d50890700039081248040b100d8011300c3c11100c0c183c1e41d6100c003201c01c002c528801c49026261013030301804031005425800003817049c01d45850401070034449070340a5040e1980ba40005142c0f0000704414496104107003101030300304107100d044c10702c815126070210301d00f81c0c001e8025007000e40000c0740400140e40c0c00129907000920010052180741408041203542c0c1c0006454881201d072100152a15a01c003000030f1207682c140d2441000b119a41c0b858803001e1031040364104504013215034000b054881c000c51a1540c9e507800a40130750707019090b441c0101e8441d0030788041264010b400e25480c90154446400046201038030030324442e502c2c141511000c04560004d1402414852000e500804010025203003100f103035140d09241504152158075a0000e110704d40008288000201e4091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 220494991 1250 220493741 220493753
    0x6130203090a15060f050111010e0d091521020702012c0316050d03050d060906090b0405060a080615120604032a111011070306150b0f070b041e 63
    0x105140100951046010031005a0b0700341c0b00d0030701940d05c00ca40808410031855104a103000b100c501e91038000645440120781d40c2d0301384214404a040064182c00d010701c13925900d1102020102c203107050201c4844411400320450700e00c4c0020140e0b41c0d1307902280d40c0c000c1d64020074403001c0c600c802ca0700e500c801002c0c2d666448403102c0c00300c980304e0107441451100c03501d004240c035000003540d0005184441c01703100c540c2c0807a020744c400b40160858540392400056000a60300828010b014809000f140980c0302605000481d10010034035441411090400c0161072800305500e0341205842d40018194032582c2d001c00d10302c0701d400c1c40108591090800300420305501860080350404c4004c0701040d00000f00c262801814603200b0f01422820190701404641c0ca000e00c1c04040225248c100000703e0145024a40d04180440d40142d03407039a1210320f41f0210040681c01d100150883c0b51520341004003900c84000140540b2000500304030018002c139081c00300329801450500301d80c4c0c1c12865000420724042d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 220496241 1250 220494991 220495003
    0x60b0f2107060c050a060905190501020d0c0c0c1e0b040b070501050619140a1d010602100903050306040917070309090c0801050d0215221409060108040b0613020309 72
    0xc19458095210302054441c0705a03850141d06410a00400c0c0b4050a9261480240074402044030144910a13100c030640321241d01c4a24040d000d0400140c0b5011080f5036001500e601450280130407000702d000200040000036100c050300c521007060b1a144100008220280e519a00464000e03840440c0c0040c0d05642c45008140f2240301d00000d000380d845000138402c10034403509040c2c8020700c401c40c00340041c1012042004c4003010040c14101d540e6a106448494440c010203030705e004489540042c840d445c1c04100602c411003984004010b20082e60f28000c106000181006100e10b071104446000c2c001c001c5c0b04401c074041014100c941c0c074507642c43c01510301203803072003408070040c01c3c280000359050090704080d04a03100640b4101d00d181056007040b16801041c46c1c0039a12a00501c0f21310b40b010101c440900c045182c00e030081d0552400e1071031803c2120304200320148140d120100304000b82e68400d41032500643c3c00340f00032403982c540c4000a10308021028100450601c04030422080c43c0b000101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 220497491 1250 220496241 220496299
    0x120c0a021302090a09020906091005030702070b0a170604061508040506010b030c0d0b130609200705030a11032b18080306060a020304030c080a030906051204060b0f 72
    0x340c0307420419816501d8060703004502405610110000c8104020720036900244030144000f0030551421403513000280d4035944a483d80000107502008022581e601006008003400039090114100030021100a0000d5080c801c41002da060740c00216030103441d00c2c3c0081000d03150b8000c000034400c401681c01051000e084030255000d104040c0001031840300d2008407070140c000050040d1506030701020540182010310806a0803003451420665407002a11034140505601040031410403019143c0340c0c100d00e03445c3d6110000030400c201103000100f0010440700d6003480d81c20302140c0e600b0307680b20b100d0135402091582e01c20007207125020a00b81e9098000300078010402e00c410402d0300007050031203c0c0c06801000007041e0480400208105151034406003a045049104482c0b5054407035031803446815941d0300c440c02540c00a902a000c0540100b1300c90090805442d085d4102843c0003d20544d62002500240c002995110390084030380310090106031004000d030202d0404444075944030112610904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 220498741 1250 220497491 220497499
    0xa0302030a0f0e0a03020d0203241005040513020111241b130b1b010f020a030e30040e1003050712050703021302070b0f06011812030809120c0a02 64
    0x40500b101a0140001c0c00c007a00018120449581c25642440b02184040b0026a03240c0b0507140032048240c000c40c0d00c9845c0515100301c007003203410030608400c041d601c1904182e1140b400c01c0c040210054400c11210250b0750240b03800d031301000702101080d04005c03071804070074011054841d480b44c218409004090080c882e4803242c140340c3c10500305041550150604044580310144d508000344c41c0988007801203641e038004800342144465001608603010044036039071840d000301d024010103030907101d103d801c54003203005040c070035103600392001410340030320b000320042115031010300d1241403044203075400381000c60700345c1056003070201c40d008041c40c01d0b11003140c180c07040801c041070048508000b420f64070350080040941500f968200a030040c215800046819400e01a441c0804c00d41c00b0340ca07000f03020788109041eaa0803d00c00042038800b104a445101441c0b05108000003810040169003607500761610b0134490f2500415682400e46c6e852200025080215583e0040c0c100404c8030788949100722 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 220499991 1250 220498741 220498757
    0x27081e07021503010620070f0602010e060703182405041a090708070509090115060507060522030e210c03070e06030616090509040308190905120a02010e0a0302030a 72
    0x2e0880d100e100900543c40051048400350b03040c05151008805006069801d81c2d047c240c0726040e004013030b601a800140141c0d118521300905c042e09004e0350b03410050914052142c080c0c204c3e140002d62400c020300030104e40480003015940c0074600080610300c02c0010702800035003058107101040c00a00c0050740072000c0c2035804038000d0400020700a0031078624801418905251508000310140010a014000d54035403a031008036150030400754019058985519884803814180941180e200a0866a078541442c0454509803000c10800400d0b5525290103400e420040c004148031a841c0604010507100c9415103040382c150100311394031901401d03011200415640d590700c00b00d8050079140c403500740e000b14003c00c044402c1e101d41c070801705020b4100260701540d00c101007030703228030111000d500003007112040c491500001852020b10600e080e000340841c1c5540c1e00d0b030f20303100c654803010494961000030360014014001c0d000310302d2030280c00083e40c0c2c1e0807506080282d140d1384924588000207041c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 220501241 1250 220499991 220500019
    0x12090f1101020c1c020d0f062007020d020918060106020106150201020315010804050f0f010c120b2209020a170c0109030b0604050415021c050105010327081e0702 71
    0x1400d100e481200a00081000e20f42c50484d480f6204200016a0030031611036118000c145002d0b640c0e0304080c404d40f40060b141c500d85024450031201d0340350703161942c4001c01029002d603450402e109295501100c00c02c1d525100c1903141400c02407100344411490041600000d0019010341c804400c0310180760424072450280e0400302c0c00c0b0701c001c40740381140d40c4441522202d2548517a02442c0d00c18400c204951030155125040341c42c052000000d41650381d12080224801a408203103840340101c07040007030203a40c0320360b00014507a40320307107401e903034040c240c450f815042505680003002c2458024100006081e202d045100742d20749060031034905442001e03023410055101d01141800c0320303040702c1c0141e05616800108009041c021b07000b5500c0350002224600304401504c02806160300041210b4105000140d500059a42c140d004905251800b5001c61864410a00040d0001110ac40c961501d03402881d02440742c2c06445149422259021141e0070050310582c001d0500600072a0000400701038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 220502491 1250 220501241 220501243
    0x21009020d0f0809030303011518031a061309030c020418080a03020721020a060f0c02210c07030308090105090604080a05090307030b0a06031403040308040b0a12090f110102 76
    0x4854002504414004000d80105508072800c080c180e02c07881d1030700c2c50300c001c1100091039904283c1180b2030080b21060201201c070742007200000c0380790064070751814140c916218000d081c100441c1c01000c00369010005030540d641c22806008402c4116004c10804010381801001c41780d014134224000d51a0284d6426074584112803c801540e1100810340b034007051901c2100650081d07281281c1c91402c2c001d0106e461026160850440c00c1c0b13070f0b03004050000701c43c10301000703884040c2101e6140e00d03d0445054220359002c500b0030300d440a074880203d0b603941909050340492013102044103580c0500807020082640c445065405844010f00901842d2104034038162900020380f00102110401c10140910301d0180c0007a085034080242502c01042e0f90b51a00715035590b04442c18401c0e103035200c00910401c52140d00100360380300d0440066040038115030341c03100709110301d02501050850118803001011321840c121000d5407061138082c0702c02000d03031a000c40b680c50941811603000100785d296000a500c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 220503597 1106 220502491 220502501
    0x3071a0f0424080f24150f03011d06061209031b0309010906020f0d030522031205010e0f0c0a02070e0907090501051203041404060305011b0210 63
    0x203100302c0c010460303000200030492180c44402805016141c03104000e12950724202c070025090704920025039004007030100c4102801c800501c0083d0b8148800165048449000300210418002c86081484400444880360401c0c1c050018000401c050141642c000f140310080d00e1404490342003405001801e10384210191303000080a065551b03005a81800400d514405800340c40c110801d0942c54500c00d04006042540b2040403c5580c0301c1c40caa13103561205004401242c0b0764051030f0141010b00c05104120030305207041d00012300c42c00c85034103941c03240070390301d034200c00c16620480001c441d60031088018046200d40d1a010410b60040d00300780e4000c91911006040c0d40d46015880b4083d90b40c143c0182d401000882c0566401d0000003065400b03540e01c0e40e1484e165080008046002855242c3c0003400c40e6080440c0d070080074400300340702d602180055007501c8002081080e000103540c = true := by decide +kernel

theorem cover : BRFrame.Cov 220323741 220503597 := by
  have h0 := BRFrame.cov_init 220323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 220323741 ≤ n) (h2 : n < 220503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
