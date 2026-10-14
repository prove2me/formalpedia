-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:45:52.300574+00:00
-- url     : https://prove2.me/submissions/66dfaebc-d2e3-4c38-9193-dc85a9a6cb55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216906474 ≤ n < 217086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216907724 1250 216906474 216906499
    0x60501080109150e1c0f0206010602191514041217010f060305090a080a05040503070504140606070615090615140d0c1205040303021b060903180d02090114 68
    0x10521680040c280c00800443c0c3c0064030f035540d80003c00300c1c440b14000c0c900070b901d03100c4564100100d4001501040359a12240d0b1208680000d0805406801403011034000d03141601081c0641181c1e5a40c99401012510300c82c0d10340501180100440c020034400751400d403082005201c241d1f0f035400203161036070b1030b2640c1c500f035821408000d43c5004d005400c6c6201501c2c50500240744254403a40d8010081d40448118103841d4582000c26041001010300084c00001c042c452030405005d0f841c01406c06407814000d02d891881e50711142c140c0240003501801c1c0104a06060048540201c4840e18440700039618054603a03204001400c03440c043c9008802000f0880940c66200c2c0c840f4030747c401c046091460030201002c411390058400c0b050700000300038070103070200981c0b800c5125a90150f40310f501e005030354903c03114001021782d5651070074004a400040800082200c003004482c003800c2903031101c40e903030074910001500c4000c200c0d0740a900311120700700200d001032588801d204503c0046640580040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216908974 1250 216907724 216907739
    0x1c0509071a0a1d090f090f0705030a03050c0723010e01020303070818070503030d0615020f0613020111030304030806031002090a050d02010309080c030403150b090f0a150e04060501 79
    0x1400303034000102003408008006095128108410403da005085882d0208030701000070b101c940180e50004200d40f042041c442180020041307030350400300c844003901c285890480000d171581c542d001c0240c00d002c0300040441c03100c2010f000440c040d01d00410b840c1d41c0c0e0b000d1840d500550441c0c82150340c0c08650351803c264100c2d8000410f80b0b00c21076856442141a584014120084810b49050014030388910940440c666a00340042c054641400798001090f525100c1c80c800c41c03180e02d640c00c02c2950021110101d060201185081d070140f400031200c0e80152051004807808044204215007502020003030204069000300568003801c070480031128900c140904044c200d104917800d0f503600c40d040c810200310f0b074288140d00604003401410000f4a680e01038450040035440b00e104171015400c001001c0c010410340340b103411840d04a0420410040030800f01240f81128090b100b058442d01c06800295030107015007004000e02410031012303400326592521189006020b5608aa4440c1818008a0700c1d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216910224 1250 216908974 216908999
    0x108060103020f03181f0207170c03030103030e130911101b0f05010209030a0b1608010f122102030913020306030304050d111c060c0807120f021c050907 67
    0x2241002d02c182c55501e40c1650100048a0f00810754106e028285c51107110b0303040e2000c07480e01b6241603000540d43d86550315001514503800d40303041141101c28080c0050221700001503905695260905141403180800000c1d001da9041e10804035441c00d000403201000b20b4400c90008070b1400341c421004800807214140c4540c2c400f4440b800b500c202003e010701c0800c1004009d03200a90040d000140742051410219041281302541654290005014090046400800300410b00720b20b240100719035040807a40c0a100189218a142c80750020328030702c040c002c0717000100c0341405000c4040c895112a1307000c040d45941240e07021520a17560340d0140c50012249000700c038403460340100a10310b80390404040107200c1aa603034043d28840484a202d00c00e42c2ca030100220824000c082c0c03044079150f0f55140c900140c0351f881c468242002605030600404513004407415840a20741400131030803551415040009000c0c0c0505000c43d001085021860030b01c0642c011030040031810180c40c28240c84040c0c80041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216911474 1250 216910224 216910237
    0x1f0612050f1b0d320a090201050712020c030a030908010b030304081002071713030b1e040b0c130f0501140406080a1512060b0307080106030308061005041502010902010806010302 78
    0x310080c2e902c219400d25502001030020300540034001030107600300400304031403244081c1c800b650300d03800160004884407080300841e40003c1d42041840300320010380c0004c201c0c1c000e10301c00a05c0d02c00100781d2048410f0007404005041403010b402c840030800e02e814001e00310351076449444003551030100c0d07080c3d2130705010040310243e4022800405103884005007101c020b6229600584100f040c001c00800d0203042400144511041c440c81c0008090550070010000354003c2d103104141c107140401800c4002d6181402580a5040850fa41d1150754a149050061040012a8440b000208000304414910700d0806042d20b6081c0d88101083c190040481218800d41c0200f40204400c5000140c0d13440d83c54002c0306105a220048000550b501c03031035401c0f40403440c1d2040302c00300e4403090045010705003007000300001c1c000b180c002e02030185140c6000d44400805083c1340c1c017400300c8003204a00389010b1070485004001d02d43c111070b100d0807d21350003402442c05a204a000981141c00f0030a0341d8400d0090720103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216912724 1250 216911474 216911491
    0x6110708040311060c071205161d0c190c14060c0d02030c070804121103070501090b0d091703010f0605090a05040b0406031b031109090c091f0612050f 66
    0x24007401c2d40c603841e61800a0038142c50740302c4000c1048403d801010f020880082030212030001c1840d41d40e11f031040c10809c2c1d0b091003059005103d03000b000040841d8288124452034035500c00003a4132503680707042941c4590481940086501141d030101e00354095150046140a965001818541a940c440d1120320545d60001503041c14000c01d410700505034025600110b801d078500d031605ca01540d455940390010b500180e200074911071001c0c00e00c40d010808542d11071084000d00300207420031001038145019401801015000410108240b0b99aa80f000501329000814001841f0224a2421003940f090148a140007003040340041d825020710155030368960020103940000307082200b440f000300a450001d40d4095283c1d400040400c0307441c010240c44034444101141d0307240c00c506044500c940800112405007401c07c013040380d6000080381580385c44108403108440da807a03104841c000036490341981e0001c81e40b40c0b42d000410039045420590b01290f0258240551340e03560269500c084821900d940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216913974 1250 216912724 216912727
    0x4150501080c0d05010906080606030a030921020402070b0403181203112a01020c030c0a030206030402062704050703050f0c0307120207050106050a0f0b1210030b07080406110708 78
    0x40658055141a07500842e0504003038208001c8800080603203900b81c1c48802d6a95540c5814000d50720140001c951100098005240303500084d5001010000148188441d0144070400c0c50300d800445081000308c95001001591a49640c1c2080880e03040207036012000710380b0101d000e882401e03558402604450b00c2408502c0076003600c2e202902d6070100e03060261354500032402d4400b03825201c45072006242c18074500015410110900191410041445451185c0e1007821140b8141d0f59207400d18003034035410354401c2c2d140d071124408140715010702003460744454454114400c030314a42c54141210b103c002c540500c441d894041003070342203c0c001c1e50a071500080520000b40f105d40500000d40d084125840c007a1168101d5030050b404a8001070021a81c5944030941080507160103041d074006440c5907000f1405003031800e00000710b203110702440c103000c01903601c00041f0405920b0318080021500401801c00030714240000406400d021201118600d107840d100b058a121490199010f440d030050b68503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216915224 1250 216913974 216913979
    0x118080604030309030507020306041412040e13030e090f04020109090c050313021311040906090b130c051213020307140f0d060905150a0e120a05072604060e0415 71
    0xc0740a404d0340e40c1c0950500104000c0c407001600d080040b240320f00c1c001c00103615038506005c03001f400c044208001d1114148280301c14040340304801c1c00d042d0029980b510304040484039282c04c1c1d81c40017079412940d62245d2864100184075401020b100c2c41035200340c4e2088802e5484442805c111001c0c850340c100003039000d00000b4015003451302071000160000307201040c00003208401c20180d821480c4c403880d01d5a00818104410079540c00383e88050440c1c10000e010040d202e0010905000140701510f12040c0c880e1520240c071401082210389803100707030301100e109160408461316100541c1c3c408902a11680b48005242d070032404480c0210f0300300405880c080f402c05402c006900541300b20940310643da900c400070000d00b042010907c1d44035808141880d500d031120900040302c0c110300724a10729400583c41d084205000314100c901018190610644909003420031041c4050f4442110260462900d00c55071130008004c090001c55181e96070394401d6444150500090b01d0744646180d000d00107030f0006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216916474 1250 216915224 216915227
    0x1103040e04034a0d030c0b040303200306010e0f01020303240301020307020607021b030c0402030405101505040b0301060b040b0a020f1212010b09010903110607060911011808060403 79
    0x1090a4600d544001e0606900001440d40007218a40b030300e02c1440f03072103101c03903024283d40460b000f1846011a149031405140b80c8002c1c0141100140050071404070900140800d40a5403040f25040240440072429810010000107141d00542c1c0880c0071544158600c0b155140c0201310141c1144103901540c11034075440d01a4044002e41c400c0315861801c000b41124168500340b0146205034400e034010041c5081051000c2e017010b4032041004c44500001c07580301c80030b0b00e002800d0401c0100c00d4800607507950b91810840c2c10072491301084000c25040104009441c0300036682c10701a10b60440d42040119403240805080720300e54815101c495030180030401003026500054244841c00740103a0b4840d07144245428180b0303907440340358007609001240d10711408000b098a14050000c0c0040c2516081d01d442c0060450081d502c40107207100594002c1d15580e03210f40041d0303581c4540c840f6050100040718608800201340c000348140c000303494004480030701d6640d09000e0303080320340000181c4820348580c1c90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216917724 1250 216916474 216916487
    0x1306030b030f0a1a010f0806070507080702090f0a050a06080703060e0c09010f0806060f011d04150801050414070f12020307050d0503120604050c18030a061b1103040e0403 75
    0x44840e81405003018044203072005202000c0f0151041d9085001d0700c4182c00c0201c0b60303080603001803204506208040c0400c07000042c001e9041034542c02c005440e106075203403400d102d100e0400001c2d007222850090008802640290314080c00343c0c0c09090244c2d40e01c00c1d085000b100c4007071061425907032000c1d10800202d17600390300c100d503660085015105a0400000072a59040007a8008101d2002c0400d0803c0070003000c1c080307145c0114044407100c040074440d03c00204003404180031222201c010001c07460060f0303a01d40c010210300ca5494200701700140c4d24000540284800c66082e03601b20300c090440100384601150b0481660102070148000c0c5040c00d0f000c01c50360554034012601032040c040c0200f443e030744800e40380843c070703104800a50b6030b005e00c0c00d1000d00300312001e844d0300c0c020b82c05c00040c0a512036440094408469012202c81101c4000c9070020385080d84240700a0100e80c03400311481082c09001030040701c01000707521140700500d054241c1d240c1c1c900c1070340b01c0c0700415541c0d4404600020f10454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216918974 1250 216917724 216917741
    0x170a0c021e010e060711010b04110a0503060f030706030e01050f060901030311031c0b040f0b0a090b0301182105040501090e060439050c06010506070f05030c01060614130603 76
    0xa09400030820b03844c50130300143c920801251004076400703110070003401051362181080c0d40600c00d8a007400c407840c1290003110200c205202c00400000c6440d2610140e0b81e441600080c02c03240c2c0c80c0c0d43c40c0000782c010020030301400d1940d404c01002030707201200c4400a9024440113040d8100680c42c68034102c50030309415640c1000f60004118140b40001d0312055002c1c80aa0042c0000d10405040c0030002100d080f840039203103203070500000c040ba50b52407145801c11074040400200c1c0d404000300c00a401061031021810101b00c504400d40306206105101001c030003070040400004211141d0150b840d406244241400108079140c28400c10082000282d08400050f101040b144101d0030034002d01d640826000198140d0f03607008030b54281d042802080e8900740c0e81006032501d48081000f41e111901405a140909000111101004844002034115170703005010b03651500c40b100900381c0030301164402c0e000003a59644050b0400d060540841c1c101c1c0103081016204103140c050b0503805007030b456 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216920224 1250 216918974 216919033
    0x30815060c0703110a090c180e101e1d040203061803030402060a0c0b070c030e06070809100207030219050109051813020a0b0409050105100e0307141f170a0c02 70
    0x417400600c90300346010340c0c0c0ea0040592070b41540c049003020040c0400071198040300c0d01411405c1400b000c1154a81108183c5880d0214111403243c401410020701040c3d91013140c4621a5043c0309131f480c00d026000c10b005e03601c201c055842030f03200c40403c60207520301070b01d0400302500308101103001860010700406694400d400d0240204a003510b400b02c0c0000c0442d091000b0503044803074070003010781c0014469040c0008990301c50a01c80f4a44625200b03000c1d8051990190381c4044112038002d008000a41c01140e00800102c68000ca00700c9280f88003640c1e101d40d6020498514000c212490310190000507402c1c407440d07941599807001002101c01c114004143d07003005901d2000300d0a071036049d00070409000000d0000c5850351500d8140301d050304000d51148104403c0901400b2990f40104240702210514501039419003a0701c0006000581c13500807611410f8400da11045500e608071810220415108020861540c2c81c4120702c2c080c4c4032100e0058005030800b0b0a80ea4060a0010500c064440d21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216921474 1250 216920224 216920239
    0x4050c060705010c0905150702010305190e100b0301060b0702060a211a060a0203220b07140d0e061902030f030720160e07031503030815060c070311 65
    0x8001080440e44040c0c8159400d9454201000d140d03900402c000c1e00820060320614040894100c981d519806081d000a040540759804201c1e0f265480e038000e0801b0540340b0040107480c2c2a0300c64182d5440c000c400c00005107040c44686074880c5010310400c012100401c0d0000d1824040e07030308003c5554400711070642840810010240b12a00e41d502c0e41900506405000500c42c015900c504400703e0340501080c4038280401184905a0380841a034260181d00b402d00c200301455130716421481040764000794064400428460309201801111600784550082610113062600f102140ca00841000960b00a0707010000100005804c04007003000010a00c1a40c0c2440300d854a803c846510a0311070400054485000d50103000b0030345010b200708802000102848074034200402798600c882c1c41900014800c410005030f589000780c2001004103c4041c1981c0390f05e480b03140250500f00181d40702c203069034160480c50b015007400700c100c5110003a40360040a50034030f55524005040c4040c0b0300650015039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216922724 1250 216921474 216921493
    0x2101b03032d021b030306030a0201030903090e0f0f09010b030c0105030601030624030b03031201090504020111030a08070f0f0e04150302130b1309030c0323040603021921050405 78
    0x60030b20809000165440d00542c0d20710303000d0748100d42c0103081c0318030074130395002002488280c0c2d1340010411006c540c2070801290501c41c0c1c0c02c00347c41518181e4001140031401100300001c01140314a507611524204080c1040c5840308210a422031700b990302d41d2909603000b560103105e21b600a07000b40d54442014500410b526864200c0c0300444000c010b04a00d611141c3c1c020350605a4160040401a000c10750040d41000c001c103141a40400c018417402020310f540d24049015a4072541d01c0c02d40c880c42540440303035512505000103101e16402c64503000050084111715100d10f105122030014446180d075154448403140301000000e116030349040074001d081000010058440d00110100b00d40002800240b6a401c00d091101030524081103411062401e40c4001c0000e41290f400c150300c681601d02114074014115009041502c541c4a4040500c4c000c01c000601c1603041d001001031220003442812030103082d04041c0d9048a10303401c011001550b03500c4d03031042525580e0051350b11500400440b5604203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216923974 1250 216922724 216922781
    0x170a02041508010f021305010c150203040503040b1902150112080306040b1002060708060607021305070e040f0b0109050621040c0509010b03010905060d05030a0c020103020903060f0402101b0303 85
    0x10001d4650700007085c0c011800c1100039800780031070380042800b800e0000001c44030b903172841c0034503c071400d0010f48030b80e0200201d01030041c10415240030704000546256a0380800040c048403e03800d400c4940180300e600c1386041c1d4012481c003010b0483d040d0b60865851590761350344e0500c06403c020510340c0c020307590780e200d01c60907900c82d92280c2800c3d12540103000a4204140c000b40340110080485018590030889040140c4811140005006580c080012151a00d2504840300084485501e07441800c0141c42c00030b151459104101111098036504c4001d90b450080c40f5460280022840104007100b03103415803005072186840d480341c42843d00484160322200041c409940a80000e51540d0000c0014084600700c1d1291940040040310f00c00700d009a580c1d101542d92150100c40c80c100880b83c201001164002c0d019030b41d55034001826203045241024958641000864081c1e1203408006080c2b1481030240800f402c43c004c000d0841c041010003034a058010380325600c00c800304d80124207000c410303c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216925224 1250 216923974 216923981
    0x2121603270305070e130803090c0405010906213c03020115052d0a03021206070e0d202205040512120613180302010209010207170a0204150801 63
    0x10550001001c0c040d09605141e4546403c64000c4161400c81e601400700200300001c0350300b106d41d4403550560b40c0c1d80d55a69424100358590744200e030801d0501001003504005a00000b007510240400300145400e44880c0701295450181c014105080400b185000d104a10803105602ca28007900340e0965110890200f001441c038101c20380060b55100802000c01c5e138404a10741c010441181d805113003d05c0340f0403400e43c104840091062443e402c1c0c80e03d210315207604003d08003c40e0000c003004450400704044c6900d49804070b4507000014032070b02404000d0316000c1c000402903a0000c01310000c0403500824001000d6085000300da121960041394086008900c0e41044510039004003c10103040600d401803034800d0103402c9612001c030500002c0441000b521565503c208100c942200d2800300060440040500c081c104d03440b00c85030300400c424150150000c0c02c03040003c8c0d003107444541e540c204400c0c52410b01102c6003801d8110002401c0549459000b181325442c09503408228240c4d1070b48640d085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216926474 1250 216925224 216925277
    0x5040b0705010504111518010e10030905010b04090c1203030b04020703030c080a05091f02070803130c05040605011e031b09030204050903090d26070303020403021002121603 76
    0x641e0b449904210801074565003c0b040d803102651407600c0c0c17005040f842039040c000c01038941f40c40c0044801981d03c13a80315142c4000e0341e80b00a03160701c10f5041681e4009002d890500000d039000d608111003410a41013901c2014600303900310042c943c0403030501c061f400000c000d8000503005c042e11007210031050b6440344000c06d411880307070f20002410307034503480060915403000b020220147d18010402003040c2e0003090080305020444d2007505490044081100203004818003d082108040104600c40700000620748842c0d0003034400c200f086a0303400800c01552070074025640000c0c00c00740c103071000700045400320410300340b1800c01046014940e0110f001606014070755400046010000b00294142442441d0300040d51038041c510340011880450f00780b500240340101407103141d01c602c0d001c4500c0e400707107070519000340d07602c076a602e44070307810020041e40146c0010382c855551014461181400003443c418080402e1100c28140081d11026100401c00c00c20b003a03040c031144020302c991844040120b03684 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216927724 1250 216926474 216926483
    0x30906131a070b090105040c1203020a0609050304050901151209021315090c09150e0a03120e01031413150f1d01060617190b061305040c1d090705040b07 67
    0x7100c2c03299003482c40f80b200c0080d01c030080503403400c018080829103001d00c0000780d8a4811028040d500b083c90101d240c08407400000e0103480c5451601d104029000c00184100c80c8200c4446050341d884e5a4035491150880c00c04c03c005c103540340450607081510303402980c41a0f00080c41c010b01c0f9400c84d8038060650307400e0340211a014140d60340c1030024542e0341c4107001c14046d00b442c20104003400c002c00090611080f250000c14050902c20f079545c542e6642d6901c02c040c3d940f204065003d00e0520f84c014003048c1c81340744140d0100c2c2c1000718119500030405031a80c4640e5490100020107105900c8000c076440c45c3d0742400200c2604d4030803d552000c628020b82da4002c160082d0300085900300c03610300b401c407480b80d00610f0420154075901c4070383d012280e014540014180c0c06e507044804503d03000d000201602d00505400040115140746640012545031003102c82c16141030014840400b4119889052907400308401114036104880e2401c01ea089242c1c407401d039081003450a03848140d0340d1841d400c1110107d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216928974 1250 216927724 216927727
    0x40b0d11130603081b032208060708091005070201180308041e030923180703050f012d030c0b0c0115060c030c170318120408030906131a 60
    0x2200c504158005494203640c0031000c004490840d5074022240c0f0400482c800800441a0104402542032045401510400079480825030001d032225540d02240e1003480380134054000001e0039680a50041407150036100040d0103030644111000000303110150001d011596a421140c86007601c4480c01c281842c003a480302e035000d140524080306202d0300e508501c001c124605074804002a044001002a2111000c6d440044178140bd030740d2500e21405920280e2021555902000c000c0015002034080e00f035655040c00b413540c0300710b2644c284031005e2044101e20284007010114820001d045201c0d04124000c40c071110940e01e0f180d8030030854482d040009680c1c80000c6040c1441424411202d100d00d584039002e00891401901500340c403135000e4040c00744011101040b0820030031b070100c4900981482c01c07031500c2c0d040a600041c421076045981488900c14000c0764040f0801c103d0a540844004000461500d28010184540350300023955001e0303400000303c80861481070b0b40c0700010000b400c1d01c01c141e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216930224 1250 216928974 216929003
    0x3060108031803030a08070f030f050c0301140d050606060d020f0a020f070e01030201020624090f1f0806010611070b031f2909030a02030f0d02010b100c0b06040b0d 72
    0x8840c5034214010f48694030400c0406610f58000301d00c241d01c10b003241070160b180c00d501070055024041041200e060549000100440e20004001841c141c405c00100508000d00e1101845070103036564201034400c4d4441c0c0005119031802030300420f800b03960341401500344151820001100d8000000341c0001da0003222035503103281000c00840c07000b05481d0a0b052169459500080e4640102812941041a1191a0341c40b5404040a03803001520081c01c100c0135031921a6541400740400e03101051440748102c5c0000c4440145d02c801420303600c000004e031145034078040341501c07a821081c808a24600840e10009080310080300a18464050a00500b041c04416900403168541c6a0000c042e080154100e003a004401018005000442000000e0742c4083e408006071402c0b4410708029818031403035190b000e1800021034841c01b505181c0d0020701020050764104187c0a440d0300d81e0800140a07101c102000c50140c0082580140010304001101000d03440405c0707001c0302007001903900d4080710090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216931474 1250 216930224 216930247
    0x90c0a0f061e090e0a0204030f06050403110106061428020a02030111040605070f020103020c0706030f05070305060102060f0a14040b1f050307030b1b0301030b040c090b090f10050306010803 83
    0x100074404030b000c528030502c003091010191040d40c1c24054612100001000550280003d90483d40910b400c07001211a56259185c03020281c80c080b202200003440942c2504568401402100d050712520f41b1034668180384481040500c0c0c000341506403034103103c180140b08d00743c020082c1c030008000c1c039070103032200368018010705081d2a4000c00c8100744c20001c0008000040c0e02905940800c0c0d4003d82d2007038501c890b0300040300a0700035110400308601682c40005181900b41d0b2000102086182050000b9a140382050342200d00841c1c034240541c00c9000010039001d560a04280d100c0c1142c000022240d040450b42030620000b11811100360000009220110746075030f0300c007401030313800789214200d40d420100829150060344c1701c020300c144658408036880ad210f03210740d0010802e16074102c070348a6949003860030b0040b00c00d460076990704c1e000f4100400c015003d4080c580c0490780c058041e609540318204c108003204001000c4034100c01035603c000c11650303400e200b0b9500a050f401c0040d9210b2403580d55 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216932724 1250 216931474 216931487
    0xf23061b010c18051201063203010207050a170d050403052205130c0509030102070807031e050301050909010e0d020f160f03060506030a060e1507030203040c0e090c0a0f06 75
    0x862050003003800780d1110054610951409441e005d49001c0c2010180250045c0900181d420100c0b1501882411000807618003a03819400c0101001106c2003030f2031001814200e1280104c0a81aa0004203040c004100f0b05602d0104002111091628040040f100e1a00703c3c0e1040d202100090000034403031907040b906101810741000d5580e03070010051316000c006141c1e2641e82c64084911526481500c2102740600c05594515402078025035503840640f400000660042108401141c0200300e4a0000640711301130650300030701c41c1c0740c15166900700020490b0034030008100203029902e80408c0d65080b001405190a10100c0740c0041c0b92400d40c418509007801d2030188040d150a00d4401c04100035810845840100d98026130006400c1d00c805000c00d04044174818098641da04220780440c03083c0c00016241c102c0070100c564200b254841d03110890981c030007520050070101c610741c014441c0e500d2036440c0c690480c181c1d104903060f80241d40e002c00c0000f880c84d8000d0330400c80d00d0504201d0341e500100e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216933974 1250 216932724 216932741
    0xe072315120403030504150e060601260c040302010207061106040f1106130e01050409170705010617030a02011d031206040f1505030106210f03120e010e0f0102040f23061b01 76
    0x4008c0c0604100c80307503280c2e44c03048024480c0b4100a280300d02c8500101c1c4070624101001c03001d02c600036062a000c4810038040e03003d884101d0040c806c0076400510b607072050280440550000002e00000d4071291a010b07000c00109800792010412200c240140c0c1da207850040c00207220700c51360940d107140382270f460b5074140388164406800355040c071404c40002503040320711000f58014114280d884040d82d0601900401490301f040643c40084510b00d41c1030b04000000e060940d100346d000b480300c00c1c2da6000c01076082a0b0030440d118203a00c00c0c4400c04103800710040856000174041c10004503080c0e4034108806880400345596090850725105104c41c1c01c0c2801004040e20108200e4001e24100018040b0f5040c0511001741182140e07581e0700c3c0815102c0c040e42c6c501196099018030041041d450b10318020198140710801c2c0e44250b42070000c0914042c02541e045660954136040311034a4140300e05605034548030314042042402c040c1030300d965920406411020301e0907000764200078601084038210788038034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216935224 1250 216933974 216934013
    0x1060e030c0103020c150c0904060608090705030703080922021908130b040807060204090f0b041407021209040207060f0212070504080c0d02030a0c03060e072315120403030504 77
    0x4020b686404800018040c0c00341c08690340e4144587e0b02d000d0742802e140900c2d001140d0190402c5000105560701800311401030b4080350640d40c140d80c0d0761041580d0b50519110043c1000402d1002d01d040d45040b03038050504404504400840085003100003040b030b800000000c0d4114440244104420744c81a54580c0c810b030f804081c07030a81462511000c01041008000500c001c8001485004000154040e03030000d15809105015140c00700403014003801040c2003041c000c1e86010001c4064002c00301110740513006070b07000f40200c5190011b01c1c000503400080c02ea60800d4080080c0c40000d02140f0034407000e414455001a00c1d07100c0c90240307081510000c0e24150410400784014484400e01080c00103084c40b044443c2c80300c2288a1000c2820f0000d11200a041d00c00286400000d200c081e17040080010301b43c10a070340d0b542d80c9503e04040c24210008200035401422400f0541a0030b000748182910a0703040700c00c40c2480300625110a040c0021941100043d4450003440700b0058162070000c40d14400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216936474 1250 216935224 216935227
    0x6030f0f09240b060d0e0708060a20030609060f24030109060608010f2304090b06010f0c0b0f040f0c08030c120405010507060b0a05030a08030f06010f081f0e01060e030c010302 77
    0x43c41c00120f0a0044091014281c1d0369600e0b8400c610f101000481c000341080c0060b2081841d01c051041e00401c80000030100c005880c851410720b00d1924401c40e841110300402c0c41304076458070002d0003074900c0001c00d00341e041012426000f403c0043c0c5000c0c0002920406560703035584d8140101503003681c645510035000c1c01007910041c05942c641042100c151074610480e00071480b0b148a4005899114401654100307152030740440038866a1803c10744510000e8075209031a050f5220115001e0306189405081200202c010900100110364907540040c003481c818101c1d00f440d030710340415100c029030000b4030702c0e4070000c0d007503100520506c012145400910300d440c0c20f00340b40100103040ca03c140075009122582c0e903c0049560390324001359402401000d8100d40e2004000c2c41e041119502c1501c03824429015600000c0c4158410007185004900680e1650346680701c00c3c1e08003400c041034042c0c0040c0f0190314800458a0740064180724002c00d12942d44400e401d901006160601c01d6000c00303581090b00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216937724 1250 216936474 216936491
    0x40e06060102100c1b030c02190b04090e0a080f07050f070506030a020a020718020a031413142401031a010e060d030507050a030c0b09030301030c06030f0f0924 70
    0x801242042d1000c03801180480c813400d10040444120008075407010702249800e0b00c16050541c46881440c0d4580b00392080d202e801c2e0840c114000c0e000c928461403141d02020881800840380e141c00903241500003608840c52823030346903a13001d07450300400c0d4072900780d102c04140c020906c00c0400840b0041049d6001800c841414040801d055100041c000c4074880e400150b40b0090342d00c00c000c0140141401c900f9a14424040c00f4510b010798813200360000040e0a2200c44400c8860405201b0b0148100310750f805000300c1142ea801c95212241e400441d090b02a52425103120070912100b155040c210084040712981185040b445100d0101082c0e0320f0343c1c02c0c2d40014407200c10040300c02a00194104d441c5081c0e03040c1840d04075454030030b200d00201a4001c044401d030405400c002d003034041500c17655000056681300c1c1d00d450354901003413201501140460b4801c00c60603010b0f030700018000c0071000300814400a00040b0030309507010840d080b1890520a144884002d900c81c407100281241810144910fa1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216938974 1250 216937724 216937727
    0x62a150f06010302070302190507081203090d0804020621010f0605070c030308421e0d031704030c150c08191d030a090f030503071b180902040e060601 66
    0x2400107041505056000424009040c020040d14440d040700450850b05507049141860322350486110303154280c03182c544600c0a1701d81440960f031045400380000e0141c00c502e108200c03a00d041c05001603030840d070200400312600c440c1c921640941038540d0040c007019450058014015903680e48070030104102030221500056040002c40b00f202e030140341c00022511b0300251421503056040740750452544003441d05811102c070320001410101442070b040d61100d90481401014100b484003c0440703c0c10380d850802038580341005030602ca0203840e0405c040d40c041c5079a24031440e01a5829400300d2001001ca0301041000f0400c8940707840c01c1c903014850b024103800b015000d00c102400c1400500e00c403d40d81d403400141c0c5c2c0d018640c200400300055110f0440385482946030341c092000040090000e410101300d020001c20b0007401c0b01d5015000b0f5141000e16210341402c1c4007610f40464004011250000d800005042a0320000d11008000100b00c885481040119203003400c1c9046203400403410090503a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216940224 1250 216938974 216939001
    0x6060906030a0b060f070303090203010b150a1d061606060611030f0c010906150303080105010305010f0e0402011101060602010605041401060c0f030e04050c21060907030b062a15 78
    0x2c14100d9022910b030310200006100c5014500c00120000c07408180301c024150b054110f800300a0003034000700500d003800070902008064101000d540c0030410060f400c00e0b0f51241c21202018150740020f0112400e000000a074545d2040005e40210003542c4800001e2002912454001b0110b50900603d0103502c000142d03201d004400c0c02508031407003c140f00c445000290001ba1a560b0311041c1008801007205401314141c22030b00044d000100d0789400800c055010340b040c14144c441c0c9038041801c2d2454002c420703000e014010400ca04005920b29000c803803800900940026000030340002c500c1904040600049426517104081c60300c09020041007415009010300e100729401ca0f4018010740880c0c00d00780c03980b48401022680045c58441003100400e6808081d100d800d5400407050301c110310300307590400c07210000c1d100241c7c000c490a01007240c4c80c1c0294072583d090300024140a06180025025042c010b2400d030000840f8a00c01900d1917403001c0078440c84040301250000342030b050811035400d202c1d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216941474 1250 216940224 216940231
    0x90703140f0402100c03020c280e04020f0405190c0801060e01020a15090f0b0408030601080703022a0f01050f0a0608030a021b0a0b1603020c0102150420030a08120606090603 76
    0x45c480b01300750003814544240184185080e000d8940c4107048203500c804452403c03110200c2900c108804030207d03a15803000c080030f00a0350020000750b04101100200801020080c003c206104c045003910545044640180c20042101da100c4000d00d40c90701d04050107500e1121040e0b8110f41041038520f002400407015100c0010814800140f26402403408110000301418042d1501004104000c1081880e000940c0306038800c2c2d817a102e040d1a002406d030264014a0032111000c004e052007404480042a090a0342421100441c4c06000c4403421030707400c66000b500c44401e840100000c001403189135009420017810088011494604440002911540311240914000e12032a00461203942c2e581c40080c0900341690035181e880304481807681415044010450250142800c401d0a941c004a55055400340610103e0344595a66550b0340054008101600212404450310499a03c003000b482860510841c007a07981d52000f206082b40460004200c98802c600401140f0400e84440f07040d01d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216942724 1250 216941474 216941477
    0xa0c05120a0c1e03020d0506011d010b120702030d0f05090c1807120609050a0b2e030e01200703121811030f120d0b04050103031707020c090703140f040210 68
    0x18030503c490540d1242140310351002e50311814281d4003105208021803428122800c40b014502c1640c02200008040c5a0902c50140411814081641d05040400780c503a84407203244192031400350b04284007011a03503060210301c61195924108611136400300070030310607524100c900c1c1c0b08054060940e0314502c0d100400c0181001100074000206004540210001e050505421310240c500a0070500c0201404542c035881924003c0c01c21000c01c0c0c0641d2080c040f6800046407004089005000350080c02034541d10514035966120707800c3e00e000c402c0e002c80c00301180080d250350b40d40d030351410002d10a0700500020301c00f10749030108000000141c04010011958000c0f0356030b12002c5203c002905140c00410f5441c114020304a60400162180c8010448401c10f14420005a00340c40b00744404ca4509000c0240070a0fa0750300b821602d80c2188041aa100da483e00c110f031940344150000c141c000600303450200120352690b560150711100c000246502c000007a054803154609038001414034150b2860010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216943974 1250 216942724 216942749
    0x80339031f03170c060601090e010b090a15050a081807180213090e0106091407050c070f03150507110d110f0609070302010201050105030a03081501050c0a0c05120a0c 73
    0x1001d140c90403a81d4004503002004001810441580280c0390360201e05040700324011200004d03010340c00b68140f0343c160b07081e0b05200f603140e070700f007900d0f00c00b06620001509510504810000802115245810101d11055514141c4401602c0c4002d00118005084210b041e0344092040800800c005810f0007214502000c03481ca03103080d01c26020080c4602603045500645150001c1444041f030380000d0101603018000f0024180c0d10003140c0100e07040c03507a280c1c05a0b802c1c6004110030f14807640141254407081d1040c1c80310b040e86c0700b00100d000313180c07580111201e00c030803c120310303245615118459000c0c0311800c0c80728204811040e0252500d05440b0320f14140503006002c0c1404060800000034100c1024007280c201c0d04091600320356441c900c0c03104074015070a003000401c5500340411024081359041e1a29841920b075a00002450301c1110440c80c1049010f000c02600c0b03040400c4050360141c02109a440e40030706240c18881ca001c3c0c940d040340c54a602214264001459424400e13045400c0d01e030818 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216945224 1250 216943974 216944011
    0x5100203040212030a0906020f011a1912110a090603050c09040320070302030f010c05040b0a030207060207030804060e0c060904051b030f0703060e0c07060b0d08033903 74
    0x103105502d04180c10f50242c4004113011040a810084040582d04c040d0210380d91203100c00d8450f8280d481081c030310742801500040e19411030414a034110204100d0f0b88034511200d4a6040710400c6001d00301c010783d030f80c0d5510050701d82d80b402c01c00448800b03030054803c140280743c01c54a4840d41d882c07540388203e004022400018084c148250040c44e01c5038062800c42224039006800640c2e11185404140d100340100000c025080c0014400c581da03c4406803600c40c00e00d843c00c8480240754000042c000b00b4160200107820018a4ad840240f81c00f512a440d002880e0609041500864610300c1c2e400250350b1160318010308035502c140507140c0107081110081000d41d500103a40b01c610319645410030044802006004001450380d074001e109149a80d02003040c15039640400089840580d00d1184c200303020020440824081e81104002041c0a0203204014000e5600c07005241c2c800c482e02c154103014030b006029801c0c610003201d0110081984051400c0c102400840f59901c005481c5a00d40c0302070341c400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216946474 1250 216945224 216945229
    0xa120608071202063a23071103040807170c153a020c060703090b0105010302030a021612110307020906040c0c060f020318060405060c030703020c120909010b07051002030402 76
    0x158000001d1080410145000f0183c1c940c407082060021703860b4030b0704204004003940c25507503050390081a442e5031918551a042d6090b5006007071401d402850b40800c00c00403c5450041100200418209000d954091a003c5e010b40c14042c0e0595140d1140d034003008aa11544050429181c070303010348941d1000303002c5008113055201c0f0744184010302111410b103444500d04506501074000302a80704142d51003580e4280b021001c584513940010480103140c0e0051095500c01d07409550f103c411404014905201030f00d40b601c26402c00d0138111000802e610002151590103108604894410310003507080440320307230001d401e1110061585015907501c809452055100c0d24207040760942240081000d2030442000702c01a510440f514588400c107807441c20040b03280019610701c241c1e0031030090207071600c60305268035095001071301010801d5000d000d110001e00b001d010510f802031182e0019585e45507010280504450b050b8440b075104c11040c0002400b207000070820b54074044844030300594a6070382c0d200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216947724 1250 216946474 216946507
    0x41514040e010612061b05120a0204170c0a141c02030a0b0a020c0c06031603090c05060c060f0a0e030a0c021c2009161809020a12060807120206 63
    0x141c4007450360a041c070000f000d074000744668040ca8000c1c4418006104142c1540e4001c4520403580030014500304004000381d06501d04107030700b01c8000f03680907250075622a00c03c50400840c02d250102ca4000c420703070085920b080398402004050001001900104820001d00140000316080d06030504c100300c50b40455500b03210001030b180d4050014246030a1a480160081d040325041400c14481d54900c0c000741d00c0c000d0240c030711030000134600403645540c00e2130031805060440c40403a0214010f65001c651a583c42001d0140c10f00010001d010a16107814031050714800580440e060300d1400b2070075602400044201c03400c5d080d081c20a20070301d81c3c0601c0450008852408032544641100d624001004400c20400d4855560080c1c818041c0c522042000700714481610b01c001056000d51240c4200c90144e0318003055040d00d200c4103090144d444001c2c3d002d83e80160380f400300048101c0d460560081c2c061094030050320b250ba00400041c1c1c02c4c100483c01d11501c0c0d0314040e02c5108040b071040603484c0060b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216948974 1250 216947724 216947741
    0x9080a1106040b0a05040f0605040b0a051b07060509031501030309060503090f030313020f0102010b09011203211b050c1f18030210140c030402060304051212100504151404 75
    0x211103541e0b14100c6000070042d070868080c0c25075000301f100c400946c0920480994040da401030031074900d0003d64000036509503022000d00354000f85616600c0d002c1c000c0a01081e0024070003919481d075034074a181c041504049400c42c0d800d100b055075200501c0072aa0109100c0103860060030a99600d40f200b84c14070b4a01a04039510080f00c0c0310000c1009450040d1a601c0003803648207840b442c13601d000c0000160700b039030b42c0d483c00729800c0510304004110740040110010244d078000e040c0707402940c0c016003001c5c5da01102000f10314402e54540a0300764403a803420b100c880c403030741d03d07454a1401c0c9131504130626140c155070070210810002c0c1c070b840d002190085910011078074913405000c2e031508000703240280d03c8103403100c600c000461901a05071401030054600724800c80b00b214860b1318554407982005450340024005540610a00d00340707403204007480000f0195195182614040ca2030301000e50402c414650704114016400c1010031a00c0c0240c1c23001a20a2b80d00d803a0000540345400400300303008000c0030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216950224 1250 216948974 216948989
    0x3040302102301080309090604020a1106180606060712081803070f030207050a0f0905130c18050c0a02030a11160311040b0307050a15120501150f09080a110604 70
    0x1c0b0405040000380307603018000d002c80318542e90b0b401181d40c59005040d0f5943c1c116040310f0000741203281030741c0109441c41e403a0800c00d10080000507900c0c07074290212459102c90351040c48040e2941800c001556110344200c5205203031003d190798880c810901080058144010600404c98520700c5120802d881180741044a850381c4040c1072100018204500a4015010380344c400f007901e05141c0910416a03c040b02410701017840c2c201014002e11000704021030001d0035580880001e103042500800612000380002140b0790f105150108449015101c07000e400301c02c101c860700468011056920098850070100400500c002c215400e1220540e18501c05444851001c8204800b0101c1d480c0c1d0304005075002c000e403000500078035980c3e01887c0100742d8412154a01041040d2401c0508009446c0b03901c0e120b01d0000b907601104043c0c850a13001407010400c00c840040c40b0359441142a540c441803032074800141e42ca8070359000c4d207a03c4040d5001d03081c020940d2a0100300e47110601140c1c0100303420b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216951474 1250 216950224 216950231
    0xa080d21020d11090f1207030f08090405070f020c04151e1503061a040e0c0a050d060f0e060103111602041404030c0b0106020609030405010525111c080d020304030210 73
    0x3d40000b03040d540d01500c0d06900c02c154204d865001802c0004144414011280040c0403880c00e50311aa805181d055204551801b410002c0400644440c000d00f40240a02d0720340349440b07620158007038180001428218080c1d813a1064000c59003040000200844200c40c00c0640041c044d500a5100c50981d40c10594080004100301400c01c1c6e030651260341200c20700b00c07180740e41c4140c5610344581c612582c030500004060510100d000070109000411201c42c3e0f80c10320340e2078000d020502400341c0d461a4044459065200707403c219a21548041642c01002403904200703489a00003d000c460280e543d10180003100b2060342c0e41103443d039a000c00b260348407002c50340d942c529052900403c0c890110302e08850044400e400041c0c80ca000280c000d0040c503c0310040c50503c0c0c28007004560b190082c12113450300303172040c002080c02c1c1c004c103c1c000c58000e8024000e1300740c1031074010b0a1004a01201b03191b0901810311806003004600320109075a0412944d00001d80e4a44560400700d140268210382021014034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216952724 1250 216951474 216951491
    0x110d050f070c1e0f030206092107031a060108070c060b0f060d0e0106060c050a02010815220606091206200c031c0507210f110304020a080d21020d 64
    0x4541121500c3e4299002c101002511900080c1620341da5110080d0882d6040c0207190045ca8058001140341c032502164011403515441d2082c40d01607598402e54a641088c0c107285004038404a03540d51041c0f007802c01502c10306003400c1c014420080c00c50050301666560101c28900d9030f900310344260110004142e507441d10700544199000303051050a1060540ca441d0000983e940640f007564800c582000c0500342041c1c042d0015160300d074004000200700b008500206141d035540aa042d81c041158603690b140f1089040f542c00c04880c220b81044092141544003009139200d0700340030080e00c0d607000c400410034040b50445c0b00291031030350307005035808140461820811700e4000302401054aa9842008103020020090700481d40140c40c0000028010903000403444900f40340381446100819001860340c071000c52100c11128882180c0354141000000d0105604d0021280d00140480c000070340b21402c15132402401ea0318000f0084081e5840702520075840034201c0d4144c402c0d80403a00c10074030a081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216953974 1250 216952724 216952739
    0x5030c03071a0a06050112050a021b030915030108100f0902060f07031407020d230706110f070f0512250e0906010e24040c08010312110d050f070c 64
    0x5010180440b20003140100182d4211440c0c02044101c40c0c0c180c5954041c62400c50005014040007060050065020403905604107010b401c0248121508000b03951110740d400100514082c0c3c640241001c0007041c03006002c3c80d04c02060300481d159006ea000101c00c070309012a079000e080c0500000c4d40c002401300e2200701e0401540b00038105184a40d803a42c619130610074404285008a1f800a5042f100d0154207500099400e1500b010392024082c501050000035440140390442540150000905104451840c2c1500300901c07180650400042d0085c942064030b046016403440c031455201e001000c070071070a002c40c20b0001301c1c1d0f140000340c46010041d0100150444091082c0324540220811000007083c5400210324181601c01d20400140181c0740c8440701950700440d075005003418040c0101e040c81c81d546034810002caa00080d03d80c51015850350404c55980d0b601e841d110024000f504e51120394120010609440c030700441c1c1408c079180c80c090190300045000715a0010013180c00c0200105006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216955224 1250 216953974 216953993
    0x325050907050a0801061e030b1c1101031a06160c080102030115080c070c09050a060914070f02060f0417040306020c0c030c0f0102060c07050c090f04110d08030601030905030c0307 79
    0x6050f540325a52641da0b960300031116425407040440d40c0000510080c1c680ca440303500040380c243c800070030355045001c048640a0740400800d5084481d06c130b440c100f4141c0c0f5601401800c0500e1850040c0b88891000040440c0186c0b01c0c099170403080c50003d0f80f03d103042094074045e490180c41e151000f1503c6e90b841e2082030103208180300c4c0440114131440f0000c1d00c0606c498049480043e400b4507000f007134518100e403910180030040c00f04143e198440a01085002e0288185641412038400c5501a420500170103402c0c8412030f8021030442d0000c40401c00f81c07170096800c2d07582041d807241c104412402e0710b00d2080070b1070081d03030002822940000790700c00480a000402c042d540b4070032000e4555140e101420400e002402e07180c80e6000da0014000201c01d28000006490b000c0d00503010713111860f00380f10000d0007024003180c61440c2d425003031040c44107200b80d2040400c23003101c003520407511002481e11100c006000c020155030400d40c13110268070402000703100790b481c8049250200d03038842d1441e19046641 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216956474 1250 216955224 216955237
    0x170708010b060a050a030e0f030c1c1e050a0201020d0f05091002040602100209030a021005030106090906140603040303060801051e1515070f0516080d020c032505090705 74
    0x65801c201d16040c8501c1c10404540b106090f60701c40ca0b103040c08065050f405805c24580000d11030040c80d4800c211480c0c103000800307429180d4400b805510720900f20b90100000641d4061040220703040070201c800c20503460542d0002c03030908100c0e85420038060101e000e0321810012189160410609698509850f00507600884515003955002c0c4400039025040b40118824030740180d20800030241864203c0d4010025068041c040c1e030f41c1862a0f40120750b2281c0c10010403400900000010412136510248071000740c01c10100500849240c101003410034442c141029118410000c04602094000c0d800003004220141c000e00441c50500041c20b540021241c107071854010300c00c00100c800c0c400c08040b16204d1001032450342c1403100e0168401490b0000c040460380c0ba0b060314081c4021030f03820000400e081010207003100d0b4103070410401ea81440380618944040d0b520070186103207240c0d00441c110702106055600c03208401240b03040301298840540c489500103101100f0b00041980c0304005180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216957724 1250 216956474 216956489
    0x1b05010f140a0e010e0301060308120108011e02030726011401050306102f010902010e030606090f10050a030f1101080115050a20010e010b0402070c03140102041707 72
    0x1105118103030300791588980341c580410140710070000031903201d01404500100c0803040c9403040030510900c01203421074034140c00659440c940890f4403048824500c40b06800b601c020030003449040c119829140b00359030300c0401e9115464020002415103881038801040d1661226020b0300c3d074071805c6d80f10b090808000e010356908003140f561301c00999402181124082d44014005140510650000b20b600c0a402410008814904581d65800c180d0000700e0203484e0011070000641c4005910015001091004003240030345c004034204410b640c0c42907007507035101d0390b03600c00e03507503181d40e00c4490044191407500003682c0841300300801300c18020303034414281100b880f039140c01c1a0648100c00545681c00244615200381c21010310b030b04001881007003c0e01d0b1495890520f41d0000012070401080080380703e5090b095695110021658140240554218220181c9045107850220788690f1038518540c00050000414a8540c1071540c900b5411200108801800d04401009461040c0c2d1181440d20400d01e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216958974 1250 216957724 216957737
    0x60a09090203030f181e03210306040506120109050105040611070203030409110d140f07050a05091c02040c110c0306010b160203010b0a060f020f010b01091703071b0501 74
    0x10484040d10a04481980050055080200165210680d5403250741c2d403141080c0b807400c2c82d051a0701c80300403101141d00d540c45025010b210903018180341000e41e044079040b4295501282e081d008034402245d03001300d01a50302040365620500402c20001109102c0142136292012030418040194880340c0564072469050121100710502c0301c2035030240e1100171b98950010801000031441550000141c1d8401d0b103107131402c0040103104442101c50750100d030001441d252003001004001c01c2c2c107503a407040103030810340d00300041040010014003a002e5a1401210144843c5812a8031300000c69211580140180300840507544020034801c20b5003034800d200c0c800c418000900385008a0141d0581d245250414106203e04160110710024201c050b80c141d50b8510182226445001a003005040b40e601e0345140e0031032143e40207203030101604d16030381c40342d15203800510140c0e4003503010b0041780d502861103142c0e00302c0d0b4140942140315000000301000c004c0140c2801c0024a0050002112002d0321541d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216960224 1250 216958974 216958979
    0xc02031509101503030801121502161401200a0908060a020a1d03030a21050f06031009020a1a0d0c0201060626010506030a141807060f1e0e0d0b060a 65
    0xf111910241c04000d0200d04004014080d40d00c05190318001c650245061020300c5000001ea04100e0b444040c0900d1424404038800b81845407945903a000f050350701d0001c01002d00c1c0320780c81c405016010540340003491000a80442100d02c00c16907400a0641101aa030940c10915030100003503005080344000b040c0a00d18068031400d8552540c61a6500034026500c1c051480c1340880d08903c0c039400c108036a050407c24a0f10300300d01481058030403984003400c640e003030503c18101480c00c998803103500c1003e82000c7c01c1400503194420701108a802c9030782220f6074018a0705180c03c60b40a01412308030034a251010840b206079054210300304880203511090050500840c0003001c502580da110172840d01e40d100100140d0511800440d48000321800000e032022800d50380e00701c411003da0307000d020300c6102840c0c184002070074406000101180e0030180d402a2000b040500f110f40240c2ca00c0300511a80340c0c5013682c0318094480c607424103000405000c0d00e500d8924040b24100000d4032610300410740c40501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216961474 1250 216960224 216960251
    0x6090d0807020f0d03050705070b0906010f0515180f180103061401052d0d0f06060f1a0901030b09010b3a0b0d06060e04051002031003030c0203150910 66
    0x1220600106006820300264050f410f1700581005405501041000c00c00b060100e155402c4a6005840703000c09802030794076244940c80c64140d42e03046940314980c2d04080042444501d0111128050f008950210860070080041e845c8103100140a820600002d805086010581c0283e03060380c3c4a460204003440e04a41000c020000c240038040d04a48035500b950002c2c5241c40605101d103da0381e500800c0d01d00c01c01c01007260400011800c1301c00c600d001c03c1c9502000080c3c020303940a0503442c200d240001e850941d41c400c200f10203502e02501c5000004101080da48a070300f09884128028000f000c003565200c3c0e00c0046030340a00003007610301d54094400b601d41c00000c0d1101c80c540c042d06042100104071016800002c0c52928140c0c1e0744030020f5444a0001605802240000c0090392138400a9243c182401030605205400002107184104204030003102c0315a442d0058a4043c0f626841002640c40428500b801405804035801542420071502c44000101000d010181040c14410754844452 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216962724 1250 216961474 216961483
    0x5010b0f09010c21052122060f0c0306031401090506060603040602120112020102060a06140103020a1b05012009090a0908070215041e0f140d0609050d0305070512010303030b0d020306090d080702 85
    0x18030080350031007c000181040c0c000f2003081c4000b4001d1200007028900154070a084614518000d800319032140b13820010b00101d0740269a8050110b40203000c0b04403a540c0705a121007004251a20940300440405c041c45125419140030241c0000c0d5074440b5611100e03420020070391490100e00502c41d50002030710440c201e004400481d00c01c555841000c0c0b10020055001e90003290f000c6080000c00e14402c01b030214402486240c0901400c00000c2941c0c42c5505031503608440020030802e45820002d0401c95250f1440c16680400c01940c0010b810034a4641070219103d8400f003c0d40c8014070070b280041d084c906200801c07c581010490703c03040d0104541e4040b00b11000d10804204c0002c4800030080c03901101c04120810303030000d201e07000d0340b01945d80d50707012146441d106030b54650200045041481d01803007495000600703809c3c05824a00348680b400b9055005000050400d52680c60714481501c944138050569580202a1400c902e4904c1d0025074948140303076440001000f810100c1c0da05c500204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216963974 1250 216962724 216962731
    0xc030b04062909031015320d080f070b0a050105040b0102060f071b0c0e07081302041a1815100503040b0705040306020712020105010b0f09010c210521 66
    0x5000455101008518020a811100341c05416006170203488955824920034030443c448400340d4060040d09100c0c405c820010510382d0703142d10a005201820001e005c05401c642c9481d0120f0369001c461402d0b162000315406141103005c0d0094004c03444038100110305044500c1031100000c00c00c026030340e5908010a036513803102010b001d6000b002c0400c55410714102d0481c0d100140341010440c40400014841030b840d012901540d10510030b100038401040e94070081a00032106c4c4c6071040450908030130618039042c191800038030841d920480414a508424000c044508005001000000b0f2112442441c03002c101d03203c440614162004064030300d410b01000c408000140d071603900715a10381e500c00c0d0010902a2150717003031000c01d002c000700040c01400106803191003490a040c010320203100203403d481c01a0480801180c3c2800149004290001035501048092070a000401030303d0030600b441c001c0134055040345070381c0000c1001c141174100b8001d015004004180149100c8103900030317078407850f054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216965224 1250 216963974 216964019
    0x16050d0503190203040c0e01060f02010b0f10030c090b0c0a02040e01020a050304020d03140703090311090405032209020705011410030c06050702130e1b0d0b0a020318010c030b0406 79
    0x11100060000c4043d4080d562061066844101e85510f40c1c5e003280404200741c0c02140050b1043d90600c03072541d428041c08000d010103864040606407240c0000b1038a0340302c10380700010503540711481d0100510408080004210700d08405942d65119810b654503840d8480081e80941d0400721070804010052007100c6440c01d00e95101800c43e20b8503803c0040380c0b070341504180e04002d5240110014112a08020724865200380c035a150340525501c0d20040d004060306a00340f00701c01c054200008a81d0100447d9520501d010000401e080e0000c051a00041c4d190003034450244007041010030094158041c071a2049a030607040d4040c1c6c1ca94040d90f81e03500d510300005205400c496000c0084a000f040540a503a1009141140c021400440b500488600080c0c08486602c040c00d902d0041410001c001c15103c410340350400002c21580301d2841d08180609240c005950010000304501c04009140c20b0400c00301009101c000c07842140140980600240320784128500f01001039580e091080164034154032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216966474 1250 216965224 216965251
    0x9040606020c030d080f012903010b121e1f08060405160503060403090b0307050d090c05010f02030f03130c0506041512140415110409021207090e160201020f16050d0503 74
    0x81180840b0805031100c1d041040c50b55881088004048d031030050b40c040c081c1d5020240d00c0d900b1035204003041100c0039100d491180c200400c6030a032100002d007400c0d40140d648060050303000c01c860554281c0d6101d41d2108060340a000240010080b002c500302d41d4170f0941003042c149554940003015101d8000b80c80060100354198003c1180d50705100166501c175160382000307400e11055500380e509942c00d0303100c03c4503900c100c0c0000380050341c0c002c07407004242d81c07a030f10045050820069403844503103c081c01808000f80d60300388110801800c014a0400341101424070b984035a81e44a100c49144800029400420a0060554500d02d010b1150b00903241d8010f1180f0f2841d2141d443d28074124400301d00445025446640850b0f00c54440802000205044d842c016030b54062480d140d000070f9000340c07000040041300307070041142c41c172001800b42d003100410b140886201001030b416802480390b0394541c0f50180005c240300805c00c0801c1c400815190080b000c0c0d51501580d064216510700c0300700c4d6404240303800e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216967724 1250 216966474 216966479
    0x6040b011d0409150c030f05010e0c1204030923040e07121103030405030d080a050f0f04110d0816030e0402040302030303040b1305070f060810081c030f020409200a0e010309030509040606020c030d080f01 89
    0x4cc02e80580d030824000d08207810f20740d4581c0703402c0c9240301080081000c0074506001030f088505080c842c800000020303401038817601c7d003022030105882000500c003400c04500c5261009441d9002e10441e0000c0000400f141c4514540140190a440040b900c290207186481c00040140c0008413229104200c8050030780e0044da5541d445a0344135054003401900401c402c00544002030000700103026480680d100349040c1c07030413842c005140800d0190602d006600600080006031000800e5942040c0e224008003d03503982c0d4415050794440804000e040340c8180c020014007445002c40f6001a6203e640d581040ea42d076040d00601c294140d4030032041c66070b0000c1a004a500720450303041c01000010f10b804541003c22002003410b82c4c206811603950f0b5969104003042482500c264810050b6807444900d0800c18058806807000d03880301d02913414152201c050034105485002150182a4014020004140c562100a50300e80348480c0c01d500070321804009240c01030040c8041440f400c3c0b03c070314088940c0e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216968974 1250 216967724 216967747
    0xc0c030f17040302010f0609021315050d020f070b0a020306031b0d021e03010b030a0b01030b0c0702031905010b0f210f060109020306040b011d0409150c030f05010e0c 73
    0x8100504032000c10000703900010090000c1240710b8040d0b806903001240c1d007103480e1a008200c91032540000000d501c10002e01411520403051102141c4201d00401d07030340780046006480a1140e451141421440054601503900340500a06541da008490094071540e61040318401c03844252203142d070640c000356000640341d90801600d03141002c0503094203401c500c564042681801040180c00b4072801601141c0744504007449210f040f80d40440060030031220a0b1510302600c10107000240403003140c0000070f05452199400c4800da240d01800b102ca004603024080c0c04d0080701d50204a916500b045005070b86490040300300181d0050060201080280091542480700d2050319018903501070510303020140035041c80780b2402480c0c60400075950303103400000c03c4100c490b00800301d81030001c2d00b107001f590406040c603003201441d0207580005080146090518080d002e00c101c020030a030401017076014080c5c0c95082000c0a450502c000c2c0801c1c1d1b20360f4480d6800030412111140600d4007840b00c00300c0c44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216970224 1250 216968974 216968987
    0x20715111206061b010b030d020c0a210f06050915010506040e0a0902030a030f020c2209050a023304300b040809010f08090d0c0c0b04061808010c0c03 66
    0xb003004100d42d190600c1d01000340c001c4040b0b600c000b11641d40d198a010f00506050004c9400800c161018144203200000081d484800d01e0181d20168001c0f58404001c201d581007441001c00c4c1c00135950100c4a480340340c1032000d40400c880180450141c4d0072406403442e140010030f4144c1b030008000d036050a0904040c00741c0f2a4009000750f2189844002d54805a20f05100e2650014041e54401c0d130000000d05010b8541710500704040e000c3c241c800d504201e40e14140c0540301d07400000e80000f089041640c20224035003010310704040d43c42402d6600800020040c01c2e1000800b640402102002c420342e00d400003018021841000300884400307600b18010400304030411000003660b144022050b50320b890701c01d8a44030413102140c00e10790000b000c0f4119a007204140c40d0640b081e00e042a0b041c58098441503c42ca008081c01c0700b40201000c6800030800d80311403a8010b0103034089843c0e00c175030b9140b40091140300c280b000d0044c40810240003041c4240103001d00403030f10415480d281c1d40c84c00307199403c4910 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216971474 1250 216970224 216970231
    0x50d0302011107080903060915010603052a0c010609090503041e09060b070b061e060d110f03010302040606110303010e060406080609012703090b070501060512010207151112 76
    0xc6558071080014160302220141910310f00071032056840342845030038145409406803520300950720104100075604031417080c1a040d03481518000c903241d210840410400484006540c42096041c151b10803180749a40107020f10840d4200240700781913464079058119a01054040c2c00354000f04014407010804400e170b0144c0306140c81091080c280c0d101d00000864403250086e02e003243c1d0003c2e83c0c0d030600421f0480903401c1382c2c086a64208400c064400090700710400d24145d03000f1030b8081240409420b10368010b503520703440190081d698a4841000e085d082d40f09010813071145280c16404035521b8400d9025502800c500d000642c603507400c1813246e90039400014141a406506d44401140041c030030320903680100d820344004103948410128000c1030242c40c01c0c42c040f03025900c10320840400d510801740c1044941e0724141030394480d00b034141030b8050440754012581010021a020007201015070080c45818000e0b0740810800030344241040641d44c9040360740310296004c2c0190600e000624510300d41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216972724 1250 216971474 216971477
    0x1060c05250302030f010204080114091b0111010e0a15060e010611030906040306020a1409010903080d09050d0f140a05030a020a020709110904050c03090d08180328020c0a050d03 78
    0x1401c0d03a682c0e00080c900102111801c0132a5008541002094400d000721013100341c0011940565141410304284e41d581c19081c5e404440000301c540c05410390007103616400000ca03500c02030200aa2941109640720701000c1c0c203c644072000400c0402c0004c041c0b02d680705807252022105400d9207007100880340070342c4400c0c081515001c200040030540d903903040100000c5209001c09a180c80451001410a072500868150130120402180507280e901c01d12a4090320b03841138a141e103410715881510010000305000400501c00d01018201141d000000c441e02154156030b0401c214220260300e030054040d40302180c000ca01c051005c80c6807141c01e078018201c00242d03481290081c0c0d83e6001c1d1602601d0407841507198242c00002c0708000740c02c0c5800348541c800d007080c04031461070402c0c21400382e4844110003c60308000544002c00c21100040c111070507881105000c03280c5031880e60342c10058000041010965140c0010000b00c181400814800c5180e500241001c4800d480d02041c480d0050150a00701c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216973974 1250 216972724 216972793
    0x21207081605031c050904020f0906030a0605031902181801140601090e0c1e0f0309031b010b03120c01020405060c030406020607020a080d0f09061a0901060c05 70
    0xc184a0030006030103400c9440340e001101038039003070602d0305015200e441a0211480071400c00b810907003003011120080d100741c0d8010303034079015114128180e00403502c60b260311460000900c00140e041c0e81042d0150741c0100c00303940c15003140c01d0201100100e4440029000004600e00801c034090144030190b000c00035034044054a09001d00340340c01c6075100003451641070241010700046503070200c002409480b4500e13002030b403400c0400c50807940740503800e411030041031001072545100c0d140070701f510034650410500c03580b64204012415140d421aa000106c207250803426490040014010900040130241c00b0b0000d109000c1c103403400c2c0358080030001202d0343d001c10001403180c03aa140141075107240e4001235515582400030080c00d004010307080000310340c004201030001c6201c1e03c048a01e000c0003008009100c0c0d110311081005403103110800b0303040e10303d004103c48000004070040c40c0c10040464900e46607a0b200d18043d110850038240c05002a401400441e5500b841c001041b83e00503948440704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216975224 1250 216973974 216973979
    0x90f091a04020706060608010618150e15070308060d02090402120102090a0b0909010602010c052704050106050702090721181b090b010c1205162102060f0402060304021207 75
    0x1c05a0340f102c08210355003640e6240802a981d40105528054105880c0216104185036003e000c1281140a1050b44080c4285003182d5a070291040200c013101c0505105e550014040c1c442c0000d42000c0c0003174011514560004a10345008802650b1490340105800b0494440c1c0d002d00130b105200700903100032503608211031603890340c5001010005203a034150640d034614100707003407240c502c10680c001d806680c100784030b2a140d0f58010f01519421021100700066001070b488858581d1a210f140d0960040c0c680400441c100f82d01c107000b04003450082d03a10074800e442c0e40c08221007280c2c1c0b0030f5041d001c1c1914202c042c03d0894107500320f01107401c240e031800c241e02d20b01d54132a242e01d082a035810344200041c1500810111009000e200e01003036090a00b90300d002015280c0c2c0c00c0f1102c904a01508003c0001241440d00191055840300140c02810140400c0106008030030880c03514030720350740035105220004090b1801d90100074400c80d070107800b0a04584070713a801d000c241c0e00807801080c00c502424101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216976474 1250 216975224 216975229
    0x70306030501180219031707060f0510090c0f0e040f02091c020111060c030f180d020f0714130207031707020616022109010302041a19090f091a 63
    0x100c440700050f9a11a911001d428030401600310a2084a64405140810104007040380111100254084050415610301842c40e2001c01040c44031803028030a4a464144150750036000000300550f841101c3c104000c82d0030b184c040c1d408034a66100c031400148a58910080d030304054004240300c2c19152805402e00c96500c0c00180324140c244614140e0f910f00d002003509541e44002005404d15140d40070b454a0f090036140010700c0d02c4000d000c610031250703081c042044400759190303990700e2115030400e03a01d071003444030802915849603100e08201440380c1200803c0501c070421402551003401820000340018410040300607400480040e42071018501e0b01c4024480e0a100c8207104600300da02804040c509a0079442c9000480036a020440d80721500c5d04104081406004110b010652101901c3e8440034004070064032882e0400e06415940900880c90b002c4500050210b49c4081920781c000031505c20300894074104180708100d0b01d515174030010004030b40c407580030980614000c0c42c45104806000b01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216977724 1250 216976474 216976481
    0x4030503220e070903110f1c0c0b04060c060c020102120f0a050109050603030315040617031201061b12030b0a08061e07020c1504080f061801060b0f03070306030501 72
    0xa0440904495003076400110141480c0c500140ca5090004912420300c00302c001c002d00c1c82400020009805081d81c0c014580e9035081c034914000700142014280046145001c8442c80300e4003048649034600c001c00b0a07440c03407650546c1c0548200ba5242c2405101a4035400f01a091b0b041004082d5503082000c9203102c0c0005803090700c118039040580c6040d00305aa230300011600c0c140e100304010b40c0b51005114407660044100c81d08000c220b40503810071108240010000c001c1c1d9840507410800c0c81180000c0001c0100141c03c161808000c1c0d001940c0e40d8280a0364980c44000c00220440c1001000b400016040c840007100500b541c6030024421851401042903c3d8140c0c01c800d5a941c090800c00a040c200d000c0003107501c0d01501021045811b00b05400780d9a003031001c650703e21800c4000d00401d040b180d00300580e0000d25041044450a400d01d4400a8403414180d61015403c44909615144401c050081d04200e07400e02c2c9500e880c025040d81c8200c09a000545000c0800d5156240000071450901 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216978974 1250 216977724 216977737
    0x21e070804080114010303021207030504050d02042901090e060d0f031205040f1b050906100e04110a140c030f03071b051b0108041a04020d06020706050f07030e07050f040204030503 79
    0x4c0310f1126a504605010380341ca0019100210220000c00c40c000c0042d60040559003100d505903189a2000700c0e42c4005009081400036106060f00440d0490300c80729004003410400c5a020780303030030603016141d43d603040c40868100c13081030b081340700c6031500c3d00040d2010181004842c080c0c5400d05020a071440c0c0f14040d104141c80564078681c503802c86009004031040c010400842607103176041d05c20b16120226851000090485100d160b55041c1d11120343d0113566001e0f07900000500c200a4081600036a1503142c2000308600b0024250120256021055108694402010600450400d8009504603845078001001d550411140517018400e070300000d81c0109500b4483c1c4054451a0000500d0080f80c08060315090304220041007400082000e2142c400c0c403c800e00840340110303a42c0e81c004600304841c41000141443e10004400c400e01002d5030115008900307102c7c3c10a030f01d4803156011002d072800e1000449041d08040c40402452825580d54040c00c1c0f0302030805400c0c29070306d4803140c0c15038020780c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216980224 1250 216978974 216979001
    0x304050f0703151406030c0f0a03050a0c03060c051c09020a0314010501031104060308040e0c041716060804021e031608010209210607030902060405060703120f021e0708040801 77
    0x420307912220380c0c0f1500403603030540d0084848030003d113008800280d0781c040c81c0072814003901c0200c85c04041d0b902c81c00c0380c1d030707003e940c1040854440034030314076028403294901e200c1079988521303110f0303035841403440741c42124902e042890744410031940903114113005001a000c00c03a408801c8000000010300009003c0500103507035000041c0300d600d0360508100d030f1440c1c510043e124524040d002e1001861940564060310b004c520084010741d500c0c03086004501c13854200a480c0c0005a0490040000c00152556080c0700040c00004196680b0f07016141d01341c007580d000307601a81035102010002c084692080124100600319030b060002d1014184900b01c2e650000c1c1d4551f5000104042d081c1082c8072514204540d0011030124518982c10b060b0703c81c41e0190280d410551500030b11702c2513650304800d40e0f000d1702c8000c007156030306c9240386809004004601600418641018501c3c01851014800c0e258604684040d146079031204101e02134055000c1d2004841e145014080402d41c103409104441c02144e80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216981474 1250 216980224 216980243
    0x519090303020d1506020a08031008061807060201050421020a080a0215010512030304080a0306030c09050703140c04140409050a05060f0903070323210105011107050a05060304050f0703 81
    0x155a40b026582e410722603960411140b42c00304409940094607d0341d4030381003014141c4986422004004514072940280e105115079014040d6100c150071405040940702002c40c0c2c1800d94800060f42610000c403405410141c43d48200594010000c9a0740c402c5a0107105a0b0103001a5a40d21089500544032040041c0e101201814110091b04000341c013504040301ca2072001c80c100a9003541da444010801010400042503040302d0380d000f900321901956112030303410001a180c150000c006c104c00c031034201c002824222095280504842c02c0740c01151804141c03480c041c1032a805494400b046074a450700a903030b58162001166051254900c0e6902c03650150926040440c00c80d51210b0000d01001c495030020031040001036080307000e4151402c08240c01850280f0b001c0700c1280c040c0900b4005a141400c0001c003022290822080c92381a99030903241d07080201c41d1000c0e810350302d0607580500350304240707c041c080c0701e03a180a0000d560301610801c100c41c080740520034260700f071054660044944014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216982724 1250 216981474 216981487
    0x120106080115080f06010c4b02011409010e060301090207121706040903110f010b03011109090109020d020c0307140c060c063409080c0f060409051909030302 69
    0x15000101680310035a407403c00000d003061807101c003051101520b55030510000c5c003d800d003080361001c901c11007400034440351004995001c000341d204100c040000d070031350b0700d12030020381c00c47c600918401c50064069480c0c0f521007009660a03566a4440300809050001c0d001c0e12441543d40d050013980644900400540c50750304c68900010304207189050041800382d84000446a000888110b03513102804840100340346900f400c05541d82d4521914810b06400b80e8124031050000541003484036203001c0e0020800041c4005440d2014011035a1040c0c0c02440c10b4010090303198560040c1041d101102401031401c215070100174131750340c800901220321030318002002543d04804c0c813140b48000710a955003440c00200344001526148020329140201d03502c01440c0c078560808c0c0e8032000f54502c003405000007110084902800e43c1c440da10420006104011802c0c045041c5207640040d4003d01070056030030682031602e030304043d0900900d400c4603e007208804000c035040030b005c0c4001d800d02035180107070f4551 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216983974 1250 216982724 216982739
    0x40303201614010c090801060602010b1f0e12060601020d050a050d0b21070303081005370801060e01080f0712050c060a0905010305060904230703063902030a030906021201060801 78
    0x416a5100c40152f926009641c1801d03283d0982000307090900340c068492007900100306a03040d1250310f5105030030241c0d103601198100c1c000261a80030390400d80031550354080223001162188603000c5000001003042c0000b8521003515008107840410003004400c2d803910110380395282c40c140c00080c10702a489140208285900084000c0c0c100020752850303070886007000003003840d0b40760385988441d5901c00740410000c2082c0462041d10003c1d02104134441550340da002d101e010341054040c450056150400005000c0d1001403410307807000504001d4004280340180c00c2d0110313006500140d811340503000c0d2088aa5480100810023202c050322246d40407400d0100050032104010200d50207140421306202c0400c00c4e8543c001c0b000303030310180000f40c000c2c44007030060704181c0e203903000030480740c03c00b95504400f4100c500c0004c1c3c08002280c00002464103401c160510700003600c22403001d40c008000506581c0c4c466040300740d040340110005854440041281900024264007043c0001c01c1c0c08010b00c40803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216985224 1250 216983974 216983981
    0xd0b0403140903070e0405030d0e06060301060602012906040306020a0906202a0d08030a11270114030a06090c0309030215180a0803040303201614010c090801 69
    0x9103204601e414211101c0101c0e90302c101c04d00410200708003d40001d020000204110350b0f515000f401c1c24890105092070150f964002990500d100b035081c0807020a0f820310500c55280b800404955402045c100190040f0703261100c2400141c101104102c0440400ca484c002001021401c0d40c03400c1c5003525205004040400e10f811540091500c240c40001c1c00500081c0d16070304000508044034041c1c2c000c00c0140700e07003a680da43c481c0c2241a03450003901744500301c0701a5104d00c190400a2000140c510340703602280c4100880e04074128181c2e0542c202c0d9074444040105020b806041884143d10451440403964004480c3c40c00080d4580c601031104c0441801040c1c0c0d600b450382000e2025010b65070b4043d4643e070310f19905084154080002079202d46009c00c0c9940d8039507050301139440c1e40080d400d06c40384540c022071303040d0042401c0c408003400352030b0704130303003c00c802c0c034540b1074207030400702c4514032045100386240d002c1e81c9500b05684100c45100007842200145946a15102009842e0545c4503096 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216986474 1250 216985224 216985247
    0x161403070201090b0a120e071809171e0913141504020406050a030e010f020307170606040311010302090d06110a030f150302100311040303032403031209050a020d0b0403 74
    0x49907000d00a00e841c282d00716011b00301018080754041400d0701ca050140b03180800f44c0c0d11440d42203481040052403441164441c01a07240076200c0c3c0f01c00760202c0d201c1c2c8a240d10900e490039818503c5000d030004001080006040d6142c0002e05070382c0e464a1040400301a10000907551350b01c01100300c28400d140d4600c034401821410266810745c1064030b030030001b070b250f4003401c64480305150f01d61642c00302d40402076100400d0300c884903d00311744a080141c4020100c4c558240084503544d000000702d2414a0b004003a541103941c000d00d070111110000c001100a07400c9000d001d034010009044003000170303065001d04c5800b1720101c107606849225031000201070b10000124206410b03d01809203461500302d035507541c140c80d01900c0c0310354511180d081c12001001000080c446144002c1008020180c1c560010188200d2030740c14420040741e0f00074100e060f0b41c41407000401107400340704980c0a1400c0c54010074074a60140c2c06869914083d90082604071050240c2122400e0308503040004040d002280382c42c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216987724 1250 216986474 216986489
    0x51806070e010801052101050906070f0203040803090d0311010c020c03010f020c0604110105390303060d062409090317071b0804050402070302100c030b130216140307020109 76
    0x201070a400001a00b40c01c410700540d40a0008083c1d00c07a100c003440c2030700d10311000340380000700f010745010b0102c1500d030441502c0340e80c00108042001d40b02d251000007a1030680d00ea840c055442c108074030080020780c0b03070a0b610803400e018480780e180d00d01c204284078140b04120b00340c000c1c1a8030380083c410542107960182003800e5681c4180060141b008002441e00c3e8065803182c3d0b5140004006001650070340902c5041300d10504030740315101080140030403000340900c242c060074606462246a00350b16400111185a081020582581e003c9129500b00e49078111000d03280040510380d07400c2c03120a00c6120f0b08a883e145481e030008404041d4010941e20940c0c0d5803049c0d00300b081c148414018000020782408102c038200b0059406c090001e02c0742101c00514008004540c0c41c08545030213525405140410103140d45050040f0300d50381c2c003c0c05001c040900050043c40180c1c120a03003000250007003403503240e612075021864000078200410030001080300700011034550303c840c800180080d6450b001010f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216988974 1250 216987724 216987737
    0x180406060c1703040201170106032c0c090a0b0604062706021225030f020607030c0e190e01030c090605060403020d0206030402040b3601081905010603020405180607 72
    0x40105184450704425080c1d00242250f4a40380d500041324090049440c030080b0500e01e50000a210b90164003619001900707100c850103248500146589219a4420408694002400455080c50300351130280d0701800b4040300003100d414000105120f41c005d5008940400c03150700e400240606540c100e10006002190b1507113550b0f080000007511940e14840b100070103507000c664005440554803203040d8560840e41e201a104c22a4140200060300310000b80005d4021100450320061081c02000000704e0f5507164801d0500e42d83d401d2041c0410041020144205d42c02804545500a00e07140760003540200c604000540c103202c2d4000c1164000e50105201d140104004c10040c1c43d14802c42d20590740445080352280d03258008240585a405000c1b0b0307010710a114044441840d00580484007846240404100c1100030030b8800d10250038058003409505c0700303045c001c0c03281d105610003075014825000401d009990b54045400d480042e5105900d211071501240501f80d07080190561241984ca010b2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216990224 1250 216988974 216988997
    0xc1605060f0f0705060403030c17250201061e0f0605130605030c1204061d0105010b0702220c05091e13020a0e0607050c011106041a0a0603020618040606 67
    0x9030191080605840d80203001060810303424641000399140a500724081d600a45002d180007001051442d10300e0000c24403104c0d00740c0d80a000401010301c12100b54580301403000c3d030150011a14403144081200b190f4840b140441c1252a4a40392004040b42451013101d250a100705000781140e56001007041003000c1c00310110f0b02000c5080d003800ca945a042050b40e0f91150141c01c1c1d06849820392600002013000103000c100202a4821615445201c1400e041d941040000600b650401e10170740d02030040c2032100c01d025140111144041c40c1c4e481c1240760031541181244000c5d9080d2100110208401107440001f5040014000a400130402032081c0c0003d2040000381441c3c1a01c20390711452540407400d400c10501454060700746500c000d10300c0e61540c8031458a0340c0d54048801a80d0b000400000b132520219900264480c002d41c0d110101c40f943d65503ca1211070b408000a0032501c00ca80c80d40000000341e02c88100501c101011400e80c581c403406044284800e9841c44d61001c0c08010b507400d0305e0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216991474 1250 216990224 216990229
    0x190507060906020631080a1d06090f040b01030902090403180b03190905190c09060801050402090c21010b0304170307090501120204050a0f031203020a09060806120609030c1605 77
    0x10301010017100c02d00f5100f83c04108800c1c03031616a0655008200540001c1e1100e05560092890100d04d1180b901401d02c0903980c1c0207001c2180a48005a6049038809520000c0c0303182540000340d1542c1c06250000d841c1c0758170703000103004500c181c4065012502c05580c0e0990601d45149848c05800c0700c0305260b107981040100c800c50000301c1c0405480c236956902900c2c01b003100c14040d007111840920a100940181f40c100028120224440c80030301c5071030710f0300c0000c0d00320060050714440c68005005a040c0e42da0945019140e51119010401300d542601000d50009510180c85022b0310364185199182c0c542403421030074846400c1c140310a444c034240b081200c0194444400801d40d0004e18145001034015039109010b400fa58010b0f6034040400c51010440e01d40309850308003124040c980c41500c41d04481000e50072449250403810020321201070520880f80601e071019041300015002e40c0003240d14205071407e12109544078041d980000950381214541044615041031134010b0310302055151400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216992724 1250 216991474 216991501
    0x901020a140307120614030f0601140616020307060e1201050603100908040b0a020a0507140603010302040b060d050c030612060c07260a020106030606060c05070b0c1905070609060206 80
    0x30301c0d100160008002142c19100341c01c1100d00c24005041484040c0e2201d031380d002c194441092682c041d03c81c005119200e03c030000f0304141240c3c1505c8000b01c801f0345000501040381d014201103464a5400c044030001130b01d0410042c0700401c282d0342c521103841a59030801501030f21240d4039003003583c1803034148a029a008640200c41480712680010082103d1030f00700160300035541706002074030010500c010890b4001c681802900d201d8000c0d2102c031030300c0700c0c0100b07001031329000120342020003440180014101580003103901c0b003004006070f0130318040142c1d45080c1d8000f1542c07041458004000d00600c0c0c20a8140c4112846a500142025140031254244035001318000034042070400592510280c52803681c00080300c120050303940d5142c03001400640607100f41e10044400720328002d80001c000d0322501c4614406075110025003441407501e500c00c44d442c1c010711140e40d107034000c240850300781e40398091002c91500d115070007030900c8508c0c1c41c10241004015502160940d00250108a0f02422425 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216993974 1250 216992724 216992747
    0x1a011d0f120607090f080a150b0d032c090f06011b0303140f040503070f0c1805041e0f030c1505010617161704150203070c03080901020a 60
    0x50246008140810000d045140c48801040d0031940700c01910900e07010209100744104a203864206050f5a54000405500418821080950085101c5000148000e060007400c85c001a80100711105640f00083c24003000c41411004107040301d100901d0b5040d2208000700c58029a040302e4060070180740480c404840c000c0000301d00605c5800081e0340d40c0e00074921040389400d0207006020780703803483c076024004000ca0709406081402280005140d81040351440b485540d001c00030b90306203041e076079400362076016184040361906010072000c56803250051200210241e00360002c141410213052680d4150104190280749080001c5050042002c454244d16a5076051820f0800c03208142020f0381c01441c0c4110703078001caa080400000e0340302c0c1d010b00308140c48042180311000079101d081002c44190040d04501d07010444a11405503030318070344401c40d54064015100d12030a014100c1c207134822680304a8103040424101e403032071700030716511a420703584c0845035500851910050301c0c1e02805c0854640f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216995224 1250 216993974 216994007
    0x141009090507030501060b0c1612030503090c120a060f060e0118020f190e1807050d0e0d0c03180305030706090201050714061b0403110114040807080102030a1a01 71
    0x14a80042000070400400c1c0c015900140200802c40d11004801c18a41c82254004814890b26000a04155102082208070380d4950042c1c1d030a003005d9a401d42d0241c0009004145c03e0041c02a580c280703441e09107040900241c02d001410408040d880e00d901200e1400110802003458400e05204003002c409503981500d071a0b112800744025904070081c040c0c8164050400005000710301e0404200300c0545035a6038000946540c14a200c1843c00d0018106031011035105a00e24003000c01d140341d000b03d0040600002070400851110799003800d8915040ca07040081c0c0000703800e41211418180e0080303500d00910441c541c11406d062071b41d25240d61702e0017450000b5100554480360241103a0188003141c05541d40a850b140a9000c04251540c541e801100c0500210109d0138103020081c104504440a59074000000010790a0180044810700d61845904028180421004c90344540800c0120010210b90002583d02c0c9800340c254030a1783c001d0744040b0b50341030640d44004801d03030300702c144840c0b055400f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216996474 1250 216995224 216995231
    0xd05040503120c0f0307030306180b0f01030e01090206040e09011103010f0531060614090901031115030a05070306060e030c28030b0f100609030b0408040312030e01141009 75
    0xe203c4514200400080038248611001514400301505a00258101d80d040ca190000c40600e810985058469182080d60301224608110a00e58020703071100c2a004c444100004008160b03501044840e40319802910040035071100f0400409001d00650146801d00d045150a65140444100102c0b0b0035015451089004001801c2c0100e0301d6510300a404050301d40100300d910025242c400142000d001c0e450010b919540381d040c0c1c0b0708210302200d0320410090007003001d90703203103131547c00001c03208007402544201e06900702c00c880341d6400e02a5021b14804d000000c0c0d6420a20400b030102d030700c164405c7d070038031402101741a4190340218040e111114207403000e20340044000c41d002030b800380359002100240038600c030200c00d208100d60000c0c4541510101039031300b03803140f540341c8580070104e104510004161140500010b405c040c645134000c1e21a0403402e0900c0e8890381d4202030500c1d4880101c0000e5502d03803500c03c2c034200c08d00038130469005080d2111194103202004650508407401900065500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216997724 1250 216996474 216996487
    0x70f0c060207080f03131403040b0702090613050915060d020a06081314030a1710060f1416030206071d011d191a03130b070201020c0a0c080d0504050312 67
    0x983c0100d42142e500355208541c0c03803074026600005140307007031070545c0c1c1c0310340340400000340d40300c00001c44040c1c03038a80c854075050540c180e00704100710350001c1100f6000040b05a000351952a00e001d0310f400b420303003c40900160421081001e140c241c00605661081461568907000343c0c070307070700071a105036012844c0000c82c0d9582c1c0810565003c8000b98020030b0f60813183c501c265046000302c05071056103042d69401207883d0411285034411407050350340040c07001c252041001200e00a0007900724002d55030400159004020741d00f0750254028541104100e038150980c6010075a0500c0480d900002c0c60820300d5000f1508003040180c003080400a5050004503c1c61200c0c03048504841c071981c15009001800107665207140c000790394041d114600610001c078200902c120008030940303220300140f80010054403420780351419903000140044055541c03c00c2040100481408405041c500503044000c402c7c2ca001c50340351510880b0443e00c130800070140010b0009940100e000700f201c3c688480150340343c0b031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216998974 1250 216997724 216997733
    0x2010b180402011806081b0906040626090106050a0803032e0e04111009180b0d0b090124050306010e0705040f080615010f05090108041401020c0a0b070f0c060207 71
    0x750420740036104807013140300040c83d141d2140d8518401c01c07034500400c1000a085544140c94000c003d0505c0e80035406010501019125644e8041c40d12508184000d04490001c032180c1d4001d4140c03840e520a035180c40090003217082c004100c000900002005501e1031410300c85032600090b60203034003500100c3d80c003001030340380321003d21100213400d032102c04141a050610784084514040742c0c800c6d001c0c1e0150501e00340301e80e020f040c040c81250350020a010b400c40741c09200100a0840c4189660700c005c00e0701d280000329050405007403203000210000150041504041541008102e5880c4200d0705040d800744180d880200b2002c0c1100c5d1110140111615004001d45003809071303421800300b4100040740007402c20000540c45001c4c000fa01030380c20b020441c6000443d10707900280c000002262082200f4800ca502c10303d0700e0341e4001c3c0030381c05154154095501c480d0a90b88a003212050030380c0048400403d00400440c80742d0004014188180041c0c01d45030050021001030401030105071340821054280b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217000224 1250 216998974 216998987
    0x120903050c1002070615180b030307060911030106051c020906040e0f1f0204030b07110f0601080d1701060c140106030f14010f0605030601170304030b010b1902010b18040201 76
    0x1035401e401034400d034001000800c0025008514155012402d2000d028807100704486100242c41e00f94224003035181001c00000044c1204200700c0b60180f00402c605008103580d4441c81490901c60401e1640c1c9002c4031040500356001904a40c0c0f0860065124400048480d401400da003a81076508080c644d031010009401403034100940d11250058201c50b183c0c88001003005080082c0c959403500030013008454800880c01940001400503030000049122107001703c100a0140c01d6600c200d5007208000060765007812800e0740b001c7c900b90701201071404006d8104981c02031003180c030700c0c82c0341d000c0d80342c010014590010b18002a00d014040070b42079622210a42085000d035412014401c2d0300d26044c9008079000c070380c000c2980c506518281107407040180d503010755011074800030010481c4c0d9080010085088030b41a007008240e01c8200b00010003d040b400300c0034001c20000203c2a2a00d2540040010130024a0030b00021a4940810710040ba40c0d514400096001d00814503041d95071030744016680c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217001474 1250 217000224 217000237
    0x103020f070602030601080a050402130e0c0a0f0602010b06070b06010e12031201260c0105210108030405030d02120a050912030714010b040c05040b2101060e0f0604030312090305 78
    0x40800004515050105940095028174000c5c0d0700d0726001e54650501c80d01f201c20640300254805180c1054200d46801d50304240c640b0142042a242c1a140280c00220000001e91140f51949540030342002001c0c0c0a10902035210b00680d155441d25084d503460030411a00141918144180f040c1c041010f03440e00050708610800b600e08403903440d102480c1e01e003c0c42d0800d05c914550400a21b0100458105502410410821000050800b102c800005503203907002503106401034003114104241e09078058800394002c0a052001c4d60340c0300e08002c1454280f10008907003070150751100c507106030850800360440d542d10202c0d02c1c00039142c0c6000400150711b03110300a25034960b80300200d036501c10b03c42174144002002d900d210081006858240c280001e450301d40c2105000300300c003407004001500d5448000c00078002511007040501c005446c10381103440081e0451000980800031840c05820158404407003142d003180d040c2e041c80d2840d03030010504010061010301550703e030b004070410503019000707030b422 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217002724 1250 217001474 217001497
    0xf0c030a020601030b01120f0b180a0f23030318120708030f0916050d0606090e030a020d020705060f070303140c091305070f110705031608010506010207060e0f010302 73
    0x166805460030003580c9890a02054449070742d00800082c0c1150280d000780c541710761211901e140c55a02d5101c489a50358018401c07070284001c0065143c16000a00820748100e1083c0c0c1c03d0352544085041000741d9007880c03140054106801c0011001c1d048001050300c0d44900001d5030b0305110081c058405052401c500502c018080000c1680701c1042031140146200703800c1420045070039a11510300c1941c4850101d0380101c0e5184c0c8031406e0205041c0603100229071801540c0128480340d80303101500403241d807804040401c2d0070100b21400c0c550342c144144582024188014041e803410040021030b60f00c26403210506040300011040201030082d003002e40d100020300794018040c03a20304d0710b001d81a480005400d101e0b000302a461300902d03c1602c0b80c0750040481c3d50760b90310042483e40040e19020040707180a0440e01c1034602c0002c080e901080102c2001c04052504070140c1c0c0b400b010942510b83c054107050564005030b0050140d10b5104101140c402d0084504030300403011040140c0c0281301380801d914 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217003974 1250 217002724 217002727
    0xe1219150501060801140f06040b0a0e0603040b1608011401260c0306040f050114040e0a0c140a170a061a0a030c0501080705121f0b0a020c01030605060408120f0c03 72
    0x70069041074000c2c5c101c0b00090b00300c2e101131a1840030802c050348440c4034682c1c0503000344401e0020000e500081c02001c4168100400240025030010710250412182191682903c0003001100741e004091f0311203640302c44c10110541c0d414400100080d5800385001410080b61050201c0303140003a1401124104043c03203032400354140b81040c880e41c0e40c4106d4505002d141481c01c07d82d4641c101703120390790403260309540784014005850200400303000344a5080c00d1034403d082900c0c0200d841038521000030f15013903004000d118244000d20040c0c40d140d600c2035803d051001c007490b404c02e034040740144109900840001e0700708000702003100240c440f50041c03500449107a1b000b004012840f1201015550700340ca404840d50340c0c43c141203c45220300d80085440b180440c010488000400c101c0e00000300300d00080002c0e0507140d880150050704100391044c0180c1c40107400514950b090301c01c820182100743c03861840c040c10f200142c1e580750460548006c6841d00040c0c13103951841c0d075400703803020f2012400549 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217005224 1250 217003974 217003979
    0x50705061608070311161a070501020c0601080105070e0d0305090f13060806250203041208090904030503040b011a07020909120703020703120e1309050703020604150e1219150501 78
    0x28444190003400c0c0c000e6100f406c0d54040c240309100c40701c80440b2494070f0745484d40140016040100d40041a00701e43c690340a000b1284280407e10545001c3c00e03109000082034039190100514034822400611301038407403071001101107540002101d5000c81d080e152201c85260090104202d03982050008081034502440491951400300340140100848404560862001039840402241c82814100940e00400c400c006090f001d0301307080354040c0594011410001c0032000f180450360201c1d000c40006100100708010032000780c08950240c030403500b242a0141c0d049150516a201c0d00601038031910850740003900f0b0950820850740b1211283c01c4041d03c5120a26002e9503809041c08100c0b100c1c1d0444d121901014894000005d040400078900c4a80d802003010303c0c00109244801a5a60300400d00c0100250700d91000410003400b03a12600008801e890f50020721000b8401e42c0c01d48a0002d410795803004220000b41c14101048803074040c48a0000c91400300d003441411070202014030b0825000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217006474 1250 217005224 217005227
    0x51204020d021f031508150a20040302030f070303210e010c03050f011d01060507050c0301090305090a0f030b0c16120224060306220606080a120c0507050616080703 72
    0x1d0707071000c51054070b085c003040482204000c04500c9500814060350300c100c5a50261400c4a42c0d102d41080e81c40400083d0340900c6081c19008041c20382a044c2c150000050400071410100004502511110301500741c850541d80c004240e0a0400c51000c880140c03409448a507401980c00b241c3e426950b40700030070980c20740400203030103098206d904039404a90b1000004070010700242d00c12502c0c21000115241360300b80603080c3d5041d003003280309450078401c0304d04d141c0c1c550b00d0911981071450300030b80350207807108186c00400c5031002c09030304909806080604100000380c00c1241581e0420407007580d940e00c0b10005002120000e842e0700000d09400c4c3c002d0b0700f2000c25038000c183c2c181c0480c20241508150700e03410110084c1c108080c0c0f40c01c0d0f0550b10810004208000d40c0780c84c0d1502c2080d090640300441016114041070f2102c80e080000349400000c036080400084d4007000d0820503042c101292070340215182c0036215162442010300580d40000c03814511200381c3d40f0840701d02e90102c056034031403003107040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217007724 1250 217006474 217006519
    0x20a031806050714030c0301090f020c1615020d050403020d11031605031b010e101e05030a0509011b051c2301081630050d020d030903051204020d02 65
    0xa0410200d403800f04c200b03d10f200600c0c1100d104400e4101e10518503403078402c418004100d05561400c80355030a0180491075401406210004040000b25070405810082c10040124011b05c0c0c220566018031240510103811500b924122a01100c18030050546c905091003050350300a51545d041c001d0700400c0103001c04640d00502942d0013075080303c6101012410300201482c25541d4a4003250b04110f80c1441071801c900116a1810300740f400e605440020b40015003004d41c1c10a940021400200421400800074411035038015031080c024881d1400303070241103507541180d0503550108600020100d5441210007c004114240400101300c5da43d03500d03000d460f024540c1034207100d482d403120000107285000091805100140340c01180204c9281c01645400b0f01c0a20308111003000d0720500c22100d5401285000118a02542c007801c40b0003084000281030012110b2104103061410003a07001181c3d00a098500b1103201141c00312998403280000741400e110700768002e40c000700080740030b0200c6041c1c19 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217008974 1250 217007724 217007731
    0x30103051b090604020c010609021902062511010605091005040b03070315020a09030203060a050912030106090e071112040f1a070b280603170319020a03180605 70
    0x8150340104486200301c4203100300220640398081540c0740455043c0c549a4010304600300580000030381c46039105584000d0b86c1003083c00c400c0c044003031600440320346d40500c409070780b00610b8a104080d04480c0c080354000400341b4040c400400c4803007200048018030940c4440003a000003081f40c2401d103404c4103031503001034103400303070a02031818400c950180c2e09002a100096942c80b00c405200310702001150802900188014420008a40000009a10f05000c0d190254049401c040b030a843e00100319840c0c21556076541c90b49400400041084d598050280000d844069040307100c0b03612484800c41e1502c02a41c10750742d06000395001c0c4810403a120000b003040f5000100310149165030f0301a007a00050008405002c42d2108121000004400900c2c181d4460582141441052541c0d41005610000d4a860b07082059840340c1c2401808841801d84401002c000b4902d440d501d842078018401d00003841c0098520b030740200e104c021644c000d80010b10090002d4230014050395060601c1c0c00a010b065 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217010224 1250 217008974 217008983
    0x31703071409010906030f1404060f0b030a030c030f031e06030c06020c06040306180b0a020d051602030d1a1002010204050a0b07030813030903020603040b0411190b1c02040b030103 79
    0xd240c0124a62100c00380c2e140090161034800c01203203480400c3c4c001e000c40c01060780c2c085503144051241803016030440b81c052405100b001454030882402e5030215045034540318400c0e0320080e0114006070b44516441c04107503045c5444095590140c4c2c003500504035171a05600264503000440d03041001c40c0d40000308490007481c8000c0304c60754a140607030b198140c8014503604240104001e101080c0f050f08404d44110308071189005009160b01c569200170420ba400380c0c044c0b0307000140c890601c842405019040f04212078011022044480d0181d41d0388940482d60b01080c2e10313048464000346050340500c0348448003402a02038403d007003000a00030750060017070500c2a6004400412040308482c00c0d00d100c10350589490245484031480c06004200307982084080110381c0b40b0110058031640099401580320b590054168206403400d0400c0f811201c445074051080020140e585004508052080f602c0349841c4541c1e40c0c0c1800320b850b8a40d80d4510205040318000580042d090302568002d604032800b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217011474 1250 217010224 217010237
    0x10207081f110301050a180204120f110a08071208040510090e0105040b090f0a0b040203130605130302030703080c04050d0311060f16031e05010303231c1d010903050405040e03030c03010303051303170307 89
    0x100308103cdc030b8140c40d0042840eaa800220140f01400b00e03020800c41c03031070141d40c24509040d61540010250f030440e002480000700c14442c01c00202d41c48030095409003c040710140004e40650b4003003010450024544000180c1240203d1b0341340100303900282c0440b8015200750755070300d804210004a03105905084500c2440c120000d0800351001c034402201c1a4140d0203503150038259102152000ea000c0c0608840450410002410b560742c1640c1d00c1c0913912940301c01103107281000000d801d01200a1079828032021400c1013254000c007400c0d40112003800c03400c0015481e00c1045900c004460304450005009190100100074150040e8241d88002c0300118403044060b48040c4c950400e015030662814413203160000030b010141d140d04198071013200100300c00d40e4665188217140c25141c1181c401d9000c80c1c40004c0a0000e41001d0056402c0d000d030020041d8036608156031805080e200c140701c06000c022002c148503101100740d1300e01100458020141c3c0c000712903442080902a44190b40f0712011465 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217012724 1250 217011474 217011503
    0x150e0c01020601140d03170106020a060c180510050403021e0301050c0a021005060f3a051b0103090b0705030106121b0e010207081f110301050a180204120f 68
    0x7001507214103842c41e403030340007441c11488000d000040e00d0041d401c81c203110000140c00044040700e40014001c140d0340e070090540d80100d04002e0102d5826111610411a000c081c00303070400d6a10910740102e40e0140d450b40322500040108640c40d000700d4200035030010700208040c100b1048020b6419010710214020085034859103a080d440c0d20684d101e420143e002642e41c0100030005500241c4d01000140c0400c40320300316200056424501400517400380d40d0010384440703500c821442604d03003990107003908480c02600d80c2c84035036464181003070810b9103d10340c41440903141d109070001c040760341c0e0220001800d41008400540349030001d0240b580010303445018800040c6180c022402201d68400d03100c0414446608211003219402d210f80f41584a21000004c40c0c82040082400d200560000002d480300d562802c0700c25034400404890070400103200500044d43c5400808044600503ea240181c1d0103114050000c1e008591051644119000687c0140700c1c4081e265211140f0460f6900c04480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217013974 1250 217012724 217012727
    0x80702030f07030309030609081902010903020d05090a03080d0f1e0b060f030109050612030c01090b06090c0301060c03020106030b0708040b060414011a130f0609090605010822150e0c01 81
    0x100b2601c00940096071003801000070a581b80c0c0a04078940c01b403071907a854059031030302200c0104004142640140c1d95840c0590605078180521000c1070010310b0b00901c0c09445400080100b01140405004000001150b0501ca24564024100340b42c2000701449207105488404035400450100940d5107420440e031300d400e6290100c2281c0007080003003440f86c15a400c008480b0001c1100500707035900195001c501088102041001d0004104600c0c000304000c4641d14001102001c081d000074001c42c0c0050a11001604900950f410341c3c0c21444c00894072105800c0803805402141d00240205c000b49040c061665030108489100d03a018090385a05a1203a078107000444000002d02d8002c0f003400d100510004031f00c0080341e541c0312100c8078202d040032000107106001c8110369000c100001030014081041c01d80200000c0c0041450711810000c943c6004000381c1003010043c110700c0840565000c072501800e00191541400341c1100011188100d1404000000c0001c41c01e002150710403c0c15540c0f081d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217015224 1250 217013974 217013983
    0x3020c100603020d080d140c04050a21060b011e1d121b010e030709090203011b0c080d1b0309030306080304050112090f0510020304030801050f061e040f03080702030f 73
    0x303e42c0600341111294182c0c07a00910380d0021424a07044a4442d14284000b0b8144000c0a00419143c14440ea50798a01b004100440603140c2c050105c1d94a200d601000c426803002e10b00e01c54030b412400200d40381c0c8031704004844468518041d00400380304098009503850b4400c2121119a404140c264002d4446404000c00851611a008074950207d014507225580f0038004041000041c1044500030207a5000a41002c00f9500150803056440480c0001e51a0034092550705441d000c0c0e01c0c0345054850320008210031b010b07034005061410300090311103c0a40303991004001066201e0025041a40036400902810035801d0a50000303050040208a004001c005c07101100d805031107005001c1804517200f0003510201505844d0000c41000031008039809000d80c1082d0f0030702c8440181d503442c00745006001c032030040c4c10882c01150441c416000944440085640180f4041512218490a42e0900c1c18030300c2260009050361549640010820400d4005481c2c2c140c400c8080e104c41607050781d0f480d0350340d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217016474 1250 217015224 217015229
    0x8070b03090d0e0301181a070504030203100b13020a0c1b080705090a110319060e0c0702040203090109140d080c030c09060a02031e04180c02100e0109050a0303020c1006 74
    0x342c1c100d00350702c11805004282450103e840030f0b00103c0c641c001480498401c011032101a00c103104000f030040a00060b85e03c50950081050604c0340c2410705540200c4e07600c0788801020700e00159122801096540c903000c0c1b5901c501d0400405560f41c1d024030340004e00c00c11008170f00312200c0300c130381da603c0321080103060b80340c000d445024000304100c0d4a40001c01c2101300020f0880f001360b540e0750607403040780001d0100071481070300419581503158081050441c01c44069600030501c04120310144190240180b0480e104542c0440303001d03840c4d45600d480302d4010994a40001c041c00003507100780b61780c0ca001144803210307180c2640700c01e0303070a61b80d000312918079104c203c0f02c000c3c0c3c4400420401c086803901d40003404030302c15541304407401c01c01210b079a111034142407482d440000b007010030100502605900d5010920720a01004c0c00854110341010359510000221019000d4a039007403500c10a009600c50a2040e030001c0032074000303038807038180a4020351007005410014011400029180e8655000f90000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217017724 1250 217016474 217016491
    0x271a030c09071d060906041d0106111005070e030703051b010302030603060606070c030c0603050a0606031404170d0212100e040b060105030403120203040c05100c0b0f1b1308070b03 79
    0x103001c01142094401082007180b40c0c442402d00110406417540340141c000b0b004048c51403045c414405124640c0d440c0143d10074010840380080031034031a580403901c81c04c40b020307004c0e01042c40d494980090361554404000036800d031041e803030000148400003940d0521403540d40b041d06c10122540e0011016440300710341c41070701035000d01c0202e10117060075001440c41e180204004042c8907100d903101c600e80740c04c59205400003a11542800541907540c864403000306607a08040020f500e01c158500c180001c010b002030900c100c20300400318103034007540803291400390090085580c0d4400078215440303500c040d140e002c256920b04030081040034131842c1a500030ba80002c4640c1c1d060356a04011074640d84010030032410000610740301c080c4600700e03001550007144540704c210380040c200b0b0144046008200000e000708108401c1b00000716003a0700c03010b030b0086044882c030011541c4800d4512082c0c3e860040c0781130040d80001d0010310724400615400140c3d00a03100741d07421107584613030b15045400103498545 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217018974 1250 217017724 217017737
    0x80a0810170318010507120e030618060a09150c0c0b09010203090a080d0621052514030c03151501030207120305070e090a0c0e0303070c271a030c0907 66
    0x50907a42003c083d240c0c2c48005141c114a0f059207580c1d03425441c00410901000300d080d500c0312a00500d81400a039a0201e98541303200c81440400702004e039520780141a440f03142d1f41d216103110a0222003551149018032078603080c0045a0f624034000c0c020f54180c582501c10140020100341d6139041802240c5c0160802d80041481d02c1081c0c81e10505640043d4440940690f0741e0800540a401d2411800994a05c00d2200e0050b80c507504085050a091201210b850034403181402600c805800ca00000d95102c00310842240071401e000c40d00d00041d00301500d40c90300c61880100008006044001d00c660032000441c032841c2c0700b44005500b6401a0400180401c100b0022010700d50300c65030083e03500c0b4080e85400c41c1900300301300c042002207105440d1240020303100c1401e103024a81045440c00151010380041d45840b078161100c0b4072900050150302500e201c0c01003848043d0500900743e41b60005d40302c0c410009110381260244400e041e404516000c5d0003140a00c42d020b25250902c0c0d407050300f060b121038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217020224 1250 217018974 217018987
    0x50909071a0712080a06080601182414150c01020a0917030d0504060f090602030a06050117070f0207090203270604030806060906070609111f020d12020403080a08101703 74
    0x4d848821000380000129a6245800540311a04010181c024520401074800b03d042039031311002918020400e100c2c040760310f07040804a82420243d15400ca0343c551124641c1c02d0622000900d600c044254003164003080410117a050140c19070083c206c860494540550440d500c0c1000e00083e10b40300f15440d01c540040c0200480c1c07480903004990700c0791103a04001600070303654118204860f500d04094a42c140d020081201100442c0b0400000e0130003402c0c4075440d16034042c480002184014000420002d0511020103601c0c002c015000c080c10040c081551a403921b01c010224803003410005158000c840380301c0f24003102c2c0201d021030141d905607444404c02e40d42d06061101c1680407845264101608000b00300c0440d40b148580b04200748114030101d030381c0d41d0b0031080040300d51811010503540c0491710119000c55030001100c8001d00c0c074038100b03007026040000410b4000d00035a400500300510004d107440415074070015541c03185048a9081c50796649490a01f020040c2002d192082c0e5803007000704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217021474 1250 217020224 217020227
    0xf0801140103090206160b0c180d08041203050304030906090e040215130e0a0c0305060102030d0b0a0b070302100525180306060308070b13020d060b010207050909071a0712 75
    0x4056500e1041c1404180320707406a010501e0782e881003220b400c00f9540701c5203520802c20590f00583e00082101000c40c00c0194500f980390078107611021240c450403034503046104009500c81a10010001c040031b194411900341006810b542c000c130340860009128403000300381140503c0042094641c802400c2c3c05540e02c0e41c0c00d000c0c0c08440f16040f40403890092200d44d4281c500508004040c1c034401500c10030b02e0810500d40d0064802d143c00c1201850300300400c11616917400801d8403455003542d98042a9a07200c1d03c04505910f41c0ca821040d04007200040030401d142e000100c0b2111041c0300c840403c00c40d60703070700500c03402401003c240359000942030b00700c0c442c542c3c4100052450600700e4080980c8040d0340355554030846109a000311030058000c2041403e11050481d41c5038049000c6400c501600d55a0f4002180032104942c01041280c1d54240c084090f48200803803005400c000d007810b5514140401700d0381d6030b000d5600c40e9908048898080741410380e081d40a5600d81640498400303594000001c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217022724 1250 217021474 217021499
    0x1f030b1903020f181f08030906030f130209390a110309060309010603030207080705060f0307020f1f0b030c09040b0c0706060320010302210a020c0610060e010f0801 72
    0x500540c80f28035950312031464030041300c41e80c2c0501e8803c014520320140407910303101e03c250f05d940402016003040c00021215104c00003107035806014690b600a441e80c1d18402c3d03e1103100300000180d040f5603a50100488040c0200c4c41c00140e00c0704540c106161054201c24802920b40ca020151799107200780801015a8012008080703602c2e034402c241c03030421035811b000c40c0140d0011294010b0b035a45408080062540511030745024080240c080c01c109401c01021884500c41c1b0240440d20340d500100083d5142d03c03d00c04000608004415181c40020640142c0c8040442e40c81000c1302a00e8813407000050320340060b0a90f050100948080f1155445440760010707020300604407aa0700c4010004000000ca1074801c0f400a1481070341ca4030081d10700d080400d540d084084d1040b6041c035204220a00362503403a001c00ca1401603d03030405612543d105c0d0981d601034002c0b8000a20548200d109010800d01304a8003101501e03000c0e9035601c4410b480900464402080300c1441c004550f1490050051044014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217023974 1250 217022724 217022749
    0x9050906040902030609071d07080403120b100801151b0b10030503030108100605010c030203220909050c1002010b01200c0d080d0f020406050d02090f1f030b190302 72
    0x100000340d11100d98000c6810041c003110641b080781c005180c288220012a078075101c240203062010a0755142c0703210701610902c130290016090140251640c18a4030340350b0001c400d0f454003d01455803030b00c1c0280303010342180000e000d000d08660000c0541702496204661000914448034a0100314010300d403102c40c05800041d10300741c1e480644800c048003082c0100020360081c911600142a0040000d4120003240c8080c0c1283d8108200501034001007640042074034841213240c8504044070000003203d00d07595209601284456080040b00002c1c08008030701c10020090580c0c2005a243c5480022400ca64004007881c1c08605c0d61140e003480d01d9200324407260850251001c5984e911504400074000c100350620407110901c0014081e40c3c001094040c17910308110f142c0096080030b04000300941203002c0c90106014003503001c10250455500c0b03403502190030101606280c010400004074075030317039658820190042820074480c8061400c048444440c160500d03100d51894074115400c02a40b00d0800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217025224 1250 217023974 217023979
    0x618160c083603061b030702011401080f0c0a1a0a2a0201020c0109030507061d040e010203010812032703190806010e040921020304090c18080d09050906 67
    0x78041c60080006102d155166040000c94180400541c455075980071804204814003c0c1c00c150107000881400207007038482142e480f520b15440380d903150012401018482814030b00303010300f040001105100480c48100c00ca0034a401d86603010035020a005000502e0712803417800484164901c0720180035800a44144201860308400351070390345c22045549034100b0551100c0c01500c1d80340c182103680410280000305003c0c00e040e40e00d145107440c0c05849888500c204418030040d58000720b4003210b040901031010f10002c00400c480301c1e1100d81d0038000d420900880b0800d114070702080140103407000030381c0d110344031080700b590710366841080300310b00b80c64403036003402146c403080c4503040c503484d42d802032603415039103650380e08641c0c1c580040010822034401400c05e005600c0c041c001404900489031400034103401682c0200000a002c40c101d15501c00d55200000c51850008014202035101040001102c00d48039081c0c011a1220444d649401129101c0400319090030350410841c205402c165a001000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217026474 1250 217025224 217025227
    0xc030a0215040308030a0209120d0c14070308040f0e250c030e130b01030501050f060d0504020616111009060503191b02010e060919030c150f050618160c08 68
    0x326600e500c103582050303071b0f50240c003900421600910f081c0050501c10000d269030050110012200c2c010b00304d04e100c580080c1135800312100520114904104074401554404401c03540d880d91800002109005400392a40e4602440041895415039045101100c1d046200c026110178100000781c0311b030504000c0c12003d000b080f03805441281d84058080e1903409442c540414801c0b1000b0006046440503001688a894a0179594a40e51954000d0b04c80c1e00203030082c0080c003920380d4000101c2d513008140120400c41c6020444a080007110164040036000603103040002c00c40e8181e080c0d43c00d10890040d88002042840000e8200c62910905070001072460700c00681455450710b442c8041100d0001c0a015030f460f070011181c844e03420001258041c0440703001d00240c20a50b403d0600102e15018007604000d1000e048205001004030340071301641840a04000038040032801401410380ac95400c0c0c82a00d040c0c4c40b141404952009084c4030f0ba0500e020006001900329051780d0304e41100c602941c04000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217027724 1250 217026474 217026479
    0x30702100c020c01091a07080702030a0b090304030512040303120b0406031202030c15010e0c0a0e0307030605072003190c020d03030504020a120b0a020c010f050c03090f0c030a021504 80
    0x545226008919000d0b50142c26a01040800504001125441000390007100314045080701864401d481c00141d00c0759615503a0b2480d800000d180071606032025000091a80c00d200d88880c001004008a9201e1400d076154a4940240480d4601a80c840600031800d040302c52140560385030310160b02e00b1001040007a0035912034860b038440014804041015034400280b13141401c200b00152039000806450289807036060a040c100d60120180c401c11410310f0200e1040c0c4954018101c0f050206406401ca07103015a1303030f04281020742000d48500c1d02043c0641c0445105601e07610344500b001d40c4040085150601125a4018141070720652400700a892803002c40141d0380c1c1d40098580760b0090703801090307a041600410512402540c0807445c010341071019170001942c4d8103a42c0341d0007400200b00684500d0020b02a502400b00240405101c600c0c040801520300351860255010b181030000b12644060071040d103903075490501044c59810791080e90544c00514050451101c207000514401d42446d030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217028974 1250 217027724 217027753
    0x50d0801180911270a050a0e0109080d0506060f0c0604060b030303090601060e0121021b03041401080a090f12030e010c021c0507150f1a4f060602011b0302030702 71
    0x30000c0c1c42050301c051b00d4000707006009089018010f042c6480b40002c1003054082d80c0c2e00c1f00f0902c1070561000782d403600d6000041e56a52100e0a5a1500b91300290320395490380000c0304a40c03500d10407075040702d4003442e05000c020380c0c0c180001944d20408640c801400d00340d00b004003e40d9184512040c4a04001045020520703426000000b1190714102e00c50141e2284800b5000d03001c030035070702c1041c51071316401400100300c51444101483c6030980b0a081c4441c26844481c00340b000f40003d440081d000e015002c6008003080b2104100920b03081e05580d08000c2019001c040b01c1c00e8541c00d40c400e8005900a0600648521501c02d41300805d00d8681417152500805980300c3c1d0340003041025a81140d59203403c2c1e1096140140100c061070180c4c0740c1c00000c9940c0c20800541c0c200a508140300c0c440c103000c0d105005148451b4402000103041603405202c0c0d00c904400500f503070342e4a00000c040ca5042c4000020201c4c01405129040c5c2540d161814418152150880080d0402843c00003184504c0d22100c0040c2c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217030224 1250 217028974 217029049
    0x30c1a12240d0c24080a0e01091e02151e0f13060807020c010302040b1c0906050c0403060b060c15090a0c1401081e160903050d0801180911 61
    0x300c0c802e0300c1007069a40380104d501ca80e04100f034140c0d0320035000c00f0200301405510188080e07100c1901140050b01d103006081c0c0d24018400c81000405e00204000c9101c01c0498803030180101d940b00721160742041d4060b070340032000d500803802c207525102c02020303105080101685c0980104911988844d00340121800041c0c40c40300e4588c41600400e5428040c0300000380e0510200c0040c0b402801d0551600c3e00d04a0b6141d954861140d800302c0003900c4400090808285411030500c5036041201400a41080143c0d01042e0f071091004445243c6042c3c2440114203160050750b2090203030102429503140e000c6000300c2481d40c000c20440041c0100c0c580303540007134001100040501100002008000700c4000090500c5601a0450041e140000304040c040881c590b992079100c03490460b10300780c0707a80c030800c2a6031b105080d400080c82d034000c1500b00b0781c041d0b5200360458102d030907041e0a42500d100002d0014120b4000e0940600a803202c00701b07440c440c0c201800700c0c0d240600000c1c070148020b2900106200e80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217031474 1250 217030224 217030249
    0x409050123040c080109320d050316030b15091801090f141003170d06080303100e0c0a05090f060a020d120b01020a06050c040e01030c1a1224 62
    0x11110241807005103c0045182005426044000c125880454903010005c24240c030140c491031608054201400214152410080690400b2a120b80543c144040c015070412110205d205503460b80101081e4481d02507038805040141050842c640c4400e07599609030f2020f00e4040e001001c0b10220042e010110901500a110240f000100104030040c4041511040d00d0900c00ca000e48605100407041c0b100038210031aa40b10b030384c0072310200c0500156040ca0080010020000d4030300710f00080e10030303070200003548245550704107444844c2d00e0312091000c0000039900c2018410050080700b03002400f40d002008141c0000b0030341c0318401e041400007030b115400840d4400040e040201030000c2c01d03403c20200030038581d80420a1240c0344080000130364a441452001c0e0000f52200c011406a03d803030703000c42e4082c121100c200321180d85c427410403a00e03011092144419512030745407064161140071042c1d0781c004230120003003000740e01c40d001c03004003000c00440d10b400f030020b0942050089544030344200c03a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217032724 1250 217031474 217031531
    0x302060a030605030d1409010c0203160303110c04090305040905060103020904020c0c12071409220c08060907060905060c100c11070e0c0306100e180103051c090504090501 75
    0x10014202418142001000e17400c50050007800c40025004a04110070fa0b50400360a10300040c500d50705000092070030320071041040480301c02c8030303020040c1540070345925244032070321007100d036004545020700c022200142c1c409000141c00744001d024603550307a0009030300840145005420324422b40006003c980c080042054241c4c00106003030207904041100d022a400c61201034040d02e2b00d00012411403912194040d4854110200001c0e8403e49011000026190008200f414040d25141610040d1190b0150709072034850f480000c2d00b104c00014000d000da6030342d580d40f45110341c50141071005a80081c00a41554040c01c61740c2e004807661885080402d4003190340341c81003070b0041c85e40d940c01c209840d040b000030402070108000380011f404040b2500076000380c41c07035148122000c0d8202c446c1400400b040c0c0c1d110007071510445001c010301d500385059901074016210b8a41c81c0031090f49060040001c110041220f2060401c12880d140c1c0c003e0034400d005030f0010420041c1600462281a0014002c03070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217033974 1250 217032724 217032731
    0x909250509032a04020706060902070507061d1507050a0b0a02130509041e08070524010e04110103110f070f060c05040b0d0203070908060709050306060312030406150302060a03 77
    0x581e803a08000204011030140307901c0d04046100000b01c1e16160154603618061600003506200300015a441540246a0020110f49a07809860600e4403103a403407140300002118010500240780314019025019100109107215045a0f81c141c00b03856001071030203540502402015002081444580c644260803203840180d6074030101701c0454066403544c00050164003082d00b00000a00d4000d44000d078054456400c07101504207184c042c07498410028018054015101c408024600c14048588400d441d6401000e4582c2c8405841d510340700308907009131022441d405104e070f030f550003603016101d42c0c0b91864606181c03200d09403407c41c540e400f20200310754030540d070300820081c0000e503c2001e40b034220742d217421351070301d0b291034101c800500035001c2c44006107500201040a031030240144c1ca0081090b5010784156141900002d480c1201512506010703010b8200000c24601c0c0219681003e850700c103848900395103c2e42c8841c4014101c0b4400040810f074649000300140e070300d00020300003031110b0b546c1c0031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217035224 1250 217033974 217033987
    0x4091401151502010213120f12080121150509031902030301051e090c13050a030807060506090615090f09160f02010612110414011401091a09092505 65
    0x403402011a050b62011644180304294031262891507040c01c46d6000301210041c4c51581c04d228804003611240200050f0107440d1000c0c3c11600300000e0b40c101e0340e185002c1700007010000c18401500c1c0d003002d4007c0c440d120f0701c0c1d800b040040140d8407168000f004103085a0800417110b59140c2188040034500c0096480131004100920306410385041c0071251048803900070300350724041030b0880d602034080d0074051004510321600301104003200c0010080105107003035540d502e0070251241c0d440740c2401d4450074140702c0090740505003416140e0003000060400fa1001c0d8601942600380d170440d5841c0340e404a075800c80341449988180e19240101c00c00201c03104120168000070f40000d26055440c81036905041c400c104040c00300c542185c04941081d6100e80b21804d400008008040311000709545c68029000460b1200c0d80003040e05280200fa01c41120b9070f5180c4560410030078100308140d0218004101024490070130084554005a8032568610b000c090b4090001044a2150031000002c0012604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217036474 1250 217035224 217035239
    0x5090f010e0c0102120a031b0c03120903020c0d050a051c080f06030c0907021c020304050a0501230a020f1b01300209120a0f02040506010504080307020409140115 71
    0x300c1c061440d03440300500409000800103034a807400c24031150302010001c100380902c180682c0000740030201d4002c060aa503008003401a2103c41081000c0e0001035608150f42440c0d20f143c854030300002d8243d00100100e86030442000100c007440203045441d8050039a101d00081d804012241d981d4100007100a045c880c2220700820b10704000b000f01866040da0010300019403408115013050540c15900c5007901da983d604103a1400d07100340d140483c11000c0805511481e98044064810380d04100c803039100d92aa9000111280d410003958201d400a44a8a8100c90380004009042e1040c09006540c078920904214600b03220a2030f91100b0885d04038044a2007030360344070001c15102c07030207000c1d056a955041c86050607d607100001003142941e00140c85d04082c1d451101d6240d6901200c030446403015858605890391820010741280101e003002c000c19810360244050f24240d400b40d0303005608081c02a000c101c00381010690a907655101003601e0080d407102800341003c1d01c61200422003505280062 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217037724 1250 217036474 217036481
    0x70c380703140313080f091002070312020304260a0b24180402010c1b080109060b0102010506130b010c0b091501050102010513110a24030b04180308180105090f01 71
    0x358140050b02c108100301880c8040000e4661403604480c040f03444190381e0150300317100d01c00c4118a56003d1005200c80800650005500055030f1190f0900c094000c0b0520003a0f980e030145d40a20011291800440300100c0c2929000031500f441200c103d078074180b116241c0d441c0e03094081d07e02d507031608410035007000c1c00c03d0303075840d008955482500c40c501e10030101d4140c02105540a00002c1c1007207404400c3d00c0070b002c01c4613080709810f60016242400182d41d601001d00909081c40101c400c141044928100c42d80103104040c412a005811610b031850700c250040b00034404e0f4001c5a05104104040c0004034041860302489031014070010030003101e4951515425020507400749045a0424042000c1f842c072003c0148855940a480e10b140700d0030000001d43c00210179040040581e070941900064131111524401e03088807181c43c2000301006020521045c4d60896020031121000d2003000c50020384108080e6070710000741d861292100010360303040e0f807d440059400d8070003030384026040002283c0038030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217038974 1250 217037724 217037747
    0x3010f0812070f02030c03010f0207030e0a030521041503060503062a0901090e0a022104020619030f1406030d090f050607140706170c070c380703 64
    0x8000c001c03068201c0c161103000c1c8501c010050810103424840011910b04100400c240c9030010000d1140e000c481407543c000b50000f036030560001e11602e0b8006203074205565214162900440035140e510f47c0c10300c800d4818658024a0300204408004c0000e00b00361001c1c0c918500c1140340e0f004941c2c145040c1c00c0524003040074211028880303c0d40e03032141a04010501100000b00516171032a142c0e141d007001620306418a5100c40355019031030b0104105040340d0b41c010206016810b0040e440c0d00e034450300055595500b254001d4018100300b0650304d0320403140c121001059003616010a14000c0c211041d025500100d80c4a90300281050a100c03182c070301484860361240765460100141840c11243c03200c00d0030588a1140107582c000343e100e007440303980d288000c009940402110242941d50300000c0170310440e064280411411140401e03400280300c0c08803194a40c0241f07801d007071141419030a20084001406880500c010421600c0d08442480c04400850032000712954552280c2d04010305180d0464 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217040224 1250 217038974 217038989
    0x160e0702010b0a1a0403060f06090c090602030a12060302030f060103031e05090f01090e1501021516030c0207091406091518040204020706110a11012f1e03010f 70
    0xb942501611903200c0a411110165082d04810700e4554008040d482583c0000c2c010500740501c201c1184110340002084405244040018000e0040102c03113114840c051074005070020805039554901c02d00b2081c1101e201c01c403000804030394a60020303292400c810110705c2f050b0802d00040040c541c11400041c0c400c016000598540005000014050302c02c90091502c942204210084d060340309094400142030550410443c3e42028072102d1044001581450f005114218250071444071a400c100d001d485040c00640d1408a038590503805002d00b420358038214400c2e9080020f11351180d001b03406142e9020700c0030f0f2000d401c00324184100200c000702194511304184282a100380c403010b1089001c11502624003209480d07038800136000e44a102c2014100b58141645803600b0003902d0024100e64485460700a00b2898591003e800c0e6a04040703410301310307180c541d0071010740e0100d40a81c22034070305044003443c503080907150708400000d6480b4001d24500340110040c080d03400d80180000103404039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217041474 1250 217040224 217040231
    0x6020c031006080c09090c031f0507090e0105091302060315030c0a030b0115020102040323010f050f06040221040f031404030c05010c06140f0a0b0904020f01080612160e070201 77
    0x345110f80713039102510061103008400b0400081c00c020814421000105030040965940324003801003440c50400da0f04504002074a4907012941d428001d800380030403510501c4520b40b2603840d1108200e0f0300b00c1d000f801050a02a20301c24407006996400045109084000c84001105100c10900d4036100c0f00c001003074002e00d503540c018008108422111411152040101c101700340c0081800c80c003900844d80000d2000b008040241c0c0695009062050007071807010003000500b40c1001c804040e00d07019941030f1000c20110f00840c01e2170070203400415010035900c0e0000d00f40441444a6200e008003100d0070741c0c1000c94480c40c50105940051155041480400040d040900359141c1da5840d505d01d2042c103040c03007403004608042260315001501c0000550b80c00034040e1074102c00866450b07508582d00d6810fa8940603242240d450400036590103181c0281940031046028001500c104001070081c561182c416030b500c0b0000d80e0104529403080310412a581c2c91a490100d0304080340d60003800c40340c1035904 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217042724 1250 217041474 217041479
    0x10c0f0c09110306061909080307030f030f020a0903110f130b0301240915030206031005010906020d0206011e0e070f080708130209041403040e190e0a030c0204021306020c031006 78
    0xf202800c6d40c046c100310341c0740700c940d9240404050740c100840c0d44c064901c0780004101d903400c4c1508904946418400c54605210038111400d65204a00c540c02003c030104070800d100b400030411840302500104006410514040340c44000a42c40d16481585100496100e8084d03801d41d040a0054070f00c401c0c0c01020042d007414400420460040e10342c014640d50a07610401001d00e408030710b422800031070700034103c1c941c1c82c01d00b00740d6100403e05a01426000c98628100007032618800205000107410650281c5410f90a042c003024140749450141c5e0b60310030150b44089150b4510f252003a019141b0360301c64400d002d80b60740b0058034a22000b00703601c007406101420015042265000904055811584a640d42d95030303250442040d03941e03c002e05043c0c407010901060850f9507062139409140c3c010201c030010140300c10041c080d10b000800c102000e4100004100c0042e0040d68101200d6100074030150516041450000c61031299503c8003005034081c11406003542020b04c840315000022007410310041d070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217043974 1250 217042724 217042729
    0x27030d08040609050c09071e090807140a05100c050706050301150c05011523060705030417030705011b03052a070606120b09060106050a020607030902010c0f0c09110306 74
    0x100003030816038441d5a40010004c0c01c2c42180100d0a00070b10300d02d00c0382400328000388410307004203110140041034103090150900454010046904203001000000c0c14440038100c00c1180025032034001d61035820100e11591041c2d4a5520764650b41d455603101401d50030803500e4164039134810f03400c1c40020001031204024110401110b0703180d506100340d640481d07103813017401092900389081da031454004020400d880000010300c402c80301000c0d00303140d840a01d820041305118903c03001701759a008020411801e41c0ea0943c202c4a890000305036406e001950f100c45003542c271100c00c1da61106541c1288202655018400d1581040e803840c907841514881170313840206a1081c000388102c81002280309420000b07542c00c24005403016600d1031591038030f10325100398103450907a4440542e0040f01c00100d101481141a03032100945903000f000261902407060b0020000300c0400e034100103109400001054101c90701e00101c80c4500c2c00c00d460203190420034812194100400d04216404105020711076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217045224 1250 217043974 217043987
    0xb0f041518080f12010b030601030e0f030a08040311030408030d050a0b01020a060f02090a0803042103140304320d0201020711040e0705090f0619030201230c0327030d 73
    0x7076a002030016915003001c0e038096824083d070820858460341c410b001007429100c2001031402600300b030701c0500441a070410519201c8208401003103640d403045c0200310b011841128460b40050182c10610510108281c2813415a4801d400810f41c9a1001544440910962284951007084201c00300010440080000d40b6807a4004001d4859a110640780411820381d034100c0702109001018100f070fa550b00ca01e150f03120f03002841901c9800401310f04451090710075402c2c60620303591507901c1045101c1c04175981101608054401d8501c00358000b40e460304000d8240380041d00d84800700110b0f4611880019452501d1520605032046900600100002440b65001c600035950126008140e603a0030a40c09450190a07a110740c3e0303c84e20042c2488190b00382d603a180c0e13015500a844102c20301a00c0c09400e2402d00161000a00203034000341c104000d11000701c61000c102450525040c90000380a030079510b1504003800d400d001460908011701032035031080211403a41d100747c0207400385030ba6160004e01031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217046474 1250 217045224 217045271
    0x804051c080f1510030f050c03040b0106030905011d0a050607031b14090a0e07030f0504020105311d090106050a031e0803010b040e0604050411010e01020a0b0f0415 72
    0x1d140002010540f440d04400c5080c40090001d060070981c0602030030000c000d45141205192068903100200d24000c2e8880220381c411a00031f030422956034600b6034120024090300300280c07415580c40e118140003580c03500106802228401c0281240d00c620308050f400e25001800f000141403030701552400e08040c60303143c04001007041c24260a0240c2c0342c1003160311403060f10455540580d01d0980072409100000d00c250082c07100c1e940c1048103041403082081203a0007510040e011403018480328074190301103042c88a10400d040c01400e034038141d01d012003100154642042420100c11a4889203a408049080343d1007400000240b02c0c0320700d0321011540ea6942404003402028143c80c2407801c5242600700301c03010541c80480607a403982c0d1015580802d80046c003540c65040d00000115405142c03501520780216003000c0040755203044a401274880044404105055004a070780700b4000c00c0c00e96203030303134440e135102d21518015151621301448140b42c80348805007420b1030b0004040714014800c032403840307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217047724 1250 217046474 217046491
    0x180c03060112030903060f0e0610060207030209040206190203030603010b03060f010e0408070c060e0a0602010209090c03060d050a0b090f06070206130309081606080a0b0619110307030804051c08 85
    0x9400802e41401c441800d62604068012030510240b00c0803400c299001c22150b4040000766071860f142c002ca17038407e0540070f229110050b400000301784050b14050880c0e64001d032004012a203170040798116920124030300422600560004404c00c5030a0a007030051500320750080f0302401042c504003010100110041c09540500203010000a04101c01901110a4117411242e0700780d4480d60341c400140903400c40381c00f9030300402141000160301401402503800d13800008240c811165a102e1442d1241c0d08002d181d103a0000074400d401010030400c0c001c1032821406486088040e14120010a19002808010780c031160f1110701001291a0f0110b00309130000308a24511085114900b0215402035954100b032406014501c101c0d0740c09400201500221119900c600d265650781d00110001c40c0c0e40000c595070000c004100c1c3c80344040580c102090840c0700c81c181003100000440900b032031508804021000310b20756100344002d02604012100415507003100d0740d241102d0161000f080040068801803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217048974 1250 217047724 217047749
    0x60106030b0a0e040f05060f04051009030203032a04290a02150a0b100c06060603020903030f130e04030908011406060f0c1227270709090203010e180c030601 69
    0x504201719082e0311744004d60000115803407420100425100e181040c2d400719040c0c4219600b624200c5802d005004e41980c064001e54210b079603504410180520700b005264042e06818200404c40f800319020b0800381041e600464002100b01e12000c81c0b40703000d2a80e1203000c2c9000c1c0001104240c1c00100d001482d40e1584252450b41c0726840b8950140c0307800e400c0158868019a00c001c1d4040d40304890b00c0140b8051042409a6580d0708030550882c0b15000354950160400c0009901580d031241c02006800040680c0550059646104404101e0f0644088002480c010350030031a209090140d04817482e16802080c05a0070280d00103482442145500c03503031003c0c04103000c07001440600ac41e1014050400301c10741d40d00e456855258500e070b140c0c01404c0e400c08501d0b881002c81e04003600e0318821042100004c84020101459103020700800400c0c0b00104510160080341c50821400554020140d500201c506821302c0040000801810918406158420190b40913203550000307000341103596203100715 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217050224 1250 217048974 217048981
    0xf01050a030f0603150b0d0201020c01051605010606020307031d060a0c020301151410020708030f0309030d06180f0504200f04050903040603060503071d25090503060106030b0a0e 78
    0x1980901070b080c03045415075240c910b00109002d0901401211180b14640400c1007030004010407902500d54503020380141d00c1864141915409040140550151058541401c1007141c3e07504d0300303552040c1c12210040c1c001103221801c0581005030300c3c0706406400868040300c04500d02003092070083e21030f004100460380c03441c002551001c1d80040d25040184c0d82c465100754466032229007200c00382000034010881c510310084550f03c007142e07401c19240000d02440c13610169400f03100064002400818140c001084404e0485140c5d1098030001c00061158101c05001c42401c4030071282d00200c1502c0050030003041000003061010800f41c8620400380380312444668401003103041154584054002d460031080c01400c1500001410440e011a5000c1c081c05484005054883c1000e100d0180040c00c04008055284d8240c031300c07168860b14141c01d4110007602c0c88074200b2415000c40400c07001c00c1d000700e414860380c1824000175015003041d0909210100703484001c51002110313441099495034854011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217051474 1250 217050224 217050227
    0x9080303220b040c06080606040501020604060c2d021b0904021003110708090a05010c050618190602120a0b061b070e010f17010908090103091406070e010801140f01050a 74
    0x120742094006111071802c1c0f82500e09415901d00750300401d0f012403a185d0009a10749091001c550030759030184d018000c65140d41e51840d000c1e1883c20081c90911100c2c102002011b0190301a00f0100240b46080b241c10740d040c0640a810300010800313a00c035140040da002021900d8021400750031680c15100303003519020104044005081809a03400c84000001c0d4181c14040f6000280c06041402c4401445481d0b6030300054400c44240780004002d41c000c1c40c00100c44081d8030341034140f070421701016691580800f00d4124501113801504644042d40401d0b500f159a41c580301c50307584500050320408c02c0c0c41c1c110740003400d24010340c0140c02080c4406043c0040c0310500f4400d80d0001c11100c10f0b00422940c4803c00e01100078070500412907101d90101010a2292050084603004c1d60000c52091800059a0045020306011002500ca0030a011800c000100c000c11080e8032607441aa42c003d41107444100042c000d00069029240c0c8402011074003540d9075500001d4100102c003424602d50b2084907010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217052724 1250 217051474 217051531
    0xc110102010f02041205071d0403140705031c0506041e1a0927060f160c1401021b0610210503040909060c05030906060603151e0f0109080303 62
    0x245481c154001300340014500600101943c0c421b00c42c009840c0074580310400b850040903107810a80142a9020105011a015801c0c080b061000c58448074501400d070f4496a00d50390001500c3d6203005d0070200081000d15a0b480b446811240894080c807603c0074605c00440340701040a0083c079059a10240f4540f49440601207001680f00a84450203510307105045504407100d07200202d15441c04c04064030112207000c1a5184a8180c546003210586c5a00f1184548010500100428005201138490206000681041c1c02800541c005617803220a040501c18014036000314081c2a4021010303c010603940b20304d102c0c1a20004131703803100007054007142340054075041e800c0503100340800900450403010b00e4211a8465000e40030070702038401c07a080100c506110031a004c1c8070320f810590100c1c03000e00e400340003550850242143c800060090f88000350003808910034140c14420071981c42c013481e04100782c00880361003003420017003a1145000c050503200e00c030051081040b080380c0301031807000b00300c286d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217053974 1250 217052724 217052741
    0x1201060908300705061603050f0115050a030608060a0e070b07021318020604030c03050105060a0302061b0c04060b190804050a1704030f060b040b03032502040212070522060c11010201 80
    0x4040301d010f4240b41100f07812000d030b00e861b07040000307045c03000140541e03000a1401e8101c440c0e0300d09130349420703080540c11240341d0403034081e0504241d100c0c080041c0580003080f603140a03074450000002c02044101a003480c062840c0d2085c141c1c03220a0204401607a0b5101511000401101d008107454074508045080f04503140c400070350040c004540803043c0500c910040b0140e0744144020007080c1c56030780401c00c0706a094800254055401c01050654540543d00807120300d1459040350390264504001400f85d511a40250000e4070004c83c2d100f444141c91480070315040c006050044ca00d003429220036468541c1082c01a080015000d14800d10603908412a4011600051442ca20120510384003000e4450384141074815400c1c00750100051501100301d4800c0b02c5106000c0884000207224005a01c1c411030059a0040c1d0a0003d00c0c402490102c8443c402c0e4400c0d680c260380c1d80040c0c00380465541605c480c48807944025102484550740111215000d2074018446915454050b40101d0140c420700c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217055224 1250 217053974 217053983
    0xc070609051c0914190504180b06040c14070503071211010b0a050a060311041502010501150309020907050706020c010e0d0f03020f040b03130812010609083007 70
    0xc21008140100815040d29801c0e41003094511145041412103403e00c41e4010792803001c484038240c4510b80b80507164560f030308109640420801e541c607070014048400304001f00d040c5104e0411309804001d000a00c5d81d5121000321401c100a801c0300400030300c00d91029440a60002d0001159030a0103020010b850810307920001603200b50744100e0000341000001c11410300d1646c20840c0c800c1440c80c0074500700c42580c10182450191524102080b004ad01f4020176070001e18004203c04950108038140f2001540c0b06a00045840e51610105440201420b1000c0d010185004141001a920344d90042c0d044408c1d842c0054450b145070600300001d2040400540c1c90751301c0c100088040540126400c000c0104549640c6100b07400310206805074810801810348841d820031040c0554074400002c0c40d0040303044e0a01c2d018031084c903075400b01254080c22111500308044801044031980c44940f42000c0d125201c0500b4400c00c800c84d1030740c84110810301c8051400e070141c10782d415101034942a110300f00d400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217056474 1250 217055224 217055231
    0x200705040e070b042904090605040507030b18070306080715020f0d0504030b040c09140f06010507030801051e03060106080108160608070e01120f05090c04020403051c03020706060605130f0b0d050c0706 88
    0x31f50011400a00f80b511826000f03d041200040c0c5642c064456400c13031400103449500508600d449090412000511090070705507141c00110340840300700f1a00d0050942644120801d118103900a481d00a50300e00100c41c0d54403045511b00c10590140581d030480342c1c001229411602c0c1e616003500c03040c8194020b0b0101904d0480040b84074468600d406000d00740080d400c142c00e0f00e030100110ba0901c20300c071015000c10200c1004000300c0c1000c2152458a10300c11800000f50307105500003a007420020783c0204002480c0754018040f94a0512080d00d121313140c083ea40303055512b04040507007251001001002071000c20ba2400d1201c0e405425008944d0034812820005400e03d1007400c0c0c0100801d40783c01c4690300c03524200d503416007013a20840f01581c0d0080d006101e07a5009075101228000d00104403820140c09005520000c1d03814040c00024241c4c945803aa11204031015500f030019460740300b88403200d00302000b000440d4600c411145030802d4940e0101e0b46a944110041c0d0611a003070004004525 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217057724 1250 217056474 217056479
    0xe0a06050904120e040b0a03080705010f02070c0306050c04261c02010c140304020f130209030601030c030506060405040c060c0219140a0911090d03200705040e070b042904 75
    0x300c440d030b60f0400d440e40c0c4843c400030f01c3c00030900003180c102034144da401443c40700007070002c03401245c080c29119100d50300200e402892851400305036004090100c4403000304030000e0040140e10701640340e1041c882201603003094a0900e886024811340492a00050828008411000428480504004c026450100445c00740290081c02030038560000000500350b41d88074070b40891014102c0340540c0e002443c40e00c40c0c1441d14200581c80d500c100080340d40c01e508000d0035107261004d208a50007103001d0140d10060354610700700350341458001040c181c0300d10315280401000030344498013502562410314261402a40510201e01201800d1132481c04440001e54005180144c11488444058050351f100e1091551f4245102c00d440a4420f140d0f800d40060215440b00e0610355806d81401d802072914410388109030003039500d480100c900980b0203421824040c00942020300421286000c0a001441181c4c909200c0c815940154054000503030000b00c000d158643c0c41e109107080030364648800c0e6a81e00c0c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217058974 1250 217057724 217057733
    0xc0306040e1203090c04020c030a08130f08070c050315041704050604090f0b010c030f121b020703050d0203090f19170705040c050c1914120904140601090e0a06050904 73
    0xc00c1200c480340c145c4940c00c00f4144508141c001d49a500250600031404c0c5000c21105079039003440140071019640ca0300e00746030082005100304803285070155039015907440d1103042041100c9026008640641c0c040d4404000c1e540d042c0011580c0150071582840031010703441039941d101d1241e51322071544482c004c100841d88803090351241a01519440041100e15011001501d401a1081c00500852901d00c44440d1613809655a11101262400c0020300302c40300c108101030051009010b1001680114010f004100c2d040103110742184650005500707101030031001640800300340499500418081524920b43c01c07403c0405000b4258255501e0b030005520032180d551084a481503e102d1801e107142c1c500c105005030112207061461201410b51904c83c020588900d90550304202d0304204441c03280d42c00100103100b82480c03130712002c28160342d910b01e220811042d261140ca40500000b14001880050307a08500c20000f200d16124464071103135245800c4c03e000b80415801242c120052408000801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217060224 1250 217058974 217058977
    0x150103030c020f0f1e10020f0d030203190603050a0302060106140406030e1606020f0d18060e03070315090c05100e011103120c03010509091204140a030804060806100203120c0306040e12 81
    0x4817420741740c900b020b40900000702e0780e480c18698480007581242c04440c442d00e11a8004560040780a1480c40100507011000001c035113080d8401d1300c49410a04410080560502c02ca600500c141c6c1b42244c01c2d1000401503501611541c881d0800341a507451010528460502000004c01c100c4002c8104141d41c4900c00f9448071421440040c403809100440c50049008414412a28041d4042a00b510381000016907956280006180c0e05220300d000000000304101030110300004100808501e0141341e01c0c0c0708443c1e6800c1d40141d072181c0010184219290303032021428814100c240b070030a5400846c0b41c501400c500c224088a00300140100030004020400c034001d5048507815506035055a545900b455140d40455105103288842044100103c00106600380880384005200b880c0065680e07444c040e45a201e54050004604c0190801416180c250400342c88080d860005d54945031042d0f03403500d0a0305008020540c0d000010011541c5604c4650002e840c0c034811600311080f401044901c13501c11f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217061474 1250 217060224 217060279
    0x30507172503260d0c020307020901150e0301021804020f0c030d0207030e0402190e010203040806090c0a050d050d031e0509010e070f14120f10060305150103030c020f0f 74
    0x402c00c001c03100d4100348400c244200400343c0c10040c00c1c1c10910b070741948801401c004400c04d003c500c1300384081350242c0d03160351000d8028a03009100805108075448040c0c0f0121240c01c0f41846a441444030b0344030b869a1400303010103070100f100c005076603282d040020b101e81c1c014042040400d11022801d184072403100d90007040b156000341c41d01c40010a0441c20403090f88a005500824541640e170030040700c6008801e40400c480b41401a00d08058545081078580b481c111000300070741e80000c0703d842d802c2c2401860080076110a5402c0c00d0805081d86546039030740c1c4000624820540c5c0c6410420f942c0e06100254003048003100410b0085080c50103149021308000890340d541030290500000e01d14100c40c4619085600120341500307120300311010040702485844003c1c445d8058900d03050044c050602c8080400d14410500081050450a001c3e1030300c82d034800038003c0c0d00e00600050020a40104c0710f041c100303504958002502c0e1084002c1004800c1c0c212a054000c00c9100010314003048d07030000480c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217062724 1250 217061474 217061483
    0x103081303050a12121a040b01201b030a0c0608040f17030708010b0406020c0405060409020d0c030c141c021f03090b0c120609090a0b10060f09030507172503 69
    0x483c605200c407440e0440d4a10360f0078590040708030030011b8280c1881c3d001000a048141060358900c010040c180c0d52a9903e90614400b03500140625514400d010840070b018640550060592074050f650380101c044460040605000c1076200090402140184000d24030b079001514030302504006450a106410540e00c01c0c001c04c95080001c80c03610303540d4064404484c050390050610030075140c140b1006210151880346c0180c0c49140d00c0001d81c8442402240061050341441f42503451400d1800841505800641d2400800e8000c51103a0740c0e01c101400356411081144004110540300113501081242010300100c0110310044c1c0702946c0582c8030903921130107403201c0c641d1903442c0903100805100c7c0144554060000350049441810107540481d401b400400031508081c03100d8171900255007041300d030303411740b0001090140300e580e500c142d1900340390400742040310142d4103503130315581c45030341500804910b074506040c200b8080c0b20411401c4d05078900b44202881c410104140c5100c80001030100340d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217063974 1250 217062724 217062737
    0xc06030c201207031e08160306050108040311011b020102030106020c0d0f080903070e040b070f0c0b0402060309070b0414030115030f0215091018120201080103081303050a12 76
    0x121501c02100c44000e500890304058084501c1800c50000141c001c5081601006681000c14403400712448028040483da900d90701e9040c036200c004111410402100601090b040c001c1c10006a60011103540d04243c0c113040500070305180d200c100e030040ca04001c139920240d10a00400c00d47e9501903000314141c50055090343e408514450611001c400c00e140010070003840c0200b05030220340600040c103100013005081e82d1200d03aa40d08000380c110010b84040d00c01d00d1982050003000d42d0003446500c3e0101d801d00b0944009007490b26030552034000144013a0140c840000050801c060500010001c1c0c501e0761002c5494640340c11010381c0300c4010204442c0030b5843c0680904441003030810307140c21680d00004006a82e02103a081c0084000c4010312415090024403003140c0507942c1d440e640786000340c10f580380c10006000708212001042c1c2580000040806a6203400142c2da100058905683e000000240c0e00c40203005011010340b1564000392441c000c00000b481040319160080120751183c3e03842c0c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217065224 1250 217063974 217063997
    0x41509030e01092c040c03020904050d080f01080d0e03010222080d0215180304050607061b09142403130b010e16030e0a060e07030b0c07021c050a0c06030c 68
    0x1042810b01c0490b030300130f0450500c05100f160010203803642d90082c8542e20100da00c0d90f40381d003c54a5460250f40c2211940c0100040348211613020088031f0f44120741201500055251100c00ca403035101c2d0300882c7c81000b503083c180c1661381d1000d404039660661200440051981c03101d01c144040c40e43e034040e00e0581d01841c207400341c005200041c0401c00380189000380d038480c0c44980522141c0480507000d0072103800f0500c40014a0741da0040a000124082e40b00070421400d14168007c981c0f609107403d00c00d201407410248001220031144d80b81c203101c1600c1c1c51091682d07001003489091101c12550704443c4000041150380d034a415202031045210f0b144040c8580d03250000d048070020b088030520000802103001c070504a119412180038201c456043d1120601287c43e0503003602d04205039082554003140d0200b080201c1081100d5001d0b0341c040480b4107001d007a50001d407841d042640314603669021859408c040c00414400005610b5200c0145e0703411070f9032203902030f000d45440c01c94200415503c1c04607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217066474 1250 217065224 217065239
    0xc090a05040b070f03060f0b03070320040915090516110a12080411030106150e010203041d04020612090604110607020306040318050a0902070b072105041509030e0109 73
    0x220390169621001009150751071070422200540c46120781d204268a07010300045124075203036001d02500f030050f403803a03070391030010406026144d00512000c80041d01c900443d9400300c125041e10123454045002061340c0a80c010b501c010999590040002e00b49400107020520b0a0000c10301c5d1640125183c4d80b2241c10345101d45d507210020300310041d02c0400580c0c15034a405104907450340d0f0080c4104c60a0208070901c101007400c40c4e0040e003090345040d003480c0d052086180c04c01807203611001e0074801149001d003070084082c9001c820040000501c40c4000110b001c5503258420743c0c80c40e07800e05c0d43c001d1640c5040b90003c0d40e105401d03181036030800c20400110681c1e003048021200260340250080021f91101e583c102d43c51203d40c90700c59140c03418414040f815544e92040a8020704034400050b03102c180c2820700c890f04030005001c18080c0400c0b881c1a101d007a07036140c0c0550310106103820014075035403035040c08400d16900c2c800003240b03945440035540405820840310001c000003070380d460059070f445a00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217067724 1250 217066474 217066481
    0x905030619020a110109050724021c0203071a060f0a0302420408100b010c060c0512010320300a0206030403091a07080301091505030303090c090a 64
    0x5002000d003126890400e400001a0020f010155040c03602d061101c0000340310724215500c26008540941001c181086100c074000c920460b6803003c0c20070711040030682d20000c0d54030380d008110421014481c1c4030786980030303009106450407550072440d4241c8600b504d45000c1e03001d10040350801e1042d4a0414038107091b040040c0f00405983d4007410003900d2484100c00c0401d02815111840c1c410b00c0000c5064049001c804c0c1e010303820726420602603482d107080c21100c80c1840b40c0d584542550380e180c8155200d49c3c0c3e84c003c1c490301030141c10820008840148100c1151140300d141569445100060000020445600034000c02071202d10b8001c8000112081007002411040c02c80015418244c1e1008201301443c0041403010304403501140c0d51020554041000c03074104130b80079008998003000030441c00a21003407000703400c3c1c1c661450b603103800f04660b162144fd000c10f000e0009440e94070403a44000340c0c070150310400035000c01801c803a22858031802240d554215809940c1c042d0100f00c000c03544ac03605600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217068974 1250 217067724 217067731
    0x203040b0405010c06111801020f0c100825090302010e03070b0415211d0c130c02010906150603140c04030602030601050f030f040b0601020f060a050c0c011a0109050306 74
    0x8061071800389000b00440304c140c0380303420507540785954800e905130303a02081004150702a50048000317903481514001905140404292080a0700b0280d900215650f502e10046084c0300d050804605a4030b60041c00b41119002d0390100c4242c0e001c031065a040755410141c034404aa100366200f0703001c0041c08051503142c414a11815141308014801441040e2500312916002c0320580340064100c0c40403614940070b0b150180001030b2031661602040280e10030b6041b2510143c2d1190010451500d03c0340c003040d41052250b441012040c4c1d181000c030b90a9200f9040020030642008091208042d12410040501d03000d208240c0071038078201e06100c402028407c5a481400034107185410545161070303031800b0358402840503041010803c104981010300e40c02441c081c01c0b01c81081513052401d40f41004000001404107410765000c140d42105884000654560004100320085900c0d00d803d580070210b030180d4441808503500304440000e0382c406071100d001511400b646d0700a40305a079034051584031001a03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217070224 1250 217068974 217068989
    0xb01060f0206150411041404060605040e06091509041407120c03020603040804050909062d07031e09051c030e060403030b1c050307061a010c1b08120304050706020304 73
    0x2c8006803c28a90031900015840c3c060008038030190a80480c0a0300e40c840d411640c20303e1841607881015042610031080541501d00f08249014103146400c00341450091186204d01d801c800000c4421140f0041c40f48480e101800011003030070300c3e00c0e0007140303c000152000c90a04c0744141c0080c5181c90100462896501b15040300101402c540134005d460740300500a40b01904208400591a210080214424191034019051504119500075040d001c9080741d0300034600030040c0c02401c0c0c5140c1c204580c10400360b05002400003c00c04a500e071410814600415891400140c101800004901100c12154498451088040c4044c0a44c2110300442400b039031648810000382c0000c0c0642e018000502c03004007003210340340c0c6484e5000802c54503403400b02c504e0707040810b0f20402c00405004101507034030800c0d81008201c034828002441d111117100068101300f40e00c0c0e0b40701010340366a01d20801409014054403614150310b0183d003410380c000e8a040700e1078461180009140da00c044103480680d07500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217071474 1250 217070224 217070233
    0x10b010e13200304051b03030301050f0904030903120906031b0906080709090603240917090f0901060305061518040b2205060f0f0901091503050a030c0b01060f02 71
    0x20003416002052021100508580c602081d038200b0103000001d544030f144a100205942d19030a0160540d405010340c3d46402980144010f0090f5682c941400d40d2120707003524035032107a5980c0d04084601845940c009804191104807042840b98058901e106a0f112602c040c800c010400151078081130455407a1000601d40c65028031025200c0d085c0650041380e0ba150980d0b0703003074880d0400c2c0d0481e25a544100d80c14421044520400d14200843c02c04d0050b0342d1500f0070502a554541002c0501c0c00c921b0a2500f1100103001750700350303844808445582d507026141c40310a40e150500030380201000e880d0103205118000d8542103001081040300c80d4040708443c08103070184050103003c0908424606994062450756a8100850015a411205202c0140c0c0420301e03080c00028000b1700c0c0b001d0103031039004100c44107552100b07880c0c42e4034141c1151003d0b000052900103140d0390107a040c0b030b2031300010f01c503002d0b64144605250b800303172000d05440e001740301c80f0600d03076a0b84500707494020140c1040805a0070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217072724 1250 217071474 217071499
    0x9060e0621070b0a080109060b070521040e0a020306030105010b181e040c030b010315080a15090213140c0c06180f01020d05090d03020301211707030809010b010e 71
    0x80400194150506048801071600c0343c1d000c21084d00f01c8030341100094800b000401102009020380d4000b03010340700340b180ca004100d0320784a07210301c0007103142c00c02808055031514400050804840c018092099060601e08200b01000080d5000340d0301244250b0034000080381d02c024110450307008107a0912f0b0898147c400200f4410303521910701d00040c0854111a6800e1292618040e011450b401c170ba40c0041c3c0c041140001408488140e48800302c0e0f4054024244129a80014520943c0da0001009a00841d085020201a19040750029002904401201c444e6a0560495160303040d260f92480c1d03d50f910420260124050020700a507142e0000e00491050000d800314100d00024050a460042c0c405000c43ca003660700c04081c1422456580003085505901482500c0c0c00c1d000b03a18096245500d0002c180440e650307030f8007900a41003414501c4504005000e0700d05981100100345880d01c80c000303814040c1c45010110b0300c0020700c1d42000c5c401591584204012012010000c000d80040721 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217073974 1250 217072724 217072759
    0x50d02070b03131a090105090615130f0207020301020708040e07030203060a14030a0b070c05060109140105220c0302040302010e0a051309060902311a100e04050a0609060e06 76
    0x40e8070207001d03540102e0301403444401450044c090b902c03a04900e8008581410441812440d007900104401d040c010044130400499441107105d07040c2c0c82000e0804180c881c1d120485000a1085001c02940f540c800200c400c2002140720181c030469000d504901030300c0c0d9444d10701b0340680c40f0031100d9581c005104101402184a2031951004030701001e01121080e0b412035070344a0040c1030507078400020402488905040003010040a4090503013000c0034000c45015100b0210340d0241070088030700c070702145901c400100c0c0140c5c001d988085551441400325840c02200540254068082a80010048059880e031402c1055a02d4110703080540141c00014400da60403004101205040f205a074860384a04056541d8881c010032104408080c1481c1003201c3c100090b40c0e01c0c1c40301001945038200040c403420080c0d0440b92105502c01503518090205150004580a030b9207000f07840c0c0d225180071706100c02c8000ca0b0f4404810340748100c404005181d03d9450601c04d10108172102d5500c540d13030301484031052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217075224 1250 217073974 217074001
    0xc040507020115030605160e0d0b0702030c15060a0915030602090a05030703110316030302120703091503060302040e0f03040302040f0603020603090d020105010f050906012712050d02070b03 83
    0x50058800043d01603c0a049599050002c2c0e2003642c903c0d89a10510280c0c0f007407015400110300c16814103070648400440801c00c09000c0000c0030f4604180b040001d10360b64028012078803140315030019180d01c0c18405095030203800050300e806e40280741e10180483e4000040c07081088001c0e8160419003180e2841c1d0729035001c0e40c070207800b950304540c080300300103895201045104040d5124542400e00d02c444501854504084481552102c010243c01000440c1e00031842d0f01c0603040c0c0c0c5d6000d40e81c42070281402e59095010350b03c984c21542c14429903aa106515510075800d0380d100322020f010610031101d02555a4525100d84545500308110410042c035180c0d200e000301040721903000c101030b6520b400080543d0801c0350074503030030342220810001c280d03030a00c181400350030310b01c4a407020241443c0c041807201000510203418070580645055249411401c0e10381e001400c4104101c03060b8655125031036580c400c00c004c662904c2641c145602041c00410031405964010f00045e0031584c03030113070404a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217076474 1250 217075224 217075231
    0xc030506060a060203180a1701020d0f0207020607030f050f040924060f0e030c03010e03040905010e100501030c020c0405090703140c0105070312060803070b04020306180c0f04060b03070801030b01090c020c0405 92
    0x1f051980d070000451140200e50000c0e8102d10100050325a1440c041c42400e4030100b50024005a1041105c980145e81c0c10058030900b40d09071078a90710000c1043c00541f018415403c80038400c85008c900055a036403140c00c507004c0c80045000030b210b0402e948031a441040e040340290004900d50007208030866100d264070640b0214018125003500c458031010908440b9510400e51550300000b500b0301c44400e00340a61801000c0c0b003903a0403001d107050060406c058403a40255810591604507061055108000307203100700344000c000700407505100c10840d031740d504544003c8a003100154050301ca030402c042910f00344085c040c3c441070f2a0281e15a01121261617801608400a0713a410012401101c100f014021013407044500002a0810380101407074500d000f000c1c900e00c8881001c40402045000c42c0030301c000d810984089044c080740300700060241072a90407042c1000c2d000f004101040760f005910a04032402015080c14590305d8a02010a5030389000d8858003580c0301c2c500c86045410f0070b0340083d82c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217077724 1250 217076474 217076479
    0xc0e01050306040c0c17030709080d1d06070b0c0d11090d0b040f060c090512010b010c03050c07050d1211070b0f0f091201060501030b0315190b0603040c030506060a06020318 76
    0x41181607544096005801350790442d1b000000c03080090b1680c00000640183c0003d200408201c1b0030f41c4030052881090603c0341c103001c08611810b08464031003030180e4103202c0c4d00c840c500445151000c1259072641004500c805241d042500742c980782c0700410111044200e000e800c20039000743d02d4480040e600d102600407210104c40041d00400b1034154400c01d5811000341d61000540c80c03408013000603115800d40f83d8410703039240c2398001007503a800103580c038540c03039060404035196003807808418104a582e50040f500b103404220400200018561045208019501c7d102c80c0307080301b042a030f55500030501810070004400c109104d2083c040300080c04070540740303a1900345030040b5540070904030034642c1d070780c486035079103880b0103000d0b540e0140280241140140c00034003e843c603c000000800740d0140081c103002c45130544003544102c0319003050218402c003500403035981c1024076221040c01c210b0711055605004810100e02140303820141182100d280b03900441c01c4c040054100401c10090605565 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217078974 1250 217077724 217077737
    0x90606130b070f0f110310020f0a080403050d0915061202011b3201050109022d070204140a050c04060c0809180c07050f0f03161109040f060c0e01050306040c 69
    0x80000c4040c401e01c0d500a00c660304005c2c41840c0403040c0761910700010701003c000d600501018200c3c400d428283c5004a0a6252211240d11030307040c1507481d40708144002e0103150422604100f440250700d4040c4010000600030820300c0d5030740020005140743d6000c000e001684100300800e551010102040e00700380036400e103606120740d85120801d2603101c100a200f5600003000c40c00c0d500c110a2003041d0040200c11410752030b1142111420759014880400004511030344560303c0d82804441c02540c003016800380080140b0f13600c0b14440d0f08a1102251030310b907050705040005000003000b6058400b00d425588070004001c0b03041d030b0b4000c1107400401c52250055020100c5105290100e000c0b07500448000f43c4442d030318411410300740d0400d41694825111544108500c0c0d100d14000011030b0f0b0b101540b0003080140150070300e403115000140003c5298080b07540da090109004241c824010540c0c49200c0800c11907a403810103403003800c030841450b4040b40051001551a0415070061050091140b60a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217080224 1250 217078974 217079003
    0xd080705041d0108010b01030504030e100c0b09061609060e0d05010e120c0705040b03031911061609060804510b03120304170c0d030b090606130b07 65
    0xe42c80e48807100c1c000d02141c0c180c1401004080d000703100c2c01a1140d400c2c40d0078006450f06072405007814454410203030244166031440030309984100000f0400560199451110b800e10b20b0907559980000d803202d0050b1050b00c0b50f100c41c002e001d4079911085880c682c9a114804444104111a001c4d96003000d85244d501c6102e0403210f81300c207111f0040d040c00029003603500d45c3c840f00710b41442c02507203401441c0514a032111008c2940d80000076560700e44105c081c1903075034004500045600281240c072241c954841c8209000703102850820450310308045940d0400016aa11821945008140e030094030501090994038100c3c24240d550360000a0080341d8004050014000d4410314001455841e412200d041000300366a1154058451400d404070000d206400c400c00d0303500400e1102810081407410100388450b010461721058072400b150000c1582d9550800c0b01d0007a0241044d9540c2c0781c46060013100190a40c80c00c0b6041c0c411810407150300440da141407529500090b0310110041d10304000d005c0342e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217081474 1250 217080224 217080239
    0x1140c0d051e030a0c0e030703020108040b0601021612030f090b07060c0306051309150e1f060b03010e16020714060c19120e030105040f02091005130209030c060403050d08070504 78
    0x25070144c01083e40000340c405600300010418103210508600c20381041e40b04001503030744483e01e207030403a030401000c031019140c03440140c0c5440b40e0040d103500014001400002c4222040c04400d089901a071145024070381500c40407100d907030b602e000305100e03c042030050101060460740040c55030060303410005856900d40e030000b8640385407a040009440c0d01d4040903410030024003008801c1c031000703030428003030070310940b0003952120380c0800c10302c0d000071340d007600c00d803c0d00c1c0c2a41042c4000c1c500c0c0c072f10580c0d40c2d5031941c80884010310121030552038102201ca251401a20010b9880c0884142c2100082180b415004005650703021400c1c1803200d1182410102d6501d0120079400e08003407007022140d41201000310302622400d0030003042da200e649400c0030803001c0782541c03541b503400d2a812542d010803070380d8201e06281d0081060700049d40002c2c0088083d4500303c0310354010305000404404036800e409540041241ca4410f42c00003e1040d00308011071a081c0c0e0240019507088182810035505068070781c100e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217082724 1250 217081474 217081477
    0x30c02030f071205100b03071a09060304030f0305090a020a052106070903050f0303040f0605060103022205040b0a0b2215050d05060414041e0c080a0201140c0d051e 72
    0x407000a0041020801c01c004c01002240b54501c0350b400c080c0441041c10700002e4403643c480c41081128540c5030740c518040c0d40d03040d04640444000901864a0703040606004041700021a03601021a250601150740750200280f000500caa00800c2410765904003401d000189807080b50344404480fa090b96800c0000d014840c00d440b910715a03407442c0c241c83c51802d250b403401d106085140e0103600204113010105105a0000c03641d69001240425a501d030200102c00901c690340c0142d641c8484030504071900d420501e00702e4129001282e0030b20021b600710042190803d4144506101c900d01000095004a04035240800f00010700080850243d0b4500264030800503100d803d8000070380001e280c486607400f03480b80755003100054038204156020b0151ba1131100b00c026102800c04505400e010990800c0010113145265202c1c040c01251503407141c0c0c655a8031400c2004a001c03031811260000b400c50140280da0404e80d0440c000c0240311111070003641c190340a4945071281002140b4420ba02c88980d10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217083974 1250 217082724 217082729
    0x115140402070f12023a050f032a09030a020405040606030b0f0f070e06090f2709010b060f1602012609060117070504050a020c16090b06040f03030c02030f07 69
    0x184d13907240300781a0b0f60009050010a402c049820460b0003100b010340002c0565000e0f058155108106008010301400d031000d00550300c2c0015410000010041c490456440c0d00740000040d2218106181c601032040a80c1c1c068100031580640c0116048000342c98140c00403a0400d008020000e1220b4494a802d54500011a46041c085440c401444501c609a9816580c016502d2034001504206040055014813071020103a04c01c00350039840c000103035180040300307443c10704402c85621039464241c0591400502290301208951a02c45008110f060200c21100c9000c5e00c0b0314103034940341e0300c1d01074101c6408003544203a040250070341e285800304403412201c00c02e413a6451300c1d00310a443d015003c1d41c50610705800c410b0280342840d041c81c0042c00005510815501c2c00c89000c2420303650b08540c540240546500d100d4240300c1c1d17148046825007441451019250a000e040c4083d081c500c0510503107202c3e501c01c502c3e442c01d400c0000c0001c0f901c1210038420043c4020b05a5100c1001216110701d00304103034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217085224 1250 217083974 217083983
    0x50312070b13140607120c0903030507110603090106030302100b0d0813030b070801030b060d020603152808061f0605030c1201060e0a08010504380103060902120115140402070f 77
    0x1e1301403000a5410040b45c403c1411551014061807079003c030b00424841d242d00c0001c040c010081042400c1000000c6441c1c0c10000c040c1c40a5180e14100d40310702c0c0688410310055015002d140b102008849190103040f07407001c0c010304840b1000019655809099010070081204107000725000700009180714191401030b54595502080d950450526101d5140c014013001c1c8076544082d01d00c001030311030000352a84240f400c604400b41348007060200b070b810010018802200c031022000b0000c511141c4806500b40d4410904445032035503a201d0b00800d50054500700e002d0f54150750020480e05d8450801541e100224550140c02d0801710f801210500c08283c2042000c44d4140b10884503c1c140000d031a0014107443c0c001b805182080e8030340d016400c4541849024800ca402c80e00300c0c0d0116202c0305a100c0001300c10000c807a079a0b40f0708000b401021b03c0b103412442540c540d521222a544140106003085041002c0907050364604200010b90080b01c5204035042a001d0120f03030003160103001404c948a019 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217086330 1106 217085224 217085233
    0x80a06060f050f0112050a150e0f010b280306031505060907140d0b010e0330090f01030b1306300b0f0a021e090a050312070b1314 57
    0x23028404800b010f849000060a020550a2135100380c08001401040b41d0b21244001d03c0c500c940c0904040e00c81480400810204c641c2c0222a4403400c18100010502d5580c1e0300c0c801d400740103810791400540d403042044610b04242c000154046802e20304561410f50f990300c4204507008007000c07805400d0365450b412503a41d005540b100304048000b8102d0f62320400c0c0d451003402550a420210002c40c802d0600c020f2b140140c20241c0e4100540144004a103111000045000300a00720000341e000480c050100329148003485070001a000c03c5821508400c50150f491042c0d602d003401010040c22145007a201007403071007034000d41229824180102d192a2400017030040d001d00000c0d83c840c604804010108118004010400407909403502c04000340e843d0704046e06c40d074071400c142d00c0f010805c0042c803001582c00032505902803010008c0d00f50641c7c0796240c000c0d00720a54501004503510 = true := by decide +kernel

theorem cover : BRFrame.Cov 216906474 217086330 := by
  have h0 := BRFrame.cov_init 216906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216906474 ≤ n) (h2 : n < 217086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
