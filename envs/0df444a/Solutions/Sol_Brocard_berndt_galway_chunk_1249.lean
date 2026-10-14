-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:58:50.482335+00:00
-- url     : https://prove2.me/submissions/b07754e5-aeb6-4b65-bfbe-b29288cbd668

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 224460431 ≤ n < 224640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 224461681 1250 224460431 224460479
    0x5030a06051e060d0209090111070c150c020109030f02010509090c030405010605100f120e010c020d0e04021309050601120c020f06101a0d0213060801210314090604 72
    0x352a0681491400d05480507a0002c990500c2d0140031281c0c0e1900c804000340f0b6011544c05907030b503d07507015850040c5803161100300001c1001c188001845855840401190802d0307001d480d10100b04e001c00c035012800244003d01040e42c0d82400e0011501710306100720031901c10f0520500c0c1c07404280020382100c3c403c95100c0c01d000d100104000170400c0c01c0c0541001858242d0324a000000b28030006085a100c040a400420510741141111144150022951010010300030440600c0e948402034540ba450034140c0f01150440c1d502a8260415200315580c2d400d415040312144e5084c8041c9101800c0003a002504200280e0b251030184a4070b48507030701d8104115002400800a018002c0e0704010004000b500b815211420030410018028941c82d11892003030841030ba2a951081210021300a5a03180101e8050910001c00c88030b0b0445141030603501a4000c800003c030301d8131002c003000c01d0a040020001003001c8500303158545820040c0c45414802021217090544807804070300f818a003003201c0301071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 224462931 1250 224461681 224461691
    0x20903070f0314011103070f020a0b010e010e0106050c120d021308010507020c0f0d020103090f12020102181f051614010c180f0b03040201141305120d0e060d020405030a06 75
    0x10000411110790105003043c0080c400300200700841015400b00a00b00c40c1805200603142d1140d034824480c41c0c1042d913001060100e2075131507504080f1510000d0084501110b040c00000c61107038050025204d10200320744c01099450080800c40340d041d0420000c00035129003d0103021002d6180409a0010340411130000501d407400f6030340285032000b070100c650700800500aa406031a201c0100e520802030f02828040740b04103207441d101010707500400d0b010b01041d003802d144820407503042d0000c15140c0500d5000750160448041040003806440c036660512090000f0350103682c2d4041e0300540b0564585000c85581c900c01c68540c0e0b90341c100302c1465001c20365510440c0850040d00001100c840035031340e00f000a41581003805d0181707030550a00a507049a81c02100050031a841417204241006c003080185444028690791101e040c50300e806078602c20494042040780c10749000030004103454032075407070401126201d01070010544c4100c0c0d0b20090242c081101054a072010407003860714920480d40010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 224464181 1250 224462931 224462933
    0x20306101443031b020a2c070306050a05011b0b06060904020a03060503011a0306010b09040b040603110108093403020a030f0c0e04020108010e130506070c05070b04060f12020903070f03 81
    0x450340d0303884404d0002c0f2075150100c0e940962246a465010744224a940031210083c180c140302c1108800c0703070181200e00c8424200300d21759071b154003c00100c4e001035540a5819454000658543d00688008851901d44a80c10360105203c603441c0b035003001005e8a101c1c9440c61001c007003002d0740e10dd069480b01098a69070104400c0c1024410205006010b2b82041011004080025203030a4103225459101d040814030408554503a0300100075840010810803040c0c5e900d1030700740540d0000c180140d0200c1e00d03000008100400218901d00400400d012071004129040101a250030000c005c0c400000c0318004084016211b4520b000082c0d40038000340000c40f0040d00e00002112071507000744441c0e500100a002c0141d8001818a040d1009800f400003503a071101480a812a0782035000380c081d1042000744030044d5000b041003c0e48074000e009030340445403140070004941c07140d441042c000501c0600c40c100d210384190b0103141c0610341004054546031314440000c4c5041640d40142c1049885840100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 224465431 1250 224464181 224464187
    0xe1306030b060d05030901080c1213030f0e032a03030307020705031204060c0222050c0903150417070c090204140a060f0e0f2202030610144303 63
    0x15842402220f90781c958052a03500c40d0380b80d004584040703050121303603004501d103540c0800c1981c0c03980c46003200f1001145011850100700d801110015400704008000180c9800d2084200c5001d00b08003900500a4807180da011296100c034020300000300d0700c031240710190300380e03002d2006600403441a03004000d05810310040500f418a401d13000f40845000304400c10040c1e8002000507001501142c0d4410003c0d0440b070940d2a040e4208010314915203060200080000c5001c05020301c01420780031194903510324141c5e0700a540040e03a014200280c500d8000c0011142600101601886070b05242c1810380e40e81608406d1342c129410514046a040358140703514100700d0703034940c01000c1c1c600c0c106030342000c04103000c1c01007103c211030240501c6c06000d140000741c4410040c0750020240300d000d043d00e401c118803404d0094005455091140b0102844046920310880b540000d524225105a01c2c0800307000b81020326441003500500c96059111503504110350303280a014100c141d01000da40340a22a00d001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 224466681 1250 224465431 224465453
    0x70213050105010315060f12020405120d03050105040624030905070924030803060d02060f0a0801031103011103130609020907020f070f080a08160803240402041a03070e130603 77
    0xa02c0d0300c40b17090410030100380d0090040f8900240d9043c0b413600348880c1031904001c1d10483d08496080314042541300400107000034034883e80102c541c1e0401259880c0c00400066420b40d11072100c140144020520f840c000042d01a03040341c0c2c0302c7c24001503900ca169111070600f9410ba00c010841591011400155080000c0410000700c0085481050740e0031a910703156a4000a00118000c0e80b0f503808850071525460100d0340d0340c011b040c14040c2c807441545001490600240011030342d00c0261320303500e242ca0a050080408000c0d501a54609580e5502000054008038080956410303445090340409616415680b031b014140c00c2d80076007080e010f02e4482034508041c50b441601c44d40340c00c40080000319004201c130210070782e200010710354905005c2d40551060402c3d1801824684c80081880859030f0320383c0226404c041038083c000700c034160550400c0224000c0d40701c3e210541c0220012030b000c08242c1802540e0100c81400c107501603200c52008950300903007422201508560303542050050100340c0b03500c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 224467931 1250 224466681 224466701
    0x415030314070206070f15060b09130212061c08041419080616050d060b07021309030f050c030c060702011e110f0c12030403050a030e1603170702130501050103 70
    0x1060b151003000d5000c01c0081c810040090f0000c03e110180c2000c01012944da000c40079801d00c400d019041e00d45592211562100801c180304450702d089085d00e0030306500030364420510040b620340841e80c1c2d500c1440024890030080e0303000320b041070700f02c0c07400500f510000c8c20203413000d40945501034010310248040c0214a003840c1c103811118140030091407400060041c0d104142c180580885209900117032800e00441c00c05007a4603040010220b20814284040c01849000301d41000c990004032035201c084842c8d1010240020f41070608a0a940340900c0c001d251441c0b010080364a040d480d403400e58141001aa1010b0051751140000802d2401c110744003a000c000702780040003420780d883c0801359144111442d0f000310304808904403402074030512050100503035034411180d0340d24103490014015840034007101c02080c074080d1100ca91420015004241140060002100380c0c1151030310700540202441244098608102110058554210300d4138486590310001c5107a5051200140a42d02c00d180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 224469181 1250 224467931 224467967
    0x103060b130e1011090307090c1b12080105090712020307050403081603030f06060e0f12150f070905030613020f1309020306090312070807200607020f07080a080f040504150303 77
    0x1085c41c40c0d80d036020945a0455180541c0050300c0049070200ba543c1202c5000100c195011844810041c8510480d0550120800d41d8900d80e00360b8890081040960065800c8000600d0f00e80020b1140c00480e1700070f5401c01041e084c40703030400c1e540c1d5841007002c0e400551030700e00400462500c8820036405020344c5003c00b107100018020b071801c064004080042e05240c0034414592400070b091941c40c0c0d0990080302e0130000701520201540e101c030101c0c05000c1510096401c00d42a800146017503c54260035007528401005482c0c1034450b8000005080054641a42d001e000030389444020b5503180b00c0a0080b4000805c08114241680101420003000411405a54004000e10380b000d000c4de01071294400c00c07905011030691104501150001c004014901003098103801b001e030381000004a492240380964215040503090744101e40d21079125120b0b50a055018107100000540d9120251a0300101084002d05141d80c0c0d500140a130b1304040b800a403503240e120000d1043c903034440c18030201c200b60f0344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 224470431 1250 224469181 224469187
    0x5060105180405060402090907050c0c01030b010e093403060b070506040f05070306020d0f0e0106030201090501051b010c0f0f0c0305091003180501020301060f0908060103060b130e1011 81
    0x10740412601910100c1880c0b090343d8440c001140d03540d031a03040d42d510301c0c4003804100a500d401d00002d449984281f41500c8503105809200d041984640102d00701d4101c103940d4500140d800d14103100010802a2a8250b402e0183e00000034034944016940d418040b544e60300660217800b400c0280459180d6081002490420820720010460020ba0942c0080c0d01110902c101600e50030400e040c03000381d800082c011400000c4021804161b500000089000d00c01c0400025845900031800c8605900c030003130110700d15031010803d66018002601050b90000200030210550300500c50865001d22409400f19405000030149998032219191b0721030040d060498044800d61805001070080c020101e2280011049030000301f803080d00041e165040f02c4c00400c0080c3c0f4180303040d6010350424042c0f08000394400c83c0c0b0519041c4206105011030705c5001c0544541d03403c54035402c01801404142e203820419440c882d1100b00046c1c030074440c2000b4142c000d8080c0c5c09070580c0110a0311a1a24500800407040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 224471681 1250 224470431 224470447
    0xf0305030a0b100315120c1e080703060507030b10120b041401080d020d1803060b0109080105070c05060618060613080307030314010e090c04201c0f151e0b0a0509010305060105 77
    0x200e07d0410980d05d20140940c00d03841e44540441c641c140307603001a009402060b42c00001c110064110318056030003518103010b128003510620110700c0899050a0008d03008407896141e40001d0b511079002007201070004039504a440f1150303803940901b03900c0440a50b10903074441c89040d605102c1015400103074a001d1440c010141040d0810000b42d01010b468203035202503480351b40e0302440c004802418220300070b011629140c0b50103001c40c0180d03c0195194002c20001400038640070010034264540400891503e8880c501400f0f125044004440b03c3c00e4510752002c142d00200b0009840e08038840d99001c40d5030030b00c1c103c0445080d041a400512000783c01001d22901c03041c0881e50300705d0f02c0410344001403100d01280555041c110b00d40044030756500c0c002034017050900c114076030500b00000d212042c4034249000451604854042440449020107900c0c20300520101043c08e80b800c42d40300680005150315a940607466901900405010810014110500d9605030081e00d41c40502424003904089032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 224472931 1250 224471681 224471693
    0x10b010306050a0303080c04091b0207050a051305040f082b050709090504030207050a140406050d020d080a090b030a02250510021c15060801120f0305030a0b10031512 73
    0x15000040500c03030305a001030391525880050b90009d03c4518028041c40c200c80c4000540840e81e61403500040c0250400804c190510b6408602210380207403000b5104440c0140e11030040c9005030084503a0180640351300c001c56440e801401c04912a50020301080e01102c0351103034031000030900c030750780141090100800c981d044824801124410440484d55541d80d2800700d0416800e900101e0f40b04440d10008590390014483c030741c203608000e980820200d6191000c09c022040034400003544050f4a0f403081d80064014006400e03001c4142c20040c0c190b50f10b914005055410445103070468942c08210042c04004910954410316401081403409440c580c650b1904c805502c3c51a40381325800048440e80e800400000000d402c01d01c034820044544008040159880340e0312407030001400d40400440e00703c004102d05d41c4890f512040c0c1700481c01e41da5600380c600f90070040c603c00700159126103440c103a0316000451201d40341c00d0394001800841c601c4034907440c80714036045a585072a40000040001c0c603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 224474181 1250 224472931 224472949
    0x7080a090506060111160b03061203040b0403020d140d050904060e071e0e030a050d020607050301062a0206031003061b091205030702030d020609010b10080a0b040b060a020a0203010b01030605 84
    0x83e080c41c1c004a04680021800d1034a04400c0c03103244052400800040c0807c041000b440c043c5008a54101c44038482810a1f070303890095001d030700005002040104014503240c0c01000619204425211041048902c2d0a0400c90300104a4000ca5030005001e101444c140c8103c0c4050511081c0301035150410800003840000d00d2010b211110305900040b00c1c085001c0c00514811500040803103059420034a0103039100e17400303009044058817585c40420b01e40e034002c5051343d06961080d601c5100b2000e611401d440109140d03180321007902d4050f1510005a00c924005512880c4041002c4008600d9440c040e0102d500064003046004103820a40840550044842003241d807410910784d1100d1050421a09500c04d40750029403500c19101c42a060b0340c0c0100e5070a01c036905140081184400341c0e01400001c0c40543c030f4003000650f00d0750015011a003280c1c04824284006040054076401c0e420100b01d85910410b00d07280564001d248510861a0901030817525580030329040c0012813501c0c0108994103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 224475431 1250 224474181 224474191
    0x21906090b100f35010b0a08150a05011a0a1b03022a061210170703030e03070605190c0507060513170303040b04030e03061510180b0903030405031507080a090506 71
    0x1800b5280c141d0b41c0041d0175085845c41100082c1fa8244040e60707040c40c0355403001000031840245103011f0001d55003040512516048401314a032909054604000301d803221390006504006002d580f9200c0c01c40e2044001c1e41052300c038825002010f9a15030b0503012800d807000c404500311941c0d10840d8440c4d0689030003040d200c20780c0880c0e40141d1103031500e410501e94110f16030408620301c2040c03042c04240d140b0008000702200d0182c6c0f641000041e80c031040c19240c442500030100892001c201c0d03030300c00f601e007665070783c0000340300b491b00302c80c66801940d8040c10140d0b198006000990046668220075031641c010800408561000d000207180b500044c0b526404014405404030642100247c145800358a096841c034100505440e4a40f80803402040c806070a80320180c012a644448045c2d12409100359110101410700c11264082c5400d90710303071190780190744003505400700b44000240d0703031401c02c298015030b11a900a92400e250000c0020720241008003110082030400042202041c0301045484d005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 224476681 1250 224475431 224475509
    0x803040510020703050a0321050603151f03060f0b01080907032901030b040b060301020a0206010515090406030b070e1906030f02041502070501110c01021906090b100f 73
    0x220180c1c203416410304200fa03102902c203019241d043c0d01010760110340d1640c0340c0d41e01101c006400c044901c1a40c01c5420480c0c0241e0140c1c81041070b0280f00c10205465903103c00d2000e4903514000c0c1e10240e070210303001540d06c11940b8580722025a1481000350050b9a0400000c0c42c1c0052549010308511fa1f030380806100c00780c4100d9042c01c5407a9410500300b00f4841481180d00c650515580d6403070f01c0c06412904507816075180c00300e030001c81d040340b906000700c400d00c4040c1d600600d2164281020098644811446400108010021000d03180c446004083c0114040c1a450096103841394000e000b145004440501c560425600d4805644644070400e050710403619001407031610700c050104c024420703600020000301d010302f000d60440d03a00054031015907000707a944c070b441c40b000c08001c42e985840034059140980c1164040502c40c0850090740400140101c20100f00d00301c96868902c80c000c415036440070400c020503028040322001c481004d0042250705c3c101c81c482e40059460341a155000f041c3e125507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 224477931 1250 224476681 224476699
    0x604110714070f03050f150411100306050301090b15010c1a060a0906080303090106061e032003070c0c0e0c0d0e0a02041e0501090506030a1203270b0f0108030405 71
    0x1d2500070001440600844980410600d4503410819a51210718a030096144112a44141c7c031031805070328a8003035940070302a0004520b16400300400b10714080c61306010543c1c2d6071400200c690b824000d045c00c1c2070281c90212150f0410018480e80b1b02c8020ae0300f01e041c00a00c134450800164901e6601c141012600324040c5c40f07032201c0f000a080c8503483d50000c5a12800d0070340120f03000c04080300441c041e015200080000c2ea58410095915141190745d00300c0e900101c07602da040440c000d810156018010802c200c0450005000071452034100b611003000203442c04420038104003542081d080a050780c401d44589600e060807510f0341d80d00c80d81581444040c3c6413a150181d00404104904166070300400500c110f00007071004180300801641c2d6032105c14103150002840001d00d116140c0200030207400340802e24065202e6800c40e04110100d10105550740d403400d240c03404840f0515842c041d43c3c100c00c6641840c02e0900183c54003026000c5064a24024010010040004201d400301c502c1070711003c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 224479181 1250 224477931 224477963
    0x804050109080409060e1b0d0209030106050a03050d080c07050712032003091504030503030f1b030403120c021501031112010509071d0108030304031b06091103010506041107 76
    0x101600c0c201100408102c0d010070003041d140300940020f01922030070394035000c15036503c050301001c088650f00210445c0304100322440d2004503980042000c1c0d030307000e000400e4a40e80c4c0e00c0403070540c0380f8580c0141d131300da0000e142180a413980142e20903001442503a403d4107000d100d40b00c0c10703118101481006003024241c10104c04160240301c001b4a80d51010301d580d08074113550585191a170b0720525903188900c0704c0001511030302d80c0360b20030746040e02d070018000c0d030039036480c02070b150318042014240d00b81c4440b8810718000b0031904030005510943c07281d13480d24980d4104aa07180141c502c541e04c134109540043e43d481e86550803644459045a402c2024032003002200f5002c5001ea07044801d406549500b01800c200c0503c600148410440b102c2c0a03490340e5001c0c0b40d10400b4111242802281201c2e0410000706003c0781c8114508d80c1f000318003221121226210396100812a862400c040740c602601603d6440640b80a01c540c40d8491002d60301031040800081d0344d2445449200d40c000d05281c00400b00c50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 224480431 1250 224479181 224479183
    0x1b090406180e06130309030605060307051c1704050915010519110607021204141c050a0221030703080907030f140106060f050406051c06090b0a08060412080405 70
    0x11006200c0300142244032004555000064038160700340710745a100d100013007141c02440e0140629180d405640342010503082d9540c45000d002c0151070264503102d03580d000303e035950368208142407540c6c031054221401c0c045440c081c0100a0008800b10b403000042c0010002070b12a031b08050b83c0210200004402a03d00c0c00068825002d080016a400b41840d05040800d6800404032500100040304450180c1c1d1000c2080341c2d1016400e10120000c441804100206500f6800301103010000a00820790441020081030b044a044602903401d644400060419402e04039041c6c6a210400f0710890b40c4014081041580e900c5101c800904200c41c100010391680c0d800d00c04031000d1035000d1206040050282410413102c15421040f00c929481c103140043d90038021a01c0c1000406262515424246404019034003500610303070b051020782c1045c8034544841c1d032910601028043c43c0c8030000d440d00389c510600911102d260008041076020500780004203035444c1811011000b18034240701a07543d589016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 224481681 1250 224480431 224480441
    0x1b0102010507090303230d1a060910081317030a05103b0c03190605090f0612010f0204060f0c02090a0510080f030901080a05070819021605030a080f1b0904 68
    0x70042c0d0380450b10401111154000c251584c100c8d250081e1210041410040c6c1480b0b01c1800d541c0c0048404c40300d078855402880e105030b012040030327a1110944026110b2030441c040300214240d44400020401c030254500c0d204450300103100406e411502ca0074041c40c105102d1000800c900c80c03d070511100c51007408600915408011290100e03540b600704400c802009030000d80311346181c040c9452101400d0109845000101e401c010322240323480d00c0750700c40900e5281c0c020b81341580090304842e203004428801d002c2c4101a0008010050340c41c0e1501100800012281011104000c40d003141e0310050b0366908070032504400103035000503280c9c550740210060382c10b095001c42400e00440c904500010004400742c008008280c0340c5280d00d990358440c072822100b040342c030b030030100703031000045080c0300d50b02502203400e07d808141c01807401d400d03042088040c80101408941652000443c107042070790060f00300d034101590101241391401d240d40680d030501e0b03850362900340200c004a603062095070f83d500701d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 224482931 1250 224481681 224481737
    0xf0203091305100803190917060f070e0603040506010e060303040b0d0e031902030d0b0a0815070504170601050414190e030f0d0203090706020714060904060b0406021b0102010507090303 81
    0x3200e1b6280704c03140d40b2000d0b1216019454021444241000600d0341c084020000600104005800144d5505025880c0c444c401340021007040354207142009140c903200015801140035200800342d941c0351001100c0e410390001d0181d80242c00600c4101320707074640081910102c110100c00072981510b0384c1045491400380000c00c0c1040070303418180c0d040480e0084020300c030485a1134024041d2883c02c009009409545100e520b10320b9200800100420182c1018203410425629141b0719181d0348401881640d815800c0020003a04800300401c0f20b4030702886007607102001e0143c0450245014803000c448000c81c04518030145407030b08614106460180308540001e81402000c03603c69540e103100300001c0d002120854a14801c02801264550001843c0402c460800c000c150200001c9000d20095410500740706800c26110240813804a0101c40944094441c0d64020b11702c050403da004107000206c1c06805055915100501c035005910000000640380c248c1003c1c555410345010030740c0c40b4840440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 224484181 1250 224482931 224482933
    0x8030c34030e15120703050a11040302240a05040e090604050607120f15031a10060c06090510020c06180d030504050f060a0c0906031109092e060f02030913051008 71
    0xb02120b2040355204c8250066a09940c10080ea030740d4195900102c0c1c02d0300e500c203407003040180801c000500c2d040300d0010b0000286400f100000e003540c81c10b04030310f0300040703140030200314045402c1c802c28141c056800d5200000100602031070505890b40d42d1244405080c903800c212000342c0034a4602c0c0b454010400a06500c0010031035811007520410300d20056000848050f020740c155480128601941c80780100c41c148001c100080ca0700700e007a90b08100e1440c6c11100c46490340c002c08045041480f841e0b00c41046110007503a1400f0b080085402c04034010100103400314082403920b80a500003d103a421103243d820001425200c90a000f03240003080400c003481d03403066004201300c00752030760006568410507490310925252520000d8090b40d80f000d0210260a03024070866805261210310340d03800c42e04103011080c003800112882d95100e060603121403040320140070200032081c2d01690052903c5000e00c0914100300343c40d00065543c104400c2c5c44012541c4490104000700300303800c507441c001e0110700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 224485431 1250 224484181 224484187
    0xa30080c010c08070221090102010b060304060f06170c01031d0d0e0109060f0206040809150a08060f0a240306050a030b1503030a121808030c34030e15 66
    0x486a00d002c1c003507007811840041d0705200810032060000440c0c1c1c040880d460100412030180343d15100c85a0000b84840341150340710217000e8000c1c0c503040700650059000d00000300d070b4510050384400a40b0051307842078110420785007408134040300c04104080c20105c24a40403030308000c2440003001c5a41581c0c06e280c46070141e03485008159070001d110580c441003c0e00d07500940d84c2d46403410303103011611800d0b440158200400007400240014002c01c1c02d001c6c01001040c0c480b501c101c7c0300301c894004001d25004501c1007010310209190012040c00010400c548540c0000e040424240c0d00d50700401c288206800145c030f45501a40c040d421000c09000042c040d0125070b5500d042c5114100810f442e009419440b001d4801001c0c02d001c402c9807420301c41925940074018950220388002c2082c1300910340b0404889040000090700e6200450103180e43c10303161034480404061030018420b94004c070341c070384c2140401120008200c10207001040c0385c245c100f850720020164040b8400b00e81011100c05084800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 224486681 1250 224485431 224485447
    0x30f03120c1e03040317010f03081308030408070815100e041104020d0b0109090501030201320f0a030c1805060c0c030a080c060c0708072018150a3008 66
    0x30005503200782d00036981c40d40c02c06c0ba1042d068250b2a030a004203418685060000d10200c2d40b80c6004004604c4070300080d4400e40e584106040c01c0d83c02603042002c00b070700031101c200070120703041080b1008c05a00c0c00b013000903170414580c2d140002c0310314442c942400c90b01500050a10480804c00114048040d202355658180f002c02d10000b03050750200c550114590364004202625940f02d4181a44c2d810f850707a80b001840100b104500d01d40c070880c18030301a83c02c0652150340c100300d5800760110030049245152980044500681569041c1c2295004c10404c1401075042825803851141290303001d035629a529036414120030300b06500310600c150103109281a04080055001c000c2c10f0421003207043e43c99603114044550640d00c83d400001c0c3c84c455003409058049402c10350640c4000d03034400030701561450032102286141000c0b1440b001c400aa240411041c40300b107190401042c002110541405410810b054907804040109107490010f0801c3c542405c0c45c1460384400360755088000980c4071040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 224487931 1250 224486681 224486737
    0x2a03072105090303180f0d0507020607060608070609060203270301020405031e01050601090303120c200f0d02070b1801050f04090b010207090c050a031a130b0f030f03120c 75
    0x815983c0380d41c4210382a10041e1801e4000c11044011b4414078045c0c041958515030464958100e03100070b80c0e00035000c120402c0020381c0d91050100030040000a801d1035480d00002405a0080380d0003541950810854150180780c2503000880d001118100c8450a00301140400e0090045030000754152240025940c04403646051000c0203a820b0f03c020b0000340c2c1c603880111030a02191000801158075510030060300e1400b034020a185045500e840d181140c00d9040020300000070418148180c0c200c20840341c4060014491450007500d103000400d186464250110441d00c64203140042e1000c20380801640ca0780f040e011a42d00028055a480c2c469480d034204100416850030317414058030800c00001031100b094000d1030302104154844038140028004150060044041520a42c0101820714546980c5c1e0100d100482d44180400140c0001418240404e5064500e03107103219a00880d561181010000100c4080b10340705c020204503078980c8221018640510300074500c00c0010303e62a48040340c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 224489181 1250 224487931 224487937
    0x31306030605040e010c090e130f03030209090709060210050a0608030408071d010f0302120a02120d171006050a11070e0402040c090305100b06090301090302062a030721050903 77
    0x2c100d43c20071204d072502c4040760880700c000e408000130515840d4104519101550085d502100c0c464541880079800c0e0784a5081c0420300a040340840d40c04500c0d03020b581042101d1562002140c10120882e03818400301075580c052144480c1400c2d034903107000810f0182e070707600b280c401040360030201ea44503919690401c2c0c4802040c040e0580300700c60b80c1c0700100700c01c501801c060b04030f80b6001008900c21b803d54080c4130b8141940351480130b5900c1109501801a2181720001010503168000340440c5a07071540002c3c030030800021f8101581282d4014010ba05298824640448615082190307858201190a40d1100a06500441c89000316140010344403408420345101b50701c21103007040650340640c07040e1040245400060240d03071001c00c201f400030800350b000b81c04050380103040c0340c00c05007034100003800c0d1840302c00100c0041c3c010506003c4128001650011649070111104107601400b603800f101c2e6001c000c1203a0204644450300f0200d5076a9a241e070013440d51105803d10451514403240c550340c0e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 224490431 1250 224489181 224489189
    0xd020c060405060103170f0307050a261608010b12100b07080d0e0a110909010207080c010b03060105091e100306020c060f0a06031707021206010e040b060108010e0601110313060306 79
    0x344030540b15184140154211500507e1707180d0681d0540d00c0d403510449498010004074030034030466605880030489000840e109600348900c52040718a00a072442201100c0ea1802c40d05001840c2c2c018443c0c00f465500b03807200d03032200021450050f41c84040c1d02e0800100e641c040140504002080c00034410b041d4028116229660010300140c0740341300050380d0f0388402d036001030181d10b030b1170680d4111032803c41401c54115800e030001500380b00d420b0f111516035602c4021030300710a0707549418442c0b1030708080c850b03540140340c00c80b8001980c0ca05041c0f014800586000c10030001600080000d000030341c6450514050358002e02c0864440e2200c4040540d501c1d801d88200c01317a162110005282e0800500801d810740b6400610308140f16440c4c0906c0c0455006180d003203911800000051450380c004014a5000703081004200d0034500b01820304002046e000b400c0c16042211000050050714144054242c203c2020710701074281c42c113059000c60450181d0200018885001100014000d6250b040f0106803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 224491681 1250 224490431 224490443
    0xd060504020a0f030506160207260115210203010216061a0a0b22090c17070e0604050d1401180201090801020c0d0c06020f030403050a0809010e030f0d020c060405060103 74
    0xb164076008100c08200e114400102584c1c0a0300000780344403420780100a17000c0707590040f290029107902c4081030458030044105a00c19100c0300b00540e42c5024000d4480003810603115a00d0242028151800c05d108002c06a64064462500e0011514258100c0301c0d02111105104031640303803881c048000d010100740c161144075a000c0c2c0303034541d481d1a040e140215000901000e141045c14201c05e00c00c984149103640704110342c0d140000d2180310b035019102071203080b950b4480f0354980b00c40f080c0c40c80c0540541a5020040766800d80d100c661a10411a01511b10450310611041150715006200003a2200c0c1080594289079103c0a9440c0c0306e074041015502c02d80324030744110b440c2c032800c5080b4010829000740c242d00c003440c09070030a4062542070395801e01980c4058030b040c140c2019810154010b07a01107000a80004100c04190790120b805500807010030000e000364401d440c0d003103940303009a400303100d200c41000070301c980c49010940c1140d01245002099484510f06403d0468445200744001c0d610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 224492931 1250 224491681 224491699
    0x23011a1003060e060409062324010e121e010e0f160302040b010203040902040f090b040b030628110a0206090d0207060e0a0803190306050612061c020d06050402 70
    0x100354020701840c829145000441c04150792a001004058020342030305503040c56403180c43c0c0744804902c40c24400001d9041c01e514082e401c1141c8641c1903a00030840762100c0c0354510304028016a41f02a080711a040206c5158030500745071005a800c210811020703130003149094000c02c1c0e4120064002d11034501c07194040d079041854240103103440355100303000e912034840c10141c1403005152513400071001070010702c1100d041607140e00041c4202d0b4400c0e003003000b0101c034850341042107030958040c001403602d06460a10122403140c0200743d5400300542240201c1d80400740e0992380000b8071034200c110708440842846449a952082440c1d58030610410f4014011600041c098407000901608981e0040e40100380c507528041e01110740341c07690300006620612482c000988a0810030180000d4036486094020072010184080c003100e020380d201ca03004407014040c1d000d07140070345043c0e190700072816030300800d0700c40c100d034001710340d1003826a0000d5012441d05052070601140d0340c0003900c107a00c292a2040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 224494181 1250 224492931 224492959
    0x100215060102150a0c0e090a05060a17030711040e0d0914011107090b040f14070806013b031203011e0e07110c0a1514040e0423011a 58
    0xb0303c40d030120318903040207031607030b4080360030340c01e19074441e040384009417400c04c125903130200000701c690b041502c3d06050162614180300035490000f18920040800b10b0031000449001c5010549074002e2a0b00038101026240044015407200e0f001781c2d659245a10a6480018604001a0841c1c245000380c42550000310700b00d003090350242d4000b80078500010001c0008610303241d2100e001d48100c0192940141c0c03a005603640c3d4110038000c03103d000c1e41741040400e117450a150006d1841800509242c10004440b909a907403e01ca00c4120206000e22810404807140c442e82c59140e4070b01c403120f42c42d00340c4250700c0c0040400c20020003440c1600d000d0309801c400c0c2c17161855104501d6049002e03641000111a003c40c103564002c103034100d03600c1d8031203040d902c001e00440c001a4003a061588110541c0046a0100380e4040d8000c1c08852903142c01c03803140303003020300f000c85242a42c48028801400c203013404140c608000d03044480702400b07200003002404045034031845c811400802e45e8249004c0da0007480284 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 224495431 1250 224494181 224494183
    0x102071b061704030504091a031c051b030f030906011509050303030604092a1703180d02130501080304090b030a0510050a0e0a08130509090705010302030c0405100215060102 76
    0xe084480980d18082d801d0070b10869000e880001030300450501508001c0004c062005009800d0020315506103d03007070210940a16042c007513008007205c03106504590b1943c4481e008810740700d11b801e1000d00c1007102e1101c003030520314600ca2032400346c54141000c010400345c100c0009041e4142e844107800e12244d14459002514407912034001ca80d03064000b4000103003035040550140341d5440c06070809482d40c1e6003d4140701040c10710155a1300401c13003030400c1440034640c039065805540c04507600440c50010028a9460903181c007c10080c440c0d020980a1000d40d0340d20fa40301c0c0d040500d07200e410402d55030348074200c0765280e2084c8a01c400207400d106910b5003900d4085141c0312001e401402400d03040c1c402840340e000506009101c200c007155192001024088100040e440080c440d54400340e441107004440349000e10980c2c801442540072004001e2000c41c0031400704100c2d0000e080158803616030108004940c02203810498118202c80541c00d002d07580020344030402c1c0440f403580c50341502d07914012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 224496681 1250 224495431 224495483
    0x218030c060c0318011b0605010501020115030c120f2001080a020408030a141902030403020a09050103020d29040807060c0806010e06090a03020a0e100f120b04020d050708010207 78
    0x2580b801c1e0010701515a00c5803880c2101c010324001451710109120b100c2d0600140f60a031900150b845558500040c0410b58092040c03241c07010b8440c050074903c92560b600c0e9982810755006c1d9004458080104c001004440b0310060f48003944258011561141d2000203051003031003109107400030f01014007080c100545d51080f00c0c182c80c03040014500d42840c43c1c1c000d5501c0c14804101584c800400c0140303821582d00070540d03600ca0360307150380130399584c600d140100070b4271810503040106400d01d82401007005960b14028141d0607a0710a8084140c9450300ba400004200b400c2200440903820343e0800040003002001045018419072040204072200c0f1400c45001c3d80032121540410341a14080841d46081406015801d4000301180301da84d0b01ca9011502028003a4044800c41c021141440003007000c032010007014050b00c1c0074040c9860714003d01a003d030030069102410140c6024003180a6454421030040116040004c490909503901d0000d4002d601c08681030350b500c0c00d9404456854111883c1c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 224497931 1250 224496681 224496697
    0x50706080f040221063405120a020702030304060c0308090105040302060c1c0204060507170703020304050405041104060b1b060f06041d010903030b040b040b01091806090218030c06 79
    0x44601c80d56255070920601c1859110400c0710380720b264842a1810b801000110f1048034190761a9403200d424504214036002c40702c201d03143c100e41c80c420780381d0510f500006517070078680b00228001c850384407200400000c0c40b42c0300010b9054000080d022801da90440300040760b4a100c2d540d42e0b540d0f031385c2c0d0084807400c941c0151170042c0103030084004215984606005040d695584015120440342044101340490740250710070804120049400010b20400140d20042c6880b00a0103034a44030665030005d40380c1c410f90103401e220b540d0b41c10102d41404003d91a019030850040c1c401c102242c0c48440044031900702c401260f6000e904000207481c0d01e072003c12040d018080c1904008001d071500400c102c054241850f40d4099902040001c003880d031401d001d1008091b020b41c40008001c09030000340029140142c003128000e03402e100001500b03980c0126030600721228ae20348640d0428014400b03001401b400c1d80840880381c00880c0005d8074402c0e815095a015204038126265030019200707009444c016090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 224499181 1250 224497931 224497951
    0x1701050712020918060111011b0e030706270e280c0512040501021312030f080f0a1a030703080414010207080307060f0b061603200a0609060b0607080705070608 70
    0x49800c100c4c180c2c80440640140c4141011560704040c004502d003110b00030700041c40342c20b600d4450340c4040b6401060340c1040007800d43c042c2145508001000e06404546006804019203640c155445010361340080d0300903005103090520a4100801c6c808445401075041801c5000754240140201955204201c0201c401d0703211a4141680c18291685004005206503204d54080100003d14a159256070003d003c01c9805611107204030b050050031241d95010000c2131051501c01d00050054002855901039010f80000c01c00010911030402e2840400008a4140c81490008010080d00c2030250040e904411070500c1c6c0c1900340401240c0d1015503224400307075500300b00810310216440c2d41010003035118211000c690341103001c0c04030b135540d03005c5050841e5a54480c94803904041c0c0c04100600e90050a9090300c2c201d01e00001d060707480303584030280202181d03a26000a008c2222a8200011294004007244c0d240d410509000b00241d00107001200c8900400b280070520030701880c0568040d4409079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 224500431 1250 224499181 224499199
    0x17130b03070305013002040207050a031e0503040c0b070c030b090c0310090809010c050102040509010b09030c01020d0f03020a0306090504030f090f0303141602090903190c02030d0e0a17010507120209 87
    0x20701c0034082c0c40d90220042c2c0c1c020b81c003027211502140041010004151083da01c5088980d00000d015440f030001411940c2041020018400401c41c0000c02c10241c070b440c40381007666030065150080d0001e0036a03000130400b501c04810442e40600c08101c0003140f41003907081e18407480f2010200412103000d8000104180c80510000001c1c1d4071a0301e050388090310810005180c146c8410025a0003942640011501d0100040e500440d00b4248504581588203000800c3d0308508920040c1010b0850320190f801c056010580340f511a00c260080750090104642c100407a0406041c0240b1014541c0600d8001c249003000010744400318102d0b81c011030760903954500e076141400500010640c000301040304080445100540960b407501c000c6402071003108029692014a80da00c40a004000490013041c04440d104400140c0c80201d00200310030103526294040340c0c110800a41060314580040416207100c0813040b12882d01540228000c401c161140f460380d81080481038182d100d0721a00c0c41e0400c00003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 224501681 1250 224500431 224500499
    0xb010b1b101a06072a03050604050a0201030b0409020f010806010203220608010f180902180a05010305010608011a120f0d030903030b060a17040302071715010608040f17130b0307030501 81
    0x10240c40440c0d245800d00b485c03016074030740300c1d14074050301503c2c2035a06412410b442d20071580c00d881400e07603aa00a4400340801c14060b00003c0f404242014481c5c1441102800a40243c0c42070040b0365003000802c0707a5608201d200103404031420807038007540000c105d400002044000f0388004102c100c1c0e00150b180c0405009045008000d01041081260030007040609042d03400c00b4029190b1080b2805980044c0311b6165090050070b5400580c0942445d92600d5031440b80c540034445603000201d41500c800c4900305842902c7da1401d60036101820f0940203264280840c1a030541101800d2030082da02480602c002034100007841c80740c1c03ca6480424078043d4600800e10b80d40c500d8641c4640a07005461003203640e2002038241e00d00c00035028495810000029001001840b5558054056881c040d407080c43d060f0b80313455038800c0500d80035003400071948070520700b20712680840740e134400c43c41c14651038280ea411501d0050340055821300e010905001c00450051b48100050105400100041e507400c02c0d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 224502931 1250 224501681 224501723
    0x2120604200c1c0e0406141e030c0319200a05130b030609010603060e0309091305010f021c14090d0f1209050c01080703090b010b1b101a0607 62
    0x11080340d00b9403500502e0052441400c800e26618101140c0362121134640b248202040103c1d03d903030300000c0880f2044804021a030300d030b0200301c1c403400c1048040300281480ca030000071b2070040d0071050b541d414422001310701007106003d142441c0321440744600e40c0740800303620004c08078036100441c6203800200021007008145410207030b80c46441400b10002031400f41110209091100448070009a40e446100c2082000410b00ca10383e246881c1b1806142044003180c00682c1144000c0c00080a0040c660350390403e000003944196451001c0c51000c541d5000d8411159013001c09100034003203294079004a0085000100d44035900c03610035903010b0401e00500c0001518032030074805040c820403003011001c000381c075124800c20007914098402000801c04000005020000040c0035100301810101c2000010300b1300e511007811b5541d007602440e01c51180300f088200103240c00da00300045205081614440f000b503988041800d1600030701080c81550a202400201d1103001001441300f203c0301011511820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 224504181 1250 224502931 224502937
    0x7170304020d120c212706030e03040b13050906030303130b070c140f01110403080d0203040f060f060f0801020c0601051c0b010e070e040912030510080708010212060420 74
    0x4407505040c6a580125244c41400d0030040070b09824182545e2103040f60340384c20209084802c1c0f0003402c40c12409903200c0d41e92821003a9445030303400781501c0b01c24200780500d090013a01c024004030b440340c58030b0b04103c0820f2a922705291151a00966086010901c0c50030701001712480f405100d0040c0c2c039a041380340d035600b00456000340316404009031041110300203a00d2200d41c10302c003400f02004010015003400ca050859501c0ca1448080c6801040100001080c400c2507400354004481c0050b100c3c1d40d18106000d0b02c182d401d9005201c1c40c41c14410030341d0881640d110f83c040c0c0b0741c6050707130400341c070b4840c80210300300d2052090f42d8402e41d02040040056103450300740c5400e00d00c0014020001d608039540c40016400080c1c021080d039903250410040c40582c04a400f0365508011a000c1c40f46000f07980780d00041010301031060b810540c4440005a10355100030004000b4618101150700c9a651040144d0003508030495004103002c6200100342c0d1031030140100105020114182e0141069103071080101d54 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224505431 1250 224504181 224504213
    0x110306011404090c08100503060415050a11030702030a0908010b06040e0907030501090f1b06120e0a050f07030b01090b03070e04050c03100b120a03021218040c0507170304020d 77
    0x1803030801021442c41034600407045200555154440725042140e0b4020040b40b41c7d42101c3d0196200ca81040003241c003000400c0c01c00307c0311520000b015161003c0400141880c041c80c40002a000000d0110669001000b0940e100c6240e4a4100c1d41d03803224481d5090b90424008964840014001400100742003429503401c07004040403a555240d8945d609803d60324004025249558101e00100c1800710011300c0c50071a5080403000d042c2d03076040a4028140703d0000e404040200da072110891900f000822060741140e07000703000c0302d040c6441c56590565403070440c00200c9111162500025841c00c0c07d014000c695a40100a00150750421083c03918045000380180d485110340d01c6140c0c05500c040c000000f002000300c0740881c2e03100c030100a105d510421021003900c030354070248010020a50200e21071141e1040c40005944d5050760001d86241c0700f60034001980c0c840e2405240c0403030b5603008001002e01912981072400001c8440003800958003048402940002007080c8040004004c0c00b0540070803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 224506681 1250 224505431 224505467
    0x2210a0311071502071e030c08071103070e090f071a0c0709050c0a030e0606011e090906090b010906020a11090c041e050f0607031709030f0c0601061211030601 70
    0x40700700c6844110075003064912030540c05500250210620070004101180042200c1500500d45851f6400402846603a000903019480120b65201001004c0c184040045e90080851714190380b6980702100002c41943c0000d510301c1070585110b1780c20808154401240d0300e0002d40640c1c10b0600100c940c09a20501420381c003800398600c0400e41e40c4651203020b0184601c401d0040c1c45049004002d0115480001d040d980d03a0f00103810401a40c7e400818142c1c605002c83c0c5c046114560848140c41c20715054000590190601e5404a000c42c007079400f111481d00241e071aa91201d0b5102410307a144d00c640c50014002800040c000b13180f5090003000326820582d580c101301e241a50368040b0010069803911541f64111085504024902d081001d6041c01e46080307070064904600e03550041c140d58541550207800c003c844000031600c102c00e106270b807908094000c415607030381444a0b18a0721000c4c01d0060301d021491140c000489440d0354400c0170700300c41c004d010300c3e403654451000540700404d401d10f0000722 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 224507931 1250 224506681 224506687
    0xf070c0b0403060b030c01051606110c010f0504020306010b070201170601021002040324060b04050405061309120807090f0501030207050c04021602090c0c0a2d0804050102210a0311 79
    0x198403031100003040114021031002500301c0e412800c06041c042c0018040c0d0402409000d8901059210350981c2c0442d0760200000444052480c0d4030400c0b4041c644800145501e1b010380d141410040d81c222070710482c401c50a8072900c3c1c0c1c80e084c00c80c0c0d21b8011444064001010081006403401c0c1c00c0444980045050040fa090840348010083c107991058004030380c0c15981000321b00451031410f12803800c248244200b072214506010044909001ea4443d40744560744600102d078050319451341c0410403004454040c04503410310b0802001c8052041c1031200000c410000003413005100b00c43c20016107090054200001d860400110301941041c10181c910380509681d41c0800d0b0342e10b2009001c01045e050150801c180d1600401121401c01070049400302c400b080448803003c004503100f0422680300d640ca4801c1c825404408201d50101615540031540c58000c1200703000060000e003085440903400c8841100070013143c0c0e01c01c40314410350055203600c00d10006074040d001c1d40010b00c080d40c1c1045440d003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 224509181 1250 224507931 224507939
    0x6030c190e130903180501050d09060f020f0406090905070905090c12180c01020106050f062503170c0a090b0a050f0409060f0501020a08040920121017030f070c 70
    0x282c918000c1c2207202e60340d40c0203040101600680b095620f5030754a000c61104030720b0400080c1051082d030124052095454103200208003150713000002101c14044210b42b9004814520b4081d54003038010100425039070a07001400c01c10382c5c003a00b480b0b02070f07a0381c0c0d0080ca42d14040501c01c0910340a0300c0000030590501065000d50000c1414500c61150a00b010010122281c940d03800e01c88502d02c4241164103000b0700340704a49035458103141481c4180c561075a12405500d101811031245030107502c084401100301810f041e40305807680010721315008102030589454420080c240319031081d00c004035603482410841e50040314060304880d200703410440d19142180820900d43d5010303401952040d561520f0a0000d4024580d1800280500380006e208031001610b80c030364640030b00d01c1500100f81e00c419170081000e400b8804d0000c4ea0154000040e2134050781003840442e024101c1d0107600e00b505c000390000715000804107070784604060301d002e1464692614007211290703000a40c243c483c2c2c200040002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 224510431 1250 224509181 224509189
    0x6030a03090515370c02150c1c020102040927030c051906050108070f030818130513140c13050a02120709170105060a0b0a0210051003050c06030c190e 66
    0x4003000c024001100c100821203001c54080c4d080400c03003401000403605031400107842e80c0110204804001e07070750b1622600444102403414030700d01440d41698081d20409070410380c05402070020784402020500c84600441104561134a0080710505842241540000400d01a10b40310749224051002e43c3c09680b40420204042020140d00b241c061383d4520040007840c6043c80200094060182102c1505145480795401406002481d0150f1044180b500c00d807541c1303c40c80300b140703621004820321040c913180c2f0b448041a20b10100a03209441c0388400b26612103800b2810014500700140640540042581200014140140842d807542e50801070076003072034240381c9a20b10031019640c8407402c0500b807001440c860180c100c02940d00b03a04050900500b661540440419a0660445207445c1c0e040c540c0b08920b0240c02c0f101102e805850241402050900c4c900ba010a1324042d104031840d0900c49002e10050340b10884610141070302c01c0c015010744640400321942c485d03031240380070760341030304100009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 224511681 1250 224510431 224510467
    0x9020405130309170c1e03011b0806010906080714091305061201050402010f0e0423090d0203031009051305070b0d051501090302091906120b06030a03090515 69
    0x400584034007141600800d0b074400c041d6005000000580924810084080e598840700c200f4034502c01c0c0380c1580301401d01041e5414440607010024001d20952214041c103004c0c1c1c0d01d503400c088001031a05000202030707502540c8210112059030b03855640d19560f48400710b41d240740948180c00c001404100c83c02d031594421004120003070300d14900040364206041005103c0708a01e0b0031200c0e0781d04000c20400540e03007100c100751020b141c1d402e122805130f0203080001c0040a0700f402c0d2031131184401c1e1061001d20302e104619481122024210340319524094426030784c074001182d0741e0a134162650f40911108056400c5240c2050320710210361000c6455640d00e40c1002e42c4e0b50020000160042580150a80103010355a0480800c0d130349001000602400241001d40c0e6020290041d200000840d00c4d8801c0001000c0250152083c02c0080a031100044400042e070b00e402640c48196840200302d0708c0c80d0100b50801007640c1511a0015145414240030b05400161040c50b00888284045c00c808075020400f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 224512931 1250 224511681 224511691
    0x809100e1008100306140723030f0402010c1a0402090702030f030a0905030705120a03050105091e060109051504030507060503090322030602070320060105011d12250909120503070309020405 83
    0x6c59030500e0819402417039445603540d003500800492014203070f00c0d18000d0407241c0000550076860f1881c0d40d20700060740c08145030384004040c010414002c0c03100c2414406041d02407803080b034160040d62540315040340c0e203019044140c0700441003000800c0b15007075907900911940384203c0a130303401c00b005a1182d900305840d50b100c0c00d110b96000500000c02a50500c1068003508085850704194107000d0501d0b1956296003100c114092000c0b00441d1060703000b2000c80c0c00804e80140421040810203c1030001c98210f840b04031450320550f0300100310580640140e900c1070510100840c104907181103014424460f814007120032603c1c0190200200d000ca0009001941c0680c5640e8091140440f1a40e10300482942c81e000903049400103200a80e840a2200582d103207510f01c1c001c0d00c1400c2c100240c418006182c228240348620141c02001c07800a0350380509001440003034034900e0340d5503140302d01620306c5104001c101807000c000700e426039805200030316002811442c00196110302c541c0441e0031210140c1d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 224514181 1250 224512931 224512961
    0x5130b0f0109060510050304020405060103110a020c0f030a050606010f030f02030a05010311150d0b1f030b01020d0f080c0d0e0d05220e0103120c0506040809100e1008100306 76
    0x4014800b0702c44a0051000410080e01d21a003140320340c070001490b5010151000f0302c20350301d6034081003c6a209400400f551140c0c40e11070380c0d4610360b00101969480041900710700843d4084160f0a09240c00b0a68480305c80d0401c024000d15a550801114480020001201850b5075030001481d8510035102851003601001c1e4005010b5045052000d6050013187c1e00a208440d106001d00344802403500751041084620b40c041450102d000000780d109100000081108446110071040d10f6495003000207805020303001e403001008845421a005102c600c0c085012a4411000c56440f01d0301000a01040e44d0b000000603807080442585070500d814032003100e00241020a08501140d0407910b10555003030350016600c4040e00e002181142c501d014400070f0400300044942e503111a0043c41d80d15002940300701510351034603003860041c000780c0110f0600d60040000c8286610900c1c0204003502e41d00800034682100d80b0410130085441c444000c1c40c0110808000c040000080c20034000c4a00d00c0315006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 224515431 1250 224514181 224514211
    0x1903110601080c090a090515060a030501090b060a2408070306080109031709070f0b090d02101d06040b030f04030e0d0506040618080a050a020a02120c01080f1905130b 73
    0x10304102100102600d0800c900d460505030360001800000c03480303940d101302305400e15982d0b00c0a000465001150307002900a5081072181800c210411100611400c800c49229404c5074458400740d03114074264444d0001d8103042d8440384800e6014001d815032140342440e01081c03042d00e482206095075000c1c901280481c51801d502d101580304105111703444080d10006040041c40d200d131048005e40345124483c40b10f000003940d1485c0783c61b85a1402020358026002c12040300e0b048400410002c1c0c00420010f107a4000380c1008c00f03601d40f0108607000c49080d60b003103500b552954030070041c0c00b500c05031040f0107104085d050741919480e000c20301c5420f00e0081002d01514909420000180d03000e541301010300140e043c1c200c90004803000d0a886400c0000c2c03901507211814100c060b440d011400c100a903110031001c41c140d002110010b106d01e0f0400e0280c5c0c070007620b070b1525802044100350503079214405018941c5e11001c01c1800e60b201d59400f00300080d002411032013a03100c84000d500305640d0030464060f62 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 224516681 1250 224515431 224515453
    0x8130f080604110613050d170a021c360e01120c0f0302091b120a1d072402010f050a0e0d02060402030307060b040b04060f060f030e190311060108 64
    0x403030f80e2140401c05840c001d2408000e205030f008020110300440d81b246d000b489a1005002c1c0c40b070801107412903001120783d95032105100296a0b14540c241d105d441200139034101c84c0c820710607206150a012002501c400054100c0e8102807403511540d40c44901120300030001400d411a801018020310400302c1d001c519001034107268260f64401d81100c200813a000700100016101c0c20045548074000303031801c1c0900c04045050110b544510440028011101001e020b1390384d44036441b5042d0492a020002c04030300e0304200254942d0f145100d4100c02c8001000a586201c54842c0c040c1c400090500c00050a401c01401c078008540c810b80340c40d50010750390b1605080109040140c810700c004240001e100b40d14113680080c0e603a00c104c1c0001071107552907029601264641c0e81003407980040c0200f00b80102030301c0708009004e20380b640c800c03c40000d50324500404041c1c001d1041d40c00e2a00c01d08060094880318815682c3e103c848540c04508000c042d000080b1445024461a0701038850340b40640611801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 224517931 1250 224516681 224516693
    0x31005070905010314090304030201050906070b0f1602010b011e0201020d06030c050f030f030f090d080a0c0c0f030305120405031b03040f09110702010e031f0b041107030503010308130f080604 84
    0x1d404504a1031035405d0050120021000060b02c041b02d60900c3c0c010356079040d43d0007156080c000d030b0100030180841441030011307403421060801e00c40d5031014030715020305400100c100c4c2660740c0c1c60512408140b0b80701c20142e0814070703807070300c00c014000300d000251801031000038020031500d03a64404e440c41c1e00c1007801032103285411142c48015103003c600a007610340071154096264405c001001800d0f44000500300411307241d100c00c44243e6034000e40308503281c800300a4050b200d16003001d41143c1c45061200c0201d40725903c44030500680b5050f6072201c1c00d0288541c5407400034980980306440c103100074440c0c64003e901c00d940b442e2181d4000005103807680d141c08400c403602d110f9600800c91050604001622842c070a00c1550b03e05070b024a03140da41d034120360001c28145906110342c5488054070070901102004107401c80074170080241c900304203d01d00040000c0b10b60103502c0000340041c07010001000401d40130000b5003841d41100d46036a11465554100000b0a1055403100625801c002c0400c018014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 224519181 1250 224517931 224517941
    0x602010b06040522020415120b01030605011407020a051e18090d0507060e06040c030c0602070b0706051905070203040e0c0a021509011e0501092307110c0406090e0d03140705090310050709050103 85
    0x1000e01700cd11843d41014006000d80c180d804103550782d80d0000c140ea038155550f8034460402001d0142c1141074160540482064080d80340203038070b0080e8075252244d521a07045101180c4107042040250903030b010030881c00c030707546e501412040d40d403140c850f00702e400c000505000040c01644901ca0362610035165180c0b812400105a01c85400d54204d00d0b810841100110304840782950701c400001035558070710031001d0110800700d6100603d00d10b042e080008454000004200355000031103040d03901d60307031b00c41c02540501c00c002e51400180c00992109050010740745a054102d04a01c00100d140c03003c2c00c504900c10848100703000401c40d1500c004100e00080d42c8100c0c80500c4c8110200403ca80c01c10b0f43d040d802c4040a48400c0800201c0124000d248c101848483c1e84041d00410500c21030381e9440204018144510511405000d801d0000e0340c0703d800382c844c1400c4083c2a070010442940c075107106441d80d40040500503090f0003a0a50b40608250521a5a2007991151611405031b41800c0004003154 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 224520431 1250 224519181 224519201
    0xc0d0206010e0c07060e0a080d11041d040c08030f18030c220216060501060e01020307050601030f02010e030d030f0c140306040b0a1e0602010b0604052202041512 71
    0x142141006204200501c000150f000b0b0300c00080603038078800b9107401801041c20130360350840d45c003a040d583c030100007800c001891508111182803040c0d842001d42c3c80000d100354131941074036188030284100d0b8802ea10510036403260080c940c6001040d6902d07012404d5074080d0b28043d56400340010a04039805c41952681000d03103081d8001c000042c404004078011092203684013076a00c80d03850922115080f11380440d58580b0315606003a01d01186440c2c0500a00028024103020412009040949520010030b4504543d0844014a016481d40d22800c45842d52141c0590411405003100712040d01c2c2000351030078040a031760300020624a504120001c42e116900c90312708018103012404000d0320702509a03038200c54210780004030f1080001c00100045e000f42d006011001406850744d007036040000514080741c269030028030405226a08202c404e01c50b81c01116800400801d44003c06100789242c9040e18440c003000510f0a40c444002c1900b042e00c40722036200040c0104140c000491050203088090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 224521681 1250 224520431 224520433
    0x5130e0f150106082a0c0708100c02030304020d110a050d03081b090307031403130b130f050607080c010b1306050310050108120d02070b01181503020a1707051002030c0d02 75
    0x40c10700c0c0360b5a170b11044800582074100b032a00158102003920050484040d104000100c4040658501c4800c1c0c8409100704007001030380c0b4000502c020340d4000b20450b8403d550040029403050403655074040459114100aa0800c80d40e03480494203032200d8051944950180c0c076143c960b85000d407800d900c2d140107155056144d19060081d45803d4800041103c10b40ba40301c605200d00900e18010203240d4080c24904064280302e9030000207001c98454000e00100c942e1104202e0701585071418202018810302c00c0a8100c8020060030020584da000030b040514000800400c03100b8140700041c4904102400e8200b84070340c1e440b81042079140030802c8020001c0b001e0803c0c4625803400054544841e14400c070b00044801c002408021a02d465044034201ea900085008503135031241c40c54003201c07010b0b03803074445100d00c1c5c80c0f2a800340e505929418400c803a401001e045031582400c2000034040c42c1201c400685200300d801c04252541c80b0541410f26648030350003141c40d155900e902a20307014480322804d0035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 224522931 1250 224521681 224521697
    0x70b06130e060a09020f03030f070302070e22030509130b010e0f0a0603090311070e06040b0d110114090301020d050a050f0702060408031b0a0c03030b06120105130e0f150106 76
    0x32500071440b10350107460103070001090031850012030724902003a4612640360200189080b9043c2c1d2540c0a4000c0a0280c7d088a180a49400c04402e03181d40070f940031000d00714403400254071030f502d40b45c113940194400e142c228140305180012030300c0651120903a003052921603c0b003021550b4840810840b840d0125000c4190a81e1140450300801d13681c0158800c04d81c58203003d005060264400c14103440580003215085035030b81c4400501420251101441745051581d40b0103c0d03e081e810100c03250360005202c03809078072000015900f414500d40010014a8140035510f650343d001e10244c800c81c6000d500202c1c0f00d141c03812503441106d800400da091400021010300681c44c1d4000365080c0c1c4158801d54440c0d4a8131392410380b00c2020b64201402da6946070001e1204034040c1e0094040038130a00c20b8400f80030711104c4608201c024001c012411914540f42d00040011349008444110081541d1400007145110b00ca0700c02d00341220b0070000c1c11245d120124401d000c00721a91000c1c014442440c0c07041c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 224524181 1250 224522931 224522951
    0x60210021204080304140a050c030105010b121504060f060c05010b0402070803190b091503060106050319020d0b060403230c0906101205011716060801050d140102070b0613 75
    0x700c46030250024182d000d000c0000740400075013031300ea0707004590300000301c42030030b004c5103825a62800c1e480442400795082c9000014442404002da5081e030300b40c401e0001040d520124101d44280a2503034490b409612a075000030b0000b1862800409003c95075103030989003806061250950340c140509901035841008503c021400760700c1502e0700640190030340040d402d407060f4620b01420306840c00e00d501000000c18070261700307045009204c42040950a80340a40e988a00130f45250008880302c40903110412190188d1056541c01014040b0990300002031000d540380107e483c9400ca50800c4808499541204005019000e0003c080c0300d600001841d00b01d1b4800c0102d829020f02801c56406202d003d40109003481c020100446101400700041100c2d40c0c2d20f0051050070701000071000054040d0710b200d0340380040316042d00405c0d41d0443d00c40480513460402440300b8020285002c2c7c0d13034070503100d89585006200f8002441454041c1c10211084d0403d6820401c199a422001034581458150350306 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 224525431 1250 224524181 224524207
    0x31707090501050c010204030c12140a080a0c0203071d060325060813140c04180c030311030d0e1c0e0f1e0d1401060e04030206190216030906021002 65
    0x80c2622020b107085600d8008800380180a80a40d4200030841600359402060142d0103002403108640101c1d0b160341ca881981d00b11340c1c2c62300002c0c0c0000d00711040801403a11514020303a1180c846500c058202c507580c5a944081a074005c40c090199102c0010201c107000c0646410042c3d0901780040b400080d6003092682c1d404180c00c1d045228420070300c0390a43c002810220144502c10308240c001045e45241f0240340c1210f41c0b2015038182d254801c6245c01022204d14000029440040b41d001300402c40084c11900c00ba5004a000c80258070700d84800c0004c2083d000482c055403400100d448000c0140340300316000ea40d41d60ba03401481100300035003400000c0242c0d0b240f0184c2013903c542955143c458402241e59110a9240300d000190050440098041000308146a40d920700350660000c22103d61078120354854a102610041e0040c0d1004010554160180744070003070100003454018541398904030491010201d410003600131500c008070800c4481e80511500040c0041100704520b0600030118034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 224526681 1250 224525431 224525447
    0x100f20040e01060f2601060801060c0804120f02030a030906020d05210402030309100810050d020105070605060102010204152001020c0a0f0c0503010203131208060d080306010c1e031707 81
    0x20010030540c000e41e02c03503044c0a00802c080004901c45d41c0290041c0c15850000c03012400c0c0b1480000903042030001401e584900d0700400002e40c0322207601e00c0c0a14000d200305242d003090006031885100d07040038000682d01040324083d202c1c820b4464180300c5140000107801d1030000038045040c04006c000c4500d0117a41e100b000c40303404110b102c0c0a1910384603400803134558081d40282035040030311605400321480e0048445ca104c5e105003011800352545580c180b000a180c246402404940300340050000508180c000552108040c400103042a54a4089040c521000310000020440d040303a0b10350000d008030420580c218401c070003546464468415282d03202410503000c1d0010819201010411000005001c01400020000d41d02d9080c804417007a85405113102c203c907005c1141c1c01003c025400780303101501c80c000c001c103005104881604c48515540c0300070101c80c10401c0740d031809000107403024500d0201c42e80d00e80c1d0316200e250711403030090f000030710508407154494000420030901e15840102c3c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 224527931 1250 224526681 224526689
    0x60108100908190e03010c0908100c0912030e04060e0609181f0204030b0c090307090608150408090a0b0c010b01030612061d0a06150902180f03100f20040e01 69
    0x5450714000b203030004a8000c80d544ea4103641c954201008104000c0d40018010140c1d1260001e484a402c40d11001c28210341c8200c0d01440440c0746040d0400040d680c500d020f50005010707050041c11403504600241c210b45003504408101c22050341405550304102c11826408414419954000b810f000d9056a8a50b0420b280d81c0c81030745a44040c4200d00e20540664004580c4542d062449040500e01040350307030804032509000340b14100740001e194501340207030000c9402c50720180c0909da041c4054410007a100400c260303800ca2041164100a03120380c8980380040080400b625100e001c1d2a00c600d0a5486624030141058140f000c22720211131401155900d681e4024400901c05d01c8001c210f5036102e064a1049505000e010500070500c0907a4000c501c1003900400050b4410761201c002c40d0490150b004c0009481c03040e2401e014080c2000b003103111000000408541401c80c059440c1000ea5102c4074082007250b0300d60500c02c2c02d000c0440028800c8004010321941032030b0a10603400200c080500c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 224529181 1250 224527931 224527957
    0x5090d0b0601050c0f06010317030c04050d03110a050a0b13051b03160b0901080a050f04150f0c05040e070f1202090a181a010201150b071112060108100908 68
    0x4a440703603018000300c0c0c082d5140c3c4000d6500c40c030101d00000d42c4580302448295005100340d2070071002001c50208582c4a0311180f48060300f801d040c201408100a40f10400b01d051000079003140f003408404001000d000c80c498801845032080d10301e03000d040320201420400c90712051a20020028801007291000382a9030205c89003041c0121001a00c3c0072010014103d1030b54552802007443c04a1030010302c1404020388414090362a0300b000034040350b50448880320800e401c5808180003500d00ba9542280d48601c540200e0f07180e685041200840350304500c03800110380006001c001d43d088803240d9650000560400601c4d50001000c090a0100e5003104c50030000c0d40041e015109035035214524010f851012400c03401c040003155020010300c980391440c41141003c01c00300016610500807075114640103070741800c81c94070b010320402041d013000700116a00d490802c196103107a11540b0301f0902d03003103078038009001c554584100a800c003048103d80b85000c506016041e0f010074010307000c4030901ca201b01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 224530431 1250 224529181 224529203
    0x16060c0c050a0f0608150f01080a09050d0f0909060506030c03190f0207051e03041a041806030c090203061f030207060f06091107020310110c0a03020312060105090d 72
    0x8640304206140541203142d002c2c80045012803030b10500c90060003039403216104c0b60038507120080d4540b0509806524035038044042c1d03c2c0e0103995403165020f5500100300d400c01103141521035603440c2c2070010041c0b10300f0008401c801c1114105502000d42c000515030200b0070000c8500f0000803810900c0010820944d510700000401d140c1100d800850003d01180142000a040488511400b0b5402080c0c1502d0602c41c100942c12000f0440c4811402d826003e00154900362500d585500c0d80401c242e0400c160702d0b82400300113154005821a01e50b41c4010311800102c003402d515150400403960f4019542280c810300401040d9102c01000e180b00f1043ca01c103840d003c850100d030840184c8101200244810b0900301680100d111a0300010255882d81006100203210700e00c020555005151010758554004032100c20080040c0d07114000d0030202031001482c22008118003860020403070002c50060303100040d04003c4084032001981c202209203403940c682098900025100e0b540300340701400da02502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 224531681 1250 224530431 224530433
    0x24160c05061b07050a0305090406090203101701060801050f01090509030f04050d0f021305160e09040b0a0e06070c1707050c190504150503010f052202210c010e0316060c 74
    0xa2080d01d1900340e10104170b4000c9000d030310b0024003d4001500300c034001c40c281040490310890714002e0724030070008116003040040c6050100d00c17040b08803801901055681e03080210324980e080c0102841101400f86c08001549800142d03811204000c10329400c5403c140200c00c0c20194180480e021180c0c1116902a4064a400c1500d044c00c00080004d40c00000c00c51030607600d02846d04040d02c100850035281484e07074160001a03038100240000c8541c0000c83e00c0010340042c0d901c98031107421903140e0800058060400717400518040040d1900804640c044850204112151140c000740414200c060380c10f20340349035140b59660040750702051082680c02c42d1000644450400076008000041042c409810300f0a24540781c5180d60080c14002c0d4240515083c00181c3c6004080c025501a00001400a03405035280c084110182c400c80c1e005050b0250103601d4424605070042082e070141c00390900104c00000509800e2184c11510f000f41c200c8034065410001c070b00440c00886103503041900d00c040361 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 224532931 1250 224531681 224531731
    0x1403040201030f0e010b0a050a0f0b0c15090313140607120e220f02040608040f0816080307020f07030305040b090a0902041e17100e24160c0506 63
    0xc0c502c020150603140c00300342c4c00300701c005400c4140142025500104a140c440041c0705800e25a1702684482c0218814200045840240100500740c0000143c0d0380710b1400c0040c4283c0c940081d9070500c201d80c40411481c0209610721108001410154411104011040007040041c051064040d180100c2442501c01c00c5014001c0380104241c02407900030010000000188002d85030714032401300070716100c4081004034a078401c0383c0507280142c440303800c940e487e07039580c0d4402d444a1204481c1180188185207034012010015040c0c0340c402c41c01c550301c9203420b2400030b1070301011700c48264181d44442d4080010039000801c50b0207a8403c0860300f5640c100860200300410310a0713002880142c40041e00260201d42c1d28803208690380500b600e6101c0d640d0b249000b003060072107200304241d507400c0441c2030001004241c1c4001080c401782000e0710403008140c1c01185800303030f920101d4100c100401e010020030b24403e14601520003018105005104016140c10b0340e1240d00500c3c4683c4a4954450365100c003030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 224534181 1250 224532931 224532941
    0x408070305090405010b0d1a09061c0c0b0d0507020307030c0212190c030506240405060d06050907050420030a05090c0d050714061809100506070b04110102060106140304020103 77
    0x2d0251040c8243d50752a84041550f900c0b02810500592500783c0200c125903000c04003002c42c40f00280b10b49191b8444404000c0302081c004504803c440035041709500040c0004101d10049c504030b10881c0e1030b0303078803074400005072600100412f0854204000300400681c00000700e18459405071400341d552950307000824580541c0340541b1091800250045d0708105414010b14107591042040e100b8035120002c0404020200592003035000241003210320080c101544415030040b001045802c001c001525034008440302580c3c2d00d40a80c2000c1c01c2444141054080c00c240140d403281001400c10688106e1101404080c0941161503241c102003410b61360204010003c61000070b250409144035403a0580e510021445000c0c0129002405848146030810580d8920584801211040c3c22414104003407194010245e600c154021072000c11243c80d4100a0320109100345584c51440c1807509000c030b500031444810034115400320005003c03284e8001103840e00c5c0030199402d60745a0300c8920050303010348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 224535431 1250 224534181 224534197
    0x60303032d0e0f0304030803040c14060a110102040e091606090513020c010e0d080f090a03080106080a0e010e010f0b040501082a1309020f15031308040b03041a0a05010e0408070305 79
    0x104c0003090104c248a21080218040d521508031003181681d680107010368170f5080c12103c1c0d403104041c0034842829004640c100c1d1215440303400185403e40305c0000010507502580c4c8041c1c0e81d030108104c05404091000e2203005000a401c01c00741e01c078580000586003140c9410141107141d00030883d40060032003500448440b22988095800b501c0b40c0d030740f0040c1905030489000b07410404e4400480e030070303410100780101880d4056075903c074141e0822400f603901c02000740010b41c4c800c0c0da503922b6580d4002c0138031503410303c403d45200100300c1c0300311002c0181c2034440c644025407003030b4a410300410240c04002442c0d40c90a964005200032206614441d80c2549401407009c1c0e040641c00d150143c0000055108503001c510072240c912032141120103202030922081340040300040100086030910031014075000050b44030751074143c81d040d1510500780c030300e40040d241191440080b403025003020f080007414980c17110340743c58104915031514000c1c0c502081c0141001c3d100050008218051512074021501e6074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 224536681 1250 224535431 224535433
    0x609060f030c030603070e090a020d0311120d0b19050f01120203041a010b0702010c140304180203090105090a11010302091206090606030d0201021602091018060303032d0e0f 76
    0x6890400d039000340c0703580210b84c400d11902800c0343c00b00c1d5028500d54603074002ca50040003000000707142d90a2008807144a4402d509000d01c04003403440306c941c10060106903000b4003508a03201c1c0940c90682d000c3d0341d070101c01e86102d42060340c601100304185079540b1007195801c0320096480201e510042e1416258491f5855040b40000100001d00c100e000c40c40108140c0558201d0700c036030342c4c0c0001c0a054041e485000b8001124920348101241c28194809003400c1c100058a2a25646600c84d41012400d072410010461700071040020103c000e1150542c05610070000c0c1103080f4856498184000f030040307115050640c00700d500d2000f515481500d0400002e203208440c01414840a000c0e960b00b41120218428418480d10850700f904c18000d840200511024507101120b00350308211580000500e070304011280401c000400707149400543d0040e10001e2400038200b8198100103007a2050750200764401c0c3d03a11010060034007015105290041c0d25a040003a80500c040e140e9424440581c440c050340d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 224537931 1250 224536681 224536687
    0x906030c0f0403032105150d030210090c0314030c030703030c140408011a010509060a03090f0203031204050c0306041104090c050909010b04150e040312061509031505090c0609060f 79
    0x205038000145000030445d5004508501c89480e540c48180c817800c4601c59010f440d14921013942d07003408800e05c42410b102c0e005994808529484400032501c170f290060f103440710f1000c0c0400c02c0c000d026466003a00781d4804060341c98407507100708a90340c07840f610740b00504160751201d510031681c1c4544800000d04c4c0d0485101a95a0303603c02c0c415003e000b41c54011000c006524500c810b60b9270050341101c45140c00a4206420400e00d810240c00801c1d0038081a245290500d0030703400160b6090000b071104000072202e0712914140303400d20038608010107000354020ba00500038040450b007003407040c42032100c040b074000c5000c891510700307a903413442c040d030150f43c00018620a0050010040d00a19885602510200020705005200c08800382c858841c0858852540c1d0108022a1141d1030966007290120340c00306e80306035036104031400315400805010009490031014401c00110307108100328071607000828330035400c08159140c0c0364420145558402e0000045082264032050107035841c88204c4295961 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 224539181 1250 224537931 224537933
    0x19180302181501020c0112020a02010908120f070e010203030103140a0204050103030201061806030c0e040f0c03030509010f0206040201020606100314090606032404020f0a0905131203060b0906030c0f0403 89
    0xc0c102620045603010100340d6015295100043c41d8175102c20503540c0400d190000940c4034025400380c0415021552200c528002140d6418000e0658000c0000c149169160050240079023000160221040041005003020a41c0e0b00100f0740341134a411020013250648010140e038a88200b13000002d400ca800c0400000038540c040d03000404440c403d40200c1885049031200801311143e43c00018103502040d1002c1c81541c0c00252001c0d8802d210742001d82d03110f01c2035180c504008115600440000302300044000035541c2c04840349a8000003030005001500305980081d403580030003414140108280000e1480c0c1c50700c2600b00a0100400c51104503031030606410301c40d02c400c012604079008e407103903070305042c0a8900500d03410504402400c1e20300c80f5884d50ba08102d02d0107800d032000c6034464108600031444540502c101801102119414002d003006440c1c01c4001c0781c0ea8440d500c0501d840c0c00002c00034401058200d41c5840011920559a5910048184490300901d00200c09a000c041000300c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224540431 1250 224539181 224539219
    0xa03021903060e010501170a020306060705120301050f01050c030a140d09031115190e16080102070309080606180a0f230906070f110a240b040219180302 67
    0x5015501115501403403680c80b0401514214000c0c0803803000812404009000b0a02380e5026540002000f4211490705129480740340c9007035824515210b80010000c01044546408a03490702c0411080c00c1242c24141800105502c90080c1144c3d0720601038214102130122107500103c1d0b811690040e020848911030307050040991120703410009042c85074401c403042440c15102030610444602c5129240c41d1101d95040700a071505000718200743c4541810381d0f0000340c0070207254002c0d100e042c00043e110719803400d00a2a1f000254001e10042c1c01000a001c0b0b05d481c1c003010300016030103510801c80141c51f500700150003042e500d80154619850081001e02c1c850820b0f203142429240c0040c02e04850b01d8040c03400383c88086c2a00c108002c80d0714040100c00c0a4024102054510359220941d445070f0207585504203100e901400043c40d070142c405140340d0341d0605200710150881e00b51411403c0070207000d204002c1110040d03800060140c070203026040e0215010100002c1d541c00f40c00c80042c03400c03044041d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224541681 1250 224540431 224540441
    0x501080a1e02210c030114060f0123130f0f06080907080604020112020c07080106060311040806040201030e0a0f0302010203060901050d020f10021612020a0506040b0304080a03021903 80
    0x454406811030904800c080c1c00941401d5440c0d00144200c030342da03070040040c0d5210342d242202c0c2d1005004081c05102503540a1188101645130382040d203140745000003c020440d049030f5055810b00640c402404e4456005207405103240c1107000e111982c0e00c6010542c107160720000e40c040c2401b521021000714034000c04000034030440b1080d813180a19a00c80362070040d00c030007560058a40a038030100000380507611440d561003480c14003210061030515014591814860540c01822841e91545010401c0e641d0602c9140e040d4408400d91300e0601c0d081818960f104d2a01401c064100f41c2c580384000a1110309000010400e64000301c1030080780c6417480c02034080c0d0821221540304000b441d00024241c1081501c1104c8e142d402492060f55040201c05c000d08034100c203105004601c40d8501c002d14403881500b149000e00422448034003009500d00c1000f40201c6250440c0b4051213062008100034000c66084e01d42265018a0068030380460b020704800900501754591160003060310071a01c0c0a0701a844 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224542931 1250 224541681 224541683
    0xc03120b0a030510140612100506060909090a020a06020d050d0c050c060f150901060e042703050309010c0e0604090902040f020406030e010c0306050d151401080609011b0c0b190501080a 81
    0x480c10855807903d0800000c403147c4080c0160075040041000d8620704030390700055202c54010b041508024512000c01c0600307104580ca9821580145d05040542c13401c007407618018441c61005040020700520028428081d021a607014580c030b9103003030855280103005640c2e814103400c4c100c4035540740820f56040394101c25642c2540e0001103d00c0c5c00c2d46414581c000743c0c16240b440d00c407003544401d260184801015038180104009440e07a105080d412004c003007001d1807502940c0c9a0781c030381c14824000d908642100c0b00314024041e44841e0000f81d51164801d40d402c550711240c0004003c462400442c01801e02a9101040c09200240109266030154401614844160001c01020300100d50a0b0101e8206003e20b540c01140844e4290019102042c1020b84120301240801c00500c1e1218142c003d101c20f80001d81c1907000101000440002449885a540c005280c181c0c648403400c240a0000041e9a4000d401c3c00e03c1c2900007201c8880040101d800c44011104c10820341d81d507440d03c0354944001000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224544181 1250 224542931 224542961
    0x20d08210a0c0801150905090a0617030304030c170d0510061d010905040b061e0a0807021603020409050f10060f0f0b0301360c08070c03120b0a030510 66
    0x301148082140d403141810520050302c8410159091014a0401ea012031044000b0010240004522030311410f907800d004203004a00416164141a032002070041403200d1072001d54024020803000c603030300c00ca40c80886c0ea01700089003003004044004079803903c5048018901182424144000c841d5002046400c80f2880c2d0b590218061952544185010781c5080090003c0c5280c0418402d81c5425440042c0160004002510741100c07103076041510400c0d014030100325840400c8079407032103400c49181548284144040c1c500071201c12402882405a400003034000d6944400c0041000070030056041122142c07401c450f0408500c0c425100030f0b203064001c580c08164010800a401036070b0a0000302511030855003141103a08201d08503481610712075102c6c06000341d45031840380c010003442d00360152030104d4030f001c5411400710002a04100000d00701004228031382e50b509010035802103c0c1440b0760780b14007010880c1030003c40081c1c043c41c001d42000c0c0640c021b4100c042c80c0b002540d030041e220301481d02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224545431 1250 224544181 224544247
    0x18131212020c0d1106240d05060412090503160b0f0721030f0c081504090807081314091321020f1e031902010f0207050607111c0c020d08 60
    0x81c4c0311640320314068a11585640b1a01e40c07400300d80d4403002c140666008098202c46440100303444452401e1015a8142c0c2c401501c2c0040d031003d03543c0100950003a00d020f80003003c107000e6801074020070a41911072000492808a586603902c2c81d4141150234240c0c0200550446580c03c0ca83c03100c2402d4002c40032008240340c8840700003526464001d090211005486162a580e1505d107076000c1a4a00e60380f0a50081e0390b1060321001444881c090301d1060f02450199813500f00b442080c0341090790681003e154491240e0108640b070395500c0c0107507400211030386541a0302c05c292403c0000a080ca44080420b00c1032840c4a6041c00d40c006688000418403100b10b40e0030202181d041c0f80800d00c10f01c01b158054100304152a02c42d50b06880e00e10b01603015200004540c2510404c200881c0c01c42d010454441d0010400d21240c5030740a440400c40e06100000b4040d144a0a03a40000400c499140364041c00200c0d00d0b44000c2d903132008680c03400300760044603840d5a640c2150014101030090011562491141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224546681 1250 224545431 224545457
    0x90d06090809030607110c120a0507062604080901050705070509090f060604201c05130201020607210b1c03030e06070f08070e060705100b18131212020c0d 68
    0x751b54410880c1305454050300030503c8220a004101003c00100c48030740c45401d00040000c0c0d000c0110000810a0f40e40d10106480111400030100c0759a0200080b0007405005200108001e0012207625110034200983d4035071040c40c1c6103041c00810b920155110b01c0300410410004404141200c08100c02000d6070030f81e48d2801c0c2040111684840921160301801001a10001d0070704001d0102d00d00c54003082ea42e01c2c544405c19419242e088413150301040c01201710303204558041111580154032802c051341c2000400020088880c0403c80343d4010949442010007192903000341035144082100c41c1c0d9081300c84034200503014105140305944c840c030520380040c222030f1007140404c070040091b964004168442c0744003125940740f14400325503c0701d420481540058020404964000b030707811004500d502000e0108106c44200003901340e0f9008050040195440128400c1c1c9034165000c0d012420703141150008494a441c08010204018030004002c4503104c000125841180c0e83c80d980e0340c00e80d00750 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224547931 1250 224546681 224546687
    0xe0d0507090b0a08120c0313060905040606050c0a0615080307300c0204020a1b0606060f090b04050d05011409030d0b0f0d060b01110a030503010503070503010b0904030302090d06090809030607 84
    0x10600c9100202d0f000a250800c00000c5d01005100d00c0792403804490400c0054207404007041c209038860000300e1490402000142050700654009103400d00784075041c80c0c2040e03d182d4480103000d4004119540e550100c1050f00d41e8440003c000e0302c480401c0340d0303e40c42d862821140105103500c0c00c4071280104020200105000720a10448074200c2c0c1d40d94421121075400e12000e0340140c04007c041c440c007903000c00f655a8480d10351070304050090f0400b05d4014600b04002c0d0a9001d11600c9004100340d01409000d50300c0e03c4000c6070708485040d0b44528000c2503d050660040a00030165405c520411082c030903060400409000003444240c001c001c0020f03810100212982c00040c00c41d041540c0d07004450114906074451400102c1c103040807141c556604030309500300365448a044011880100050107681006c0080c00090f08058000b0001007003000c0019000040041c8010101500028101d0064468001e106101540140309015503519450020f18941101902a001c1e01c10000013482c2c10788 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224549181 1250 224547931 224547949
    0x6150306170309100c061107060b0406060239030105040302030703020d0c0c05041503060e0f0105010b03011a0a0507020613140f0f061b03031812071505070e0d0507090b 74
    0x18001e00c1132101c1c02242100362104401c00c2026a105951200d4104000e00140b005201c414810180090380c0d06600041004513031203500407600319400000140c02c292070103c80703180f214440800d000c061100844c401d41c1c0e44800d007400560036500340828403040580000103041c0551182d02070702c1005c056504101c0c1c0c04050004003904041081d0001c0080d030803d98080c3c107400e60780d40b404030225520307600d5071420744000d0b800910140c0d20284100d41c500e01d0a100c1e05014100d104400c0e40346500d4a00d50380754002d03204440000310311b00019600d18443c040c4080b03508180d0301620342a140c3d483c101c0042d2184245104051401c0e001c0f40c201e00103890048043c600802e40201222005100c0c51309211040e0042d8044528031000819101c007031540c02c0003c5e610800c11081880300075810045202c0c24040e844100100c10801404940006085040c80d881031002c111400580e541d1164012200529803000d90b070f030080c6426070914140324012420005498034040c050141070600c03028000195 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224550431 1250 224549181 224549197
    0x61801020f0304420f09050309060307021606081510021002090604030606080610150503060f061903051807030f1e020901060215070828061503061703 66
    0x1801c10400500001e50034100b103c80e42d004042030100ca4030074442d601c211114a0b29214440c0c601005602c580380c0303407600404010005050301400a1041e0360b8035917640e03001c0c045a880c828500440042d661501c00c0103401850034080c042034000c7d51340d4004c090004007080d0b07032078500c07580b550f41e40c4221810907401d01b40c1c440180d83e00803c04001808030301d5000390000302c1460b5002e10b0400002010030114000c600190980201070111810a100312001504680d440020001000c1980600954019041d42c0e4001c000b507603104c03100034180c0c0c0001c1e002d01c60081100484da01505144500316416030041d803240a40102e9081d050902c0c088907680c880044c40014108412480640700007509110403e50354039005801107146255540012058203090b08480d005a000d1402ca59030081e03440070513904520241030003000750030b0002c03458029903091240c038208007030345000d100050102984131300020318a0034011288050b1085000700502018030440c00d0503400304507112281d0102008480c0d41c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224551681 1250 224550431 224550457
    0x70309150c060c121509050106080609010918140c04110903031b01060521060604020306090127020310260712051005100e090604050d0e031603030206180102 69
    0xc00700568a000c080d00c000d10b40380341001940b980340c441c400c03054000c052480c419100311007803140c14a1444000c07a5016800078080003245428014241c4848680c0380c1500c40b80c40307000c00c000041c250700c0140e500044600420401200700d07100d802c9030021030f20070b40c5040c2c00c45e0140001000e40d006c5030028040e13029000d40c1600304100900c402c2e4505502c1130381e45000c09001040d40c6a07280002210070410000c000030b0f003203200840c3d0701404024003105a21400880342103046046c03900c0412294071050041c0c0e00e807007000204080650842000d040c0c9860840881075549203002e0f01082058840f40c072a0800101e601c031142120010312100080c00711242c0e0380103104c070f24030300880c60b1880d408004054400b0700505610b01c0c00070106002d10f5204007114418508000e1810600c02041d00e0000c01c09051904000140310000b02d0124001200046502e4030084070210803001074241280b215200c0c0c03d0404483c0700104054020407035a00c5203910034180d840800e01440030b24240c0c0f14007400542c407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224552931 1250 224551681 224551697
    0x160b0d020702010e030a1214040b040b0307023a080c16020a1806051512061e06030412020f190b071101051003060b0418060b041b030207030915 63
    0x50004698080e14840b4014980500d4510f806800719040c4902a902903a4038150000d18002c9150003103101c407014140960014601132520108030928082c0e03015108075001c002000c0740c0b280d07100f000008210000700000518512000e5080f401001c50281d209003004113440c901c0c1c02c011b00901200d840f50114600d41d40c60034400c0c03074003210b00d00f005000c12039002c0c091010110748000540000601c0c11320180000802505003810803000d194146a510781c0140200074150080c00c1c2c100f4134940110003652880e01070b91050050019a890b00d001044d0000c030044100024003a100061421405840d001d550001042c500802d448102981d01d5015210b211105c200000b0b854001455125440d807409809410009840b682507078015a00140581c01404040c001d010b41071080782c1e102030045030200305410039842c40d07580300311503c41c0240c4501e55031801e00000740c9854202815442030000d400c0c19030700414a000c2c0094000383c400b600001c00c107035808140340310030307000100346080309031a02c0030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224554181 1250 224552931 224552947
    0x5010b0f090610030915050601180302100305190f0b0f040509070317090405010801051509100501030b030109020d0f17040e0105060d1409070e090712030518030304031103160b 77
    0x54401d2904400e1030030141c0d601114804281141c0c41b5904001e103002010030319080c000001010407003500c19409503525124070400043c3d607071480001c03005810b420045a04d5542000301c0302e101140c282400c4c0c0f05802c15084d042c1190322940241070344001100d50070910b003000302c148000c803103080b1441e42c01980031840600106005800f141c06030f95080248c00c0ca00400c1c1d41c04603054600c01e070303c4800c181c2c1d100c0080c0071486d041012410740030785080c0e803521982d2920780c0c42188541405d2203443d0516030744001c019400e481c00e4000280e0700360040c0031034001d09000c0ca0711250000d000a000e0b00c0e240c055001e030f1081d074106242202c0071111208202802e59080004100c41e940c000c4001c401c2e401e5580010049519150000510070181d040c05040c0702890003028914000e0001d20704c904541100300148028869603a03051466909443c040e03855083d04100142d1036000b40507200c0d4184000318000080203485e5030440c41c4e049095003500c1c403c5003c03010780e00342e40446000716080c400050007000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224555431 1250 224554181 224554189
    0x60f05101a0906160b090c01080a0e030d0c050c0609030711010e011704081c021911070b03090c0a170601051309061103070e0a030f0209070504051201060305010b0f0906 74
    0x107150340c40c0c034060840c075080c50040041e42e03c0d40311103001c0d0381c4003074940005000c0c84040c134040381d030218400011344120310b0054002030601200610380c4110940d00d04002c000d10008000380c0d07901c495404810064003145000103809034021082400d032a100d003500090030420b0100a0328001d0364071801c0d10121031912001500e0503640516154100001111464944c0c01d11520190140740100c002a94130100e10300c3d03820040d4420400c030300d16140104003000d04800345c0002c0e1420741d501482c01010180808603400d007840140e41c0400c0f030085000c0103102d0b40d040b006c14003410300502201c64035541650790520850184460035441116000600100321900b803901c01c00e1243c80c203040001500184555481040341c04a610300352040340e02001b04039402d82c04c01c94032300d959203046600c1040c051071540c6d107512300c0c0c6160200a00906c00607000c100014010b105a030040d060040029484403a450100c034028111480181d80e41e6081c030a00d00000d0030101032810071100d01804414441e95000140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224556681 1250 224555431 224555459
    0xc0c0b0306060c1906051b03010e06150a020c0a3212070e06090a0203010308191e020c0411090105040506210106170601021906050a09140a060f0510 65
    0x10760005800c2102e0f520604040c41613080c80e03984031000d040398034540d081c20380449900030115400243c61141c41d450b45903083c0161390465001c801c0c035004c595034a01c0031a1040003e0070054204010118050740078a401180d8000e0030710080c0c0e01e2036103040da44d510f00c3c980101d848155540402c0460346031030303100310f2240f0031030303140e003406007805441c104141e42c420b00e0b041d42d60b8005403980041206024451030402112508a114510194219411516038075414414140420811080c501074002a1401340c4200d2016580768006401d011403503001c0030792a0040c0c085000e02c29840c02e0102143c4203680c50965800e0304041c1e40d1942040d080000307008555014a107064020030050300d01000c107102d030341c3d070103030107401103036104000c281c60362040585480d00503040f541590440070010031054948807410ba030050700041d010441d502e072514248010110340790050101109240d0305400740c4000125144034034440c070810800c0020316032424040300c40541c2c1510141070900d0302003222155030203c0e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224557931 1250 224556681 224556691
    0xa020609010305060a1e05150406020607050703030f06030305040905060a2301020f1902011e050901050f090a08010c110f0c190f0f23090a02130b13150c0c0b03 70
    0x41e45c810701e600c40c103070603803a035201c03072003e01800c12110000d010506002000f40d441e07000a004940c01c040c20300300041d45410340244150100f002c04100e00e402e05200e6040102d45085171003042101d640c9904000701681d0203400b541c3d100314200004503c05041c0844000c04442241c07410a030443d200454508920300884080c604500c030f48510083c0c0701006118031010a41880c061401950007840050408501c036440c00b0a43e0703011130045c03100560030904940d80306509107450b990b40e0309014070040d03640c040d0817295030300079008041c003041c0c03640154049101402030791519455110210402a591401036455814a4101104a410a0400e0032203400303040305842540462a44640d141c41d82c460040c3c0c0580041d4428100c01c024943c695035588001d0402d0405003400c80c14905c002c14645d07130014000707020080d4002000038600c001942158007501061080c9170703458691000002042c1164040d5146e28500180c0000c2c03407602441c850942c50f9030206100c41002c1c07624100070001d41000300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224559181 1250 224557931 224557939
    0x5131a06120106230108010303050d0b040e010e070e150d0b090a0f0302030712030e03070f0602090310061e080604121403130b070e0d020d08070c12060e0a02060901030506 75
    0x24074248150020302030400036050104499049010140581d464135502c0c040c020b051082a90050012070703440b4040356000039032203002142d01030000010800604000000641952070b1603000c0d04101804607105080b01c2038081c4101c03e03a111312540228404032144100e43c0800015100742c001907440900f00e078400e0003003007a0b8140f0011a12102d1110000110031401600000b07202c20030011003007148809001c0b42d00c0c007003000c250700200d0035aaa228003100a020240407a611804200446d01254154070700542034610301802a4030309005040301b402000300450310303400c0c3d0070304102280781e1320002c031440d04004005649558941c8045100208200420040020000740c00c41110030010343c0a5000000b181c480b40d0660305029110309006440001081001803407482c02e40e440719080203481da01142c440a01c1000c6242c0344034948541e900003088258584800079107019101c40411070540035280030300c0f04108100919403911800c400082d803000040c00803546a510a900c110341c0a80050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224560431 1250 224559181 224559199
    0x2100f020d060e0f22020118080322090c2003040e0103080d050915160306050a030302030702030706030908070809041e05070f09030b010e07050f0403050601030605131a06 75
    0x1460107016103640307400a00345a201c0e5803c0c80f8201d82c1c2c035014994410198114070070482106a800a101d0383e940301d0107410041d1500c00b600f01c0e8140801000e0040120a007207964400c0c0c2c4138030301c01080d03076158118070080c0c4000c0760002d00c9000030f00032814121010799400207040300c8080c2c0700c408880703d2040005641300601010900480c40c408083c041c5000d40c403125110502c0c20264020b40703030020089100c07a041001c4c0d40044d8919a004035800c80b010110f164450302080e84101d008200c603500595019107452400000e00d40c001c801803130303078030300950664078842d40b5801c3c107605984241d0802004e42204210310780205940c50040e00c0040030080c0041048403500703000950184140f054012495075030014041501d810080b0102c40320320301e09100b0780369855500e0f810808101449000300c4904d0301c2001401c0f407482401156014030604032030039100c035102c0c1003d40e0b803030800f400111440c07460000828a10080d070088174031341d550b210000c20400d4000c0884280f141001030103040e00107030b1030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224561681 1250 224560431 224560447
    0x1107090c0504240903020f030102090901030c17070608040809040e010c090906081209060307020111041203030b01050c030d0902220f0c0e10081906030b0a050a020a02100f02 76
    0x5806022540400e6a580c00c0d00c69040c01400c4861083c00700c0602c410a824694240c1600d40201c203450031260101c030b442c0120b1042c0c1020030702910409040607480f2020800102c1080042420b2409581301c200022040700c1781c4070711265075900c0501880e800700f0000400100016a008020031060368050808500c010301ca000090940c1e02c600d50401c0426524002401100f995119600003012900c0c0101850007001d800003541c0e00c224041580284000030018104900035003110b60964960300c2001e60342c90f0303108401d03584290883d50480001e4101480110030750320172000e8030719100081010710303e0000581c240c44018115503404a030001c6c04d00600c8041c4100980640488606840000c0381d60401d174000401101c0c81d51034903906000000c00403804c6911006401821018541880304180e00d6881404d2040400481080703142800e100000c01084580f078041d500800703000c6000d0116454103c1e074841a4001d4201940059121503000c01c0c610700b00f5044203c258651485c014645160 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224562931 1250 224561681 224561699
    0x40b0a0806030c1c020607020d0506130b010f03080306040e010e01021c0605030a030e0d030c08130302010806241308030d06051008010b0d0906140412020c011107061107 74
    0x1608012603203040410a060409109810410508891142d2080320b24880745102180c40c4c00040d00410010402c90b085465103e07010020507000002c440700d80c40c00c880800b01e04000c8040c200c0d0268840c06c0005111072503251a401920741c01042a401c507512181803000a080c188901950f944d25541c01e02c200040030710082c40068070302010b25609000d4824840d054412941c026130090b4005100b00340440e6100c010703009007000486c2c00c13080e9000302c0e00f000c0760485100079000c0d04800000540c2444440c0440418040304c4c401e80790340300700d07650340c00c204594407100d0040200d24402c4022001d5451107410001c0400b0386054495040070303500ca0f040325155402a4000c0d1007910360341c503800d000034076041031511320f00070451a058a0f01e41c10100f80b41000e0040e00103000c4a2925a0b13030700342c02c01c503070360b00081003030608841000c241d071500c0c0c1840403a5000700344100025001d1900d007040340f54404c208124a03d580c034002000b0080c5081c2e021070b40f0000d0801024654090300d00c010070743d104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224564181 1250 224562931 224562937
    0xd0f080904051611070e0109020a1106100e010504051b0a14030c130e0702121c0203090106150201021204020f0a0302060309011506031a090601030b040c030906180c0b0c03040b 77
    0x1901c201c030412001e1410308094003112107210703c00d04c540d000c04030422918200c5a11141902e043e100c000da11829951001d640600c6c0b801d03050003440c09840200324008115181301000ca4070300f080700040a1740d88005000c04c8807804d85400440300c00c080301c0f1703151503d00300008202c600c080303150841c074085c0d61aa21500d145c0095605580124001070200f4001040c4d03001840503100a0740364060310300300303460060b42c1c60160341d00307442080d840456400700f1031800740b0710f001002c04a80801c0d9070b685809103913540245640c1c0505503000c01380d400308411451052090316084000080021503a4446408001c1c0440000d00701640c0300380043c0000c130051315180c0145020311503100c00840c80204070700c2d43e0707803c10526070014801c00d0305c2d00040100d40d040003e040d06808101369001500e50300c4010049018049403a4142d070840c0c1480c0340f00f169958035511100b01280100410011600784000720108040f000c80702402c0c01c04502024000c01c0078820081c0707044016002240e00e890b40d24920700910760 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224565431 1250 224564181 224564191
    0x6111e0f0d030902130507090611100c110610050105090405180111030103063c0902190e011a040608090f07060f0e01080408040b070f02030a060c140304020d0f08090405 74
    0x30340380c0200307604604250070700c20100c000c4901d01340f20038582184001c061489034032441c41007217484484ad0141820510040700e10754608030701401036000790000580300070321140d5040302d5482540b00160750111042021000e03102c0594840b0b161a0300c5008101c05000c001d001d00b0075001715690440406142445540c54001030b550040340c4962440c24008102c9207295104178621000c11000c0800b0041400c4411244907030401000740c0601c00c03881e02000340b12208009400102071f9a00c114007040303028840d412141c49002929081c0c1e01c801da6031034042c00200c6004076460040c4024016140204c401d0f0b83d005040d20202c1d03e08982d580d0900b490310005501c802d0110b00c00b0384170300640d903910003454042c9600038280000070381041e940303407007a911481c800c0040601d00400d84508109078031801507078407600101100c0840d425400c018005201103000100400c05030f184240301c1290a0060341e1180d900182000e040406680310820b45208002c2e080754034030401c0044118695484c42043c1c050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224566681 1250 224565431 224565437
    0xc0801180507060305091c03091416090204051f1701090203010e0c090d02040e03070602040b1206011119060b04050403031a0616150213090e0706111e0f0d 68
    0x10360364505055041020380e4012404042c1050200814000002002c50505040c1c1e41740316060400300004900030a21075078020602e0105151000300d200340018880e0303500307038124801e030035043d52103802008a20a070721035950800801030700503000403002e03010321584500740d00300585c0108a002c000910705500760417180c900755000c00140007040e9544016039024040200040c90800c1010020304980d8060b0002880341b900c850b65100c03540010b005440e07680e61300900c21742d1559103e8141d1a6690406100505142d00100000e8000e601c510080f6882540395000b9103500300d10038419500e0402c2141e026034040b9107804000c4010740b1144125446240295000121000d00381040c1d0340d40c90310040a54812103051006c0750600f000e02051080c400c3d444120307821082003200704c0700c019009112410401d800c51150000b24400c49400407040d0307003042001e84407480c0d29000103940c2c032501d240c06117401d82d029050424241407041840b00c00c80201d002103070061284c11568071310700981e0035003007800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224567931 1250 224566681 224566721
    0x106020708010f0501060c2409060603060c0c0f0605060103020708040e060a0f050303040504020309120313050706050f1801020a4407120c1a0613050603190c0801 71
    0x2900038070070241803d40256080c00954074203c40101310188200c5c0151020000280c0404908600c4810300c50400c4a88014400e1079200d00b00b080080129110660f4103d00b40070a80309050f114800c41546207030b21440440d20b110740ca440b41001054020714844c18035600301f080780c0c01b00d000301c409080240b40d08902554240303008010b003e0142e03c25441b0191508030000240000e075008810348050742c9003560010703200d986821642e8903000810f144c54031071b01c60000030f02c030001c2c0724103056545090080c01102c01f1a595000101c60600c1070800321708682e00b060060b0f01011a0109039400402030520480342d81d0409526681e0064030000c039103e81982c04415002c21113818025402020020702814031221200c10003249a03510400100038080b00d43d9403491444103000d19981c8500075004042e5400c501c0b540310080d042840162096407142d15202d00c00f401d240d6250003a644a044060040c103105400014010340188444a0844083c4071644020403a918240b1545850301d240c456a040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224569181 1250 224567931 224567939
    0xc02010b03060c0f0a0201090206040f081c0905010c0201022a04060f03050703111c0507030b0c09030c09070c240b0603040309030b040215070605060f011b0605150901060207 76
    0x100311040e868195000741c010340d00300142c10303085105441110041c1908607a0b80d08aa140803401404582c80095014102140226108002104040076a40e40d131040f28a501d03241408003035410b00b02c101801c001412404280310a501c15200000114070600455640811510070707103c0001498208051440401c111047c00c1e240500940004014550350140c043d0300f1034451544030312007400302401005a9034004c141c25121504104409140c03403400d10000a11072800d00e8a550052000391400d00114003c21040c2032001d0455140000082c01880c01c604500144148460020000003d00c00006540320200e00c00d444024948500159594800040410050304a44a491465001c3c40080c010400020340002030082a2508922943e401e80d4503071002403404804024a503602d080e020840004002903a00b0560049004540301e46100c4400320044900703030044801d2000003240780d0100004a0156404250000d00805400c00d4411014012900400e030030381c06140107a0184030200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224570431 1250 224569181 224569183
    0x2010b0405011202011e09050d0b01050102100203011401200f0609070801050108100218060c062a0a121d0f0d0315031103010603020418171e031e0a0c02 67
    0x1030150030400805080c0700f2458000034000300d44900315072591000005140da0150243c20b9400c004d007030090501102094900e03040043c44001e200f094003521440141c0501006a402624107035403840003001c401200301001100d440311001480c28549001d001c1e216416a014800100440e210f10024012801d088a13064a000010346c040d4032142d250000620000001141c06c42203485907010160715846804058a094501a01d100303901a03000540e2001e2520081340a030311946164440811071600807500d071000103510309a18910a00070400394040d603000310452034038408000c00c002803807001011780e40300c0701004d041c2c0040254000351001d490004c0c00c000352000315003985418454075000422042d40501c1c1404020980201e586200c6016182580100c00540d0024000e001d2180c200301e4996822185440544160384a80c111041e8565a08215008101252008110481d01e400c2c0800182c00260a2401516001043c223908001594400d40140c140c05030014100d02403003406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224571681 1250 224570431 224570441
    0x9060b0418051507020c1e0406062109030909090f020d050304051302072d0b0f1501180302010e130f1b08040b040303020309030909090309090702060c03130609080a02010b04 76
    0x940010f503c00040003d401d41c0421002c20541040c0d412a83c1c0324266040c1c1d141c900c500d040b029400c10307e0031000048556000261071010414001141da0a00c07035150081c06441c08440d01802040c0084020050f016003948000384150103001545400c840701d40c001407800421403000e8030103070310104050006280507950088041c00c01da1046152007620b507111107514004900c40d640321200e248240101c08402c001e08411030fa8801d5142c2d89a00e0002c0c0600c002000c259131b00002c1305c1d4260002417042d40a4026a40810340c140c00c0310b5802c4c1c2ca1980111008069038204e9900300528034080c1c0c1c0729180c64052038081c107112020204086c40c51048140007004d107101e400c42007101c15420721011a10484445030025054a40941e9039070b1042d038603c2c5148101200d8980044842c81001203960010021b020040e0040f9403080d501d40390117400300c1e0b80e480213980c42440300008002041380b42d21284c0125200703602c40d41001c07076030744060380714145650880d10840025035111140018245018821 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224572931 1250 224571681 224571703
    0x2010f08010e0103030c03030e0609070303020601170601140102070b070c091a061206040e070611010c030b15070302070b160506060a06200a020904030f09050d080d09060b041805 78
    0x301940325803524401c0c80e80b1103030600c000340911881d020018185442900140603540050f000c0b5980d604000c2342203595107200e44030503001801039038008140200700d40d802039046103640005144130303424035443c400600500385910341035101e04c00c030002e580c007000b00c00f03005018010780c0a42c0402c2e2924402500b81d40300400c41488c465860360442c200e59581c07009517010590340e01c10260882d030b03818000c2001000e06c666a101c6a1062071030000e0910f40c009101c90391500309000034041c052044100f80d0555442c01096030b8800909601c115000c5124009082d1840c00b070301c11104003e580e1171000f5441d03840250608400840c0c42c03142d40a000301088071940102066417100380e817906e044d00c0142009511800040502440c19a45002075000c00900040310b40040c103039103c82c01c1a15015002a0000b100d034008a14403540020f01484d025001212140e048680b0924050758050040f00a2200c404100c5d01e80f56111200c0882d51070701e2107410381448211105c1c0803040c03020b0034003c0c43e101200345 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224574181 1250 224572931 224572937
    0xc060108010216150e030412020f0f01020c06070312020a0c030f0c0302030307050f04031205070209180c0103050a1829060609060a050f130905011202011d040b120a02010f 75
    0x104111102d0380a03036505000725046031130960040c406205041c0035201059603039805100129001c42c60701c5840b01080d440c90301c01c4030326458032000801131000c20032854030b00310b0150f080050f400c0c0d014103080f001070a0940c440c0c0b03807072940e013405000340000302d800035503001d8000761a17807011004068003d60040b42d0112181851000e500117560300075038a04c0002d1501e000c111000c1070510b41c210340041510055030344400c403288000a9150024441d41000d841039104600c581e02084d40d0208100b01c9044c24100000a002040480c50054014000240100d81d005a40e03405448404010a049500092141c10410402070000072194000d070700c6042c0b04d0a54509050a102a5075501c80484d4030b64101600c205840c0c4101000a03203030b9001f407101407280308400141117030110062070f4105040d558540c104202c56604ea000000070001410350007401b2030300804100554460080307000540758801440807610940c4800800d02440f040345c1c04041d00d51103c4884011903804c04c1002c00ba000e100d01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224575431 1250 224574181 224574187
    0x90b090615060a030605040e010515190b0a050712020a15020f180d12051e07020603040204050615041e05031204060804050a17270a170a050d050c0601080102 69
    0xd04040800700c011803159104003800251000094041c2c0c00c00001030200070410400810801d6540740a003c049070b03100d4481e811081d01d02d005241031400703076619884030042d4445490600d07038a003103150300003180356080c006c0901010001030410000780030304120b0365002e800720802c18640304021082c1510201c8a09005004d8207101c255a4000d540f00c02c1654002081d4800b8180c01181c0c41e01241000500301140d240c240c840c00726007010041a40d0940101c101080004e10011070045008a480c020f40c00003080010402514254219a4110710b0040030011110010402c0030b02650240c2d1011040c80c0030050516030880d03241c50b00400500c4241c000d80204503640c2c00707250051189000700c0f810704c52550089010f01c4020400f64402540c4401c410080302007008500805030450b80b00c01c454035043c00311403090000142c0d8130100c069006014008698100300501708004240b40d42e50600740309003500040460000c01034800c0f8104103842d110350320300503152050309210050700700003500e80c010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224576681 1250 224575431 224575441
    0x1f0b0a0c170a020d0c0f05030a180603050408090f030c030d020d09050a06270503070909140a0b2802070809091302030d120e0a0503030717100902070201140706090b0906 74
    0x1082290342d00c40c445c54501160340681ca000d0b0511405510f010b071180c40b010804a5403180c03c100094508401803000b901010fa441104a080e01d008940050140701d0038480b190090800403003074030440368010141d0b000106035002181c508003440100f2401640041c048501040d005030144003c1c0006440c0115418100345d80601400e100b1580b5018144e9504805040410034070003130800b40000800b0f8540c0c0c03d549110300b601400b0100340948455413a400754441840002540d440c003980e02c04040383d401d0740c4284104400f03505415048004042c14040095560214401070000030310403200c1544503001c04081c0312048100800c030304402d003490074104015a400107001000d002d40d078500345420409000ca130101400c203810220307030144503400c2c8100c100080030015601c11111582c402303e1001c9c002601c00407050060314035130310038589407900740071034001c680041603400d0044c10600b051188400c0580500d03807010505580160362503480d141040321a10a0030b0300034407984020a25810704c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224577931 1250 224576681 224576683
    0xf0a030807030f12050c0405040c080f0c0c0c0603010b0705010c022a01090b070506090f01020f091003180b010e150102030901080405120c0726061f0b0a0c170a02 71
    0x64110140501c01051079080030244180c135945180888148148210706044088403044d400900070980324030704100b152041503201e400c1c218860307480720030860031a48490f1507a003165403042440310801d005040c0c2c01301003a1a01c5004500801080004541d111643e0410034212061070344007034115000525103103002d00d907030701800302000c001000c0041070021060058810400640c805c04a041e4045040350900c800800c070240300b00005c905a03110301c090341c1c9280d1f00703c0c4584254282e012a090180c2001d03418840c48801c100c4c802d509002541c0d00c181d40c140c0c20941148842221914440001408010b0409030346a800444e031514010340d45160400113074480c018000c026042200b40c0c0001402e0000400400168004070085a55140300c8101d070320362a50039a010300b0b40340004a91880102c00c2c8082c4007400c0062000000d40b409440c0c00b141c02e150410466240445000386c40c4010502e4031035100240746410329500c80c400580310340d12f80140d01050104900c01055028840c1c21324040d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224579181 1250 224577931 224577937
    0xd0e0a0f0b0702150c060c09030a06090302010b0a05030c0123040f030503040807050603040f110a0306110d320a1506050d0b01030b09061c05060406050708010f1d0606070203060a0b0f0a0308 83
    0x440c655583e00c0d502484c0209181150790030008d42f000382046c03481c00c00d0540652202112000c151030008007551100c1c245a500c2d401e6003055800a00d04c007440c6020000107050f5000040702184d6010320f0281c4e90070380071000c807c242e001510f054100040c208204801007011000600040e0351445c00c48c07400344c0b150070540c0069030010b081c2140f04140f660095a070b007a0450080c50b072281081103001c8690584911075082040000d010354a8003584409041d0036030f4440600c240142048000114420003c1440c040d01500580c4030940340c00452210780d0003401c1110140c07009a49694498544098070801ea414038403a26050529040c030a0340c80e41c03200c21030301ea0f12030b01c1a80c120007415100024203080003031144002d0014010203061004100d550b82000c4c0c00f0740d225076200c01032662610a04445080184079841b9035040044444c5c4680383e4030002258000e000506035801c201c0c00342c0110381000c60444541e0754190360b1310914442751400c1e18a005040b08161400700196007955a007945603c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224580431 1250 224579181 224579191
    0x4120906140f160c06031a01030216032003071a0f060312130e100e0105090c0304030311040e0901050f0903070506060d020d080703030912050702030d0e0a0f0b0702150c06 75
    0xc00075405031003c48860b48026035903803000011604541d600c0c0f00a00420034407074182c554440031000c041480d8460300944020390b001e07645040403d85150f40540da0110800824a01c080c1000c84001100c1001d0001d020140d0084017240e01051100c01c420f4001200100f80c080b4140050091004580300011542861550720184981d180d0a00b0a81c01c1540c120b90b008004c00c0c80390208001d520800601404e04584107020034110700d0b601e8408000c200107040396401c101d600107100050100384280c00c030f0004a0712502110349416180c0300c01c0c0100300720444094680340c0d1110140042c4081c2c0d100100e6002e1025001b846c1082d003190345407500c0b40340141c4190710580e014080301c03082d543c610506034400d603804210315584d8030262070301a0103080364801c1514103126942d03c03502464022011240c20540c003c020306209070a035907064070060550500150080400140840c0f015118106000940319244910317445020f00e1041001d0840341d0a01d1a100c1c1da070522a124a08000042d290f8000f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224581681 1250 224580431 224580457
    0x3110304030c06020c01020a020f010b01050306010c170409020a08071112041811160b010605030121060f02030703090c05030d08180c0301050f07081501050306040e070e0412090614 79
    0x14164500300700f0043e002c1c003c0000c501d940b0004010700007640000c3c1c5040c0303a41d4441c0c0284100242a030042d01c850100301c4141707000c991a4030780d0100060f080b10003072915101e01001142001d0b21585014101c0e0030118241d00030402c1c0c6410b00c80341c15003128507821720381208001000240c00c000464003060003144200c17580280541c04450b55003216400640070501000078075611801880c0c000c0480c0040d402060381e40400039000450301314498021241130b9a800a403000d1440350b9810403100a04610714251203007030303403407510600841c141e00056001f9001990f02190a00560a00865040080d0f100074442d510903420100c0d1a40c106c9503e80d032080e00b226441ca40c40c0703903001805041c01c6201e030509900d075203041c0400c03500e100c0c02d1007102c6c002c50341561380380c81554900100d400a80c02d2440d805011070700a02c001a00303498941c0100244000440540f03044981d0b8071803011140c10140d60880740c0740241c50315812034039802004140182801d00e0600140420090071460340d115060203541c076 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224582931 1250 224581681 224581697
    0x10b0915060c01142a0a02070b03061801090605010e09040b01092d05010609090e0c1903020306040606030201032a0c061d1c0e0f0405090114070f0f0311030403 70
    0x64202d00b0360082c1c01c0e92074006601c0c0240d00c0c01000c01031001d03400c4a079412030102010703051801180400165007001d00c60342c0062560394203213a0681043d40009002a6112802108040040341501d844d10300821030741d080812a80c0c104030000d0850203503d030100d400345806108000c040703180594014111a6400c4000030741c81590500e031988800d040c901142d6042c80c042001c26281c1d4240c0c0707c0b42c100d84165486110355921140c000080c0c0b019140880801e03800940f403e4500c0c54805001d410242081d102c0d05000c2d652513000c2420007000b22800c0d120700d541d900040055581500403540080c007600082c54807240300165a550504107007441104003c1924880710410149500c0304800d4628209900c190540c100d2006170b42d0598a410040c102030a04e60b20703002c80f80920300c0860b0a200050180960004900601004040c001c04240c200e640321120001d90b00700b100d9043d8000c00441d030b11440c802c283c50310003810300040d600c4c108042500c2d00050a4180c00c0e403205598100d40d0514103000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224584181 1250 224582931 224582947
    0x6041107020315060108010f0b0328140109060902030103080d1a060c0a12050c031611040905030403030914010c12090e100602120a050417070e04080c010b091506 71
    0x2446000d0400000d4051080a020a0401c0a909400c2d481550b007641c0d40345c0e8607030701c0d800c032521001d0252003a46000e08003440415030414052110a903001c40ca04400c002480c0700000301d2050340c5003003100c03a0500b182d0b540140708200c4c40b0300400c005840405003d40c41c5500d0b51351100d907240b103545041e40100e0f681307a0381da05c10f0200840c5840444040280030a8999401800042c1c48040b0401c04841016110116685841c000c80070388200241c9003001d5070502d40c1001c0100c4803680008030803148404c84250300f00317a543c0c8500c205141103000b4001152a24211b140c06440110b040c1c014245920706130400c10303656070344034910700309080c1c1c020581139480d400401c0c2520a14603d0b040074242c0610a41040b2050b03034010000b00403a0324580c201c50800f1220210040c140c4651030141001540c100011301050040154107040007840c003007240c500a598600511881034142c07411250140000b401401503002405250210201142d0550850428800600860f06c01c80c0300384d4020035010503069 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224585431 1250 224584181 224584211
    0xb010902090a3c06080f0c0405040902030a0204020706060806070e030a03030207230633061c02030c03040303141504150b0412020109080d05030a02030415020703110c0d03080604 78
    0x241d8000b02500d41052244003901c804001e0f2240a14030020303c448000a00c48118040c116000e60704601c20035240c04d0400302440302906039400180c0c1c03d0b00c0703101c130700310010389841c8000c01d00107014040008800c0e0520a240703003040301c090541401c0011141d9580501d66000c50154035044c0d040c1001030f5600c00c03607e00421f5562003114290705000303050105031102c220102d40544a0800e041020020502481d13125603041403260f041c80702c070f0945200b001c01d0380c2031581c0141019540c241c600d86038040d48480300710513070b8400c87d500780240c00048103201c10140c040c0124107400900741c0e030609032440c00140f04081c4100c8220740d94030032615961001191425005804085c1c4003605010b5030f02c58980a2041c04626109004c0340050b0241c00e00044001010600c0710320509943d541d20300d143c4480030001e010390005002910b00d401e100c112118088040d20090003030303a129840300304103151011966400c1c005801503403401042031243c980c000030380c03148213181c2c03000003150005001c1c003401d5000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224586681 1250 224585431 224585489
    0x90109032304062307060902040b0a0b07060b0103110408010c0e060a020c04092307030b0a092307051e0301050108190f050703020d03080115020d05030c2d070b010902090a 75
    0x1d04089200103000e400384405500300c006094009d807014040030581c001880380712000c92107140305890060040200042c45508056015181450b00ac115140340090700c80c9154029030040b1556075403600c00f190721a4004ac41082c0740e500850303809003018680c02010792507085e07200c4001e120781e0703a034110743c8100710200000601d0541c1042c192422000003408241c6e0306d5049000940360041800300145d05418035020309049141e0080b102c0300e0000c0c003803280e2018103020307009082580c09000b0011038561281c1c950f140c3d41305481c0c07403c00f41900c55901458211601a00300039101c0e0440c42c0a03880d00700c1581a0340300c0b06a4480503210604420b4185141883d005401c001c2d404101480f0b00c1060640c03000c8124140c5040018185041c04598402c0c1d0b030700c1c140b000042c0c1c0420001c0c40010458a005405400304e0024009c03403910958505030008809500d0380100384103400080741020a21180d500e0f51405821890070444c83d182c83c01001520300081445220b100d4111628190b82d041001001c1d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224587931 1250 224586681 224586737
    0x307031b03140c031e07050a021509090a050a0c030b010906050a0c08040605030106170907050112020723070f0302090c1308070303020d0f051e030c0c0609010903230406 74
    0x25a03500c03480040c2d6203e0300c80e4010904005000380e00e8018200c550ba405d4110394007647c0c000c1c010701c2113200301d0b424005480010341038040d840800740010021500c96180052281482c0d020000d03031494a86003040440716a15040400c0510300b054191850b40c1141151040d0350b8181081c6450b40c000710380c122041c01d00709000030001d5501040000d88145c006000d181610125118004115815049507004803400c94810030190322100703041001e0750086102e0315aa40d403003000949004103580f2410020384501c042004680010f160600007140c0503c85034004d41200801903c01503d5500011581100900910700801c0300003041c1144101c0c50700018003c001c88400d841500e5985d00f40a91100d0555000782c022500c01071015001d43c3c0718804965544103800001a02d4044d180d600002a03007000b00300070034071141001900240c03c0c0400003a071003040b01800110f0180250b03c1d0080403042c407e0f074a002080212180030002c404102c0994040e21075500c0d000c034040203640c151140240f030000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224589181 1250 224587931 224587967
    0xc0a030e220e060612070513060b22050a06080f060d12050408011103090318040f1e1d03031306090f060c0206090d0c0b0c041e1401020307031b03 64
    0x8007504414419005494801e80300070903981e03641d13920307810b10640010345c02d188041608100c1d400c0c056468889501c00c1000f12100000a500fa01c80001100a51100810100791068075400402d83c00181440401a00c42640c2245000d07181c40000f411001c0d000c1c058140302030304240041c2094030b404c24800c0301c40360046080b910002d000398000d080c40c0d100b03010b108201e5081200c02040d070381074401164003603070307001d4011482c040c4d20030144407480c44060300c6158003d0b1a40c0c594540100c80c1d0140200e40b01000642d526203a059070041f1084581d00c1500b4040d00400800c941070ba081c000c02903aa100d04040c0300541001c0403890704034000e180c0c54000404c507903c208241c100348410750303015174440d44040d001c84144e500e070b090145c4d90320342d4045500c0c1700091044011000140341040075035045200342c0c050382d08080d101e039401c401c0717017410032800119401d0343c1204000a1000c5101280c41402c00e00142d8980402524000d02c04100b009000c0c0c20004103040074800c00d48119088144040c1b01e803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224590431 1250 224589181 224589229
    0x70203070609060e0301051608090f030a0e030f0601050a0e090f071401081509070c051c020a02090c040b0306120a0203010f0501080f03131401110a0b1b0c0a030e 71
    0x1200c05082e960482c0150000140d50b881280e1907803e051007018058004042801c803020f0303c400d0300300c9108a00908042050180c031282080554040014006c038050944400040200e03100a25181021448103048254095001040725443c0c900d0100306482d40440d0f441c0341c5517100d529482c50032840219440851040040000d00705078482d4019400d900b0998425650b6143c07603106000e07207142e1403800c507401100300c80403510403402a10240001d9114005031401c014107007190980c141002618080540c200d058110210300c1c20910300c3c2d074002d410554450070035081000c120350a00000341014054082640e514189080404c0b81d001c140741e0080080c441b20300000c1d46040030701020704c1030500501c82c0b80b51150403100e002c801e0f04c800015040001400b203142610303183d90501d40c4000c49040c410100108090101d0610000b00814010000c2c58050f0074031601d2503540606101005040e031005102d09072801c2c0020480b02e00158040c40c0403003207401c400303001070217032100c40081c000780342c26007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224591681 1250 224590431 224590439
    0x14060c0a08030a06050603090d031503050f1501080d080703151206090c060c020906041814030c060f1303030504020a0b070506040b01050114040e090c0d1110030b030d0c0807020307 79
    0x70019803059900c42c0c010320910340e652007408003d010584030710106800c410282c8861038440c0d0b00040105076440c0c0c99144c80c1f0380d030392034403801c102a818800003541c02c0a080510050044c0182d03600414645008180c0e207025228010105840a00700c04101510b540c002c0440802c440c01c08030241c1040c484074101071805207400c1000745030000c01102e40313034400030000964034014068180740700e03005020f1202541e505002c000c010071018542d14010326058200102140f42d00301c28040d015284002199206181c6980030f00d8514000c103001245070aa100304010007200003042030000740d06050104207900e55100003030424915410112b10b1000104d6030b07400340400001c0c00b034007132030003038001171441d0340c1b19401118500b2a0030142e00781e500041004120f0a0303440c5844640c810300ea0000e56003e8110b0000142001d032280d2000c0d99000da02000350b4284d0b142c500000102c083d500d003401c10034146d500b0301003600d4081c0c211300c00c1c0601c2100300014003400b20400c111400c1560040903144000e4031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224592931 1250 224591681 224591693
    0x2060c0a09150320030112061806020328060b0904050a290f090f0f09010e0d0908061513020c0106030602070803010602060711150402031504050d14120114060c0a 71
    0x40301050080c0b0703a07800a4070350b81400c48812a8140e5050000450f003c1f05582c031140003400c04200b401c240705501c140440081100d500c09540a50140503001988180390088544c2e000c50611007c20414503040e0200301041000b4100c42c01c1440c10748000c995640d5000ca0240149402c2540c074000c0c0b1078800c008034198451425955410344100d603503010650350a8284a903069003111004402c80c8460f001c608100340100a0940c060700660010403075039286155541004000b00030400400c0c5031315424803172080c0501185900c01b0141200b0321071160117000042c2d5160010105410169000600b468204000e4110002454110700e088d90307296000e20302404c0b1940248614030042c001d0030041a441d5115054a0001d484c19000414110b0301c4a208114080c1010708100c2e4984103072a41d04c1e0400100050341840b49000c2c001800c40040c000002800542480349040448079042014140c071009008400703054541e6100902c40d0b150140c0d000c01c10341d100311a00405035215025a050401c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224594181 1250 224592931 224592941
    0x2130308040f0602010209211c030f060e0609040209130c030f050d09060c0b15092521110f040806010923060103050403141216050a02060c0a091503 65
    0x584042c2620300b550303642108a00301c0c0141c4000c19880001400745454010344550b000c1102405d045c1a9003881d00d500308803600d60b030000b0840c480401d4a4a04042401603284681001010004001207451078050001002c0c940e0040000340714100350001300f4a940d5030504064060340d403002d01e4044803912420880d000c0c081c1c200086455225285540207000c3c0f10b030f12540100c03401074a0300c040008c800c0e03450700280e0380d00605044000c15110441030700765940800050040c540100c0c4402c5c011010441d00d51036001e2508103034240180c0c44828950b5039012962504c0c241c0482c400000c008201b000700c0c0000f4441c80c03601c5584404041008903021001107409030480b080350408002004661074a0004040d611540c0041c1c40ea40d0b80008460754000c4c4c002940c400d2203490058101c2e10003c070802880d80014004202651440c4204000c461a020f82441000100e00340b03142080c01c0340c1e4000359203d0005100039100c06011400c02c4c4845d028004600181c03081ca003c001c144000003000400400e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224595431 1250 224594181 224594189
    0x30203091510092313020904080a0e060319060503240a1b02030a030b010c020d0308070e04060909020108010902040b0417010212010914070f08070c080d15050a0803040803030412030213030804 84
    0x1404d0700110381607030b078040c030f564100b554080c096141a5881e41c4442c0d08a4004200d86000c5c80303d51218a0100d582d41030041d031082c2a002c0302c0003c0d2901c3d0b05060b0045070682d401082c020b038009112000807034003400d00700f03641010802c11842150b5410100c5000740079011409000b20a039545440c100d81c2c0c01102411607482d06a50803c8043c02150044070010400040603400524041200c4080391040071065030200380fa0400b406007015600103c0c00301d440f682d2000148603070b50641c0e81d08540c0c0c0b003500503005201c40a0300b5814a410000c3c08055071246208404618a2240c00d10704898029015980c201d040d61081511960b521039040c40071700f00003c0070008010303083c00001d100b58014481044c0130060380e03803540400e82d40e010064910001c028803c5e0780d5200f0900c0703c00800c060901505046002e48660028507520b44000d0016440392a04010b500d41c00500c01400303000f50010070703070354003903040780030b800084804400a800034414000040c401d140c1100001c01405140c5001b00211 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224596681 1250 224595431 224595491
    0x2e030b090a050705122e1404110d050405071805060a09150e06030f03040f0509070f020a120e03010c03050103110f01020a08070311030a09060f03020309151009 70
    0x1641c94421110845004442540c04258240a01c0e500b0b0800400d8041c0d100c00490700c0e001c4d5001a2401128030b07004150131043c1e920844400c140191480300303114140031007003917030180700316110f42403200c2d254003404042500300d0755924001403c1c080c0402080b070040c503204000701900ca6032445010041c10307080b110343d80903100c00c480008040340306100d00c0329002d1000d802660502d040181c050311511016214940c5441081c4180321000c400b4002480100205141c0c4403503c1e250030140000000002c2680c014072040c0c40355105901e030085400708105504c20341405c4031710000c00d003c2d20700d845003601060b010762800816014040d0141e201c24140c0c1d000ba120301c41041843c100b08038000c550310389414010380043c5051000101d501002d00b4529200381400e42114072f040c080c851858100700c82030b000060102c2c2c41001020340041c1c010140d1025071800758038501d018250b8a60f1070115041000c1c411244400060340342940340c4803c00900a083b4092164040303440c0b0b001072010340400e400400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224597931 1250 224596681 224596699
    0x1d0105040515150a0e0a0b07062d0b03060f0106080705090105071e020405010902090d060e2b0f0914061305100507060b0d05072303010501031217152e030b 68
    0x11780c0c5080791001044440f1000a41d1030210f55603164009418100c000d010843c001d090b52100c0c1d42010881c036010b0b10040280081d07000781039010940740c0f8202078002207900301c42e900140812548000e140354480491f08000340d840345200012500e0744981c2d1070152104030b40c0d0035280084811881100402c40c001c40741800540d1f203c0c0c01140032440b500d80c0c00c990000c20b0b4966a8001892500b05401798429001511855142d020001410307000014440c1c61b606410600e461150750060341b580070055044c50041c0c1503e08150341c000ca1000300000440c411800460030101940c4140585005400081c050b454405c413464006801a045200e04030359160500c0a1500b0074248039a401e00c2c0d0320b4003c002008000c3c58002440e110544d05410b44800801040e1018100c0c1c80c24015503008521820310801d000001d05801808491f00b090001e1808039620240100800344034a54000c0b07000881c0c03d225a05e13142d05c4020110454004902482140005000a159055070160000c4241529100b42c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224599181 1250 224597931 224597957
    0x10b0a030e010b100c050109150b010207060203030402090402040513020d110102120c150c0c01020703020d0f0e090601081801050115030b0a0305030403081305031504030201061d0105040515150a 85
    0x20070780e0400d42125800800141444c1000381c807070f100b95a0001e001d40300004203885151290148104107181840049841c0c03170b0340c400c00f564100506801000c45202550440c1802e6002480075940038001911503034407400030a458011120b860341050b0b0b40109802c00151083c601020070b07000400c0c07150b0150280034030f201419031241003102c801c40c20090140400c40080000c4c4038051034060310410040c0320074400850303918000d100800c04203003c2d40062115581c01500242100c145040c08803c100e1800390b021030946030b07183c0042d002070090038005030940e83c080c40f038075640301044c2e650340d002e6081200004892220b14500f0740800607650b4217014441520052085001c40f520008119502c10002007000c140d0b03880140090149003034021240c2580d50002074034040000e405140008110420b0004045d02442043c0c002c123171002101c44082c0300380e400001c3e0b1540521925009949503000201690400708030194099401803e0344a40c1820400d03200c6150403e860540200b10541c8541e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224600431 1250 224599181 224599183
    0x708060a050d17030a02040b0a2a050a0b180d0917010e070e13060903180f140f1c0c181a0103022b0e10020a05030c0c07080303010b0a030e 61
    0x20307070190001c8280c03160f008100c428140ca03a2009001d0340601d82d00788401b1403a4a101e8008054859031540c610900480d038114181055400541e040003a20052030050005600422440307a0583c00c480700003607a036500c040318540b201210000410a006045c80190341d103800c0410035003601c01460540030420f800c6e140312070807215403070b00303608990303000305401c00c14030140a2040d5400310360f07404003101345150303507a403181902c40e0031000b1008030360404064551480d0390410207000b0000c115569031501e181c82c880b030010b89504660640103400b009604520b6487c2d00c0c2c081080400010110f04500c10710341001c880000c0e0602072610109135049107809214081d0083e003802d0210344501403001400a0b0040d03000350310455940005d00800300c41410300e01c40f1494081c814040c18180460008800b24049003400d1190b882002103a02c140b1200c132540740d0200070b4982c00405002503540d03c14182300101c4c81d090455104210740c1c40000004100380030b4107405005101581e403424002e0300c000d92402c1e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224601681 1250 224600431 224600449
    0x608060f04031704030c050a0606080d020c060a0e0a031e0b07020d1d0102011d1606050708030a2403030e0406050405150907090509040602090f010807090302061b0102030708060a05 79
    0x500010020f4003002c00e40801c050309a078005110f4105004900c2d126030b1424103061081740c0c1681d941d952680208294807007400040400d0515101400a0340c489400241c0b16020340c440c504200044241c04010340d40b6a80866006503800c03007464076002529203a08542c1000d2030a0440e01003010304045035080f400060044580c01e900c0d03c50f1a489400b903040c8504a01029605904543d283e2030a42c06a00600110441c040180b4010340416844102000502c2c8060380c803c20400070204034050100d007001e0142da811130903a0602240c00d51580d00e111170000c01051260381c00914810002040540111000d15942000e9030b00f0f00030303a40c0d1402004102e407030031100300c51a00340c898111002441c00000c082d9008810f03050801031030340c81d8070100d541c44204a80403075100d5400075600103103203080c0c001c0725100102480c24107401c1c60f01c030600a04054051200034011103000c102c080007040007184185400c04004021501e0345801c4074000c1c05000183c0e005401500c120301d0210352800c0103100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224602931 1250 224601681 224601683
    0x70501180b190b040e15010609080c0d0507050a080307060f18020409140d08010f0b190c0501180b040606060203160f050c060309070f150e060d1e0608060f04 69
    0x1818032595500c0480e14282e81e54481010005582c3c862807211a59184900c3c0b02e12141e403001020015881c0c0480d8401d844182c1201c018070103c03c4080102d10300028448400160030354284a4100d2075203000c9282c00b44d0394003c0c582c041c840d11004a00ea0300d002001d4220113000b444180f0401c02000200b00485820742010f081c413400c046040c0b00035081540040040c0e1b8411681507120049000201d41481c0f0001424000540401c00401c5180b04900d42c02c0003400360800c44038502402c3e0f00b161440400309940c01406d0140c54545141480b1080d48200006514200b44800b095400d107400300c003080c8201c80c220741007031070300101040c003c1c800010f641801d00310030901a15005c46450b040c20290070310004644034032a80141d14866203a040185000301c4a400082c9802c504140c02240d824110b600010314a40700c1d40713108a58035a0282e40040702d11410f5400c55903454101300300f44044c00b40032110604181955100c0800303803841d81c1c40a4103e030185001c0c2d540344e455200b10600c6807401550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224604181 1250 224602931 224602943
    0x3120b0d030c0618120309110406150c0f0c0905090115060504120809040c0e011b02030d053603280605070c0b040b010e01050f0a1401110106080307050118 68
    0x20b00b00c4006045980b100114600103003054031a005680c1c0d514108944401d010305c0000d89502d01c1d00100081c0d5002600c90200449042c000340382005000b11110b981c240c0960100920704038004103121014007481c1c0c000b40c200b070600190b142c41d94000b00c06400c0035505040c59602e04540d41001c90040740007542542c8166441c285854030b0040d038040400804003044e10340301000c01030a8450340d03aa01c10b4170b200c904107031110b49800c400304002510030b800c1c1051030b4062010442c9104016540482c03007082c80551800c0664581f500090840000042049203008418010141c580303682024004003103451411001c441022407007005034185005202a5a80c02000d01074500340020a01d40020f6030001c414075004043d002c450b15080303206403065500b6514440c002c001400140078072038015000d07100940f05105494030400c00b00d0b030040140c0c810004c601d010860700c00b80340d03031080d13600700d05402e6980000e12000340c9513824140c0300e51040904880f80c2d0300c0c10805003a550f10ba4010003a9003a0096 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224605431 1250 224604181 224604197
    0x8060403090b0c010e0708060a1b0c03080a060e090a0c0f08120f09150d0b01030605060316090b0d05090c120304030b1003060908030f060405093703120b0d03 69
    0x8404069046031020100f84e548030040e496040b0810414200201b1030307203008003071905250031030500300d03680304032144446101084804550703508541400c0c5445d50526010840b0b64644070004014020380c0c00c400c0c81002c14a00380b1003202c900041041000d8050048841c5080d80c5e112001d0068400b40302d100c0d4160440c050300c010f0108050702800c02c43c903043c080989014401000201d003190001501800d92001040030522001e50b40704040b4195002c0c00c0401041d402c00700041c015000040c410345641c0c1d41942104091441060600300501c289071240380c60303d0046031351300c0250070b04555020030352040401c0b040311481c2401e190003604a544001d10304e01819500c0d0a11300e61002031091080340341c01000000001d01070710590201a0003803d01d01c0e10390801400a84030000c01a0000f44101d041c031051080c2d030301010404012058603032540c4440340d004242c0404a07540e00c000c42c100201e0000d6071600616400c108013107000b0100c00d0040111200e1002001000784882d880680050024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224606681 1250 224605431 224605439
    0x20304020112051b07020a091815060308040e1306061d13080f030907080307080c0f0109020f0607020d060203070201060510140a12091b140108040f0305160804080105040b010806040309 81
    0x44c3d005010305400501003d03541500c6d00c82d40400d450040c40074416807003856403000240a20030024842c0304036002c6041c40414550740b10a41540254064000c01d403008001181000390500140c085640e4064002d00ca84c969540e601002030412070382c40710f06c0c0045940015140080881f1505035150b1020b0700d64204003404680280c01c0d00014440d0100388690640810301910400150a855100310740c410b0340d440e80c2c0b141280c00d088548108400e0350381003a29242c010b036500964060102c0c800d45140341c85101500000f01c141d2110b0f840904000d02c00800d00c421070b40d06420100a6034000d441440840601501c210703072600741c0d030021114251080c89080141ca106054581c03002d80603000104040e856600c8a42441024107480b400c0845030a004202aa030300c0d0208616070502400c0402952034140c40d201c1c0c104a09620040401800103001170a2212108072219450b410104090700c80361242d01041c000d21040c2e8080c3c0d03050b003120f000068541c40000e2100e215562543c2c03004003152070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224607931 1250 224606681 224606731
    0x303120405210304061a030615031504080d06081203130c031e0605090304060504030b07200318061804050603031c021206010507260d05040602030402011205 69
    0x340040307885006400c9182070303000c0768110420101e007010310002e039641418548907040ba6540301ea0f00c80642208030300111170740c1d40071034400d6010801e030a6480b80c002c1c1d030314000303402e250025594002145d001d030700340820300050300c0203801d940e0b80310740303042015980710000d60740d441c82e4081c1d880c00b103a0001c00006000c081d42c03030300c125880c1c0c0c85440700c02e0401da2255189000450582c031071245086041c000b01050000368000d00e9044000d29018618080c00e18000030b02c0d40c452030001030300404600005c1592140320f4460390f400c2500c0860085144000d2181d115201d5002c03480d000c1140703001c1880c01ca4145013a000f02c1703070208111030100b54044009014070005c0c090060900f5414007080c00b014810000480685207034084034000143c6e030b0505424030074405540981002d0421406000450004d104900700b03280d61142c52000c4980d008220042d42070b648124080c0300180d604102c18003040001580282d4041c030b100740c0340d45e003040d144051034000700e8404a0f40b03201c80e14031a41c800455405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224609181 1250 224607931 224607967
    0x103020312090334050108090a1b050603090d030c1b020409031e050901140c060718031709030d0e06030c0a200c0a0605030405120c0c1003020d1107020303 68
    0xc40a01a51030684401804031032919207281341544c40d01c4c194031407406400d01043c488010b00002d007880041130034039002140e1381e0251050b0040643c0064421101c641a181c0241002010004c06442c0e40c0c0c038042d60007688a14001c5941d5007c6410a0b48a540d568050800d001318400541886980803a15408100240011480640a114028031042d6400134540700c1044030b0300301c80d1919907580380960001801c80d400c0c42000b038034544061201040d14003003c1007458014000b031030910030100b0f500e226806d5889107580010b001000100700d440742c45c40458054444210700700c090303800e098219041900c040500c2600030768010320400c00114001c0c0140082c00348900285041c100d14080c88042072040200e002d9401c280c0c0d07100d404a46244d10b8a0301d180c41c042c218518040e030460425aa801c2d50300d503c640144801d0400201749041d8030581040030b05600320001b0300c4c0745041d040501014000794003c2881d03480e0340381414040340741c11001400f01e5102550140066140800041c1105e000300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224610431 1250 224609181 224609197
    0xc050c3c031c0309060501030308010f06080c0a111207030305220507033203040f060212090f0f0d060c08010914040206130e0103150b0d02010e102c0310050103020312 73
    0x1694540c2844d020074440d01c110760180d44070f034480102d15414040b10301c1d81d5040c00d0744581c0402c072440003049200001481603a074200e01c0341c00d1851841d00c00483c0b075418610440b2804004d0342c000b00e0070900741075042d0021070107081c1020380c9440100d038824001c2040c0380700d100007406540c010003040002800c5061400c100030500141484d09101d203001820190700c640007202d00d25400800d080c0141601c90b82920014041c034001080707002d1002c03030144803900458040c01c0c40340f8081442644252104186400740c660010001e2000b0080c07450804000c01940200d240002d10107000440d00c02c8481c0b04200f41400e200e418061595a00c1d400c1001540c0140722030740304000c0031700340018905074112545019601c14402d03a21002a0380e9858006c0b64083c2040c14070030b020304000303140035076000b042c14002c4440948054101c0d10713400d03400362056072407484412000b00c500d0302800c1120b1028400741d8181e140490640d035444c40000060b200703481003804065456001001c42d00d5820040a000740082 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224611681 1250 224610431 224610437
    0x40912110309130204091a0114031009020a0f08150a03140a020616061113090c0e0a061d0603040803010509071107121a10060c050c3c031c 61
    0x400c02d80d4002c1190310038040342010b10303290042400d02001c0031070701500e50206810b1111a040c4240000028004890654010319000340000400c110362000d40b02000a4250244151750310500038000412107070b84080001c0009070000007044890340070020340d60003e00028103c038013050958842c0074081800c0041141d00380301c0d6200010051f11032801604104003090701042100c45903050042c02d81314840150200d17844108641e100c801c0c0c01b203080c2d0b02501c603851800038810380001c10a9030b581c0030745400c1c2c542c08070035203000080712503001e61742c00b68444521910b01441e400b840c00f0300c8601d000945008060060900041c0814206480040d520503c5460080e180700d10014850f400d10f404c5421200c14030442c170b1081014043e9000c1d010700249110b0003910700600d0098002900081c990185808100d01e0304811012310104015158001e0b2001300f0340c0ea410308802014594403803040c501c2044a00448006040400d49455400e020320005000342c654186100d034020300a8060071924018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224612931 1250 224611681 224611687
    0xc01030c0c050f0f070807051806012003041d06100e01090b0406080709050102030a021f0905010f06140909070506070c0b0d0e070503010c0219051905010f06050409121103 75
    0x7091003000f11040c000000001307041040d40d00510503080000c1a00711a40d02c1e8480c4804200d03d4841d41480c00c22a5844503070701200c1c0d180c0304c0041b03d000c03043d0411403800d8544030f100030401990100c01042150b507541d03c40c0240c00900000006e94041c02c0780c0b403d40c448401e40610440c1ca0141c820ba80e00d4100502d8808405501c03502c5000b04c1d9045074108000059124080000145c0c000d007158004d023200b400194101160108001e59450111100450010076081d104401c45065001080e0390381d8030000903c044001900840e0003440c0c40d200c1c90004020702081a00c0314108804014014108000909030550500092080c503038842c01003142d0884400e400052000b031440046c08266101500120b0b070704450842c81c81c0750130320503084107229074980a2480704c42900002d80401e8005040c0f8541c0030005641085418851020303039465980c1007030103807103007000b0741944030f071040d58013202d420000309854105000849a1111000301860300d9000c203014290b0150b40c0c00b2200e0600101140e20b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224614181 1250 224612931 224612933
    0x25171009050726101701090b06180412110708030c060604090f060911040c080f0705190e03010209042d060f0b090406091b020f06072102070f03050d0b120c01030c0c 72
    0x220000e08003405c000180d648000d04410841211901a00a481103903014883c0f46c0080d00c4550308200030384010320034580344c020508d030b4900400098220142600540d020079650b1040fa03610b070b0703200a0f501081405800001402b40c074040c81414400c03604000b0f03043d0000006e40c3c581c0001d200781c08003582c50071104010589103990b18011081d19400a544031401390400340c90141e050350001d0a240c040c00750034848508a0310490030340d03208008541c500464003070340c0030000c02e00921543d000250090308041e54111005803851501e0360141c3c0d81e50280715944020b500b203408540c1e02d8090190405941c06042010704d800c0406000da100c0028000078610741c1d680728a0049406141e1036400b10925041c1c082111a01401140c0a1808480140a0a01d4510070080144c00c410b25298160800c820003070051001540c141c98210f039011004c1d0700c40400d1410003030925004080c480044906041c224081410f104004601d0112007200426201e400c00e00158080c0c2641200c000811603000030102c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224615431 1250 224614181 224614199
    0x21e1f0603081309181110050906030a14010602070f0b09060c0d081509041a0c0c01020406020105040215070210030b12010609020a020708062517100905072610 70
    0x7143d94040d05480041c1140b40000700801c0e503800ea92500500c084480350340380414552120360b00c00b00000c44240300011444030b41602c030f034007a40000302c0c3c100c0710100400080645d43c1d4840003524070244050700c0300da0b07039444c0100d940b81150301480f0040e0300c98900c1081301d030b01403602808054000910140c1031059000c051840c180d4501d112100003050502845040141448203007802d44e000e417054641441d0640301d98140402c2c03402c0c070f070604240c5403000683e04100d10b003d81381a8001390f402503585540d1840028040c003002e48059200e0300e03588803008100440c100c1120041a8094500000780f07200803c00c1d0014409800c01e2604080001000344100c017080c0b09000141c100503a0040c0c6413002c1580c024500311990704200708680c00b16091102d40100d02441d00c888949103041504034507000d81048460544d00140c0c44112140401401140070111903050140d642e4070317804000f81d580302c1004540f00a407440f4a203103160310641a4802c4002e42482c86a03120211070802806140c1d208048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224616681 1250 224615431 224615437
    0x21806070c03060f0e0c1311071b0f03210201110f0d05010503030412061a041b080a021903090203070302150319140703090c0506040602010606021e1f060308 69
    0xc55026100700800d00c2004551300c10b640f441c2c60700080810415800d048074658039200d0550b0940300b00041c0005484468180d0084007070706612103442c5890b00344a1a02c1c288549171112104a5100c10000101304030700381810940440c0d4201100d42c03e01c620741c1166000995454030b0354000c40d502d5000720310f602d0441c900240300a2404103101903848082c00043c404450060700703c240b19810402c000c03c45d500d401114000215003140c00014440d90529903071140d81ca00d80e044541150511803500600641200416a8040d45131030b044d0040d66024400403c0f4801c8500d2220f0303411310310000c0c0144c2442603100743c10840c4090b04403444c283e00c90300015819090a01440a4580300104000d102100b0f0a03c0c2d41c151590000c0c1071101e482c00d4000d03680164001401003003016914003066060203079884040c0c00802014084d165190740b00c11000f80640b000d400350300301600c610300140f045000c80700c0200e682940341c4e601400854034115a0780c20131505034100992515210400400491210002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224617931 1250 224616681 224616683
    0x6010210110a02010e0c03060402190e010303120b031c12090b0901020304120e150309100603060f200313031701240203090a0b031018090501140705040902180607 71
    0x1090b4480811610007802d5848203d501c10041d00207040100041e2000210560003550446501210001c01603d0551104060b403190f142a248540000706140d000b02c03001315000b003607541c2804905018424560b0343c09490806000d0402e80b00f2800030180d10800136150211648100490354203425118a44807441c00d80d0110380596000043c001009001804040c00310124144500c060594038006020b252000300341c040c20b02c0d800000906200024403003101001d0036a4402c000d003a80b01c0c20b00308024042e0300c0003a81c0700ba190480c0306012810542c09894001e500c103480700e00c0d6540e200010348041e00b8442049082c403824000050074081c1c03c1440b40e028010350007045c06592107011000690b1350f682401101503420400c1070050603101c030241c44043c0c0b403041007250b07640d440e10042c190358079500d64801d110b11545203100a80004480d0407003010980181c0c0280b002114119a8180c11b000941c1c040c800714030b04210400c07595a60340c026000741c00982044410f44502800842c24070313408004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224619181 1250 224617931 224617961
    0x1081b04090b100f05040b091f020129060304060c09030507030f05060c0309190c18020909060907020d0e01021c0c0c2c0a150f08070e04080a0806010210 67
    0x1681c04030f070401000b041d01d09540c13031900b41d441345540840070b4036511550150760302d100400200d80100e62500100045602c0f0908a40320911050a9009000b0a945004403003107100446400c2468490140400007400e00180098607549aa07600c040003000c07080c103181c1c203018403108000080754042c09100000c44c000e40c10390308090350a00d05542020760040c220040d4400900605c035200c3c6000a281200754081c0d0541c4e00c1c40f501d682842c0d940c0c50300b41c4e8002e0341c495904904101d000303456034028003040802510041c20302e4035400f007000000a400c890f00c500507071203110741d80c1c005442004800441c881c10f00503a014007400701401c1c02030b5a510070340700f004207800003a01e100b0007400781e00503002040b8000c0340000d8610420600c10024444801000c072288018012403001e04460344180001441040040c00d01036581102c6a2044402d110ba01c18901079000006041c1e450414501d22032076001b00c441d40342c00300c0c0c0c00301940c0d9004050301c001c1c11441440410941034549200b5200c1102c0006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224620431 1250 224619181 224619191
    0x10819110c0105070f080f060a09020c0c0103060e0402030c211207120207050310020a090b03130309080c010e060703120507030510081911122b05090901030201081b0409 74
    0x2415096550242c807481c01c11900310381c03c5c8201175100407076980007580501035500b0791b11031600003180c0700130381c4d0403c00502e880000c048040e03500005290041c02c0080e01d00f488207a559040c0d0001141d01114080e4040d041002c42c001c0900c2c00c025515164618000401c080f241e10184052902a000309048500c1e50700140b20020301c811003010040b003490510040203914104030103c0d032a09000d40a0089951f0081144030813240224001c0b0060040d01000e0790310783c503250000413562803600d0800e0f0080b0782250303004036504001003034a090840d4103031684010303000c401c401c3c8034160784921800d0b401c0102d03490900342a81d02e98020b4a02522180e500418a42401c02d4070035004919075100642641c812540f4074000581d841041c2201d9401120301400c17051a00d022400921070302008100d0b9010740b0381c20412410001e201c0100d01e000c01910b0b900b4550208009469600c034100e070481e400018170004000561041c00c1059101d1004827150b208545100c6045a20790441c1d04a550000c4d260 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224621681 1250 224620431 224620447
    0xc2d06190509010908010e071a0408120702090f0106050927040b0115020109050a08090a031704030b0105010807120e0c06040305010608010c0f0c03080417030906060a09060501090501081911 83
    0x10f013010b0302526000d0020465600b40c6110107544240c40d01c6149051814004180100c07209203060354001c040100c00e8034841807020696031040e80c0400b804034071403c006000706140100780b07403030325041e03d110b13072100d0b8a054004020811119002540d100d0009411011172440c42d40f04211039009910661007100e0b107504040c81480865031140000007160b1509420074041440020751107034060b0051002561080d12101040000c00140c20181c49083d549038040814103550000300304890081b101000641d0304c40004450400b8162400000154100f104801545095000c80031000c905d108131134042048002041154226a2040e5401c0c3d540d03413810080f04c04d0a000c1c509103d00b9a281c809089030341558090002ca101900190400945034001381c2004490f0004440c04072021841907181c0c41e01c00c0e003441c2e0ba11f4044078828000d600744800003401c8240380c0180c00660320161500100725040c07000454600314001c20307440303a1850f10038000c0065402031184550030208000303125511300107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224622931 1250 224621681 224621687
    0x140a170f01060918110406050a030302030703020f21030901060512010c0801080105040b0f0403050918150a0825050d0506040302070f030b01061b0203011a030c2d0619050901 76
    0x1a83c1c00010030342d0422140c070a110f070001000b05072103507010010040440084012800a00240e00019000b2007402000300505400001800c0da0521070f608803036860b03426013405511606802d0b141540700486410031115015102c02442c1c1c01160040001840743e0307a84005400710a4502c800c001a954442d024001598080b07209401742040740c00900076810650364070164800024405c8607941200c07000302c0c0816120754111100030a0080c108800d00340c400c85c1000b62074100340c61519649078403880000050801a0600c002c0701c0450014001c0104140034002c0408030011281c1108081182c020415a03550310040d9001800740c0001c10340d500d858030700030f85818a0743d04081014281d005d010030014100c40703005410345240d491b0a42207034010051075111844040f10096155082c6410f6001041d0101074209405034110101c03503040d041c0809100f1203a54640c180d24905c6080000158406044800c20350b41036030280640e480e010103040d51000c00c911030303540000082c5000420001035a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224624181 1250 224622931 224622941
    0xc0503010c09050f0607030207360e060406051518090708030705030f07030302040504021c0b041103040b060111100b090a06120314040503120c0d09060207140a170f01 73
    0x140e40c02c00161031820400003421080500a1442c030581000900604252090001c880245007042c1100492074405212203000c02c0c03888110b2010900642e001c2407e581c080c00fa00d2075100805019000c1500c0d0390b1078420143c880104004409038090b00c0010142c0c8035040b25581500800c40c7d440860b040030000d4a0a140c116072100925034001d0040d8170100304044112030901003a800402d90300c1e00c1c0c9282c103070041d006940c45554050300c00b25244400c440000e003c8090145115010050708003d00204401c5503501d0904d4000020203000040c00502c100c0c00c21030f00140d05060410710940d21183c15031900c540f0000c504041920745402c1d004608100449903008020070314203014107070800030408080100c00d00082c00b08840442040c5072104080104c40c050040542960a11180000c0c92503081d440040c4c951107500c20251140c0c00707184103420b020280c60702503001c0c3c6001407800040b80880000c019196901000d0030790006464003004168800c2c441e00600034011079101285140c0c00c40e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224625431 1250 224624181 224624201
    0x15080f010506030715111911010e060406090b0711090405030a030c020706120b1908010204082416110a06060501080f07120f0e030c03130b13090e030d090c050301 71
    0x20b401a0420301a4554a0f081044040300d00d00d846c0700925000c0c46640d1800200c801556001d001610307442051000044541d000590f007a210742c070f07a140200050166030720a0384181f07000240c1a00007408400701c07210042003268040c2031030a034442205000603441ca1801d8070100c401d0341c00040c04800c003d4141c011442418198005406081e203054030160141d00c02c40b0081d014503545001200c02076444d0201c290300d210804d000c1c20040c54440070390600030342c81801040c00510804158030142c00707a40324001c4003002481c004442944030030210100302400d52008400b4020b911500c500340110401c00c800129020780e90102d020361401002400c1b5050140c607100c08014808200482ea0750800100002c0c0341220400140f56101924044010300c00003a0384001800001510160700c03000001070032015008900441c001030b5502e00a5455205490400140040200c0100205502235100b840389004100a480c54180304000000c2210310704502107889140e0094148068103091003590251 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224626681 1250 224625431 224625433
    0x220204121205070f0201030b0319140708061522050405160803130e07050705031c0b0616030806010c0209071d0126040201141321032115080f01050603 66
    0x10600c44d44480702c101c0c0c201c2c00042d060503182c2000f0300d855242000b0308040c0e03070188000c00e240310490307113080c1c13549010081195051340306600c004940c800b130111f4900d0242c0c03001d8132242603142000081c00301d010101305000180340340d0401c00c0b00009406005203482540b080300580301c52007000c0540c000d14406600a800309070320600011142c0d000e0b212206064800364013200d04160b5031142c1c110388511070800010450f010200e48414400703055a46001c034a03004110601c03461103103600b8801c0358014001098051004c440030b80c004a40140395981d00440c0601d01803402e0043d07a0040307445004240c1d09a400a41d01c0142c400283c8d120060500781803400740b81240c00c1d1100c08040007181c600748480c3e80c41e0070300c00c0030104045a000300448007100c50392600054a655180040d40340c05c80c007501c06c10b511214243c2d40190005041c0704801032040c2c0c5a19a202134102c0c17030342c0c50b1410703003540000394aa403681c50200017101c02c1c0080c040700007444031000400003401e512903001c0c25640043c1240f406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224627931 1250 224626681 224626687
    0x6200c01060905061c0c1206050603010614090103111c1110030519050a0f09030206010303020f03030f0f070c061811030a031403040c0918121409220204121205 70
    0x142c1e40c85072200311a41409086805c1034035003504040c441c400281d449204110140280603041040503040b031071140c0c034110002c200442da920507811004804440301544003840c01c0051001071080c4148441b0710748041c1800e01c2c3c4841000d21700c088074031044015a400c1034000a00c03440b51030308a224020000140c5018001da042214000914a045014904141c0e84802c00102d51035030304c2c0e000340d004441e01c031006e00c00c0d450241006902d0382000c0c00150700500913001d5001c01e449000080307a001d22500501c0205c681c1c0c0c0d410f017044c00301030007030149030030810039100350380115582e8000c01c2c0480100b440d9150580320075141071140c0c0c911507210a802138003d0b14105020039040400d0308101e02030380202540d039588a103080807001015412075402c8520340601100c000c0360029680c524188170b2500280c032800c0070714060317415851055400b801d41d5020800d44d40d11b4140440390002d0b81962401c5060355800126406041c1d8025400c80102c02030300815030414040f000302c0e464010340441c2000c5e45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224629181 1250 224627931 224627941
    0x22806050603073b040c3b0c0d0606020105060120030a0807110109150f0b03060103020f030703080f0a0e060f030a02030606040801021207091706010504050406200c01060905 76
    0x1d04613200e4511141e810070f64042400c04a030328401441205480c0d41184440f510300f82c5000101418075018180d0b41c0000c10f04010500360007956590114900d04100c0650045100d444008401c0b00424107500080d090140c1f094182050158401400c10347c0c001013024030700103000409940181240d0301040c0c000d4814803410300c4000c005c940c68142c032072401404c03030703a00c152040e01d14200c03101455045620786102c0030f09000c0010900b9104500000c0c086c448140855403a0040d902c41004140c0e154101c90b00410061400601c0e0804146c000780960f5030090342d94440c0500380d000350702101941070300050110f92850b0300506090780900100c2d0210304118601048640e20300000717041428545d40040424425602c2070292002010302600079541c680100003807a10030303403066410001099440c50f011070b00b80c120450b10351001800c0310080055a00e080c00b000013030880948107a40035952a0040c01096201001c410200302c041030f540ca6451482c024640d08444481d40101e101c0c51404041c80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224630431 1250 224629181 224629199
    0x510060e011803061a1c06050114060a0c111306031707150908040b0c031b06061309020a030f14060a1823060a0b031507020309090702280605060307 65
    0x29207420040019001c0305481c406000d00c00302950f6264001482201b4400c041c603c0da0700c0c0e1045a210300f03424002e507641c2d41040c034001e80c2603601a80e400f403004c0c010811030500c40c0c10031281480c0545030000e010f01c49240450307051401480c40a94080c0c940c1414420300054900d060724003c05403140302d02d0071246464141001041202885149455103604c509221111098501412555105641d904414008142ea9610a94111240323211b8080350070032003040422100e1103254080c0400d40d640b9081c0719594028080030004076800a040d00b8017102055401a9501082d482085108580c0312068841441c192004280a040d24108119138000520095031310032650b07408844d002030040d594403084032102c1e540c41038400601c2140308110441d8260780001841c408c0a6051b1035100d00d140f0400c055128080714602c1c0581e02c00c10510400d42440310f07240e80c0c00091b501c19140c00310214201041c03441c6165407e8000f200102900301d0600c000c5108203604508124000c1c2030310361500d0455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224631681 1250 224630431 224630477
    0x2306060306041e110901060302040806060f0f0d1703040c170c010c020609030120030601030b0d08030f0612010e100b0316060302032e060e011b06020d020d0510060e01 73
    0x201803c1100c8035803a010407141c40315030703540c007140103210350003941c1c440030000c0c0290482e1140242d984205c4010400509000480a15101c1c014080c108090514010701111140380142190340d0100c048983d00c000301c6280182d8041d91064541800d030500c1d183c4054510028803008054542214601007100da0308031500201460b410303107800d45c641540c00b00082c01400d20b0341000c1d150b5000d58070305441e50b001220041d1700c1010240c07810000e1407105000d002540c100780380014101441000807440480c080035000b41d01400c01043c1a54070064806914251155200078510310b40c851b01031041500c110303014a04c00c28000342c0081c07884008007095030150303d02d10b00c9190245540040440d00f00c0c40c1e1400c2410282c0e00061080302c982ca0800456a40d6000740d12504000030b9406c040c5000d5984144043c2c1d401c21901088080e0011407500c89000940c05140b025140316800c002c44042d02c01603000e41c0b840781c0524a82074142500c1d0030300103081c101740c108142b4100300020604552003e02c036905 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224632931 1250 224631681 224631713
    0x303211008070510050d02030a05040c1e0909020409080c0102030a05011a0a03090201050409092102030c0319020c1e03100203070c0605090111030f07090503030405010921230606030604 81
    0x2800490b008413009496038480d01c541040880c1c0000104607001d9620303000305003e10300c41e000003e501c035500c02071303403a14904130803100100008000c0104410754164000c100c0c00e030700042000501c0842a0366186156001c1041d01040d40d40100c10403c440c24180315140c01031182020b04601400d080c04c40c2a424402c4070422014559100b001c44190b9103d8020354010740b80041c01040b80c44040e040038181065080500002030340300c4a0310703083c0d5510220a5421014100d4011401c00486032600122108030b8038200c41148030b4060015040e9a03011507948440160011158400c065041450b0030549860840d820450042051043c4e0076400403800c1501a00301c01d00080ba0340301c0d00c040501501650104043c1d0b42000701c00d000b04050001e0b0b1040c020030307003500d803940c0341c560f00c80070f260301c1e07014501c10320307010131b200a200300510781001071480004c0612092014128000303680380303d481d2603040c404811821002d00ca0703842d401e004004241c0c0002c6d007100104a00d10f02079803414120050344031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224634181 1250 224632931 224632939
    0x4050105031f050307120204050a090203060c0d0207050d030204060f09050f27040515010e01080d080411030d052d0403110a0b0309150c07030c0308070e03032110080705 74
    0x3041011900b05000c015014043c02420340b5103940d5940103458450b16100000d920803480c010110b42940c01d20300c10500141e901401502c2c0f0791342c440ca10000160400550000d000e0380070401d40c0005030092048805d0800235490041c0c0f07650600d00c0040001644a4811040c808000d60034000c55a80030381c03003072070f0000495085500312010802a090848042c02000e0001100c00611040000114180c1140403960b0060320044c1e90718024451030b140701384180810b44d0002450083c1c5d49104448903a40b04d80201c050200303140c8100c01103890884c48010746000541c0204000901010b5a01a0248403d010510619510000000055038402e502c0014203c0c042c1d00c00c41000d60315003110100007852030380c29690300c82c0b0308a4015034488003840201c8046807000b4000488124410003036466854060341c44c4000c100c1d496500751203c580c003034200424003103c0708005104d59020402400c0110341340110b0b0070750340420840c44ca1a004060000800c9405002040c804030000180b00821038108031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224635431 1250 224634181 224634211
    0x504020a050708160209090a0b0a02210906040c0b04080705210a03080604110301060f08040203190f0b010602010c021009060b090405010209010e06190c050f010603050607030b060405010503 83
    0x100c8151510311650400a0483c0c0c00407603000c0c600c060110386850318500980b48030000341e0f2500c0006480e210224001402c075048070f4045000d01000794041c03c0340c9480c85100c60070f448000c8911100e24802140d001196601038010402005101e540d07500040c0040301c87c950505051100070b5456090700d001e81070003144400c80003890b07000c0b5501d0200c01c070307a01c2d030040e5601030529050003802c803a000c8858500450030a5407000b4540469000c403412201c0c640ea50707108081402608894000c009007040c0d925106810307103000c003485200a0101303060300c155580300b942107180c6450348100605900500969140403000940c254020884030350304801c0601c0022400350303610340a00200155000d003a0840c003490200002c01c04154000d10660000340c899507064040c0008116542c82240070001242a145401c80c2d02c0c2030141400c04a100c0c801c80c255986159101c0c1c0d8142114000e5109540b0ba6201100f803180e501d030103104414469409903019458a801c000c00607100d44009400180c4144ea82 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224636681 1250 224635431 224635447
    0xd08030402041112010311010f0c06050603010f05090a02011b0f02240d0e0c04050415090302010609020f04051206091209010c0c14030c041406010e03030d050103030801031104020a0801050402 84
    0x241d40800d00000e203039020262136410342c8440d844401002d00048820500030908141c00f507015086075032800e0260742c0c0d0580450550fa407180c01070308000d0205901592103400300800885180240c0d4403802c607450041070030b2480303400010200710402c030900e100d488542c81000e0118682d507840211a5030141c6250040d000c050702c0d200c000000c03c0c0e1400c400007001090803c582c500c1500603084100c2040221007182d40d8404c1000122203069400074411080f13289071991001050700844903590190000141d0a9a034400d1202030303911401a6840046000905101c03c2c500040400b480c240b001c00145207601c0d2041e40659204031a41113001c4041c004905900341d41e2003440319002d05944032908440040d5903205400a6065542043c1e100b07004000c450420b0341001e1160443e8200441041a81a1903500c01500c484001c001c0d01a0580010007545980a00074041e0a00a44c42695a006d440d89107007040d11350302c854807030328038070490040244501140d070003401c00341034031000c507801a550009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224637931 1250 224636681 224636689
    0x130e1504020a1e1e030e1b04091b050a080703080a1209050d0909060501020a1104180b040b010303020c0603040b040b1041090c030402010302070803010e090c06090d08030402 76
    0x60384083e0b0780d10b0207802e10b1204441d0300002290b0b0400b40d16110001505000c00705800b50744036001d00c8a0650b104001c12030b10a00c510b42440c04905016000040c0e011b07198481015814610603034411031004240d08004900300a40d4040017040d035000900f000707505559605d81c05129040c1c00c2c8081101c42880090324800e0786d4407804805134031074212182d034080518042c0a5800d40d21508201d00d1815000064a50001c00d40c074a10b03e900418811040390f0450802000700005520f120103081c0d26540c820001d00c001c03101901680c0500c40482040d8598a00245003406000e2214002d00090040c0400111400001764000354044450280da50300c00409100300d5445034041c3c80710410144a40200428100c022140494031a55041d42600d1582010500d0f10b50200159040750320800069a980010000765400c54070515016240540c9521800015002a0041d0640c20b19190501c6021541000300d108041803d541c0036080004460020301e01c48207265000e0411070700040003600f1540c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224639181 1250 224637931 224637947
    0x405010f06080c0f010e01020c040510170a1514060904020123091e060301061103040b0403060606020d030501080c0d0303180f030f0206010b030105040207230102130e1504020a 77
    0x100c11810840c540e9a480e196a540e469a0551800b94060031000c3c00c40303520510b07039030317404c2a07060b00180380c0c55410005000017800020003e1400e4030142a002c0f4aa00012240c25454503110000700b68030003060802601d4030307146600b041c003401d1410500c1d4480c0d00382c1c200640d81c4410304407031400141d51180010789508c0f200195400c2c0f45001d0420443c00ba102d010043e10031544284c400150058800001c80c07030048000f042e144e0b0000042c001040360340e00c19145515280c14503000e59050075950303801c10201c0c1d0083e402c200e40494440d14140501c0e0340c100000141010b9070302c0c1c18041945847d1010f1344850140b0740c003034064010340d01d0701001d06000741c10507071420360006d40c4541e0966082c10700241c01d016420b805c40014030310f00318041c0305074800540e69043e04c0340303512150b1841c1d2810003084000d50010f20115008a55000006507820407141c02d103c1d00c0d0200d100242e074403c00c20202880904182d080900600c1100c000e0002e040c1040c401d0605081d0182c40040c0d5400e5806800c0d50450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 224640287 1106 224639181 224639201
    0xd0905062403031e090a031505010905070c0c0312050f03040c0501080105010c120813050d0210051003030c020409020411040303020d030b01030c020d0806130c0302040302240d05040501 81
    0x41c0c0480028210b6045c014007072415607541c1ea4840d0103940b0034060201e4000c1d0380710010030441d0003d004169002c40703d480c01c034141442d04d03969808100700c6800094801c4000541d2003490b640038104585000f081ca00d80c040e104d28191030100201d0312240501741c0018101d400001e202d502070030043c54030700d0707100f000550350401d80c8008a0710050b006040070004640c019240003c05e1050080743c6084100f5806807a55440314640e0109480d006406211448508242000170030780c86641c888030958121004100a01c1e9400040c0203480d0840708000140000600001059000070708105a9061610144a064000c5006500716062603c0800158101c89401e5000d9489031404aa000d44014100c400c2c4c0500d0780400340466280b280c90001081c1e00140600039440d100c52880170941e200807040c0849481d201485800e40640d241143c1c80a456402103410000c0a4010107941 = true := by decide +kernel

theorem cover : BRFrame.Cov 224460431 224640287 := by
  have h0 := BRFrame.cov_init 224460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 224460431 ≤ n) (h2 : n < 224640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
