-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3962
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:58.820136+00:00
-- url     : https://prove2.me/submissions/30b09af9-9cdf-4a7f-88da-63a60b5627e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712410071 ≤ n < 712589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712411321 1250 712410071 712410079
    0x106020f060f06151c0f050106020d0c0b01121a0c190e030a0204020d021603090510090b09040e0712051e06240102010e0109080409141303031a1206090705 68
    0x2850010003113048a6281c2075090140301d00403a0800000c01c3c2c0706909400e6541c6103e041058103001005400504070a1083c1005030207090002c1112a1003814031880543c6c000a140f015a440d0002e0742c80b2185c1541c4081d982090100f4a10708160b500c2d04440f8090011030003215102c8012030f48107020100d018107a58184041100d2801e11031710040355000313029804940c0141c139400f0700c0048001074801c8d140680221003400200004150300403039200103540e410b44080f0300001082000f5252068540519440080280702d150b03514a000c0d001030721441442000d0311681561402100c03582d0003086001c488076080000b40b0503060714007031781c00000c540b0841c1c000c150905000040008602a8421549842d03100307003022480e590003504141010341548008000c501c8c04c90500030f04c04c2d0032500600b00300724242046c0c60441c940c01c1c080c142c000e02c4140101c12800e003e90f42c05900408420502c01c190800100c020300ba6942c440c0719042208510070060310803490816041d0303040c103405403c284e01c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712412571 1250 712411321 712411351
    0xa080a1b030f030903030906050f040b0c040f0902090a0b04030b090d080408031314070f14103f020a0305221407032a06030603150902040e060106020f06 67
    0x320b64440c44224180d00d60b030400040c500e006090031000380940440280006040000b800075000c04001281d21490243c14800c49a0303c032002e126203e0722840c0b103400c0e1215441441407200c00c072954010107400b40000c00c0f80e405035a0354441c3e001190020382c0181c803664007041c01c02c40d4940003803003400404d600a2402c1c0402d03180070740d04c400b81800090700c8003a00380030a014030b000300601c0d25000d11001807110200c502495450800b030340040c41ca4041c0d60f03150940505100d480382489900409202c11a40361032401c85805421100308026662803c24042032500812048001c3c2442505107103004103c0540d980c44a444080c0a42c0d201a011101030403000d082c6c00841b070148860449020703070000441c522984104242c603e002d02070b8101030607001036100e0750754116841c844009109040c2022041c1401d6644805808642c0c551001030021080541500e1160640391702c1075401500c01000014a040d07074400661506400340c00c0000580d010f0380f43d20f5261901041100d920801c44030424030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712413821 1250 712412571 712412573
    0x1107030f0f02210f01060f0f05100e060d0c031406060f0903030c0d09171f020d1e050a0609180f020d121e0302031006050306030f0a080a1b 61
    0x1400da54150310291a51a03424080c60441d80c44148110700d01c1941e4594101c0b031107148080c0d984840910015000941c40d207000010800e5260400204841a101c0c00c64541032506042c03080b40f01a00304518104280100410032a0b580e03280681520140d06d00001240481d49078080e080312843c18003c001ca9003c042044400d50381c0380101c80700b840d5290640c90715028413030b002c41d186000303088089420303006900903174619580c004041d8045070405035103003041c1000004995118002e84100c0e0301220000d0000c0c0320f07170407021780085c613a0399828280001d03500c0b411040707611501802c009044215885400b405074580150050a005d4400700ca01008100802c54401c03110711400f50009006000701c039008400c0d562041008203000740c01490030482c0c0a4500c3c0010410600082100c00c1c88110b00401e0110038424402e60f4850b101983c04500f00e03a080c02c1c01581e042e08000c14080c1d152040900c40c02c0c060342c0500000000b1481a035445460303080354000a801d001c011900344483c1d058603040c0c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712415071 1250 712413821 712413833
    0x3140402060c01090807060b0a0b03010602032706030405060a0e01180b070201110705010e120306010c020d111201021c23330103110313080c0a05060c040303110703 72
    0x5800550440d56a0b5844a182c00a140500500c0c2030240c0b0b049404184403003402655004104104021180a100d00ba200c1c0c00b2109180070a018490040e4814003040001c12040220094041c8002c0c04108500d054500000c40d150b0049070104d8460f000107082c80120001c5010717071444240098002d000c070108800c01403080c20b1f00d100c03018102d401c9000100704240d00030740c0044001c0400d000324554680e00c0b414000d000e4a00d01c0c2850216100c0c111828002c800c030b0600f900d010300350507550b0509002803a009c0119011503190242d40711003841c42d1600e407907038542030780000c400391001c005a2503000362610691200b05c80e044640b00d09003020007400c52030300180041013440700340300b20003403160f280c1700b02910040030445060f1441c0021030810720f0843c0d01607402e101d044c102c2680c040c800303c081081010700902007915034001398403010b11400c0020307402001410240021004440080e40c1030346500d4a4a0001d6a00d090120307c009810f2041c10340c8260760340015900721009100703c40c0340d55100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712416321 1250 712415071 712415111
    0x5070201030f02042103020c0618040e1c0210050c04030309170a0210080f0723071a0f0105030f01020c3d020d0b18060402030c0714160603 61
    0x381015035038402964080c0555064070b028044c2c0c804048040302078164468100c605000081d0054454150715003010719003801102c1100a00c82c0318811000c004806020140503002c05240403402038202012900780200d8807518600c0b0290f0041c0750300c031003c4068404580004d0134924502c8070030841800402d8100b501c5038111070705544480b04032007842d10000d05095030b804009600090800d00c041d8520b9004c1140ca000e00554071403c25203071a40d40081d01d80c4480c0120060b0107655140600144840040c00f0f000b01d2802801c440035048020340351001c0c2450f04503620014a4000c4006004504080103200d510703101c0b072002103107000620b2440036960448480a004626801002441400c60041c0075002c403c1400042141015000c1e00c03107000ba411181003000c503e031801cae4814015251031041e001801e070302a074581d0042c0d00c4640c244006540010b0070000003440820100d00054803581caa680e00004800c047c1ca0001080d1340c10300c02c0782560740e11090801d4204841186141c1856050b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712417571 1250 712416321 712416323
    0x2120402011121030f090a0c06140706060e07020712111e03030309060105100e0f09100302030715201905070b0c0a26030f04060b0a03030e041401060507 67
    0x201080c03907140d0203100b51410450000f6008480e00c0341e081204403241c07000140d805440c100d0025101c6541e440390450703070b4401c00070000d41580d5401104000c6680076542401e0101c01103d00280381c00340036152041076858541c410b00311000340d403007001070721541400792401810002003480b000d0031301c50701e80303603d03820384650818802c5500700c0204a034030b1141e000703000458002800f40c0340c4900d400090251945000d2040500075881e02c45600c248074402c00c0b1803002580004c0c952800c90071010144010028010b1103003050b040f40324004000740e6010010140100400248044050b8071944010401c503801c1740d00c04110b142100c0c900c0b80f80500407031591842002019491400603050815a00d070500030b5001006404000030707401ea84480116111800602030514241031700c031541030040c05a10082840002c0b1001400400c000c0d0320140c010350f400c0341c010315000c181c1303841810006111350ba0982c8110301060401000b48600d0800c2c0c020807800b07005000c020362076589001809000e512900740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712418821 1250 712417571 712417577
    0xc0201020f04170127030e12031b01180f05070605090904060203040501091b08160803040b030a0f1b030f0506010819062105070b0406050d0f090f030509040605040212040201 76
    0x40c3c1201100401d60008000c0000011400c1c011084510400b540c20000d00068000036807426001c410f909091004031a512203a1004502c1e180c586681704e441210326020b501901e540701d010980d400d80000e25888050307801042222a002c150389030152802c0c041e0f07400001030042c18000c7d80450795852021543c45500301c0320250362951a803500340d0060400304802002204a48851030442c289920284103540082086400900340ca624440000d64a4802c840b03c581c010402030000b80071907000746800c8804800c004c80c56003080c07403803002981e940709290245001444d035071005107641030254450038001c814003001070307040c600002410440000c1c10048183e0b084c2074001c600310380c580e100c14020500941c0000b090515500e2050444821480c20340f0b051141c400b02150781c01c8c1000c1160129402c1e42c903501c1c40d0046042c495001b5020100c0d4040302d6607078681522002c81d0501140c4c00035607201c0e50346d581d901da401004000480780705130000e6005070701c1031000075a80a800c11010740c006809003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712420071 1250 712418821 712418849
    0x20d03050606090d1401140c090409030512071d010f02060105100c1b0305060606210703061d041e05060606070f0c060e010e0d1e1110120c0201020f04 66
    0x140812820f200d000101c40c0c106480b203949800f4800005e1084501c0503064009001020003094805008202558500300e24401044010703d1403034541d20106525120b400c0440c10701802172011280104215100c0011441509617004007814000850b13090074801d08000d0010300880d04000d64410050117000c2c003c00d0301c460a00f040703d008840084c841a48003201d0500328003a05512807124843c0e200c1101c0502c2000007140302450070348207943d03155001882922904e0b003401001340487c840580920b0034140d54070b0001c82d08030b01969000c0364000390141280c000d40dc152030600300c0740440841c248074103620f04401000007100850440d41040e821a100d6445030a43d0402000c0c840451038024500803d84000081e2075812100321211a502621050701483c043e40620180100340400140200740c0c01083c0700c1400b14071288800c200707000d54031002e408400b41010500d01e1100441b68000b00c5c00c922403151070200c046c010505032842c184000c0d4144481601d900040b07005a0040210105502c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712421321 1250 712420071 712420081
    0xd170301080706050a0f0315170c040f020f030a0f020f042601020f040501052a1501140a030204050703330801061406071a0106030b0f040c0f0302090102010e1c08090a0201020d0305 79
    0x8c503103050203000c61810601115074210a0300e80c0d42c40c031405456010702d040800c0540c801d1a28820741e44074543c410607861440c3c2d2016007910080450003603624040d9801d20040c0d03c0d038120000a0409062440d101e80302003000d50304070b10707400011403000020302e03801001a808000b140c1000e80b07086074002c0c200143c030740401101120003502c0c003090242c900d50a540c401d03002d200e000034079452304280c2e00e002c6451590700d940c0c3c0101d83e41813160503540c100d680d0707490404c0142403da00c400c2d406800d501d0300040c4804248441e141c012030744100080c1d0a41c404254010507800004007200409860008018140c9040394030114000c180140c00e12452010600c0c1e0280901a48515800186030030b00311400e40c1c4422010b002059071403400e5000e845450a000d07120300705881640340d0381c0801c1d1102e582040da0001b0480103540003101003411550cc0d581000300001c402c1101201365030b00282000781c01880b1600c01000c03480014903d0045600031000d82000d03036000b01e506110200940f80c042521343d15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712422571 1250 712421321 712421351
    0x5090c01020c240a030213120b010303050f07060f051e010e0103020603091c030204090605040b0a21050a08191d0d11030a03030c09090605150304020d170301080706050a0f03 76
    0x4850084001d1800948445131590550080100112040030569080c0d12880c2c000d030b81c044143e82c002c04070101d0700f0051021030300410190407030000100d1494070741070750342e80c40d6815503260f1641b402c09552904140b218074204428001d030003828030440c4000b25803402054004000c4180300103809682d000011841e042400e00c084408c03610203503002202407112300f000030020b40c840d03c00c0080b06441d00b18085880c0c0b50500a440030071000820502d000b9040805042411000d01c12400c5003030200c603041d5000130000e101c5900c13014011403e03181c9590000050402010041241c0d208101e107520700381000040c480d1040d9200c0c0000e60b055074800c0c206291000402c0943c00320164944510045001015419003003130314850400d5445114441c2e44003014016140c1c00c2c0280780d03120444400507c0e40c484100050f66025000400ca2203407004240c461200b44c0c0035882c05503014840000c018080c440c0c003080f0802c01880107251032072604044403401040c1046468036441055250011702d00c01040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712423821 1250 712422571 712422619
    0x1a16050a0c03030c0c2705100f03031709120403060e16150915020d0c020609060f210f07080a060803220b030403020c1207031b0303020105090c01020c 66
    0x703402004601c100c0d490307003000f52010860540132206070b44106800b003200080c0304051743d441d4152103010070013011184085406420003e00340000320003141e00004001074038600340e00046000752250544d840c0c450b0303000015440b004048600940c04100b441d14040f103044125011645c1250b0001403c816990169050100500c50017820240c0041e000c22419404042c3e24a01034150712038124455881101c00c044400301030400300580c0040320110402c07402001d150754124030040160f45000c152400040583d041420f02c40d9103200c1c08101c0d50700500c01042140d0000e511054044086e01d0035409003620810020704140c00c112500012a410041c40d0304000c01500365030303040c3d9456019000c00c0403d40c15a0a0340c60900d592341c8503000460010f1401105d0086070140d000c0e00a402d510414030900c0300780a1450445072251a2000010603015402d03d03091008074611000c1d901e00d5030030003d0947d4009001c820301c1c0d0b086883c2a1745943c0c2c00007168036060406440015800c1c2c8100302080004d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712425071 1250 712423821 712423823
    0x130b0711060711040c02060411130609050c0403050d030908090f0d05060c0307031a03120a17130c0506210613050405010c08070203190e060702060d090501061a16050a 73
    0x101c01040550030400010b800000c0004107440800c0aa50411000ca98a800948014160304114020310205080840c0b82624401300000f01255450741d600c40241251002c5961540300f65001c02e080c003c03c402440030300c4500709070746001d011010150701c0f44d4925124810382640706d19030000d070211840d1101c1d51f4a000d803076084000d0b02c10528000100114640c400c89540001924040303150440034001001c8006440c130203402008841c09604040c0c10552080c0a09014040d8807010030440a80c1d04401da84168120710803204180d60501d0504113401c0b00b9003140703100304002e204603444c1c445041103070030201d4007182c003c0c1005d03201c0d0703c04510000748101c11a51000e0030f00c0104001e020054201c1d209804203992250345a683e455822030f00c0e40104150a0a2500034441c61343e03080b840340044602200e4010700342c40c03034441c040d030020b03c040d440f44401d4800103495403a69409c0c040c082c42103000514000c1210302030401d0020034201030f442103240881001007050704400c180841008000720f80c2d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712426321 1250 712425071 712425079
    0x120a1d01090312110a0215040c21120302040e1f0f0609030c05010801060c12020118240b010f03050c07020a0f080607020d0f0e01021c170c130b0711 65
    0x54040c02c0090807022004903181d1080d05005403041001c81c1c0c141210604c0c112079000e00410703141c2041c1105810710241c411340785100044000b041c0909c0b04200030205804101480e60348840620700204900d074000503d00a051043c04100910641107081070780c03000c01002c0350744d0310441c15400000c8030810780d0855081450001c001040301a0000000420b50307005002c000011944c660045481304c50900643c0001040440c030f41000514021040c80d01d07100c00d00001c50340700024500b040c1107415002051310320205001e004894542200c1200581e510790000900003411502c00280203103292a054104055850f400104030000c500255484254010203c05520750744020716a940a2180200740c01c502407840450300d0207000040000f000303c1540c80c0c2d0b10070000d007100142c403000d01039680300f819800b074401615000710403a4804c0d0103111103612054032a42e804ca0600018840c00bd0100e044000c080003241c141c00d03000c01c0c814084502c44025155540c2e801e161008983c0031140c285600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712427571 1250 712426321 712426331
    0x20f030417010e0105100612020f0d0b1311030c18130c080c04030c0b0702013c0918050c1308010b01083303010e0f0109050d05120a1d01 60
    0x5510100314075404010907000c024425404030044103401c0300e409030f50190b0200d41c0003a00300300b01c500400d80904c259501850060810390030420b5040f00c0ea01c121200301050796a0601c00b0054036000d2130741c109800304458100100607501548445621001c0e0180c901807402180040c00701c5c1d42200110702a00005d000295100f11888004005d060071400305000701d0180710004070f4207900d000503101117940104a2032446441c00510509035446107c0503410421030300b0041200f8458003001c20783d400d007100c3c11151001c00609982c1546448018588108103584900300540075285441d0161084240c3c0b0006d041c1d2a640364103045031252044010000f0700c0d22000150002c0107600042c820329081c2c803a6003c999034201c0c0f18416004071180090540c440501c05802106001e51074180844007500010300043d080b0385c9145410421400705656a4507200f5440c00c01400b8400c0e0503598800f41082d030b0400d070001c0041464000000d006001d042e50300e03a080034806e508031100c220750340d01c0d203002000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712428821 1250 712427571 712427579
    0x19180305120306010801060f091203090b0711030c040e030912010605030d0c050606060a05160521190309151104171b120a0609140313060806091e07020f0304 69
    0x350300d41045034000e000c18043c178000694540a0180420145101d07034460703200c50304004202504101100c410760811102c510045100746d0600c0080c01c19070b02a9070303900400c1620380c082516200d510001d0720b01980c01c0a42d003d054140000c140c46000a0468001d29208448008640180701b03a41c0440e515100b126200d46160b82c00003640c42c0054001c1003075541c641c2ea0b540510906224404883d00002c0c01080941c0020b40071404c04c5a52038468010b5079034102e04555980d15a02c0b0300c8981140213240090400309211100c40340c1110280b04d4203051040a9064649404822b01003450100d42c6444031940e40c0d035114460104c4014290301c6c607091207a00103800c8030326a51100c00c000600e4450103401095818a006c2c180503100d0000c080040c0300340c9400c0d50701d2101505581030100e882d034100d2030880c410003005202070f12840000c011905d8055190400013840c0c80c00c0a0700103401428075205200200c01c03401d501a82d200d0030a1405455900d071454200e1900c401d80c030107540300d408046030104d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712430071 1250 712428821 712428853
    0x16060e0915060a0807180605070308090f0706050c010b041505120319171005130b03010906020403060b1c02061e0903060f1e0f01120201020f03040807060305010b19180305 75
    0x980200100d58980403181030a10100d804601b40c0d004a01c04035506101703010009100c0d904d455880000e40090325080b91580e1115031a2101035040000491000f0400210000003480b460007100703400c0307505110740b0300e5070107616013021118004d81d1300500e55400002020030042003291281c07045483c8205080d40c0b11100206100c00201c50190700444090120b00c03003208031607000042c3caa00402c0c41c03088209401e00e0720000d202c24081c8581554842d640803020803e0351000d040114014180130130203d01150421100199110b440f20405034840070311000341e280e80c01078924805c03103000e000805a84100994049010b402c0039142d16100b0700003000700d030801c514802800f61f82e07007900070500850b00ca45840040c5000302c8040400340b0b0401d0040200b60780520a0600003801030041e50713150403d00c07521906542c410303008009540d200c10400c102159061049900402084540d94280b00c01d1030700c40100c041c0030503100ca040101d0500202e10006001107403000540d8007504550349001c080f4494 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712431321 1250 712430071 712430087
    0xe07090512011b030b04090206030a0905070506041a072a030c0918110105070c0f14010c030e090705090a030b011e03050a1502070b0a090516060e0915060a 68
    0x5180180a800ca455840c00da050280709250f114180008155145200048006100b44507480c0d82c0581c0f40c4030b0030f00150f194070b07009502490710725101080160307441c14000e20702041e40c0c1c03140340581c03020001006030008041c034500c050f40031703070001b25522a114202008003181383c0505922251035503400071003806d042030b50034046921960103ca20242d4072111841190140d0311301a80b02000481c408001491a251114030070704141003150030700600e40c0301e00101c113246821080c002c40b448101417001c400810341c403e4400101746020071a4881641d070041c4008140e840c0c0c02d001e491150040341d011800b074020b85410740701c05004081890359904281544600a20070000303030031041e590f0210303042c400e41c11000c03c1d690008010312030108640ea4844810b0503c41340e08a000364203000110008824444207400707150000e60201e800000c40c18024105001e541207509143ca03515810012242c00003192034800c0d0080324111a00d030346011042c3c2100d0003040381190311520000301000169040743e05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712432571 1250 712431321 712431329
    0x20405150a03150f140d051c02010b090103020d1b03080d0b1e030c0603250903050f07060e0d1103010e0d080a05040c03020628051b06101403070e0709 66
    0x2407090344007030003c188494455009400e40340c010700c88144001003030f80d07500d012800d40203400740740b001e0000d440741401e18811182d403104c8001c1501c1c010b00300541c2401988907105046503440e040c0d51450740040d51f0b000c11442d000341500700c800349424031400700f03100040c015a084210b2964036060380d059000100b41c0000d165100307005091160709c4c100454144805100d402600504651500c0b000300426500000c10200210b1000700c83d0104d080300158000c02d00d030070103840b124490ba0841c5022824440d030031400c2c000b42d82c06580c00f0032105501000c0410f2940003501e84a0300c4809508140320440f510101c4142c0542c01e02124604003400080c2e182d56410455450080d981c880c80840001c0d00c4096034080c0140350350300414005464924010b141201c41003900440861079100402a0001d4880301b19003c43c1d00861203640c600b44449a407819a4103480240a07246060401890351036414002c0c0e140713111100d402d841d5603031010410b1401400c0b49981e50700543ca0712843c02000d00455001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712433821 1250 712432571 712432577
    0x1081e010e10080129060f0708030106030501060302070f0605100504140a0b0d1511040314011d010c0c172101050310111c06090e060f070c03080a0c0201020405150a 72
    0x2d00144291040c45011404000c4011130803156880c01603e80d41c90b8001c840c483c0c0d00c05410400d584c0d0a150f008000d0070b00030f11543c0c0d00e079140e6140c03000180454505a00c0b0805040c01040030000048241b2100da215a900010001d916140c65280c0c140c1101141c112a42103440c145c40350360302000c0b1884043c418200d0030000c3c0b01400701c1409110084e105901c0c0101a180751601c091802c00721900518110b22030340e4081030500c0d41d00d4a42c005000003084e16014141d64032503201d128011069107141003510f10000a00120050b244002c0100d01100c0010300034403603403c00c2c6910203200c14202d411021035000c11000d803002c64020b400c10070301c0030b02c01c403486441103042c4803d1000d003600400c441151080c003101d09008a00304090128045031050064075643c484001c61491318030302c503561854034180c009241c18070b400b0765064a003100103010f182c240841c02c40c9401c0086e60200e11642e22120844010800800c00f034010f07070281c0190340201d80d110304820a0800310405100203010350024540d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712435071 1250 712433821 712433851
    0xc050403061d15090c0d03170c030c0a0503090a06050907290d050402010207080601060207030b0f1b0f1201172104050409240b150901020c01081e010e 66
    0x542105030314450106005035a0001810810b103100400007051340102c03140c0c1034503882c0c02e0110000f405030034290382c214049400ca8822005d2500d06066aa074080360303a01201e45582440b4070040000c0c001d5000d504104400000021440c20090100300c10300c9512002c00d100701c0c104100e0040c1c80307460600600d00060410010039202e00c403030805810145061802441c82e144103020340c003016240081c41a41075205189c40012040c2d401c0118038003c00c690f60240050905619011451100260401d1850304003002030260310351210465101c24401c9150302907031407a910701004024014402c0807458030425100000d880007801a010220800e03a10540e10701c5e03003503c01c20491101d09040c0d44071062105000c1804030f4105640a201c840e801407004107880f200360101c40030524216061240f10075150744466229081c40d000c41da02d4100120a0507082c00203070f000007540e9111000c440e5042113181000305032070407401c40041400580c102585402c0e51b844004050035084181d0700c1c1031040d1401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712436321 1250 712435071 712435091
    0x504031406041a0c040608091c0305011701020f030c09120a050a030f022a061b0319140307030908091c0b0117060402060304080906040f09050708060f12100c05040306 73
    0xf11006520610020985a08003800c2a004503041180104400ba25100d1070650b44900c110b90b0f00400310406107541c0c003140e190b060101840203000808032004941c2c0c014440c070b4061a0100003506ea009901c12025606e0310401c0703002640b5540318102c0c02096016810010003400340100c0c11080c1c03207001e43c0340c441d004041c4220403070360340340032080280558102034400d04400500ba008000489001003196051808207950034044605181000320f5a501c0041c0c00345800501c5070358940e880c2160304200180301402e8840802e2803100802c030104041d81c3d800d565040080c004140c0c0e98107180900700c4540740e1200720503c01081d502030025140710415000000e14105149145050041c0340005040709031501d500b40f14071604040c10858281c4130130320805030580c44e100c01420042009506d610300152909201008030790b0060092410801d2400411841361102c41001c500c03000f0517604540c0c1810441e001a0134200343c400c0c00101c0c90b00344801c10755015400400340c0156401500d0070007882c070032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712437571 1250 712436321 712436363
    0x708011a040306090b010503190507090b06091e011805130b030309190513020703090603020f071509020a05062a0f01050c0304060c140304150b060a090302120d08072a12020c0109050f040c050403140604 88
    0x40b071040b075a2007401192050304110655e000035125180140880b0b080007440c01c00504c01c2884d41c032000c412034005450400452501b400003c02542850901b146018200d4500031703d440054040d40091680015008842d03d4040040300d020f5a0030000f018650b203810000c1c80041e02e03844d1010307445000d408401089620300401110b0000d03a500e81281640c02480401c0070351403000304c400c14018011751003100741210081c0200c3c0e04c1140007418903951b92811b850000102c3d01e10203c03901c100a50803100d06181c2c1001030480b50003580201c01500c015010344969005004040c4101c1d40082011139107885507030700f005e03000b810f5038030840e40d0308100c2915a00044d529034520130380b1000100c1403804640c607180145e407181c8450090811064015880300240d40040140140842d840f410308071400c804181c1c180054640350340246040c2c1c0f4220701d018009400303c10403c0030700d80710383d9450f0b000c1c61880d03009800302d6000303540c8665407403a4001c1215420780c0f104001c80303060300c886170055140145440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712438821 1250 712437571 712437617
    0x1203160c180c0e0f04090501050a2c19061e050703060b0306060301050603060d06020304030c0317060a0e0a271a0708011a040306090b010503190507090b06091e01 71
    0x3841d07901c1e4983d508001c01000301e8040c031031210a03007186c0d54954000c045a020b0103007620070002d10002103207000124161596070602800005031140c003568160180c0c600105248407005660aa404c1880f191410024000d040e9407208040c00310a20101ca4020b400c645c01c1188200c450f80c908014059036840790001a105c103c0307640d0340c40038003080144510f180100296400070307006091003002c03042c5aa6400200d0b8015101a4003044490b111907080513440b61000c846030800e070000c88410b007031500c0814585c116501489140701111320000d0101c400541c409030300a0b2903620005c1c0c900c440701c1060000d20030b41110a40b10b035a004854414510300b050261030103a4030700c0c1d807940032503803a1403110084008402c0ba001e01c8a0410000040404c01b18025421158010450f180d125450301007018500400f610404032441c92100220001c990041a550104d420b5410049038441c49000015a03a20809840c2c640c41400716120911405d1100c0c4d00d0320f00e01c00f080c4c0f5040740c0c0203409040c1d102c0e181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712440071 1250 712438821 712438841
    0x3150b12101b170a1503020604060315050d050a030311161110090f031203061203030b040e06090a020616050d081503010b061b010b04230609090c1203160c18 69
    0x220f84101280310a41c4540c04032404500c40100c01c60a542c0701e41c00070342d8540c4250f100b500000d0b1144403000007240d000c0d0400000713040c100e456002c012541d40d22907440340782e01d50002c0c0902d5691003500102d1101c0d070044410010070035010003041203041c0303803408021006c4440a4003a04030000c0c41810103014154600c1600c2c291810042c1c041c0c0303165680b1100b0004440403000301505c0c0c900c0011003900410b040110380d8881d0b1004104109100f007407000b12000c503010000a54040f80a200c000704004c141a076140c1c0e015180c80d44d499603017181a404a010b2848000c09a102d040c0e044504154000c6a90380210580c0034a00c10111804042500741c45d10a44c0030b0b580f01004011000040c1102400c00030310903508000480c083c3d00840020b412520364040000c00c0d01045c0c1da1828580ba2140c1001e503120a048504a5460030200109541d56210703000740c40c081c0009c50102e20350b800c400c00079a081c0b0400301c84162148101031400c0e1804030010b100ba043c103003003c035118174000c1ca101d0150b05225 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712441321 1250 712440071 712440107
    0x5100209011704082205010215070917120d020309073011041e0f0504111002030408060907260d050f130b091903150b12101b 55
    0x46000000c44101c9180301400440c0d00e8030b0b0400030b41d485c00c000c0c002481111a64094010b1031149408006810301500b251080ca210519034200301c085500403600340295841074403d01101039120004600d48402e2403038003081664049050551583c950300114400c92109040d500c0c2e05a40d0a5540014a003136010711065158509000701c880d001c00c1d5a401c51340740900c0b0311852401c0c01d000070404450203400d24142169100c2c03c044540c040b1802010f030110b9505504002528003512a020810a880e490501c1140b5005110304254070810603180a001d480c3c0c29204242000c03400180e030b5003868890f803c5803c1e407441544008240c0702c03090302c5801080d14054141c082c0d81140c1101e199004c1c954041d0755140034071102002e500100c0410700500305100070981d40b61880310070021507c1600700c2c600341188000c2801d00003c1d210160641d1000442d2001145540e484030005a03282d88011009070180b141103041280d01c003003070b04101404042d00304002c1781c40420b00c0341240d01d01c4184c0103000032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712442571 1250 712441321 712441337
    0x1a12040303092a032001080c18130204030501110a050319110f0c0c04090503070b04020a170307021003020a051b16030b1828030306050604060c0510020901 68
    0x4a4082d4221910b02c81c814541c1030301180c000840c00082e01d0321641509035018820000f88200144442100680000104542100c201d07a0000801c003010003010300d200000041110321804000c1111406002001002c0704101c0580d404180020f4000740701c1560150b0a01e4400040d410f03a010803207501480650703819144d41e541000e14403800100315600c8403140d5540d0b422194220940015010200c240890103603200e054112162402c020f01c03501511070742c41c1c2032030000040d80c004211148030b60b000c140d4a400e0b91b00d0740005606841c04e980070f00681d03400c040b08079003034250100c02099070901c226148648041c01c09400c4080703000d0082c000001c618108201a28840200c00c0340003040c4a40084640c49180e900c200402043d00f60b10454402c1020401c1c803140890750005400c82101c04401400b940310700004045884600c0c04540320a02000c0c3d06440034148250080307400b0b0701d80a0089551035036981d2000f40805860401036405008100391402608983d001311034541105030743d5106 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712443821 1250 712442571 712442573
    0x1e11010e0625060f0902010e03120703080705130b04053a0203010207140105070906020606030d050a020c1509010201060b0f0301031e0f050c0a0506210703020d02131a1204 75
    0x4070700c180c61511414a4041241c0b01c40011030f1402a811300a20050740841d9280e55480090282039075145000e01c01e400401030044c501c890311099941d85a0145401c2466480d0440240e0b458480c10310440784400c020303040812595400c034000c10813a101504c180740c0100003141c0713800b4030403082e02d00b2406213000340300b075400d05c203844138070582240d0b00081c0014a0040c265803941d09442c2d02400924a6075140c50170448850f420801800040c44540050b01c0145440700c0001d449035111741010f001d2000c00300b2000c4085100b08200c41c2468805800c890b00b40649411559190700410b51036030040d030800c00042242e2220a064410748480680581d0460b42156140c0f08100e0f1040544c950605a112481012504c1544245000b034040c43c0a4510424040280b1842041d240c00a034066a01046004c40001c8081003501581342520700d032408588864000324040c3c0701d4460f0500e203160001c206401e5041960010500300c0d10000d01941004d6448010296180540d0040800c0c400100300094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712445071 1250 712443821 712443847
    0x1290a0201180606030c0501020d02031227010504060612020f04050a140123061c1a0d1b0603200703050d05010902072a060c0804031e11010e06 63
    0x892280900020402c0605694480b0101140d0741c1c0581d0700986507a003c200303010200c1d900801600c000e1014128854001402a56078416041c1d0250b21100040004040c514031403201c2507482d00d80c81d10550782e9810840e0712400f800041d02c0c241d500600d031100009400c00d100f80c1c861a6583d018181d800c1543e44141000300803c00181000c0c1d849440728868480d40950b142154060000d014420000e45840519001014804913a070360094004000ca001109015120300101b001d0405010541c40640046009120318410010750000ba0013080501003003d1018020981c4000345203201060340c0d0390700d0850580f184c0075928240000c0c819a0310f03c41c007007241c005000c010301908007549841001a1031f102220700c02d0b401030b02c0d02e660100d0f0b142c1c01c100c03164802445150a40000c3da0510101c00d110030184100d5229032010721258101e018104401f90007074800864000040801d222140b6a000460011118045540c0402100480741c00e40c0586500c4054041c050040303810086486105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712446321 1250 712445071 712445077
    0x9150409060e06010f0306061d040f03030608011109091302100f020f030417151005101101021b0d02070806010603020307050c07030c0906050f180c070b10030b0129 72
    0x360741031500d80b00c91840c0e590040100d60300900c02c80c6403861005d807840c01c05000710791540e040f114599103440f0b800c401404418910a400a411030002c41c240b41031480c0076001001180d0103415a13500748103188040c4000403000d08100e50b0184c0d42c00c03030140d81d09600414124070a003402035010403c81d8240c241188588902240865a40116043c00301b11a2440d440c540060b403068520a40c51603000c40440014004000560324610a4a40700d08003018031701454070b4180109c9000e04040326041206911541c9545182c1119034021951148000301c1512046d80b0140b59103070a100d0b201400300e83e688000b82c0030003280e03074040c040d0080b030742041421406980044c2c410342c00c00034144020b1000b44020300c2007a00031440b583d9440d015134502001070099480d6a40161301c102640c1101581c50b03240c1011100f1445034044e854401903413444c066800da8042d2900103444040c0740780070040b40300e1201c0980740543e40190460f69081e07998440501028401801c650041c00c824141c07540918803040107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712447571 1250 712446321 712446323
    0x1706060612100b0c010204090b03010b030c041107080f0c15090d1b0b0f010e100b040b0304020607050a1115161b090c2a1a04020f090a0c0e09150409 65
    0x1850302c1c5030703101105103050b0482507111041e6507002a04004503c01485030040b618019402032282461070000203840e0040b60420310f0245032580c41844442800e0341c01c4490302c80c0d103c0e00044e20b48620004204164020b855070080c01c1c499441d01410f5400c0480d0b01c1c6110302c51307040003848001c0c0c400380101c0b040e40300342514801c000810aa010000340e87d240c07038988901c215140c004403e614046008030001405400e100403c644060140b24029102d001c99058462504950f990f84d02d5a1004c50700b0fa00c10814090500d0140040d1802004800c4074000c501e030101315003142003400160b510078428481d00a02c800c1240c01c0800d0500040d070500c00d0350403001c21b0941c03a010900d40d507183c00c1e000d444d9050581000100007401001c24404100c50420a00402d11280c01101d060b6554203200342c1c8030500340800840ea41c0c00058119640e01c0030b500009134025007508841c1c24031480e02e102800c13845100c40c020a044d00340081c030724100f9002c214803909940c10622003902d16042804018080010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712448821 1250 712447571 712447591
    0xd0219170426160b070f0903110f0315040507061805132903061311060c03070602040609240504060c020a03020d110306091606031e0f061706060612 65
    0x1ca40300200300307080c080c0210745007440300f04200420360714003451510b0004114800f404161407010001582c0414400b09803544006021890054440015070000c1c40d0700089034544186000907201520195140e809a80300b00c048900807a01d50100782e4801d980f00100c4140c2c0842041e04201900c0d20a540c10342001319070000145100c403182c85080f07070b00c14102c20030350301d5518518007401ca424100511680440703082c0c040e225030110f50340c4013842c03e107032166058410380000c2412100400e0620403280c0040c2d01203011551507a4400c009060501c02d03208403540071f41021440725400c88207140128a034070403507580c9464a0705180741580d00a0382c0c00f406a0704440010707004001038a9160a000760305008900c4003a90160450400d81385c0b00b80181545a540c0141c106114101c0140c907440081c0c60541c200414003080102500344112000102c061070141444120000c02481c0d90019090383c42440866010382400d050095803440103846a5801a40401500540784440b0044a0308442800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712450071 1250 712448821 712448873
    0x1804090327060e09060315180d020c040c030c0e04020a14070804051f020601030f020d06020316030b030f061506091503150f090a0903030f020d02191704 67
    0x19070814000d1211280041803080021018031000f41c010200595241080b5000c0041d8078140022903104c07440c40b034202c41074a17240030100380c0542c0e1b4445052048050401201c20303070841c51100941c0c4000040c1c030f0724051490100c6500171301c0c0c464020281c0c0c3d02425100c07a414043e9000034440250700000002e070070000e0302d080b02c2c55112075a000502d81c0e903020703094040c7c41d54144010050410404a0081081b80706030240d0980c5507004503e403411240c01c008a612200e030715002040389140071f44001800d0510010402031800222030311001c1e145a0b43d5000c010702e86203c0f040c1503888405c001d00d14101c0d400318000440b118502c1c1300c02c0c1d5000d00041c0c10b6506011101e0041416150021141080540c0100030004c0034000781d16644a008004c40d05042200600000b00d40b00f00e01c054000790645072034a020106050003074001d40285547d000086540d200c8100061009402c80108140804070f058200d1a850384520309042c04074501d51038030790198803665110005000082142d02d4840d4090b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712451321 1250 712450071 712450097
    0x8010b1b031c02040806070309050607030504150f090b0702160e06060412030c140a030e010e030114011701050f0105060301120f0c090501150f0203031317030109020c0f0318040903 79
    0x121103244118035118a000d6111402c0094013030a02ea001087c480425190030705183c04501c0004400e6005800d50400142e1070b21503040c03851107080c0b140941441c0a040085e200406d90b200e911444000d4041c1034a14215113904104980f01c004904030030029400303200060004111018640d5044035000700514075140d51110a034034000ea40310b0042d00400c07a80001341042c0030313094440021240344078000e845510303c01c0d0740c00380002c0c4d1089015410014220b4810a003902e0950201e482e03104162005117041d82c0d00c0c80d500480104401d40e19055500304030100b200b4a05148140707050b01e4000344020f003140e080c50010040301d407032444c0560701680300881b0000410a280d134a4006014141c101042c50340c100350310214411494802c0c0400c01c43e40b02d9080855603400b10589070005099a403d080300078213410000c40c100714a10f5900d21100e800000040e80c60640e40c014030800e90020306542c2c0e1518055074058a9000d0100300514529800b040c5210070301e010b03480b5859603442030809a035003c0348 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712452571 1250 712451321 712451347
    0x10c0507150807020c0102060a090201030b09090f011802092802031003020a080a020109090f020405030304180e061003060c030e0303040c090b0307060516030302040b0a02010f050708010b1b03 84
    0x5540200440320908001101d026404905180c1c08442400140481c06440000030b5403080002c103044503c590b180c1200086a1082e0400e0300204401002005a0309200c0d803095216140c4150003132a6628010301100c040a4030440d40c0b80840d002080c3d01910b80d40c84a00c2644200300f80c03000c0101c5e07000c00442c1c80c050740c0c4074405180100c02d00322803000518114414405521b4254001003240d6004801c060b0060781d0042c000e000b07586010780c022881e016013a007240040e01558001e164580004200803607115814039a04d0400901d450041c0420701e56020000d0719441c00f40d4519440300130410003031000c2503083d044200e201d0240d1038000741d010951b1248a085800603a81152210b840307034001c0141e251076015102888008030050419107140c08070140c0b0030b202c2e0522181c2c148a05420541c28180281d050b02e00800d0441007044d510307040480003d001b002051110118246821301240300c4510458025050b138030311105d100c3c64660780010b543d25400b0114583c0d80e251008016842d10514 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712453821 1250 712452571 712452583
    0xe101a0f2d1504080c0d0303060f0e0a060f031208090c0a06080403202a150409062114010e03040902070c0512030a080c0403020603100611060603100b010c05 69
    0x5140780078020060a0803003000412a2641103201c51110144400e02a03100c0104010300d51650850382c01c128000640340941c054981030744004910102180000340c500030aa180b2807180e440800200700203034071880710740007161840c0800340c5412012400800c0c82802070030aa60007080303a038120f9540481203070014004501d681c0085c0000b40c0e04405000c01c06800c4100360740311650b4040080c503401040c0c1035869075150720840300c0d140700f5481d0f04142e0100c207800d1049a412000078041c0b94458a00d146603501c3c9900070301c141e00c0860702d400c1002600c0039614056445102c903900000d04840c640391500c8429405160016640755a10809221a14404c10080006141d85900540c0b9403510307042071180c0c0b403410350105000e4058100391700b025101c00b004842100c034403070501e00200d40714454944441d00850700000d40084001050050003809100d1140445030303150740d00c21020b150300000f1a200e01090701d56981607403098aa91040e002641c002e4102040d0625049a0004040d200c0501d068 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712455071 1250 712453821 712453879
    0xc140d021903020403150e06130f0b090a23070b18090a1a01030b060301060f090b07030203071e200102010b220b01090b032206020a02010e101a0f 64
    0x181c3c0c0042c003002040340034070600c0511282c050041060baa80c000700c2c2525004010400001c00700300380f40320400c1100b07441300103074a160080d44005240c41c10901041d03890345030a609440c2015002034802039040c41c0007241c001ca400d18000f4001452401907421815048400c0c060009440c50400310620f460350200a48116000907010031020940c9030144402a494500380f41018100405942252100011241103505030310f444a180a00000e046a0102c05174015540410700050154145940000544230050052050f82058881072449031454410000c00412119485003c0c010a040b1075a4000d002c51040c0000701e00b00d0104800900f0744440b4400440c8001c000c0000b00d11040c02d144a4001c0f1000d080c00c00901050a203211604240401480c09148407810944003c011440c51303040c1c6601c43c2c1c4900155110b8182200c042e0281400703c5006a543c41015254110a800360055440640c0d019110203004000c401c01e01002e5a02440c040380c0180d46403010501c2c43c4c501c0e00e41c03603240d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712456321 1250 712455071 712455077
    0x12021809010b0a0b0906160201030b0904050c012d110715090e0a0c05160302010908030703021c0b0607021e0a080304060f05120105040b15031006080a0c140d0219 71
    0x841c41d040080160564110840096003441591700360f4640d0f004903403180301440040888442c042c80100d001d001411a0341e5081007040003400100702d0b001440c1011400b00b600c81444420403e4460f09040d24102d0440e200380c0040c14107510104d00030803400d2940a0b803081611080c585415505d80a1307001e120703000b0300180e030380c6004124071071003044865000801e1403003e00a44003501c80003000e6008818803040c0c00c6500c40c250108043c002d50007c03101d00da2120341319071640380c144000340c001c0d000500390305400c2c0a1002c40c08195507044c801d0007410740004120500f440303103607028801d1944044159403180e00c0340991450a5640e0f4025080051240400a40e074507420302400803d0044842011418449c05205401c0104020200ea605441c425500011180310000010705544880c0d01307100c0a13451700205001d080304042500030150785c030356140c21405440d014000c000700c51031105004009070032040c6010003012108000c1a20f00c00d030410141c20203a00042c04910b440c44c0182100c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712457571 1250 712456321 712456331
    0x603061a0102011512151815050604090b011e090f020a18030b0117030910050306010e061204030e27010504050114090103020f12100e06011e1202180901 67
    0x81581d09004c3c098024490800d59190303035103480d002c04018801880010101000c9220a0510600030360046084c219810880c0884801d40d040801c0c1c1c41c0441c544d4000040e0074080040c000c1d0405006031003200f5071040b81064141e280c004c00c0c21407603412415504500d1040c040015070058903005100030708c0001c2c5070041c3d403180c0500020300300358165009040c10201e042c004102196002030302c2411145100300c44603041801405450a40c071403e002c1c1c030340c05101420080342056105000d107120300d40030b0700d441c140c441c484020000399004d401c00182042e40c001d00043c00080c4120300401c0b00180280c07aa9080c0c12503407841e06616213281c0042e50b8001b041200403c070030300e130900030240100440c4030b11070b2115a0b1000450320703510050001074007441c0c3e4281c0045d0a40c0301c10301030034103c00721103080d141c6003c00f442443d400f901d071108200805120720310000c2030510a410035051504070941d074280c44103280a1604521195514050b46c0c00305240c45088012650381050901c600100c900000e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712458821 1250 712457571 712457621
    0x103140118050906070c120c020303071406090109081909170f010b0105091c0c051309060e01020c06011403070e0a0516180909020d060e0a05100504020d0b0a060306 72
    0x11a10000c180c01c0f000d610030b20510200750303000f4940449072074004400041c00a85428240e03021880c0f403100a4151000003400414410900600d02c49104458152051625103c04071801c0e1080c4820190145c84100306900204642d02254038030b1f0103690410f40061a40d0396481103466940742c80d0b501c0d0a42002e130101002503000c1c402c01a8070503090810a09043e2032401080c03480c0d4040d26200e454615400c0f841c01841184200c040060000902040d07000002c10b2848000e02445941258a6820802c810b012543d060081d210450015402030043d03a28114401044405810459030103015001001c04c04c00340105c02c0c140300d13980d44100800c8a040c0003100409219184003800104003000c4003082a0000040c642411910b03881c0300400c00c281180009066801351000040c159460103503c001001da010034101c185030300031802c2d11104d00c1c89900400640f08200c07402540325401c1c00f614400a076245500343d4210700444400500a84c581d9640402c41c0c5040010540484c00511848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712460071 1250 712458821 712458869
    0x1a0304030912080a1d06030c041a2115040c030c180f09020c01060810061503050609010b0c0a0c0e15120309010c03021915050f04030c1101031401 64
    0x4001409400d0b0000104121615410701502400340040100240b030489050592100c41d4480342e40e6038001e0200f642c9050016010031a0b40c007900c10030b04034036444405842a2615403054a0310301808100007160f202d000c604205071520010860f401c3d1403141034418045481d14071842c11007402e81d8900054401c0c24010142110f500c50454010542c80c004e01400203903c80c200079001c0742c0c40c04001686606210951074050485500503d00d5032080c0d00d03104107181070315003041003101e03441412041110010706080302a210100e9005412504810040104400c1c3c03900420409139130b41d041d500f07051030710754480881c1d00c0207921004481c00303044d041c403100482480f81440e03440c0040715003810a018080389292240900d580c15818030450031042030600d80244034002401140404010f001d140d0b91070010303010322002c00d4280c01c05190600040083c0754403e080d60040da0140c5400401c190320783d4600346a41c0b0500c5940b410152121141503000c441c0c00345440c041e0082e4407210103882e09480d105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 712461321 1250 712460071 712460087
    0x512040f030606241d1302040e010803070f030e01090905041b0b1303060b010e030f010c020706030605031c030f0e0303010e0606070314070602211e15040906061a030403 74
    0x41c100300c161103c0001a40c91300808407080c3c0c24050400c0d0940d0074074141c4920385880c5446029070000d0340d5200c030052a00c2140c3c01441640c5258841d00b81d5071740c80c0c0f06656a02d01510300e0040000c201c4044100200e40101c6001ca44803105160004601e41c684810005840c011b41d0201c40840f00051800b040741440020f0a004d803641401182c1801304407088810b0b440668030003d450300ba80e17590108035591180c13615940c003c801404481503071485c1600b0034000c00c0d002d0071010043c002c0070408203146200303008940407214000d00605608904000403082e20003c401c1020516542e2040117645081502810f0f440201880195840b50b1410007041101980100150b1107400b007040300c035001a80240310040d92031144808191218070703501d030210007071003103203140c40a0f0300488402c041303c0549101518450040c0001c0d0f124207202451b00b06050040c00e60f0512141030704601c0003e0b65003080d500c00340c820b6000700800300305d00ba9218190044924100c4c4407502e070343d600004200505030403800d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 712462571 1250 712461321 712461329
    0x6030c081501170604091b03140319050309012c0c1504030803090f151f03080901050717070b010f08030c060a050c0c0106060801050102160e01060c0512040f030606 72
    0x56018201d80c1440000c201901d8030b100702d0486080d10f80400c56940b142ea1204c04441d40c0540460515040210b04140090181c40110f50003a0010003101d80d140001c0181c84211414500344422091a02e4090765660401403080e0255035a41400107401442011170100c20071464000d10072070303000524406d0924005203002401024031001d603140500c1d0110843d4100c036001394031346882e03440f419016402c001c000c127104030861140382064598070300420348150050881c64070001c03281d4401c00710400100c400c0e12014009840038080b01c2200e5000d40300504245100700510380c1b00c1c413400f00c0d6100080c0c0080005940790900310006100000c4588200c20107044400010f60400c24400d9034140c1c1c0e210700400c180c40440d00c660104030303c441c181e010b03510b4003400d4a0080c460941c4410000b00b10810902c90140103100d00c8003400509210740ca0450281c55186013094016800c001c01518403c0944030200d40b9886402e401078072541d820000f82000e0000000b038501100d00d1400c0c0441541d0840d08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 712463821 1250 712462571 712462591
    0xc01141f080102280c0b0a14010e07020703021e12031b1207150b0310090b0a14130804030c1202030c011403040b090321041e0f080f040f06030c08 64
    0x20180101092042040c0d081529283c000c55041c0310002d402c48172552034040080141c003409051050354142030f000000305140301c2000036203980c0c2e50904040000c07001d445c400056048a441400542003200030303c030441e1840d88405107807115807400700b4007011549144054641001c00c1c0d103900e407011518078103910034004c0000c0100b020100403250092050b100010400780c214040707040391010700d0700480c1d4510001000d0303c10002959200c05d000d0040c13050200d40b01071011000070148080752080140150403c0e5071f0010301d50359900c1080740703548003003402e85040c4000e01002000911150025020340322211003d0180b0741d091040c54604620b041c40e8605002307240d18061100c0c110801a281e10903080307500000345403181a001d600714400c0c440b44500d64241c0290400715a00e1442c24940518802c0d806442c924041404110028541030300c01400e000c00801c0c4000170420200141c442ea03100c0851841c0362503034904020402324960350100340429114030a01032040d4000c040d507644516084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 712465071 1250 712463821 712463827
    0x50a0510020d180b04060503040c0b03100302060f0702030102031017010c0e010c0c0801111305040c090b1809070c0515190c020f160e091b01050c01141f080102 70
    0xc000307915111440c180c1c03410000020074450600e4242450f420040404400071603440c0e881e400002c160360b00c206e0303066400390941200010038018610840b441504d403003500e01282803c40e42005106d40c4a4081d18000c0d000c103001e14409a034080c0300039402440e002003111190b901d0301e1440301140784c50440c418601d901d07000a001015030003c980e040307408424a0b10b41082a1b2900c1e00e0040303515207030401103941d860404002c400000000003050250501841c0103403050b034a00c1004143c070070544c500e07000101c00c814104401c0f060b2a0141200b0310104606684035202803001c9000d0740e20844c0e231000011b003080c0004086c040d0138002c034403003482c0741280c400f11460006020091000e13204c410106960792911002d04091003440055454032541c0c00ba1640030800f03031030f40726202c030b03290141013190705003100450707102c0c040084c0121034103122506005070645800c0041d50b49400881d101d00c803d549030004500724154521409114641810b1565540300010724000c00803502a001860700b60301c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 712466321 1250 712465071 712465099
    0x7050601081603060c210b01090f05151605011103041707030801050112020409140403030e070e0c1c0903021e071208031b0d02220518070504080a0c050a05 68
    0x1c000890550b074000e100440c55a030080400c880005000d83c006d281002e9848030036241d0401ca8120f090040002d076039961400780c0740c1c4028040030480f403150540c04001e00d03040741241c00c0103e0140c9030f6102180d1a0448550741031b00ca903420f41c6e1491110300120240041040300300442c41c107450ba015841c0240d1141081c02568000e00381c0c0304c1c180241c0b4140851010003881400c241d4040380c2c00f40088004c14042141c40c1c94520b4040c2c5000e83d0f0483c082130501c140444034500009070300040b5442c02d80e02d0b1406803030b245150301c000c1d0301124007462000c6480c00d0415100315540540070109200340e00a0001215000c1c0ca1130141000030704184c0503800400040009840d050040d452468200b030800b6902e407a6408158020081992901c2c0c9402c00494428003aa480758090211906174900714000300c84691305030480c1100700e01401c1d5005113100f48590340000d034004010b500080a00300145019195200c45107811048882200c900442d0001070040381030182e0294010b00d8141c803010444040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 712467571 1250 712466321 712466353
    0x90b0907030906290f03060c030109020a0504090509030711031b010305100e04150501060302031b070201300b100c1e020a09090605060f010e01030e0a0c0b0705060108 73
    0x8050941400c050b1079100c90030500101c0e5000744410790070b0031540c40714400b03c103000c0d070316403411509401d20a14030100c048017103050200f00e05208045590040745180e003410700120080d0440e01e441804c0181c140000f265419041c82818000e034044001191030b40c045181c210038404005041c0d901940060f40020103030050003e40e0b00e0380c80400d003070111f0700380e4070b90380c0703d04e800c40c3c580d4405000703110320505020501c501c0c0c00300d0b000070300c3c0218818441680c075980c090b406c3c0d120540d41010b1240902c036400711480100c1004e8061588145007610300041d0342c111000c415086954100030b0b03680c4408814019a10034464000680429140d03240d0702d100d02080541002541540a0291640130f088106486035030075020080d50ba0007407d40c021503888a05000040c030344041d08640172417800c40400c0c0c443c6402e0349101c0c07800c50305a4441d0301003a1a4001140980602c1404038068414800008002101941c414024168540d0016102c002d1418641c1c50048c040e40841415000420f20700030b0015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 712468821 1250 712467571 712467589
    0x6030a0507090c12090305040302010f0207030209061020060a1d03090f0d060c020105180a02100f110102040305030a0207230f0a150309020109061727030f030402010801090b 76
    0x500703803030000c0d07102010303103055030f01c98101039954034401d2170220801c0c209070b004806041a64002c1e070700c04c081e12198440903a554006404080c0d4010b820300001405403510441001ca54070b128076001280c84452011400f01130030354254085190800802c020301c0402c1c130321503511201e900e94210585400c41c071400548900c0f40058141c0284000e00c801c00c1035442e503030400303000c3d16809030041118040d81c0400a000707080c02d8540d0245c0084c0f02c3c070003481885000038902c07c0c0680080045484014403c015619410540752500600c200d41c10780c410b5800c002c0c400382009600500c00f4594615a40e04000e0812751240c001d225490001c481072603106582a1310030103451415580d405100240d0000500002500d07030045014243e43c1820a05050385030700107004462007a2510086070391200c0054a0000003e90340c40c1000f000b11000403144490a0084200c0355060391035000c104c403090a0f4681107500841c203085890707400200780011940d2119490f4010059a0010401b10f1403410000318105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 712470071 1250 712468821 712468829
    0x30c010509210d150305120310090621020109081b09070206011a0906190509040b3703080f0403031112070f020f120d0816020309120c0d030e040506030a0507 69
    0xe6071408100240c4130030300c000b00007841e040001c41d11500d0550140302c01c1e592003101d402000441100740040ca0800500640f002e82d045000c01120b04031700c03071061031188078100009030304001291000041011040c42900c2a040c1c81d440584031491951050001c9900068031150840d802a001040301441c1c4003134009058400361140e40e03948901ca00011038a00800894035070302031040440c101003d81000003000704100948085c061142e140c2c0811900079042a01d00f50780a07400c0036540d00b041000c05803030102c001083d00701c10712140c59440742101500004c500340c80c1c4540c0040d00307005040e0420021103540001c1c0d8001e0400d801b400300702700f0842c02107082c000c000600f2035207044115607406030b000d086400c001d8001030742800f400d201143c0c1c8a103110b400c000403403403038000f088044e1b8081807031031480c10240c0c00a6150804010502002c155001285005801003000c19012a520410380c500458041c5ea11542e540071140200310440380c1c00b03880148a548074000c2900000c50100f0840100d07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 712471321 1250 712470071 712470097
    0x10c181409100b0406050301080f07080c01030e0111031501080907030305090d05030d0f23010b040509070912150b0603090619020403050f0a110913170c030c01050921 73
    0x40e2511000350468002c6030300074480072140481d0100b01c1591200142d4102d620030000c880f580881c03220360750345501ea180200203190b00249280c0c103155000e030304401000c0b90284000645055203218050030343c0c0058442c0b0220b07240b8800b6000380d940c2e0000305681c200794004094861a807079590042e01c80d100d640000342c0565400c0c590541032150910503107800615030704040c05081403c1c9204001811058040c200070720140c482d81d024292251030744e6060f103a01d1a4024030b4581410200002c031a001401441007281c035030008100d040110001d980b2040c403442d41c0301004810041500c2c2a2100c0d40c03a079500030344040c0200b020140c0c00141c11500b03c60251103c04d00f0441400029000e40f0541c0c0000c2d217184140c6040e4001482c002a0030f4449500403000c5018048503201001007054003030300c00c98040c080f61502c00011441d01d0303808003c0c000e5030754100c9103091100100e450a6400580c10403400ea55114100680080c0c00e10269131420032019014030140f0b00000b2111040c0a4007504c0000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 712472571 1250 712471321 712471339
    0xc170f0619270608010b01080a0e0319110c0d0b070c050f0a24020903030f1c1e20070f110a08030d060605040609120f02060408010c1814 60
    0x360049607a0310202a04a60b010000490300c10344058a0149641d4103aa009901d8031200040c60312041c07180000082e0143c0d034002d140e44a084804010382459602e55406010030400347e0100403011445200c3c4085988694180e02520750b00d540c146103549a40070f0007001c8840035580002d041c039082d190311405500b0a28896501c0e820120718020908200304e6041c4241305000381800f444403c0300500c00c156014039420800c65006000503800359208143c0c150b8402c0c0f0042c120f500c4903001602d10002020000d01402c0d0003403c800058584554452901c2050008102d0240e403035400703901441c8006100f940000000d201400c15684600c3d04081e00b0080b60180c2c0104004005c1a443d80031000140001031203610b54003a261030740c0c050048200c0d12443c04030005140390081094900f100c1140d03da42c81c50790b161090f1171051031045042210340301c40d01c1d040d02e001680d80c2c20161001e84090000040c1d41c01100002601130408054401d4501b41c104404000c0c00b40c2d4541d8078026940c0503100c2440b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 712473821 1250 712472571 712472599
    0xf0106080405011103071706030c0102060f0403020316240507120b0a0801020a0509012a1707170c12041a0a14070b04031b110913150c170f06 62
    0x3004261101e81044641350000c1813251850303103c003154a240402172070540482e182d4030100b45e5159402d1130503601503005400055030001c01d941b030850f8450b0081c01a42c0c40c10040020125024081207030880b4451405c12444840d07130359001c100100c922000d0810000d1b420014000f038041c410b4540c00d522116103556003c4683d45611042400800e08030009544030f542041001d00150490400c0b40e00103050103e84602c880e11405404103006610300049480c0f042e03980710f244480440f4000c406a10508010b100300180d8003088800e20380d0a00f0200d145c40e1180903190905120b0010002400a041032000388016140c1890f115a0090030443c910717500d201000d81520600e0440c081c00f0a140300204c1c81000303000f00014030320702c41c2d031003507607190345030040b400c2c08110405d4055000781211500030800e03440e50505039407040d0000000c0842c2c2c46008025911548034078188050004640e4465101409a581110100305a03444441410b505890040ea904140800041000e481a040c0450541c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 712475071 1250 712473821 712473823
    0x130e0903190e011218060908071101080f060607031103070c0e0105010e0112050717040b0601080a0203090a02040e0f0d1d0d021f090306050f1e090706180b0313030f05030f0106080405 80
    0x380c80d1750780994184891402428603101581003107000303844211500e001c0c02401d40c0f080303a441d4031410301d038803045400c1e8566105000c0e4940084100b1010f000301d4281d122850501000a000c40d10b10401d28005c940c2d040264102c15108181d10290501004001d1482c6a0303800158400004001400000d074541c2d403540700701e600c0f1420310321184440c60350206000a000803d08442e216540a80751b00419031280100002288000c4800381c1d00c0703400c60302c05070740149003a0b00300010102c1a5021564000703c2142d409082203041180100481e4410700c180c5400070072a145516909800c482c240441000c98000c901d60405200c44c4080c160307030110641e050b842c09151104045d5400c00400c2000749003a9603645a101c0d070036070796901212042c290403c50442e04001c0b0511402000010340412850f242007520141c0540300341080880e002200803c00d1035042d80074601c01e501c0450748140307405181c140941503005885400c2c00300142003003000b4800e8505100c150450300b80e850b000300f01c0e40d2981081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 712476321 1250 712475071 712475111
    0x40605031f1a1f03150609050d110910080f12071527032c0f01050927010905010e061216030305031008010204030b0c130e0903190e0112 60
    0x1907a00903030810351040603e051a8a020140600f514200280300b00300b8004c11103040741e40300e08000180c0c106421301c504d00340500010b01841c030480c0348503020380354a000170781205030450b115131920408007002c1049020800c0a54101031000c0064101a020356a125145208154025100c0440940d90300b1000030254060001240444181544043c1541c0c140a440d0707914581030740081d801140701039441d06007007044204841c02c0c0b85406201c8940809000d0100d03081c01c3c2c2181130090601070240d00b6100e0720035151035004010211208492224441283d00038180c010f40354191a020042c080708603104441c03500310700b044640d00c0a144140c100c0c0c501c0d002d003000c200300c4040140040002010713042405140a00c0b4044110381f4143d0304c07118054201d008901c8098500040600402c20410f105001008070300922241034140a4581b0710321869080c065608074116840011014440b0004015054070512940f80c00c01142540c072000900c03010f1418408240c4560314060507562035841c800c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 712477571 1250 712476321 712476371
    0x1704020402091f170702030c1e01140f040c0803071505061f0806031905460605250e0619020a020406090501030c090207080409020c0c040605031f 64
    0x50640044207180e000f48041041520961041c04d81404104110700100989aa248810000344042940c98002d03010302da2070140c141070300d950780d88040c003021004550140c0c0300c5d00200100c8407840c10a480c02e1030810105a0081010380c20030f12810f0001861020b5403131400c0161070001c9a561203c80005d01143c0349040400340c1070100040b8034590b5034001503500d120b480c084040d14940144d0800009400c200c0410003081500540100d1201310488040b0282e40784d01480000160382085801c00c3c00d05e800d400b43d003048000544412401c1207682e00400360300c04503098811020f04004207983c844121003600d110113100b29150542d00c0c40d25060186c500103001e01c40c10101c102d4060001035102c0c582c0b07042c2640142d00341030000c6804180307409030354101ea500441d48800d81d45814280300c02500107503030851b0002c02c20040019000001c2c0003800c4904c102d84007074894084031004100445070594080d82c080d410001c2528802d00c0b22511415801e21310820104000140e0388071000d0b04060412 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 712478821 1250 712477571 712477609
    0x7080904060e150907090821040308120103050d050f04051c0501060f2c06060a09050312030601030f05100612060e0702070e07090f0512013306170402040209 69
    0x4204032038103202c0e10441080f008240c2d43d0788545c0c1c84c1c52800b1243c402680c0650703011a0722405881042091000c580788040e0f280306251814241c130b0303954014155000480c105825150400180b041c000240400d0005036514108181362907159400e50b0b440e40140d06c180c0e446280100d031419060450009a6441d4075032100c02042a107484681c001c04034440b5003d00380c1404407442d00860010301000e07a4090745030709840002190394858013001800d41c84945040b0820103e0140082c040d1000c02c280014100e00c02d0000380c0341e02e071200005080320755001082000608010900c030039415000500c0b403d940d0945811088500208e060102074030041d4404503ca200d02c10030420b480d0340c04230700e078801d844014402803110303111010216642080703802130380360b940000d450400035031501000015107003405900100d00c0c054020301c1c00700200c5800c005d0721540c54082210700803803898035a8103009022749040187c4030320448403104030904030083c002801b681c0e000034562081d55075000e82901d9072071440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 712480071 1250 712478821 712478849
    0x9150201021b03130b07080706051f030809040f1e270b0a053709051504050d170a110c03030c0705010f110304061e0f060e0901050403050708090406 65
    0x2d905649900864080350b40e04409070b0301040300748991080b6034185400269040c14000b143d01d42c507004140c0541248080001c3d8011045103a2854012a005600800340303207807200d4105040c00141c0d46148072501d0b425240c00407a040c640e00c01510070700501110034001494025406501002c0344a10710078150005c2e20004c288108001d40c0d01241c810f0244080502190311090f240120351080c0c20301c0d01249034880d01c46400201424400c4115014648401180500c0ca6071142401d00001100080306070300d0038001c20003402801c105000000c6241c2c0b80c2101c0e6020031402003400d07444064602a05907403a4250b041c051603940c000d07542d0005600064a543c0d082440c141e68050340607240440b2036508001041034802000d02c80c1104408039403010a15503950356460400030080700b01c03008125082340c04400d480e00c14510415104070b010550020301c49050440260414400508411860f0304210030000000d41c448241e500443c4c0c0000c140703450301d40480005000d07000540080321802800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 712481321 1250 712480071 712480117
    0x9041b08010218130603020a060c03051605010b09090d1d1503010e040303050c0307140d090c0b070c080f03070f0c1a04140d11010c02010314010e040b090a030915020102 74
    0xf0403c200c155010444800b401841141d0341c003070640d403680c88041e41c04018400304010203801410840e4046100f4a000d40c42c280010300e00400035583e035074050b41d65a644d000e40034118202040c083c4d40180030200200300f00e0004010084c04c0405070055141c1164000f01c03c0709281d1140c0d80403015980031524031940380d685800c0e0702c11302844101c030180d00007814000070a2100c03c02c00201c0340110700c03603585c0d0a001c0c50a20000d200c0c2c0e0303100e9408401305c640c0c0c6580c990003054141810b68041c0614030740481c1d0301c01c0c59041000782285250400310b500d400140c41224030010000480f411181d0140c4400120b501906010b85c100340c0303640c01424000c40310b161600301030700b01340014010b56001c0c103101004030503000e0600c0320600d94140024a48409942c1340025503001d0003407050030034414035000c03845880c0ba0030740561460081e4400e01200c45558180010040e6074441340e90301c42d0b0844000c182409040c1c500404000a030711410740c50b151a00d020302c021030b200707404807001c24820344650410080b030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 712482571 1250 712481321 712481347
    0x61e1306030506031606080f0613050a050a0c020708060f1305010203070302030106030c020f0c01081801140601021c080606030712150608070219202101060509010509041b080102 78
    0x8116022131003801034060582c066090441240f099500d41d42d141e420a40d64544c1140d01010040c0520f6030049200d1170000d02d00d0401c0c001c00d4401c00421030080f84500344130bc1d0400548452500c0b1038155000540148101c0d03100283c850350021111403012440c2e103ea40301c01050340f01800c40600254000001c0040081d010380042d4102c5505a038100042c0f0000541281c4460420501801c0c94109031110815984651107181d0400e048007413407092002c100d01c2840c02c50b610f03c036510840395540b40c2002841e42c1c05100d800120b808610304240521281c4800521028008009610480c008408240c071300e4407400c80d070107190b86081820044140311001d00c0c0300b10702d8288a200000b41409002400291011480c00311080f2403a0f184102c0100342ea48840300141041c854102d41c45410314010030640c1c501040302d10302c021100c0b0302002411000c442c40d081d180076800c00c074002c0300140300401c056161801015400f070f030840d040b640400302a2035000c41e49205540214410740c0081381a40504807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 712483821 1250 712482571 712482581
    0x70522200a0f080c031e1803070b01031e03090905040323030f0c0f0403150b040507050c0601232701061106180a030c0f0b010b07021003050402061e130603 68
    0x25442d1070f03041099640c0c03c1d0b07000c0c070342c801103403c40c00b0350681841407020315024100041d00502083c04c003010111608903194510f0700a0b07801505d004c60058010820b1080084c0114100e002081c0f8240008070940c07806008441c03a40f0500c00103a50740d5002800703140c420240f80c04018071070300d48029800204034981d05590016103030b0030594141d040214240d0020a02200c801c480c110460b141407610352707142e00e4004031000865003850750700c0d010f03440c17481c0c1e03114495140326035003d49640741c403004030210345450803105030444105100c04080380465208420404080710404650b0f045c1d50320340d220b04044021311000780f50450f800d028000070489540051880a00c4601c02b021219642d035030100b84c0c010000800340c2e480180e00001e0b09100441d101c3d40ca4108140e004104490000101c0c0e5030341c0940d103200740d000100d00d00002c94480c0441c5410368520352500d94503d004d10040c10a600040ca051085000500c0316984c81908003002c5400340040d11450388034680e0940c0703216512400034010b0a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 712485071 1250 712483821 712483847
    0x23011503140109021f03060b03070809070602030306090f0a0f110a030c0206160f170a0b15181e09041a0c040f03080a03020c100603020102070522200a 66
    0x420941d40c441d000014410b04024540040c84928610580e00d01c580c4010400a4607008060f1100c00200790205040f0040d801410f0350342d62030b0340d10700e040f0341d040b03003400e00c1c0d90490000c5400030424080155242d80441e038215000c050440c0040d2031741c019035030041400420b08181203080580801c0060646030140c80f119619032828400520409000c9031100c000700ca100804031640d141540e02c6c1880340802040840007828078200711380300900c0340c114040f07003254039002c126102c2c850f400702410f0080c5100c00c41e0900c0c420b040e08004010250305e01c8801c011000c6030280c0c80401d02c000c080b141e20038218801c048050100900c9040c14241441065501002104102c07504004a140d0440d0501150100e6042031100380e140d6040d0b03525404164001c628503802c1603000d0001d941425030501118221025041c000103410f8514030000e8182275050b030001e4801c0c111700545170078070007040e000b50b89942200600090507038034139030403511489100c0e07201c0e8101c0300003c144141a01d0700300c100316101c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 712486321 1250 712485071 712485083
    0x40e0613330501170406150b0a090b03010b0a0c02030c0411120601080402010203121e01150207090c090b16080408070e0a020910080702330109020906030423011503 72
    0xc0c0704a00c046040c01450310426001035008803000c80004142c0c961190403622462000c00c80001804030703541140ca05400c40e801c100303c0000c2000c40150000e1050f4024040381d03008900355858a501880340d40078a8000305d0900100ba40c8810840d40d040c0084d82410300020f208008205080c070002c1d180d90032188040c0c0e601c3d550314004c16440d40c052034040e0321481d0b05a0081d4904441640400d103005005460788010b4000700d40e03120742000c021100c0ca4040c1401811244400c400607200030320b805940c0c1c0c4080c0c500c0b840c4c40ba200e12403c1c3d100c03190906507241400c0c02035445c2d290007014180c1c400c010401034544e450129001c559a5400f1501d042110070003c001e98150b01c40c050030f00d0480c4034814049600042d5030191a4560f4014a40360b039012810740107450620740c0d11680c1e10100c441d041d84c00c007480c400c80d25009141900b416000e80c05800003400840c03c00c841440800d50602c03001e0005032489101c42a0f8103c2d21a81c0f01c0210a000c00e240300a1215031502c8022201c00840ca000445030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 712487571 1250 712486321 712486391
    0x1c0209042d06060b041214120a030e061e1f211506120b1302100302040501030c05031b130f030302010f0b0609030703020609060c0303090a12020f03040e0613 69
    0x246855074045e201a2040380140c0c2516149a40d0340344034107502100e90325103500070400e41c0f02c00c100c40070011741018165502c0c0810054078200400f0f0414a0050408810302890352600b00500f003d802159030191598039408510507880c1d0007107002180c0d0b03502804c9240d0003144900d0303080304010515124141319415005071178440324501c20964140f4020348a8503841398211300081070303c50ba6040c0e044541d00c5200703d030008c0c0316004034200050200c90080400e400040401265a05110f0211040c0480ca845030070747c2003240c0508000545002d644000c01c41c04581c0d151501c4074454160b00900202c1c2c400c1c02c0f07651380d070314002e0301801181c80d000004910b030003404250343c2400d40498410030b1004001d440c1e014215420400b040d00044001c0d500260280b00002024034200700842c01400120014209130030741c0e240c0304000c525213030216421900180703107052103803500005840030780d04c0b13131056140e8603960384020460248003010440655400c10600e14030ba002404100325039405c52005002d6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 712488821 1250 712487571 712487579
    0x9131202030a020604020105070303060801020333060d0e070e16031d0d03271407150518010c021017150d0305070804090908181c0209042d0606 63
    0x203164020184150b015820180014005611600042185522170704001034416100c44155003260402c548490a824401114003440c4015050b41d00a134800030b10005e0fa9514000302041a034000d440c11740071020f8a40401c204240e0062109078050280c494000e06185400214881c2d42d050707940c00100030a140c1181030368128110104480804d510350018400102c0b00c0008400601c100f03031085890321541200b110001d11202c4da4540c846000b1007501c813049a1003d5144e050588951100b14030100b041c4a804000303070480c0c241c5002203a9040b07a5407040c16400016600e130103600c20001d501040c05800004a15003081c00c0e40f10903000900340b402c0075601e001c0c60207178208034010500d5210703a40c8520203001a104400909805202d00070390f60030559100300c1c0c1400d0f20080f4404480c510400720308082101d8402184c1c0100c0c0e102114000c000c485500070100c0101e0b445480a405580b80100243c02d00c04030424a54403450011550070603404a449809290309503400110740550070540001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 712490071 1250 712488821 712488823
    0x1101020408250e010f0b0a120f090204060519030f03090801050408030703050f070203040b090406030203070b3a0c0309020910060f03090812041b08030d05060d05100c0e09131202 78
    0x242c10380751005e149596003800c0c90300004250700030700c1c1300c4420841301440c100d4804400d400386440e070301180c900101c3c03811444e20420013038a01542245004d800203141408290b01031604060803640c02411002031000b95040841e101107098000c422950b081070180420400707501c00552060a041c2d40400140d180c6490248070000c080e1034800050b0300c180024802542c0120041c070140c40001c00009082d80d0302e502090410381c0e9544980003203480840c82c00f207824004a10b05120380c03000312080340500c074000d907214408a003c6400d109d0003030340d0384416500c85010340e1180369031380d80050005541c0d10303040c2d45d0441c1c10085401094001090916446280e500034012601003903030150042e41064800090983e8802008000780e80401c050389806c20802d4440785810040c0c848040031b50b5070b03600b00c3c861050517034202402050141f49910b101201007034020070040c1e515400007101244030503070200d04544200e441c010403503001d0380c41010f029100c007031100d40041452083c02c4d00307090706034550320903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 712491321 1250 712490071 712490099
    0x1c110a06180f0804260c1e15030a060f060c120e0d0c0611010c1b02061603030510170c0f01050c1005090d020a032001060b0c0d03110f0a110102040825 66
    0x1301564042c945e800307121f01d010b040f0302d02d04800c66000d4920040d07030340002909904d0310040e0901030710000411b1008083d05801484098071050001c1c110706407422400905c001815507010305000c0100045561040c401c40c00225080c50007010329588075174a081008010010b40f080c140421420610901e41c4074041c05076052201042e01c03400b140030000b01c0c2403032180c0000c17001240d20102c03c105240907421440d5031848414061350b4000707503030700d44840c1e100010070568201c0c0862060303c46007002120360009641c92043c0302036519104210703c030030060b41c0b01e0041205104007400b5103500c140d040d0076194050341c411501241284c0da071400e03103a400d23038032111020800380c00513025091b811840310014103585a0440305000000d0f00c0c9030b40b008840e040340c004c50740140c034a81040f06584040c6034140940c044440d61080c500c1d150a0341d90010080d14414003d10b24280983c010540c1c1c1103010a40c181d50091075082c00b41c0d98003100c00414240940e85002e59181821801c40000c82d01950781b07090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 712492571 1250 712491321 712491389
    0xc09050609040504020d020904050303070e0307230a03120210060909080724090309030209060a140103090203010209030105070e011106070912020f030a051c110a06180f0804 76
    0xc0d1840d1070140c205000143c00c000b00141e800c806612240c0b00140c491203a094801ea008030003454590400d00340042c10f0000352810b07039200e90b000c840c043c000480c5102d40d00d103100346100e001c04060f10441000c40c0d0900000d9001410000d40e901300412016008503c04180032070070782e02003028a88030000c07081101e01e6003501410f107c8091101074001001d00c541c061042120ba034038542c046014403810019152040011000034820349010821401d0071510fa58004100703c42443d00941480720540c060443c0343e4495040507154900384065444c01e50465400c0000a802484a440c01580c00307003038401c90800e0640011010030301c2c50032070240803440e14080c0286940f1019194a0050302040c18420001c050b41d100c889510403100b1590304110800013a4800e402415100c60580c00840d00c106441000314140074886441100180e000314440d280903a10200c0003404408107829005550f0350810001c01d4600d40c54104403d00500341c011700125091040192010802522940403044501c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 712493821 1250 712492571 712492579
    0xa031107080703180905041208010e06030c190305030705010e1e06010312050405031501090e0706140c0f030f030a1104030f150e01020a0e040e010509060a050a060e0108030c010c0905 80
    0x4814000644140e0004c0e2250015142c2c5103c40f03525890b00304c0440304180c070100d8042d4240384428100607040014140100310700340c2040542c1c900040800e07280e02c100070086100b401c10351a100d8014100580300809950040e01301da0321100b0a1034000e00038008507220081c10300c548420080c840301509100c03c01d0b51845409020700341d21796625145009401b8048800b881420700010604d40c504101c20280c864058aa08007254546844c41c422a0803948000005800401c42404010340060700e00c074000300407194880c1ea44c6100344106050101c0c900d01c0070290f0000040f5207540c5064907002d1030003186241c0040100c03260341d40d07442c421032055220082c11034529143d001d02040a1201e44c003034490200b8008144100c102101e40d08982c004030740040800c6a804003d11310381810705c1400703a20311071b800c0200018200340000b50799900005141000d95602c80000500001d01600f0820040c980014030302e8603561101c8003162139402150485c482986010b1600368501e00c1401503604449000d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 712495071 1250 712493821 712493827
    0x106051e030a120c1a0708060a0b16170307230415030c020f01020c011e02031b0726030103141501050d05150a1b020f060606032206020a03110708 64
    0x5a24043e024108061a9050094803143d600c0412032080e003e01d0304030f031000b480c810709181c00321018150700e10141009001d00e20281d070902101440c40106c400502000400303034040350345032030b00f08054807106203015550700c2c0c040240f01071300d42c11403014581d0700390003014100c64007006050951a8002c2e40b06200f402d184a0700c0161009000358010302c2a0b02d17642c41030300c0e80f0240c80c0d05c50710300760791008680001d245e54440c5a0a03040b49080e014120480b039148055145007080d158254124144503040c2100c00f4000500310100701140c510301301d50034040b28901c051b860301c03c81940c40d01d8200344400e0f685505190b080c135180c40c8001c83d00203801d044c03008205e90b0300c3c0d0904007806112143d880040b0f4061240c944101c0034030b054404402c2c800c401c0300b800030030408910100c00042c0d440d00c0b07201e00d06651225401340c100400c007207170303483c0c5c440307000e48030300c4d480b66030f0703400940c10400d030541703803611140d0002511005210240c0c00400012500352001d014030003414122642d20711076050003500d010414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 712496321 1250 712495071 712495073
    0x7061e080604240b09010207050109230d0611090f10020a080c0f030d0914150106030b0f04020c011b0c39120201020c0603010b03181e0106051e030a 65
    0x30380c04401c00584000340f10300060ba441c2680d410410341c94108022443c008124a20b0a42e030411038140640428640b0841c131516084048810755440302e48a035061240b103a80c1d00080d01d48074074204000740c10420a028051403060f03184040e41c0050061400f41070349002a40b40341c204500c400603c80f01f1079000b000384d49076039250200960410f41c00b041c114000c40d1106007000404001400c040103200400040d004620700e081100510000280d0b11240c0144d1000d500881140c050707241100c2d01c1741004200e90381c0110005041d901144180ba5000b403021501d01560141540100c1c0700034040028100c0c12440800d054500f19548040101049480d8209a1541c03214554400641034075903c0042480501500314200e420660041064041c441e80c00801f0f560f070410141c1c0080c0402c0d6407031803a65042081091091000030889009503600f02e001c3d41c0f0543c000c100060441c1005040c0f814460166070355135010309140e12070030344a580c0c80b40b43c800c18501404e0500c0d240c0c1c00c00500815002c20f031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 712497571 1250 712496321 712496329
    0x611250203240f1b2818060809030706020d151403032203020d080705060c1e13050a0f2328050d03110f070f050f0406051207061e0806 59
    0x107080c42c00c00c00345401c140b104d600411020b8005041e42106000369041c561803260424488200200c081015580300c1401c480c00b9024564150742561801075050768440c420140b4500c1703600c1000341480e00c0044c010100304020341c0041c140c400854512801969941d14500c1801654120194190000c014144002c0424022032103032408003c0c04185055503030700040c4480e18004416104e0090001e00b0b5030811200303000b090741c800c3c0041c6182c1c0c180040e05001e600c0d180104120008a14000600410120840058800101801072402c00115124822010032180358420140071407440f401200303009c014202c0140031840c020345030508031220880030003810149042c54641c640c44c107800100300342d00c50f2980744a03d6406912100c62007078150142030715000b07108414100c10341102c1002e01000031710f010b41008462040720007d0380c0e4224480040e004055070b9000551150441c51b50041440d40460700c40c00701c80305901c030503400300c855070380728100048044180c00000e5031450007d2110b00e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 712498821 1250 712497571 712497601
    0x6020d1805120606091311090a090c060f030c110c090414030409140114032d01021c0b060a0905061606140a0b060a020604061125020324 60
    0x4400481102101c1e551004145007101404541c48207410000402010b414171640c01c1da04030b44003003484400a4140e4480d070b1420001c40c1c0680307100e06440130200b110f417180340e0880c02081e504480000912540d84501514140b5404680c0c3c020034206048403540c9401801c5201d003815201c1c01400c04a52000200006414014070498003041c455190b400500b0042028001802e06a04002041c000c05280301c034240b8416440700705c092004401209441d2030215100d030040d10846811101100c4010703241c0d03425812401061400d610115082203801c01d2103042003240c0124001c05c010101d1102c080c001d0512132102c020000c111892400c21150410f03400403c0c0950300314030011007042e150759460050340c45888650300740c004960180a40340f003140c031401c41e06007800ca40040c602000f404000c1d40301c01c002000130301490b80c2c50035640480c0801d40102d41021b003105484a03070510386100f20030340380d10722480c0c207900074814184980ca10003407283c0500b8005040004004195881c0c103051001e0b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 712500071 1250 712498821 712498847
    0x4060e151507060204060e120c01080c0d090312060608010605031503010f11070606080c0f04200a050703030c0903150507020705090c07021e180c1306050a020c0a06020d 74
    0x10446035110310070a00000050300700e80d4070984001d43e40d1031030300000030656081c00c04018440c14502c5d940a20003640000c40040c2c5030070a00740792009a50b16007002ca00c41c01050f1030030035203508088840c42007560141d501c400b00303203464600700061380d1a500202d030940401d02568000c21410804507001c0c0d07103d8488600800c3d0001d0000c1400703098107440c40c065410940101141540c0806e13048200030940c007a00c006403211030001c00351a449000020b668500300e01c2c0d00da0207035070340c1c0f1402c1542d4841c0c0070103449244000c900d0a956000300900091840d4400b42041d80000e1800420b103103028843c0400e0001c5a400c0244480d003400910300d80801000c1c00f03841c0c50309501c522900058551117142c2a6071080400301881d035201d040030300601002e50100010400d0b4102c20103001010381d034451104101c1882c8000c29441c142d40c0b61784651006101c4c40b0304065440c5a0780390b0000f281c0d82e0060041004a079180d090754841102201440030000c020f010722409600300b0b1000840a501ca011030131206 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 712501321 1250 712500071 712500079
    0x20426030d18120e03062d0c07030810030203060403030c11010903350c1e03040809040c050c0601210f08310e040303141305060604060e15 61
    0x180d001c0003a0011205074402c6a5001844024001c080c04a20010103090b0750712800e007190504410030000f07807561001800b4440c14101200940b01c0610544400414144640303400710450502018440f03450300204c00072400160034070005038402841c000400110b83c0d0140041a040d01e45950640103002440d0801e01084034060031600640c509000b100e11140c000d403111404052a45090a000424550200003542480c651001e00c1f039058012140d1140b0328045c900d489086404080304130005425002c1100c0901100740020702008400400c600c0c02c04850410080d0303188a415116805140001d043d6134101e00300420000301800e004120109400754070110052a40d545c2250041d02c140e800d51b040340000c54800e214605402e040300d8245143d41a5111000c0c0c0106a81e00300c06141c0146448a50010045401c26000b0380000019600440d804d8150346400d248103d40040800016101c0e8410080030407128203082c86024143c42e0442480d030041c1d0358442032402d00a0800340c0309a00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 712502571 1250 712501321 712501327
    0x60c1b0307031a13021f110708030417010b06031906050f090402040b030c061209100506060720061204021509210a05070b04091b0e0f0f0316060305090102042603 71
    0x1a80c80300e10740210074810001c00102d0f01500500202a030107118501c00423544010310600800100006460440c1c0b0201c8950740b401704000f02140c0500b0080c841c0780d40003c0003006019441402828a61110803024801c00110b5551010000c04854216407203800000d4800858003500380f07500500e100c0040902280e003040c8004010032855440015903031010b885410074040d810380e003440b2017400c4404950050009091840000e102c1348141503005183c0c6a040c0801c02c44900041e1500c030901c1d000401440d1034020105012000f410100ea089105d121101c5028400707600c24403e80d40341c208042c0c440302040d40002c50080110b00f80c1e480c00d901501c01d03401c00f8000950304100400c060b02001e50074a4a5038034091820080e0b4007000c5021000780000d500c1d2001c0d007940300030480750100044607080842c004150200d10804100001c15405005000ea030050100c44180d1080403150195000c1100b079030313034040711400c034041c85c0551700c00402c2149124110300518844450880b01150540749 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 712503821 1250 712502571 712502573
    0x115031e051b0a090c0912141209130515100306080307030903050d0215160e03161401080105030d0c0305120708040b0a0903020c01120b060c1b0307031a13 68
    0x45021051030402c2800d800d10340421080d400d103607001100a200382d00c1c003445840002c1d000074008003a103010755214086454000801d1210321300101c100a0004426521911108082200a98007034140d180c01030390483c0d0052410280c13440740c1e074494403400c09070040706c01071207080010034581755464408064841001203402202400100311052098443c0c0202c00c0c5185032080c1821003c540c0101990800c046000b0034a08010440c0d9010000101d1168503035400b0700169004400e49150755018490035081d400c4401841040000307846803141c00c0c407903481c1e80c80300446038070f03c00340106a0507400404100904174040c0407032003000c0e8403c0c10000e0a1051a001a0ba40440308a40e1900001c600c00e050009100c4000501038000c45541d00904ca84c12140e18065621480c1d44806810400f03440300c1c50781400001d500010f120038004084e507079a044030300e41c22641c03001c2c41c0818258100d22115580b0243c500014040103caa02002c1d4481244400200e810249002081e507140b800904082c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 712505071 1250 712503821 712503823
    0x90e0327030708122101150e1c060501031502070201020c0402070c120b041e021e03031308151609061202040f030506162a06061d01060f020115031e05 66
    0x4d88034600e10401903200d41c5140c4014146900742c19100000b84030040040c4640c1d000c0b01f01840a0305810b0500c03200d15004c610200342100720348941400400859002da00c104140742d00040d040b01d004600e203c0c000f04a140d003a074128481c80d0380081c0075a22134408280c003810300350050405180503140700c2d2045c4d561442038006030205d1480449114111908000400800031742c0c5d8503001919620a41c036540b803550100b03540041810003d44000f07086600ca0b4000d5070104111040660b03490401782d004c0b0760710500780d50703550540d0100c2c2068003481d030b002801c00c13000f0361141c8040318030995606030700d649095001d0f80d9141d000c0c1c059040c50b80c2c00704400718069003044041e40045100718000c0071145481e486400400904840c8882081380100c803140c2e012002c0840d41c5100e1404498503032100b80d05261983c0141081c3d0320464145042100407480c110911910714100c0342251903a03203441c208080128200c902c0801079580c0c5c00c840401c140041140d5004891b010b608996086072603448540b605 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 712506321 1250 712505071 712505083
    0xc010e0108040812070210050106020304030f0b09010f0f0209040605190e0a0e03070b01050906090606250b01270905030409050606160804090e061302010e01020307061401090e0327030708 82
    0x1781015078004a143d41c14529540700e1740d8010700c8681301450800d0306564802001d4080c00788094002c00010011440c0180207510000c03022051890401c5160215000d03c8065000000e50903c00c501d810310020310b9007011b0103401c2e12070660401075100b41d420070090f0000700c08094100d5050b00e60b01c00740030041304010401414880d02841210340698540703000c200c03003d5402080c190040940310144800c68031550b09035049004482c060003544042400b030f03010b5500741210042e100101d110000070b0840101d071100c0c80510003c081c0080b03400c50103c2d1000561740001c0c1d0007000c0781d0040100300b05111065200c960803150040c606440c24803031040045140c20984000e80d456180001e0800500030913225175a40300c09504050800c2d031500f81b011031410243c070180a81070207a4180090326580c800c0c41150b004d00d900c15030400005030f02d02c0c5213810b0301f0b0090080d450058a85000c1c44080040002600c2c94400710344480000126070a00c4c0c030016100c035107281501446660800300d400c0c841407001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 712507571 1250 712506321 712506331
    0x5010c080d0c2006180c010f05211305010e0a0c15050c010c0207060e0301092a240210050f13080d02181305010501020703030509030a0b25020c010e0108040812 70
    0x74140d6080000b4603090700c0c03178120741800350ba50200590a0321640c0011030124480314504015485108844107440b40401c1c903620006084500e8040003200c544004035800000e0040f4000c000d0085460120340e91380d1083e02000d0a81c01e03038078030100082c0101c135802014100039850000c0c240791241841c035080d140101d000c034004d0707040340400307000380760384240ca4100c402c40440c024880e1104a03121000c07090100c15046c000c18102441c084c03950100d200100d4000c1603d155104e5000a0700d404001407040581003000050240c00c500109045050040f5401001281e1000d012900d40b40c8054005104400c0122000354060007007014078040d502c00f52516540800c0034032242c0c1c10100802040b41510700200051074940070052040303076400515002035070342c0746c00c1040c0d48810110000346000c08500c030040500c0013200800c44084483d0050b003030b000c500c96440642ca030492030402e90f112202003490500140d1035294407d59584540e4000b40c1060184003400d01e40b0060a0304090807000c2124 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 712508821 1250 712507571 712507573
    0x130b1f030c020c09060a0306020f040b0c060712061505090117090a051903200c0d0807020405160f050a0c0f0b0f1b0f09130903031505010c080d0c20 65
    0x100c0d00741c2540c0601036601d581c902202c2c00d0301c4a182500020f0511146404007810441d0b001c655160942c04100c102e501510801000940395400d015a0603600d04085501c0c500099501004d03602040d040d0180700c050303401e2f04040040c2030030b1460048405401a1600d03034104414200140701a820980c640ca018200307030f4000d4402d00440d0b00b00240780c0501c4c8105a00c95210494003203000c41e5000d01e14000a0b120650020601c8000715042403070000c03500740c01d50703001c480d450f0003004008141c0001c080481c8203071014401c0d03a80e202080c00701001ca49160101289120504881f454802c00c003d002e1041d080c10140200421900d1b09c080340000c5000031508440c100c0180070b4500c40e0b0007880ca60029841e84021030300d00f20040641901e000e55144203520707050220354440b07155201e100340080c401d00300a0401c400401401c004016140010704001700d0035030b80c0b00100342075109070b6500c0181c03904070583da0303e41032030040e008008214801404003040241c0e940c0c0c2e07100c2c201c2000c3e0201d510755210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 712510071 1250 712508821 712508831
    0xc06060e010623030a09050703120519030b1e190b2109190206071208071d010206180708030a030b01021504031710171e0705130b1f03 59
    0x186000c0e00488048405243d403030780b070392080629201080100d90b03101031200c1c00400d800699242452410b44c841d00000c1c221040c001809050b16880009040310350200d0300b070030b42c44c1d01e1102429400c507002085219041002c06013034a0004d0240c2d40740c1501c491003e0320002c1c040300850040c1e05004025006140034000000d02559890391003540700f5a44010084404c90340d081c0302e00c060365242d01e21002041c0801220405009640d1406e080e03500c8290050030b003e80003c40d1071401040d40000711a01408039001241c0c3c0c26410344003e001106000707042e00240384131f4440c0e4010442801542005c1510b40c8910103000ca0744060a1019200110464802266030b808550001e400c000e9600818541c01401c43d0801002c00e500070f80c0700224608488810840d9150212410b0140b0500e0b0020812202042c0d2070030000c020024111640b2a9251801c24021b154003001580710030035481020341c01941e80484040003020340d0f02150b00000002c1600170031001288040c52040d02c0000001c012071381c3d074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 712511321 1250 712510071 712510079
    0x90c130f0c030623010201150801050603061b18030a021f080a050c27120f070e010503031b0115031a070c150e07050306010b0403031b050309010f0c06060e01 69
    0xc1c0030714001d400c007909080c4425814004440c2e0124440c086407140b40a100244000310790003940000b84d40c450082c3c00c0c1065540b50011359001e4441680da5501900c03600000680040c8400c0c42c922271008541d41e01c605e000910044d0b0000c520f0002e03041585070207854540b00040e0f8410400c55207072040c0f000c191072801e5000704007408912004108420540c02c0070f04205031400030604071180400c103400140c030341400390720613103442000c03206400360000c0c02c0b010000201c82c40000c00c01118003200c0200e5038510b484152242415400b886900c0e0103a206100203103071003004011031012082c080b000061040d41244968503011003640c01a030311440d41e00301d00079080c000f21400e0780e848100380c10214555082540ea00a40c0c02520240d800f61950383d09050481c1c940500030200208001811148a96101c1c0008031180d07101d84421030110b80728500610000010070b10f244020382d000409503090030745103801507611041040700071081000540c07194000850b40c0c810303080a0702429151701415814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 712512571 1250 712511321 712511351
    0x11041e0807080703020a1a222c0105010e0102030715020703120912050c101a09370b040c020f0607020a02210a14010504210512090c13 59
    0x125000102c0c0c03500181d1040c40941c803000442c10440b030701152007000c00c81d00a148607003070b8040c43c181013107400d020715101d500c50301c50f0001e810191000104950038000642d400842c1c03074100c5105040c492075a0303000400035076000d070f110b1101c00369040c01030707070f240403480e0307450380c9450004545440c40345074003242c12010316a000710a5485c64458030020852032400d40c5a6038044540104c88000f000800130b040303010f1600074003050f1040c0909000510800301803000800c5a103003015905405890200c00066a06c40b84114050100e000106440c5042214000d00e101c6503441a511019240e118041d4000c07a49407407040e0b00d404d0509070f014203201600015960304000016045108652048030841c015a0ba80206d1000150340030010101c1d400c41c06840700d0400840000240c801c00321480303076004251040d001030744241d1103041c00e03c415100011190018400b4482a00f0004a00740500510003407042c010701d030046484400c40c1c4039100347d04005444a11210007440c8090f403181c0455400300c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 712513821 1250 712512571 712512583
    0x40c030b01050103050c1b010608030f030a0e01061d131403090102070906080d050c0f0d170603060705030403030203040201140307030c0813082706040b18030a080d11041e08 76
    0x107004d1900380302500305080444010702510040713001040d441081020300b1802503020800400020050742c2e1105041d03c4c41ca54950170441c0d0000c03056090400d0100200810b100700800c2d02c180f40c0c24182c420300644034051203007070b009242c1003190b8507490203100801c505d000140d80c44450000156626101c43c0300081c182a843c0d84000d0b07182e0704090381403007400000705c0c48032040560f500c1c0581c5c82d03c900204251522141c1e04c0c2c0710126005529024415980c480e10b05401201b940203840c5654403100c0602d941c3d1401100c4620003e10140003203000030384a60002e54000d40140b4050200307481500c00010280e01c00c1e250100407036654131b812220f294001b203801d60b224410500d05441c3e11840e40310354259128010100c41250800d0003610245801145980c1501c08042e003d152a5a2a4989030b80282c0c09800d13442040040c2e134100002d9443c0025450020b954400d8810381005034868065014003945140008072100600010075a10780390351032804000080040384540b2032500c0d0159081c48 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 712515071 1250 712513821 712513829
    0x141c020901021009120c020414010f050319120e0d0606081c0207050307060818030a12050c070c0302060a12090b100b2107090306020c06041b080604020f040e06040c030b01 75
    0x14201300740c6402003600300c8051000f0009608007001e0080c140c0c400140207003c0c003154040d0355203400002290780074803400c1200030340d8001e4003210002c103404a5078505c42007401c1c10042403101703000b02003890031b03201e4500302c0d0014101074030b031040d80c1110760388d19401d0b83c0c45c41c0c005550039400040742c6a11040b50030700c0d482c00c5880d1070020f4045030342484c000ca0f03250001070207a1002d009160010690400c0300c0100940c640c1c0044050742c0c1c80f030805203001041025081c5c4800310700c0c2e06000c04035050703400700c0c1c0480d4140c0d584041c0c2005d40394516070a21450360400c00c0240c0034405800e8154540412501074503610300d1043c4020315003840c01c1280d8042120250700700c1d00c407208003442055000d110781c12007080308140c81015204203580c0e1181c02c4a481716141c00084c41c00b030001c80e01415035200080c5550159200d0415120254200c51107484a06034a12854000c0e9120b0400300e000350400c0c0d00042139481c000350010400d0903990365500d01d440819601204e5905900408105210851003158090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 712516321 1250 712515071 712515103
    0x30105160e0a0810090809091f06210905010b03010f02030618011206050a060f06051c0507091418090706030b0904020a0905100315140907030b07141c02090102 70
    0x600d0403c1841542d0755071081000c403284c1d0ba6170100106000c0701c00d0540d214104024945d130b080c6e2030038000c40020700810b01403014503070102c041c01084840c0106100381c464404840f40710000c260420040b40641038011003034070303195030342c8142600300c0c1c07000e0103400410708200d100581d072403c0c500305121121499040030004492001d0040c002100350114400c4025002030b004105522404030420040c10107038015035510440c0c41d4009186904038014090040c0b06041024074404100d5990041c5e40d40ac652039000201c08680a008a1080c183c50882d42d880c007802d540b851014030300c14115100340a40b0080b42c25805007008011407503050180c1d16490300c05481000f80c41c20107034049601200240107007145d403515400014020700030a00904010742d00654001c0e40c5ca07030740c2e603c0c4900501440109509442d02c130000a0b010342e40c00241102100c3c3c0c8003101402e140c1e02d000c0d04440d0344002e21410130502008106191074041c4840145c041038103038182c0103964061407400a482c10400341411350308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 712517571 1250 712516321 712516339
    0xc0e1801050d02120705040609050601030b180c0a09080321100e0115020a020306150f0901030512130801060f0e01210303020a051201031a010b130501050702040605030105160e 77
    0x1d9072180d07040c0a0003140e040c0d03002907040f8031340042c2ca42071401d10340016070040d250500c000303050000390704228003400e42a2000c000480030310083c04031f440d005c00500c40d810010940801d00d0b206102004104c0c002007407822a00250301d90300c6850656000c0940003c2195400011800480b00d1000762030b08820344a02c4450450300e010a95071aa0805104241009956915044450f402801040c0e012a401425585903280603031041205007110309540b402030078030481111290509400090580b90480003c0a072584c400a503014180d0211100c0c1008900281d0700103500c0009020300d00184ca100d0b0361021502d400d040d4000980d650581c003505080025000703002200d50500c403045001501842c3c0940d0710b84501105a45900c40c0707001c0c0d000300b40c80f5200000140a04034a1145031240c07d00842e0a2076642c45800d07810501403d02c1f4441c240101003001c0040c0d600403002881c2d0710b44003801c0844c0d403e6a0703400003030031507000301c0e4071022080c4007034150884154030000d03400003124100c0318881 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 712518821 1250 712517571 712517579
    0x304060207050f060c0a030815011b02040b03010905030a091d0402011e02010617210702030616090902032401020d020703060b040615110115050f0607150c0e1801 71
    0x591001c0c544152800750564100d4035103291508011a03c0c0040f0030412184172400e90328000300000b03412591510103252014079103010f50300c9040c209401c07d030481b41c41c0414820a800300700003498100202585596200350070710001e81c5c00d00241042c0d0045480e024501c1c0e10381080120a0480202048811611101040010303a0402c4c8202507051505c2021107038041e02c14820790050030b80c0d4009480c0401d8195580aa04000080025448031580402991005282020240e60040d071000942c90740101c0001740c040c552038aa1803205082c1032a1010f065a5900c0a0008030392090341d074101d0003615882e210000000000c0c060005200070b01c0104140e4030558030003034403100c49000c01040d403506c4401600030355075a600041c0282c17020820194040b0311652014081d1840100d40b25642c1d42441c0c1d441c2c2008403400031201c102c1c0c0020704018000c0c2c6500e800c01c0255400440101d500c0140c0380f1001400e20f106202c1d0709041091a256030500d29244404c0104c80400c1c41081407411060f640140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 712520071 1250 712518821 712518823
    0x612030215010e040b01180f0203010b09150a0512040c2301031505010207060e060c0d020706090902070b061507050a0c171b0d02010c051501031a06091b0904050103050309090903040602 81
    0x42d0447d001000b5101c0805180c003440d401402c49500c440500d10700100c0041100b039646001032a1191003281c03414800fa44680381c0c00311034001e01c414100414801c0c4440c0001100c40c403100355101348120035a068140c1c40d0352003141d43c030704c1400c02c0103444400c0504012172542c00d842000ea000004522201c4454134200000f9903a030780e94005d8108120784199000d40c152600802d6400002e111400d6845806051030000c0da07441543c412440029694480000c2c402c0c41d6100700c901140d049a90302c946560381070180481e009400748205000c3e0810403800c1c012074400c1c0a00c03106148120300800c622440e000341d800b00542140d0760020550081c03076022401c1c1d6a0f000c03441d00c1510083e50402071400940c00144d5010304a90340c0504140a00c5400401c3c03550f03414800da0580c1d08c5410b1350452808085c3d034280084104461441d00146001c021915006146443d5040031107000c080381e10b001c000c8800b1405961007030307004075000c1c1d2000c02c084403207140851501c1e600c24040760042d420145009002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 712521321 1250 712520071 712520093
    0x606080f07030c0c020d0f05010c090b190e1e28050f01021501090501081207020108040f0611160209071106010b0d11310503150603010612030215010e04 67
    0x10002d040e42e8403201246180910701054241c0c0d0002c04401d0505000d06010050520032101203955520b0004159182402860400107546080010b1400e240d02a088c11000d101d10156020910812800f81d10150361000d0020780700139602c40c9000300c2d00e44071a080c400d5080d1440380d070b940c0f14507444030800581d000f40921881100e50480ea0001d002c408000140d083c064150018165080343c20004116140203400160407110900100c44031101c0c50010500c1c140610600203002446080c04140814800e017880f54805008900000f84070790742c00014040c644c000700c2400900d080c41c80e02e6506602e045014268407844c0c3d824071408034003c0700240e41d12200b050258241669001c00d85120b26110b40e400100c0442910302500c0d80e0b0010703d000d0002ca40c4083d08820f0717800801064034100500c100400c201101d4014000301411010310200b2426100c0007030015030150750328100000c5000c4000551b852041c000c4e0013820061113418690342c55840144c002e0210728a06005104c00a0300ca4110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 712522571 1250 712521321 712521331
    0x40c020d050d050a14090a0308131a4212030a050a051224011701140f0d08030709090b010504030809030f01050106050316080c04030221100f0606080f 66
    0x100055a80c4d60135104001440d200b030b10390b100101c0c40401c00080140015039000c04c24081d46030460700d0f554413940000c121a16010080205060510300940114250400e0790040e8084a011a030079990031a4496020502c003103011a150000050706104e042e40310700c0c4907a000c5c0580d028440700000414859981c415070801d0b40411a0000b0000d400d64407070401c3e500000e203d042542d146007040042001c042081d40b14103007184030900b0002c0c0300d030340c0109501000801008070006040e0700e00341d411510114a4032406400c419a000e01401c10768508030750700c00844c8203811980e103a00340520000c18100d40d0f41c018445079460040605016038100d0300780c4044a038440e010954403e040d5002c6030800d2545a000b00942d82050004540d107500103018608c10500f4407402001d040002c0e01c2282c040900f51080301040500300414009030424501c41e0400e0a480e04600071403640c500601781c07900460100c0030809941e58440e003005030031140620030003403038185446000c81c1840b0041c50700c90b03000504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 712523821 1250 712522571 712522597
    0xf070807080708040801090b01140a030221100c0f020a03090524030f01032a05060304081309050103050c0d031704050c10050309010b041b1d09011202040c020d05 71
    0x40030000c001e0100211040c5552000c0c0e00d0391125580c4040f43d0182809610440301c81e91b0380b40000c10101482040d92202d200001c2000c000c007031840c0c00b8041e141c80040310701e02c0d50b0948840e00b04001d40701080ba1310700d0303032000c400c000038035040b15a401420101101702113802c40d0050f41b451804a5070100980b4260f8800300d50300d40c4511500d00143d40007075611202c01810350401300410891455a05200c5e04903402004031041103008000c45030003402007a02031214030504076070240311504010018607800307071080401c246000c503900c0d05d42140584551000407000c0d250801441045018840b09030103020580c0c041890081d00e0750040e060101e4981d071440029681000070b4203010003089491124500541400036000303a501006115074803c442c0d000300c941c02c1c0b10030644076060500c5144402200d4160344031100d07080c3c0c44111540041003044c0d020500088040036070665503000316070b009000303440e40c001117146c0c00d10512054416002e500001c0d500844000c900041e040401c560401081034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 712525071 1250 712523821 712523827
    0xd05061005070809220c030b04050105310207050d0212180906040605040e011d030a09060c03050706150e1e0117211c0923011b05180102030f0708 64
    0x200104404c07030b0351080c1c1c020245c05505282035000da101d40c4240076100c4961350501c920044401488180c84083c46140c1c3c104214031031209549040003036440002895490034480780350000c800b601130f03810480302965182c01803d07203141c0d820b404002c1c030703091454030540e92400c240d020710b100d4051002000045015000e40070001f90340f9512a0702400c050f1000400820020545407609402044082d2042c00202800540300a100c5800010780e40f002200d50b0f64a461541090011030b000c28180000310140300c401e000c217400180c80c0b0f01031011442e0350900d1581c1142e2800c0041e08d04980c01070541304251910612408152035100303130450642c1d801181d4441540040e0740785506c0d01264ce001850031211019105d4443c0400f140240414085040c881425500714078000c021200b2405005101d861001003089590396100c04c040074500c0d44c103000103005e071100060342403203140c0001e5803c0081d800044150105040783310000c08100700b07100542c20140c3c8521510356038403c044010700440d8002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 712526321 1250 712525071 712525087
    0x120c0504060c0519050d02010e031602060906040b0309100c031a1908010e0304080d17131a04140106060e01090b1b07080f060c070201170402010e150d050610050708 72
    0x100840040404a5104c10020041d41e00f0081d40301d0811500200c015420400e04040030392000041c0d80c508042c038905104418010303800c01c03555500080c401600300c0d005100000d0040001e030040c40c1306806a501030400c0c0030440d4a00700031120040f856005040c134040a0641c1c1c01203040858400e42425545580d170410844a40d501c1030555503c400381a40c00c3c0503040c0c035404030100142044515400440e80340300c2440c1c1043d41c1c40c241c401c20340c9544000900014090608821070018510f000c3c100d001103050326441d41c2c441a4004075010703106000c0d040004201c000003449524002c064030b10f4102044512900000c02170569845901406000401e00004100ca8440ca0348040005a81110f500300c0c0c1e504040c50300c1d005e051820514034007813500000c68240c0c04100b10b6030411345c140d440130780700b05010003513119007840a001a4108009004100200d403181c41c0d62600406110301c01030346916600e94250252038005006900034071840c2028030714280c00c4402c0d500f185a01901241e00c0c4c000b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 712527571 1250 712526321 712526323
    0x5060f1b011503060605150408151b0c0105060109051c02130b0405011d01091e0c21020403022d0108090c06070309180504080d020f04050a08060601120c0504060c05 72
    0x328400b6403802d610080d00000700700c0350f0b600c200200c3e00203960b001c0c03881d0489800f035a03081c0550f209a42c4e113034006210f044125000000030b02d074000c00c0e100c9a40282520740541d042030b5040303402116002da41d2042401455a0480101001000102c0707070100c4280c142e528000b0a18164600203014101101080c001148141c00106050002420401041da5079a00100d0700c4010701d080859580c1e140c50010034441c0c03450041050012400ca80310611a003401d0108000f001400804010804004050003481c10417605100b01c001076010003588480c11030041010140c0c00244038081204a4a0078500e09101c090807000c05943c02d0800110b15560801510308100f070801196600c11000500c84041540200d45801910344890034410b0300d248249010b000c80341c0540e00604001400e0041000c0040c5640003052900301703014115003880d560f9004207400b14540d401540c0c454100804002c11941c4c441c09040544213120010f10bc06100341c2d82c0039107244158013400c010403154089a00c00e001c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 712528821 1250 712527571 712527581
    0x50f09011b050312160c29010b2104020306011205030f1908091506220e010c03230a090602091009030c1505031f03021003020705060105060f1b01 64
    0x48040301c464501d503840c18036203e07801079440180080b100004101c80d10303028581d00d240d9880136122000c4640312603c40d19030302529400c010b0b401c034070b05559581c0c4190101c1c015074020650f40300e98644802e8130f440c2e10131640300b8250b10916030003811410000503941c0018010304480c02d030129415a12001e0500c20b045200d00c00c00c01c4203420380000c8804241d201048940c0902e102c5a032045100d8581c444851f0301c8400c0b00200c40e00d000c0191004c22100d2400034607005004551000102800c0d0541004400380c4114900d5550141d40d41c0400b00c080c0341d054000c125480304411050311007030f0080c4045059100c000740940c2080e503652400c901c00c020b81e0b9811180c21400c000d100f0000b4121959008151449034007040f41d0405204400140d0110b48051840201d1080d1f11554110390780c10031100015403ca24003403030201040d490000150f01c40c3d0300d080c00c2c0000c4694001d40c1d2008241021450a003040c7c1c00240224002c02c00710050903248819164811640710740701d80c07510420108180900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 712530071 1250 712528821 712528847
    0x1a04050405060604170c0f04060e0601031505030114010302100f02250e040f020a140139082101050d060b01020a171e1303120c050706030b0405090d050f0901 69
    0x40005204154200d00000d500110100221001c000542504023884152050b5100d468100701d44540032452640c080d8001030b01d0001d1592803a58103d40c0c410000c0d080d01d2035003580e482c3c58a6607100500940c00d018405283d083e64234100700600b02520b40e4001e60380e04800c003500b48000c07074142d9006200d07064162814010a5a01c1042c2c03030306d0404c0c3c200628420030040e0200d1203525000c1d4009038003990305141c5a50808141c540e11042d0040341d0030004000d00c4124034003581751005040c80c5208250b140091040c0e0300800d0241d80310300740803103084900300580c0d40030702030241c03042c00402442e61841c061800c2141d01031000b1959034503250050345450f2460500a140f00c05524944000100a0f0080d00c100310980e4001c45014000406040c1d0a104441c500030310800400c00078404200c2e0f08100b02002c2e00240780c10101440c01e47c6070f40c1d04102082e08014006901d406100c02a441c041c0205500f100c101ca01401d4076801180001e000b5105e0048500c4883c500031404060030380c0a00b00c194926 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 712531321 1250 712530071 712530089
    0x9060f0915080105030f060603030f0d0e2d061312021519060506130b030601020f15060907020303070f21060f061808061306020906130f1a04050405060604 68
    0x1081c0c0244040e10b100000d00a035030003413084540e40c3d000c0130400280360f8000c1c0405006140340c0303584071520000c50b81c0000311141da840d1325031202440e421400c01ca06a00b0600c041a8074400680034081544a5600042809155031000040c494148940200d03c5101e81e8041d0354105500c44101040c0d04210300c259420020b410301108010406400701d549403035450707600c0c1c0704024458480302040b0b402d0040d2040c000f8602c101076000d01c4086130400096401c0706050040301d40303072030b80c1140c20303850120141002c016041d6401c00340445418100340c942d0708a1801c0c000345055250229000380050080c01c0d201c4100f0841601d4040401c1c4030b0400c001d90496107041c244001600e0300c81907414003c2520503240050201c18a04018211b51014101038034001406881c56868800707404401100300c80341566555820031101040740e80b04801080310cd036490b0410102285001c10a10420a95600c14402172254901c0c107444104007104a0302601e00844000800c2d0303caa43c04502180142e410404039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 712532571 1250 712531321 712531349
    0x60603090304090f09020d1401061e0b1602060d09200616031e020a050706020102070c0b070305041706041202030a0c060914010203010305070924210b0c07061107020109060f09 77
    0x340060100c80740402c1234490020311240d035403003510706c0c4840020260420340140249082c04901d040304000c0071014040c41400c1200c80c541c0d00015116800240303151a01aa070b0250001004258030040000c00b5034400707070b5048135280c0030200760709114600701203c112208585004c01c240c0500248400c3c0400f03101e1a0b0418071001c84065514207035107074241c440303128611001528074030500840d522998030280382c00c069850161030b2142e5400c81e40084090000a110200340380c0102d0718154101e0645400a140700d0629081074029540108540c000715041001049150794000020001d0164400307030001d50356035981404452000303094442c40481d4000800003090003400034100c8140c80726150200700c4450080200e811b42c101180420100c04030303800c0c0400c0a024031200034244400d96810149003040386641e0606022021224590080d0000c902d0344240503a03849400d085941040606107401200d80010380505007a100e003d003005500031001c0407035403190011000030f150380300810007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 712533821 1250 712532571 712532573
    0x7050f0a0324050a0c0806090606040e0a1107110103050f040308181906021b0a02010903031d0d0c0f0b130e0c120412081303090605131d060405060603090304090f09020d 74
    0x405032542c00c80c18000900745d0808181c87c0e1911407001c5005110003402149800e1400e15182c0f0010b40003012800b2555946852501d00e0006c10001c10000b0700c584980982401003a00150440790701030641402074000c2c00400c80066008001c03203803c0085503c0b44104c54100034503a41c41c0c8080d2046500411100e0100102049080d130043c01c0130201e6440e01410611034010f02d256a00f0341410081c0c0002c80350a8104040380c01240000794038610b1b0a071586440c0303850004901c00e0b0740388080440f2441d020040c10884900e003041c00c1c402a2001403411490541108030301160140b0354010505410617640104443c00c0b07000007144c00c84441e90504101900d4103042c103000d0400c0244e43e07040400c5250000490748400f94400c40501a030580b210f2504a09000080b18150860f02043c44241da45120100300003012034000c810041c00d881803080e079490b059041c0002e44401600460003507001740f003804840780d03000c01690181c3c2e120300c900007070740e0f00c640c00c2d044068003940201030740004102a03200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 712535071 1250 712533821 712533841
    0x30206040b0706061a030f0a1b18060c0c0b03280e0105181b010225080f0c0607030e0105040e0705030403030b030304060903080f0c1603030207050f0a032405 69
    0xca020f40001c102c02903556403c00920905000a9512a001000010407110315801203c0d0808002200050500780281d023407890340402c81301c0100410340c91903ea440e8084400c0119018000500c0c2107501e17a02c15954046908256004130443e406001c000a9031f4491106500c291a000000c07803000c0301101c400d40c50780104600b681c840d5640d4280400a2810240c01d03070036444890301c0000030100010010313007201c40c01c1c1c400000941140103e1000000e100c1c00700001b031081c603141030810042e0368501203e0030705c2c3c548000d540c0c616a800540582d4904e942d46800e440e0380d5a0503060605000c10480300480d40c81c490b030b81201580300b409038140034006620601030f522981c0f081d2410070024200808140d540d00a0f0300c210f0000841100342071000412200203001182d1a002c412814030000c0d081190a0034410801079000481c0c49804205166040107050f0090000365405500400d040b00422200314503030001900c2c80b20400b2142d05042200001d80d0680070015208200328100340d001c0d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 712536321 1250 712535071 712535077
    0x22104081201121106030405210a020f240a0e030412121112090d080d0b031218210111030601090b12071412040503030f150a06030e010204030206040b 66
    0x300403645400000f01e030034101c0401601815400420740d1380810303e081c082104503400104129a14028500001d4400c0b20b2000f41070580a060300105c6d4440206c1e810003481c2003002241c00c03040d41c3c80120103c07601140c0092101489001d007103101c50582d10025210040c1000c2800806c0390702c00020700040d00a560b0401a130045d01c0f0345069080c1d40c00d051800c03201c401480f21400c00303a400180464a00703501c038100405504602030f202c590202d2494540f07403143d8115050000d841c07511941008003900d001e0240c011206046c800c90750803c9650301c8501c80210300008154002c2034014610710000003d80640046070794600007d00082c5540c00c0822820740098500c179010031282c0d0740c0458030042c84400d4612540702071a40c0031042d6203040b0106c078500030562400700304010801102644085503602507100e2401030700210b40da81400d07940c4251408008201c2c2d8446070f0941c900300015641c2400c000200d071184e2178085500205120f001d802031155034402580003600060001c3d001800d4005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 712537571 1250 712536321 712536337
    0x203160303090e010501021605040c18030b090105060d030c1b0312030614011112280f020c0402040509132904110103020a0207031b15020a0b1503070302010302210408 73
    0x3c0c07144203036030721801a42d55060007422034a4600d05090140124107003a4000014202d852802c3c440411000320301c03000c144101e400c2600d039002d00a04200004100340074080d04500160356100382c06800d034600030034035200901c2c000e00022200001c5520024150460000b542d001040e88040a60304c07517001d001081e05118010b0244502e080300b138265070003034012880c551208005072044030b20001a8500c1d9a000d401030780c18030b0785d41c080003020010200c40302e91854901c40d16090f100c0341c14200080d00c1c01c85160070703031442603004000612882d210390903100c5d0065600d0841c18090340c40303440c01c883ea0100c100c031020344008440751500c88080c0040e0303c5900650027031b015501c01c0310f4640d0045083c0d108070009038006d13030f2001c94100b00180d412080403010313401140d00303500e96a460307040c09400c08030182a2200140c0c011601d007010300400d20503641d0000340e032402c4c2001c0440c034580031a841d1307000f07882301030305140d8042590151048041d614540f45031408811445510306031070598200c0d000266 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 712538821 1250 712537571 712537589
    0xf2e021b03070c05094b010e0604060b0d23090c010e09090c090a02040902070305040e09060106020714120706020d0f02030901080612010905011d100513020904020316030309 76
    0xa60b1704000c01d1090013180c46a407020075640d00305009103a010300c480c48092400408030a20483c0c50b441d00f84060b00414641260919035251600c14080524042c1c2814421441c089040080b0144442200c2068101d10000b10b10710200040c010800c90b44031071031070965a880c1080101080d008590010051002d0b2102001d0f40c9841d000c1c480e4540c8200c42d0460b42e07600a110800c018038000c2641d079440801d910000d840c00751150300c1c1109a8101d42c0088010980200342481400c0e40009010b6211107244002d0072950314213013000351341d011a8451a1900c0804041c1e0100913290562030034004d10f0301c1412541c003156122002562408190070f1040003844441c101c0d00340c11301c040120f46015105940311a40b0341c039104108061000640e01e00d0403150350720202c0100094081c01a0b00c10011905440c10790b00d10916842d5052100c0310115248061500003042507200040400180c501d80542c0d50410580d2244042490301190f46003102c44881101c000204155000f0741e08000e4071a014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712540071 1250 712538821 712538843
    0xe0115030506091b060403060902030709020a02150c070c260105090c0108071d09060414070201050a060b0a0207030b0c130306090c06030b1809031312050f2e021b0307 73
    0x7804c2000007003814880c3c2540b00307908200800201c0c02070b401c4060007500050550325019074695081c422a8441300c1c1060240e00540100340354103018844e12644058403141c42c03031a140c11503480f820303040d640b07000d0300300380078103480c4040942e502c240104582c0b00d1441c002044142042750303040f40c4d98a035640341c0c1c40c0044c40e020b00081c81740d44a04054111704841d400c0d0303506082820401c021842c1d4000746000d800c180e0342d818554000803503640e070601941c0b031a000064a418608800002c1e1202500a801501170411251301441d44c00100f80c0d045070381004805c1100c1d10f44022100350b511032245810305083c130b6400b0110074045113a0241d0318192003404041e4200f540d500b0180c0540d400e0080701a07201324401410f01e200d5109045041e0711015400c10b40c2e213401c030500000c3d8500c0300250040440c21110003c030b41c0800c40200b002c01c00d00381c1100c004000840c800040d00c10041c031007010544184080c1c07410001510002e40540e9048450380030321142c403405614445a0325042040156510b0b0310130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712541321 1250 712540071 712540093
    0xb030f0601030b0a0308092d090106090807090504051c02072102060a181a070203060915010b2b0209131a06090a0b0c0307030809030414040e011503050609 68
    0x2e40315103490b64002501180c81c09145484407540740d0407240d041e68009003803000000310302150380362400f003c1d60000a200d13030303000454090100701c6005030400da0a000010304d00340700c02c2000041c01c00403907403c0540800c1d15a101d01e0654104100c000c0c02240171030340e02d50040340f120380100300c1034261003009441144902c41141d10658504c03240c08080c1d0001030400c4050031840c8558155040c45001050484031f0a68a648401d89240b0b8600c5404a4150118040c021864107002003604025040010000320304100040e101c80d81f41845160810200001c605c42c44401c80e011046d00201c201c880084a0001c04901d030011390300c82030b8541d20604614070011080c1c0b089102c2c454090505642d0007045480d064140000c0380c0c0b022040c00d501ca16076510000d8104a80d4005150781541000616102c5056250160254102404800c00c5400078402803040c060910b03500551033100300c4011507041d420301d0310140100504e650340440c03150922804000c6c040c00103030703660082010204a44404800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712542571 1250 712541321 712541327
    0xe070503191a0705070b01081011041a09031005071d1e0114040302090a020c010b091b0703090b030403030b0f220207020102070b12012402150a0e01060b030f0601 71
    0x55500010076114010201d810280400802c030b80e4486054202180341290948a00b11008400d80c0715628513030207550400c503c3d07401d1340282425403400c129140c1c01c0034141482240301a41c6503415001c103200c04150301881d507800f0020000c809002c55001c0015040040c3c8c010510703018070405201045890301d801e42203040c6401006c101d058a4031207052007042642c01115000320b2410200341081e0144004000f5030354000d5a06c1c05440e0b04400107940d03070315030380e00c2c282540c16404186103d00300c1c8208004908001f16150360140031a034402d2590390980c6d140a444021303c81c0c0090341d54000201c100010180c06a2154aa03200119004411050f1a40030843d071080c4200c0c0704100210103064640703412600d1303001342086078814010355602548030303211084107400c00c07008400c00d2044400100700b0401d07400c0d40500184400031315444000c50508000e5690b210241c1d2215040681800054407042e0b182c0c040300d02001114020b1051542c2c3d2a003174802a0800d44a8042c480c1000c00440c502e980 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712543821 1250 712542571 712542613
    0x210020f0d050c03120a240e060405040510111b06190b01021015082e02071101050a030b030f0f30030a1503060903031b0801120c05040e070503 63
    0x110f03d8011891710200717030210795400a000d050204960f40741c40e03c400c091104007503582d910180706403615100600e400c81501e4210005481c0c58010b500e40001d01c0b0100d01c02041d03a070300d4911246404101c49032131440380400c2d48078005420036440001300080c4114580880d01c18001c0c0a8a1880c0440c1d4000090240c1100d4941e001c0c0703400343e0701414001e8101862504802c0724030506e00744c601d0420740c0d030711503050601d448007400d20040c00c810b500c00ca0544000400e86207445200c20030031824082d00e9030340c0d0401d540c20200d80505004011611f890120710980214a803e00082d09448004140f10540ea5032149403410142d40c034010282c0c030040076540045002e0300e401d10801000c6000c1c107489141d5020b584050483e103851501c0b2000c64a22914a1520b07000a600c00d800015140d010b41c103000381190094000940340703a0300509000754070f039408040981501c00070034400d1030014a13490035181000b40d580c8415002410048042d18035400400d00708104c42d4154190b0b10640f195020f4803480301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712545071 1250 712543821 712543837
    0x31e1302030d0215130201050c031201081b010e280602010c020f0c03070306091e030203070308010b0909010302060903011e02030f011d010905070903021c02040f090b06120a0210020f0d05 82
    0xc01390000164112240543d80c1290743c3c01030510500d82496400903a04680c41004049451600c0d08010080540b0410806060852071030f5035904036413042000a241c4040a10038510401c0c0a642201082c03400d140e080c07524900e0b02c00b10382d82c0e8550b80c0d80007a0191010000e4030000d4054501e12950016000c280500b0b00c5c1d800801070402207046940c0c00000340b02e07223841540c4140f59619400d40340c0c0c80c80806000c14074040c0c1c0045450f9000c51034020407810b41600b001e02201000d008280c2c26450f0b209200b03054031750440700300b030b101c01458021a0040208180d40a07103032000a2000460300c41c01d134015230207034000820159460b0380b01c3c0c441c6611034002c00c0000407020005401000010042d500040e04050745203081540c0640d26000501810a40d80b00e803080e14500000034411841c0078400c032180c0d503e40c02020303c03404040341c03142c603045100101280d0240306241402c95541c50244502c035821540145014504449240002d40d1680c01034003a002134496011890f8420b030040c020f451101e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712546321 1250 712545071 712545103
    0x3150603030e090a151806210303240b070c05011704030509010e060a031a1002100e33010b0306060d1e020a050901091d010b031e1302030d02 62
    0x1201c00340c400d0014003400100070220313072035846054403011044d40150200801c8042403922030801d140700c5400032205241d0001c4c41c0188010410b983d0b2401c0900d100c52129013508000840c804458025102c40785808041c0c000c5030303001e00002c00c061a196011b07111060040d0300800c580c5072154010344640308203607000b42a0060310800500040c0c850001407001200600d00b038540c002040010074503d03004403032200302080c1c50303801e8882c0550b1622040311210908070790a00c0f0901e107400029461300d1240c06426a01901d07034158a03c1801c040181c481451072480f00c010071002442c4400042d04607002d0240d98268480c0c0000405130f020400b580e0182200800852814880c140000020319003000301c4881d00d4810030380d103076020781a031000d414442c50301d40361070380d44d2450b450005000316202d4001014101d00403030300c02d06810840d00d0150558040c109066900d07101c2c43c1b100d01d0700120500840000300c40c84402c10004036000352550051a100307400f2140c0582843d0310907a11148044403502003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712547571 1250 712546321 712546337
    0x1b07081e0a0210030b120109020f010f0908031614010b060d020d1d0c0a1a030f1b0a090608181c12090b060f03061005040b011403040308010315060303 66
    0x152440300e000e1024010034541100c9040600340c1c0811640c00c0c100c110070000c0b0780d441440708a10704181c5203040381d850611008110340e02c039540c0014901034101a2181c100040310317444031481d074000e01040015188240450f17031605c08542603440d091561542c1124203209294081601050502905654200042c85a8142103040507010000e402030076a94000d95150030300105107448840c14180180d03504000b17000386c50020024400d40c01090350001c6440e401da194210300f402c401105a03a00300748403c009040540711306840c0d09000c1401910b00c007001900040000d04680c0208078542140c40f15200e2201d140c0e20495034559041003061070230010303081003901c8903e540c2c90300c2210030f0300345007403c180b00c180c1c451a0b400000c40c0c80c50102102c2d031176060406d0001c40c0c90040c07022440341102f10001c28036458113040c200240f54882c850320303004545510a008481c0e0052003c181131075480d4810549070300d07081c100202070b01001e1000b0340d041f115000b20442c40350124081e12003541c0d05903c400074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712548821 1250 712547571 712547593
    0x12030c07120504051306080c010507020f0616020a0609060201050a0e030a0c171204020a240c030509090702010518010209010c0b0c0f072a0f0b07050f070b1b0708 71
    0xa0101c20781468a02006010840802c042c0e1700d5402900038011504000034019060561491034929442e1035181031003003e009040059942d64400484d6000644a964464040c40c1400220b06110b250086d80b2400024002c02c03850340c0090100f0450b400740d4002d00007501c45850203812503a1405529101e500100300c1494902d005046400450348168083c80e0ba00a0f22820681e42d600946045001114078006000c10341c6000c0b01d10a000c5c180714001c481d03000011408480304101c051b480001444000c180308001d250148069801c40c0c103003d442034206180c581402030003090111403035000c2500104035110451340510946400c25010317100d00240030050349901d04c42030001001c40000c1a002c105d181070f032041d54409070950f032b17214411070303601c80200030100700d40341019011206052102ea10200040308d0405295403c072929850302c169101603030308003203061880c2c84540042511500000081c203403c15402004e0000c441e4841c015900044176209894070414450703962103900860b2000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712550071 1250 712548821 712548833
    0x605070819020a110607030f0e030306010504120302011821080603030d0b061b030301030c0b0304050604061e15080c011706090903040915031e0507060f0e09090f12030c07 75
    0x104845003410095074501301014894600a01200e0000010b51104002c0c12075002c2401001c2c1c1c102c1c03814010758114a45000000d10901603803060707501e01101c800d0303200b06060007075000154250b21144001e800c00d8040c1428042c981d90b00c41108a4030524160314a609441140304601810004010314030340600425400d000e071207450b900d15405003040180010621509021850049011010f151a985103080c04009401d05921981c0d880c0001c00c200800100046051a40654411800070300902410046140c4405c501c4502c038200e0328002c2c0d03400f44141e10006072400c80e0210421500080002c1d401180c040000e03084180070300c41000d001c105140740c100e02c0c161344039018030300312170a00c0d50b944c400760182c3e0614040c110b003220307040406005002c41e408946030380d4030034031642c0d01e034540d1160345e0369968441c603209210070022031900c0c04014038410100001c44601c001c000c507140d13050221040e6100c03080c40002e204544107a0044960303403101d410a403440303140c3d0350f50f40300c0c28007155032114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712551321 1250 712550071 712550077
    0x60204301a071808100e070b0a030515120a0b0601020f031228060806071b0f020f03070b18010e0a0317070b0a05090f010e030a12090204020a0c060507081902 69
    0x900707018500d11003d65412940442000800385500203180d024400d9220740110350610fa0080855045104107002d60381c0b03920101c0396000b01074500020207a48940240e501140d04e074030802d911104200c5c00107106000041c0240041e4060107072010241c8503100166598140f05043d1a40e541040c4411604030500206c4540d10480c0590210b403810800003103208941c00b684000c542c203598821050003e05e004000440d40311200d41800708a070409061806001450031600810131101c16984404644944e0594410240050b040310061a240c040c0d1122541283c103900090345050050300f50550b100340c0484003440000340c400e400d82030454803030301003004a152070155441c404000c0b58001411096040c0d20407003c40d440000c0f2800c152402c0d6040002100d410707a01c981c1040201201c0010200c125021b00300c1a0911003485d00280ca545409001c2e1002d000c0c0d4403070f202003481c600303a54000002d000001c0c89a0020000b50355600c50a95130481c082d104024441c40d881400340035003840d6401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712552571 1250 712551321 712551331
    0x24050607020a03050307050a0b01211101022b121a06030a0209090a1a09040c061101180308220b0c07020d05010603140709020f07110607060204301a 65
    0x10503002c00d0302c0e030710340a1035980202400c039480e500c1b001d096814480c2c0800101e0262600040900118021181107020b9548001c03000e0044080c094004107680c0c020000b400a60100f60749500303800d00240d148101c1d4204c002c04031030215152040e081c0d81041c0e40c0c4100011141000e00c40400d9880060910129400080065a106508001c40e01c8646e640c20160303441200d4501002c100400127460340c102d0607101071080741c003c019400078803000480d13040d003501c155081d80c0b07440781401ea120320035540584055040c20043c6400102c05c101070540c0004030511800880d0030071508035641c1b24440c005c59001c1c0c14094250419003001c2420801c5010042200a000030400320f40661203880ea64216440342e4400c171810320001d0040342d10079906201d66001010f061404608124110f007211100d44240480140a0008100c045089a54072015500c0c106d803c040119112900d51400341855041c5040c00e201560a03200f1078900c018117640900c510650100850361240c0107860404030800e80509 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712553821 1250 712552571 712552579
    0x80901020a14010c0f03020c100b0d080304080c0f0a03050409050a0605101707030b01020c0d050a0b0118060b0301180902060903010e06040606080c1f0207090216062405060702 77
    0x400700020910110201202e0762108000050300b004489014000c69641321030700091600500c1032030742e94600030810038000c400300c032008078008031844009070208802c050000c02c684004010310003844140d001401e6003100a00403202501c401031051551070801d08001800103104110038000074450381c001641188942001103515a100e40005c0c9118141d950881c0005487d200218204c00c03250039000e4120303043e800d0411841c0c0d800c2000030340319601408550300031401e01640c50308004040240c06029600912040d0a41d40c4590186504c507554407042c1e065a802c08401003803540f0904100c078102c400c3c4545038540420340c903c01101500001009076403014040c0320a0b0000e403428050544400300c501c4c05091b0741c0c601440c140c01142c505810a519030b278400070340e0b00d00a49610000d80c4d450f00030303400391502103030b1603460880c5801ca094124203032075030002ca00c00800208141036405124030a480c2440310848100d0383d56480c1100084104810140c0a400c11140c00c0080c014424030703001074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712555071 1250 712553821 712553833
    0x29040606080a0b160504150c020102010b0a0b070b06030307060504051510210c03080a1701080c010507032a030e01020f12030c1326160302010e06090d02030d083108090102 75
    0x125107c5031018108100e1001c078800b000380200710b40e828490f06024040403600e4101550401580d40d543d40940040141042d11040104074965810001e075500580e02010900407468545002600c5018141c29595100388103008240c0c55a01c000d001815100002c41e10307008080d05c44001c5004100001040da050030440700c001c07002c26025001003004d249642c0300c0e070a0000350030240d206542c405034001c10303030750304095000d00d50350b80c0c810220360000741c1602c2c00030104100d030140302034400c07650401c40846560080c0c03824101504142540304800d0240c003070300c0c0c2a052142c0c4603503c50204103094a4250000c000003407048000c1005002c1d2a8100c000584502d0b0300c80210186d550310a240b0030101c4040001142840c40c410003d82c8040700c03c0b201d100705402d00e1039001030949601c3d00340340c0c0e02c02c0002044801103521041c03030756840790382c0040840360311907100040503111a20544610308000d04561103448410045048401c1c861202c0b45000c80e003d0543c1c4860100c0d4000d003031000c0c1140510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712556321 1250 712555071 712555079
    0x503190c02041103090c04020903340311131812050417010e0c0d08070b06040902090a09020108061002101d030f0a08070806091329040606080a0b160504 67
    0x83c418488000b50761000c542c1e880c18100320f094a00040d004081c3d21503401007100c8001a10003154220000c0401c0b40c145c0218038134000441e00040301c501c514481301c2503060300001400368150101121040607a801c203c20003542e04550f0640d2070f00c6841e07101000390b04007803000044031000000014079652416605254654010010040317005c440c20320140c4d150f03900051215810711021100d0141200d0480b8031103055940c4560500074480e0290110443c5070000b000758655800c004496a4003c02d030304642e00c1d103204003c0060068003c01c0e8000b80c1540c0001d4420b050080000c525400d054000340750300c03040508850f001c1c00718880c0284140c00781c0c226400c200441000a03001c004140396840ba02c60031108001031542000500e040c0800c10303640140003c5488400c0c1e459007000d00c01442e0b40303484180d401c4c40028060103d5865014489007416a0b6041d80d210614602480c8a10002d11590755204041a07841e8003041000c0d00711540c20b8086041c149001e01d0480104901d07080c0301d0f040c540e407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712557571 1250 712556321 712556329
    0x2030c030a110d0503010e01270f050708010816030609020a2117091518060417010e070501020d05070303110d0c0e010f050901050d1d0f12070503190c02 67
    0x4018612404600580b00ba040d40c14030500c41e000b40007802c0d1908608561500d2808410202d062041c0000200d00e4941082c2d0f540d00c058403040545603441c0244901501d8032840b400508007102c0f500c002911110022458200210b00400503139072034a1074180860954031218014480044100e0344890740c0300c0c0020351a0f01304620345845603003401380500000d9880c20030b101d01c610106030880b00d0910030420440656a9819014054400003140d00e8941000044c1041c0c0207545842c540e5020030046000102c1c460101200442254424000e10414080650055948400d4000c490150b0803c2c0d490481591044002d8024035020785000701d11030074400c0c082107681e8000c50074280c0303c0b500c4040c400c401a80044001c0d000344401e02c4d00750a5251040802402d0f402510100c030304100d0001407414160401c6d400900e070740004030140360f0510070400c00302c5540e07100c2c400d9914500c0c003c07a500b41254600c48803d0703994980d00100a185001d00200c22400542038980140c000c0c040824110005132719 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712558821 1250 712557571 712557577
    0x60f0105190323040c0b0a051b0705040605040213050103020903160e0402040b1804033609061203050403020609060706051303180501120c110312010905010504020903030909040302030c03 82
    0x2641c0700019600c502d43c1d0100040302ca840b0700d07003480d03e240406001c00a01210303400c90444004102d619280c0140c800100c90714031540503041e0f001c045140440886400219800040f103104440410940790385100780300070380c000c1417511030300388003106010026940030750020710307610800a055840d00c201e00c00801080702195000a0b0040050108000450505100740010341c4c40403511003a006410710000c0c01c0c0510000c1004080007002d0a10610480c841c0c0c0380a01140c070f50f01600e00701c1a074450079a107400e407841d2040c0e13011181007440006500e8021039442c3c00140c3c155940c80d2401d410341e02031040a5200807076003600010308010b02c0c000306440f8443c7c04c3c045d01e001e40005401040300e080c024901501603001c892402c207000da01f0442d40e13170007043c510b611030500f81c0d02052081c1124400e0701c1d440d24907015280c050100140d16000000c0c100c04031410b0b6559510700b04400d9807100144000c9021341415036415070320401503d10030303140444510354020310a1049a01e800f040d4042e50b400c42d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712560071 1250 712558821 712558867
    0x91508071e050405430c050601170307080c120a0e12010e0d030906110a020d1106060f010c06060f0906090b06070f1b0e0c031f060206060f0105 63
    0x510401075090031040a001c540340146000c039414450f07414442c00c540f032242224a207110400d00348603c5509001a0312031035580018a074458902005c828000c09040302c0b0102c10112081e0155038004a10619070001e2683d2410304c200003941000310941d140740e140d034400c101d8103140d44251b412282014440000038200c9040c2a5134411096840605000c0c25107401265480703580d041c0900c09400402c001403035108001180740100307904001c0c0c1000300c010208031418103001740000698000981c2c0000d600701d5080da1907594805505000d00070562680c07010b6a40c160322014001000a056108900c90040c16010b00d4000401c40c3ea02c2c0800e84284000e0350102c84e006864040400400305544505074080405031142e500e003210303030b0703a60703024071454840001c10502c001c0e07110482000c100510b030000340c20004d4000809040c01035a0007082c1e0070858420b0b000d5078080c00a608600100a140e4040b141c03641c000f0912611080c040080041411000360704100040c04140088500c086029101d0703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712561321 1250 712560071 712560089
    0x7080a030e010b0901061d060d0518070f0509011211040615020114010f0b0703110105042001110d0807050d06030b100609030503030a0c1413171609150807 68
    0x38071111101c00d82503c41c03401d9018420782075607004201e841c0d0084082540c5480303200406030300302158000128603008665102410518140400222045031400e441590300010204c0701800d40d107501c0405048014054190003815400041180b070020520000409100b4a601c005200782000400d0858449a00c4040b424507c1c030100040e854081c4985050f241c0c015940003529810103402c00240341d803510410510307440001c3c1020506100fa003d00020700c0c59200280308c02c0c00c040c10310054203068104074001c200040301c140f00b034542c0201d405140c1d86060784c010b0510000311035004d8a000308024901401c0c007004100143c04200148903280241d80700da07490401e5410242d0102c502c07001b0a8000c3c0381400900d06c02840030403c0041920b82c440c00a00010540075404007040b100503e42415000a2031808500d00c9400c048006078802900d554642084403038004d003204554441d540c130840f8482c40076030b41c8240700b2a041504030410341040d030449100701c0350b5036034140c503e8040381d80c0c000104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712562571 1250 712561321 712561331
    0x30303011406030a14190c1b0809060c030315041503210e03070810060501050301061407080702040e030a0212090604060804020f09070f08061f1b06050709061b032307080a03 76
    0x81c006d441c0300300c000c0303509907290000840d21282c0003c90f40700780c8103001802400000c10b0140913550340004072a103d54194080c2c03500d80c10104904116086080000d0b0311490400c264520707122030b0615000c084907004a101c40716502d01c6c03d01e16545440540d1101c2c1000000032044031651030030003404004080c001c00a003003041c81502c610040b00c10719001725041200400040014951040c040d4611485040003143c0d16403051404c12014070507800000e41090600000d5880c111010001c0e0401130501d400b5285001c01540c1401018071501c65510303031003c8184001d0140b64030a00c44942d2140c8080c00183e40c45107903800288070004100c500e4400507000071892100c095114101c03541001c015585a602d513200040003a010f80030711690a0204810440c0408201c2e04c0359590602d4103801050400043c1401032006001080c14003402c404201c4503148281075000c0100141c2100d9003581c0c0d20b080d0b00545445911103c029400c914500600034070100001c00d00c2100109202c1000b80c900141c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712563821 1250 712562571 712562611
    0x1801020109080a051605071e140a1701020903061608060301050403050313060e060901150b190302031f03050106050f120604030302090d05030d0605100305070f0807120614040605030303011406030a14 87
    0x4260344140c0080100315105212740c10ba9403078200111080c1c0700c804654500c2c040c1000312050080c0141e08005a0503c503090130b100603010b02e8103410341442d03201c1e610004a580c0341e0742030500342c4070180c80040004a0810001c0c901406d544005100175100344008512403590549443c90a41c0680d41611180d560340b904919070001c0c140d494000742010701109081550805041a0160b0810001030038035400100003841d0400c008850700d82e648003004c5500c00c960310381c1840c60090044c0e000d054010181100c0d0070341e030781c905260344d429054018001444140d80b01c0d5000c40107508181c0107150440501001800000c0e000d01c0501801c0304034900010701d031440c08003041003146118411109161a1400b0b112220368000701100e115901d80c2004076450301c4030701c000c540d511018800781078083c0c9402c10200315515131582c80060010125001c0c0070241c1c8880801d61244030a01c00c498465420405140141c10414082c0da4840c403500000100c900e42180d0459020104503132500900500380d85040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712565071 1250 712563821 712563869
    0x9060e0301090629031f0209010903020306090114010519090c050f04031103070b180f15070503031603180b0a090605010b0a020d030204060f05032a1801020109080a05160507 76
    0x4c22a01e5040340100501454540c03201d54030505128444400d907000135512809074010384d41d9000031030b0301408071521031400d07101c00303802001040340817800d0381034040002900b4907041810700310551550303864020041c503058900004000c11403d01d414043d0a011201e4162090300140000318040c00c458145054014201400e084082d0400001d007042800b24903000e0b503900c100c0140c01c003c2508d02c4080140a50001103007001c0e06d46044034280700005601041040c00b01c081d40c000d20000171a10246101040d05034162424000c43d07007040328504207580c1c08030b03541520302c03900000311080000741307540980c594805546007600b1806528400107071b168400785e4100301040349031425203130840c1002c0c10b0220040c0345010000002d03081120100100300f06000d101480c5038600101c00661305840040c0044802c982c212991200c1004000050000e45500601413910725503800982c07140780c8036070040142d580307030424a0402c05002101407040c001500800801010f004080b10702141030b003041d4140d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712566321 1250 712565071 712565141
    0x810051c110901031a0403091806060905030706300908090112050f18120c0c0102120319020c03120906010504240b090319030504060f020d09060e03010906 68
    0x4600400b80c890040020031000c61110300e0070172510030181d9280d101c40c18100c0d005502508001032088600c0c104050320245035000b0760444d8029100d9001040d81c4400f0151500303040e101c2c4601269607041851051000a0b0103080301e298550103030820040d00203010402c9424a8200315502c890000320402c1c0307580c00146101443d600314805004a1825005541807040b0103058400d0901d80c480019142c1032048c01030040c900040e143d0140c9401000b220b066903181114885030150282003a41d070741030080b000840b84202c010152490402c40340c892900f000b5440440d50780c00c180014400054031140480303a450103400418002c042039410f0000b000103c5890349010340000e000c510a03c84029100c0d82a081200c000e91645a10b030082c01c808203080c0402c034007809a002c840d1000d24030400d6007000140060301d0840e43e82502d42a050a000da81c2c8034004400c050100d1390647e0100310161141107041008907007d0f0001c5101026030791940155441604c50f140402580c000082e0100394a03c0e40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712567571 1250 712566321 712566353
    0x60a05150a031211153412050604110315120a120c211709011401050d020105190503040302011802031c020115080f0f01060f1716080f010b030f0705010810051c 70
    0x801041000700b91007e0540c1029841c554422034503031000402a40e9a640701100e004040c0940b6507885c41c0c0015801d10013162000c2da188500904005102014030001d041200558030008102080502c10015500c03031440b00400c0700c1000c000980d500114845943e03074141e00d03c1d0f94a440703491110106040c1d26010b001000f0b020300f68076240465030070920206100703046581c10703a080802c00e401800100c030713030340b2408a03c005a5820058000003850b4014001c52140b402a0b000f00410100708404001c60300d107060020b9810790046100340da0400303028966814849031400005442e80071031004140c1d40301c07107600a0311980c00210116007114070a10191701070b4410f890007002914100a03500405201c1d0303000b00c4400300701031360303210071100400c00040b4002d0346040880f4274943d070340391203156641c040c04607901c1c000d5003046043d52040c200054040859203202020b000890f0401e401102d44050040820410140146000030141c0355803207000f0304c080400355004d9151115003406079000e038019038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712568821 1250 712567571 712567651
    0x120a0203120c0d230a05120f0c090f0d02040f0917040308030c030403030b06030a24061407031b030503070f02070501080a11070203060a05150a03121115 67
    0x14600c8903540c00f00300d4109101407800c2855103c004000421a15200745101d9903032000006000001c56400030003070321502c0c120326170021301135650740722a80a0000955541e01c2c081c90070300c40080a071034004051880c0c1039000d400c103401d08032650001010f80c2e046940360000c00399a0007003481801901000814075050030f09403207141c5413442d900c60141344402400700700704450100c007160405221381c0002c02400da0040006450b07083c600c075024004e115148000d8603d8000e40380c0e41c00d5050b20869420200c0e501501c4958290a84200c17800c0940e00208041b002c1021524400402400c8008280c0391a4002d81e580c44c0c891400034405041600c10f41804070541d40000c2041041d40c2c3d0144409a0004148101090381004403c103903546002d8540000d625000c4c43c030420502c2070195110a100300103428003403082d82048000d026400105001c0038142c0141e509440154902440034441b66440707410032124484c0d410340194034800e5040e5080c003142c680181c00310030540c607485c821480c9040910 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712570071 1250 712568821 712568827
    0x709050f0f09070908070608150102011b0e12150103031403100302011209061a011d2d060706050601080106110d0f0e0d06060e0a06061b020f120a020312 67
    0x2400051081200035401071045000e800010b101c144513884c46070052408400710b0340b026840d014090200f080403582c48103000c101e5403401042c1d6205000e1942e01c0001c80b542e80003010648030702210f080c410b0394651900129410030310350161608100000305c1c6004400c15203905d504616005000d0709440d100c4440321034003071040c4121420640c03410300440350f090900c40416108034124202a000006024000e00d00d0f00d0760310603070440654030b4240d4090302682c0d11903441e020591001801840c500340c40d900201c072007a140410070381c030281c0c05040c0c1d00d000c0f40980c0d5542182e40000c7d025444104102d400079290400d1041e15600803605c5030141c1014140715018411444d0b59603541d41c540c07481c07a002c010840f200001414090020314000e5040945540c441c0840c50500d84042c00061043c18070031a211800104403003800e111300c00c1541c2132603840c80844009103018865405000c20181c1c0d1045042220703c2d0700e90f81c2c00303800e00040d20b0034002421080e00140100360816500c554600600c0b2020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712571321 1250 712570071 712570099
    0x20f0c0604060b09010e071b08031f06051c050a0b1210140f190f060b07140304151409100809010b0a0810180c06020106080609030406021203070302070f0605070905 72
    0xf0f054072580c0a5124a8208c1d6400d4036400d00c0d94801c0e0800801622410001040c040351640044135a284c0004030800318055550b101001c0710a48101c2204034103a00691356002440c03002a00700325048044040c000c5000c08201c1c000941e029581181000e05520050120321740ca545406040030344c00b0b030b483c00d100d41443c020000c1d00304801c00422001561f0b006c20810ba28881c4180d00a00d4543c100e08001c03c46551070f012194400c0e40111000d9810f43e0500c054146411000401c49080e070b0b0001c00483d07404400f0710407d85040340c1041002d0b0801005000b11301d407903122400d400c104032400350340d40c2c0030714107003040c40347d00b1548200c034024042d1520340f200344040d500000d24403417a640d110000040300420b8a241022074051481d000344803101c200000640143d0541000303095908070000e4414a481c1c04030000e030351b41700d10302c01e10015030041d000301a408000d03500690b81c040d0441c10058580741c2c80703940362590b8081da17190840d138141d40c65050012240d84007034007a02509003a22254039510368 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712572571 1250 712571321 712571339
    0x703020a0909020f211b070f0b06011211092d120f010609020309071e030f0c0b0d0c0f0c0c03020904112106130b19020f0c0604060b0901 60
    0x40d500440b0901034000651000740a000340480300c0341ca610b2042d0281ca140b407241c45008800081d1140300140c00c4200403560b44401e0a0202c6a5166101c10b40542900842c0c0c0d0b1140e51040040415060258040400080780f08600461582075840d0f042d855681d1800d8040110702c02d554401c20008840c81202c90400802c0620f5829241d40200c6c0d22240c1c040d9a521032510b040050f40c00c0036019400c0010024616110b80c02071b600403400b00c4240c0b000c29440f01c03400e504902d1a405050b00c991043c2c001000815108800130b010b85002d081d20144181c2c5030348000b1840d501c00040f1620740c1c2e83d40c214044000d030b8000848003040d50945441800d181d91034446805010b80c1e400068400c2a05001180401c00746d40d00c0052140809800340301c0505038011703503800590595807185a14041c0e03d002485402d2480600c1d000d00740e02c9040c030b007242e03150b46480501c040c0351704c2c800100c81d86c0c0c2000581e00f20590040601581180b42006260514003490b10806450440c001c01d40541d803900014040214 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712573821 1250 712572571 712572587
    0xf0a021f020f030f182e09030c170d09030503070f030227040f060303080a110405090f0406090c1e050927030d0f0501080c19090b0f03010e030a080703020a 68
    0x720030100300503a0f8807460050260318017500c8817900c1c5403041c20451790381884814141c0d9007404000b481ca80e01c01041c90192010b56003000802400280d0001c2c3e0040025a100c0c420400240c8182d071140c01c3c14150400c50742210121001030b4040f0b00c0210820603055400b5410401c100a40e00d41542402214100b00c01110007040702a605644070305000c10030354455501050311403044240c00d000ca6035690402900c0034205445800c141404c18401c54248903880d01100d0403034001070062403c2d680c80b404803041c0810040c0040300c0280e168505040130a01c1001e1120250548040d02800b0b9480765411003191100c03680101d00034442c4400b00f10740c5120305080010200c5568a108042100c0b1080c0541584100660f104500385001c8582070010b40780c0c0d020034140e0312442c0865002c10f80c82c0040150304980300c900d00c04400000d10041c0300c94050b68010b090b05420243c0b40003101814200001d0035aa082180f880c8a6407004c100d10810551108001d0780000250030b0842c03400342440360061400c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712575071 1250 712573821 712573831
    0x10030210050723300307030912020606150d140403050d06050307140121060b1803011505040c050708191403040503030106080601270608070e0307090c03020f0a021f020f03 75
    0x1040e03d24804584e404e502010415001142d000513504d20700220090020480440c06070344407185100102e50fa5400010380d02e0190f000103050004610780380c030040c480d980c066103080c0d010b281c5801076403103070150406506001d6031182e01c45940718084800c0000458403140e21151099001c61010071212481e20040946d040e030130f181050664100300260300c050f002a000e811b00042c90408000380750b80760a005084408640740120000d42d10050405007030b2040e0701b40c20409022420010011460217030700c0040303003a06030304015042140790303201e000158000c4400f14001c12050018030310829407041c0c000044500e440d400d142141010b03242c065a034007050050000340f015144c00b01e4030381d07030092240c080362001c0c04c00350070381245021030f5000030300d4054030460b80032440c10300100b00028010040e0f05411200900203000d00ca00e042851000f030b101031150401495400c0120719a9410b41d40010407000c40c1e9500280310020003101001980d000542c0210030061040c0712400008103510100c0b6000b07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712576321 1250 712575071 712575103
    0x10c050f090d1e1b0501050a0c150f1a03030a080726181b060d0f0603020d0c0806010b030402180601020c0301021309110c0a080310030210050723 64
    0x103410000041400d02d00da02c040545486220004061210701c0342d003a40d114184554003500440301d0088030072002c0180b502484d40800e1040c403241071124480c2081c0321900c0d00404030001414419109101156941000c01d2030141c3c85101c070140e50701040903805401c405c283c0040d4580010039000070004000038003200100507080c0501040103010340788041f54080c1a209029282c10054480c6118091018150403a40110441450100307682c4000c1003880601030503041c0340005c80c0c19181b0082c00103104496040d40c3e0307041c0200150b141c08449603001c5104131128270718a13041012881c0340c458142d000d00ca150408208110050b03c130708400003134040221080c8040da4030344400607030070301054803a1a1b805d98030100d00079051315201c280800464103860000c101040d1801002c286038420600014950b503c0100c0303403c0010300050085a01c9175400e20701070000c40e20f03540021800b10300d2000060008402054a500f072215010a0f54400110022040c12200c0c070401d006880e44801c800c0c242d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712577571 1250 712576321 712576327
    0x14090606011b12120f06052101020c030a0e0a0e1005060a051c050106090512070b1b010204060c020126011a0919031a0403080112080702030109030917010c050f 70
    0x24002c41e0030401c210140c1e01c2201c220328990302440040c808101c001c002d5007800e08001c14901090f14510500042e070300d0150000c54a2502040d6178808101051784a01035594208501c000140701880500703a07100d240d98032141d501e0008000c02c0f4801c00c0ba900407180c03024419092102900e80710b203c2d03100b10307601a2103081d101c02c1c00060640302405030b110407c0b42c02c1c20400c08004981072980c800383c140c800c144c41e40c4a0181d08c910038090505020f00383c5640c140d1140c0400d004909618001d0721500c1791840d4500705108006c4c2081e400d82c1c0150307200c240071524a6001008640e00580c1c1c010303000b241141d00c40b42d41081503500e144401c1040c4a65a906200034445546440f0344200f110700720fa40240600214101281004601301c10300c5c4800c2e039410641410103c8000030305035542d4000c41e0155594240c80c1d00300706041c000070684660448400c0760800985005072403c0c00703068801c1d40640c40790744000340b81c640b804004a850428140c80340e4036049034114495000408e407004c0121000b84592 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712578821 1250 712577571 712577597
    0x1d0c0304030c020a1d09190812060a031202070f140127270b0409080d150e09032a071206020c121c0b010c11030703060513061409060601 60
    0x2918040a0300a0081603da41e2004155415130201c0580110058812140c401c10380041287e6015800407005003004070411100300300d01e00c2e00b03244a4010710000c00d000841a41e9079034411921540c8a510005030308003010820506003803529249c010b048030994a003e081c14400002c00e0440303030142c100c0750717036003c00c00070304e440b48000908a0103000684003a04400a2140c41c90380d001307500e000410030a60920400146c1414640504180141c2c012a803034200b902400249018000f440300705a21030762007400010b04c00780f02c403054038001c4005002456407040602d100d8030103440b07403401440c100644151000c0c201d070320018070201260000703413400c01c02e0031440c0f508501912036a80f0000440c803c0c06004e00004403202d008100d03071b40f10540340800c0214200c4200342038444000406010481c2e1045c01e0020660003150523070100ca0090580740c02584079500c0104892040d25014100b00b4a084403c08001c0607205600c2900307180c08040142d8540046c1e49a079442000380b5450410400f070344104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712580071 1250 712578821 712578829
    0xc09090c180f1e11040317030c0c0a060623030d0e032125080703080a1b08070e090c03070c0c0e090102090414060d140c191d0c0304030c02 61
    0x298101d03403a003000b8002041000c2c2c180a240d090714003900710f094540141c4580f038003480012202101d074480708240b40240290004203103a00020015004030074200520340148009001e081d980c6882460001011800d0011000f0941c2c4d00e4041200004081e040003081c07542c000401710300c801003d1806c0c04110400701c0219040c0301944005800803502451481d4013104450042d2a40c2c0070001031554102c2c0035160b08170080f030215400a0000c143c00c20400700400d00c00e4681d43d40c4980005004240442c95848441001c0580b0f00c0620001d14680d042c05101a4403c0e801030402c84101c400c0d410900b00f2256501c82c83c40050f11440a000c42501c0b0f6a00300514550110014544003801c41682d00d4200c1800c0c0c040d5010626480c8220300c0c004005c44c00c103184420880c0104000741501e001c0c1040341d40d60344075010f406040720900d4420300340d14003050380c0c800a01d44540300d0744425201c8810b24252107200308190061414140c0094071041007000750280050b039500a4262500304a20513450000c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712581321 1250 712580071 712580081
    0x120406180f060c1103031005040207020a0e15090903091305040c05030607020c040f1a01031a041d1002070f030f0302130b07050706020303070905011d0904050a0c09090c18 75
    0x5095146030319506050008640c0022a030083d1501c030b005014488040c0191a031208841090052031400024003260a00ba40508900c0f031015024155085e00c444032564052011101c60130034402902d110742540c1452140142c0090b6504000c41c104840c140000b2820713101c000412941c144d45030001028442030080c04401040d010b819100307981400c070402500c4104008145010b64201018000013032558810380c442246406a1905118120340044024014104e01c05441482d84540302801d41da44d882500e081c0d2800702c1d40f4145030b01240701e81d641020104500b4555030b40c41402840d0200c0d07006400c1c01e8589606241601201b01c0c1c2d0030050300280103640912060901c00c45003c61b4840d400c100a0030703641c0c00303002214001030351000220303036a11049548400140074100c04002c1540200c2501d4207070100c11070502c03100c03182207020401c00f4504607401c3d21564401c100240520001051740c4010303047c903060501104107a51141d82a951845c40784d0894403100450039500600f00750b101c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712582571 1250 712581321 712581323
    0x9120f0809060a02030d060b04050607081309061202040b0d1a0c0708040f03031b0302071e03020d0807020a0906061d04090203010e100f060e0c1c150306050603010212040618 76
    0x100c0d54683c0c0414000940c3c80d001020110f04103490000041040340c084010f40c0c0403518000c000a00c1e2001c1030b921410190044a19000c92042400700440d640c612400fa00c4090000000200307842ca07194010070013034412801e401400b81c1c0352140e1040203d02c01d190000ca000c0081c00b0100c0e507e4071a4914201103110f2280054002c0b00042000b00b00d03400c8031540c3c2c01c2141d00a03500c034000d100042429141e0080714001c002c0260b400000108654011406074002c103100d50060302d12915902d0300401c0c40c4c80030b40720088418800c0003030741c50114a0030002903805130854000400415040c4240a0404100355000b1400c8002e9222080001c0e41c503500300c803110a80c040c00078001d0902001c40c0310355645403104a1310081c2d013400b540351492400d5100701c0007114443e8108807015100d280c0c05148a5020f039125041087c0011000f1a052400b030080450300507180001c049600d240d800e241041728070180c0120f00c664010020901d10126070000c09802c80c2d009000058100c4000c0041814041c031408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712583821 1250 712582571 712582579
    0x5010f050f041e050f0a030308090a0503130e0c0a3c020601051002150612070b040e0103060b060f0306120723090a0c120203070302090a1202030d09120f0809 69
    0x15001c01c1102c0d50072242243d0100100e0040e200546940400c20039540c3d49104a4024060480402c0030900c00e5104035006031104013500c0003004c10b034031203508551207085c880f5811083d03020204518640d01407010f601c4950000100d0400c030220000800d4142a4600c00c1c0050348542114541284901918461001003010301464902201070103521500240b150074821024030400400050010945800f204404980c0c1801ca5844004010b600142c10715640740e1846013080108244140100501c047c01800da04120258034500e0f040080d03404510381180544418440b4008182859040c0c0e904520102e449002941c00395a0321342c680022640b100c103942303041961114a11600b0701501416910a440c03039081a0340b075030021800d85040c40b400900190007800303007101c14407103603000c2c5070001d85a2502514240c0510005003d071100368001d840b0500504010008602e01048940041100c0c2e007044c0301d6880c60100c0403e20703000c1e44c0d44041d1484061201140820000e04201c80c4c0c0c01400030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712585071 1250 712583821 712583827
    0x1e170c04061502010b09060604170c030f0f060901062301030e120d11030c071b1d06120c090606070203010608070e01080d0327031b03120c0504030c05010f050f 70
    0xd44081e4003118050001c90140d480c0a401740300c0c0d07052450000c2c1c413521000e4051482d107844c262014115001c5403611544c580512404d0104c6c2da42d09102c03011800320900000c02c158030012548504041014040985070307032400e5401c02541903c803007003040c2c81d2104c0c0c00030110701860740c005802034a801a0108090300039a49416440307407841002d0001c01160010400402c03030130b20301c0e078071840c4001d0f00d101c079080e0018041040041e08420002000d902407883e0005d001360f840162405644502c43e10342500000d16041103036030b0404540d074980c80d500c100001c01109600101040b042e82d8041d0038913004840c001001420364409410500082c48108211512140e035640c48404140d07080c091840b69004118171621414420f02920b04204180c200c490304040581c0c0711101c00102c60501201800828a1042c5081000c1c40c5003403980c80c0a40c072822401c10514a000017228801c040340c5091160501050010405800e0384500703440f42130802c46580d0a5429003a107980c0607490541703029007000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712586321 1250 712585071 712585079
    0x1509030d0c08011811030c21042f0d080a022b020f06070912020f0d0501090c0f0f1a0f03130b0c03040b1303050409020d060e011e170c0406 61
    0x40750b40309040b1000c2e1005060f44480c0c40c0c07505410b8500c60604101040414008943d500c1d40c0301005010b030140a6070f2581a0002815044011000481e42038030a02c05203a84a949440b0760345032039a04010302005400540c0c44c0c2c500040111381500b0300a00f4039500071900040c0b1600030400e2610340d4180d0004900381c00c61898000e00119018243c010040c02440303403600c550000040e80b54029049030f1180d10142e030034500c0e94002100ca805040e03034840181800110a0384840100c500d0150080340003050b07030040383c248812410303040d070310110b02040030403000c101c864081e5003c2016038080034205c41e1220055000a2424001c02484000300c0d0340000a000c080300300c540210101034030a80c1452030b259160384030501c05020407a4041d06081030702000600c0803079a05904403900b0701c40c1c01c0c103506064984e046031003240c101e4483c0300314080d51034000303001c0a4030048229005203203803441410f83c02c1090001c5030020046125504141c0305003200c1d50546282804016284400541708001ca50303a5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712587571 1250 712586321 712586327
    0x60b04020d06091b090e0703050a09080a020a02040e031806071b060504090e070f0306090c08010507050c010b03240912370509060a02030d0501030807050714031509030d0c 75
    0x10708144d00d6011032180b07806560140640c030300004542040c10030082d9542d0309501030b00640f41c000c0c036950a803a620700c0d05a00040c80e520203802000c465038000e00c1d11a409105020446001c1c90030b1124690080c0100c1c0c9120038070703140044c0581001d4960503160507075454148421000b0300b800039003500d402c40b00880c2d501d41c0000070700f0172101040d10511004242c4510140c03550800c0c000c16422440180c028408580c507604152072862040d0030101039540c3d40c80459086600c19203c00000401c000b560b20304100090107180c0c40160110080c04400e000000c4601c80661520748000310b0034608000240010030903c02c40e41d01c00c08003008180e803446015007090b81c0c4240c1840134603032206188410399950580c03500004403540c281d200c0d603141102100401a054101c40d41150441c4420003c24071401482d0064500a41c800d07012240c40da5154640182030076591703005a10b40c600320752031001c507907503001881382000041240c41001c2925502c0000c4d00f14400e4034040504203060810703245a00354 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712588821 1250 712587571 712587581
    0xf0d180e0f071e0905010507050f10050a0f0e070905190c0503040210030e060402010333030201020601061809090309170607110a02060304080a0903021323040807060b04020d0609 78
    0xb0a603840f00d150325a201d100e070800c114058039900006241100502603540a10000c08642d4064001c8805241104400c5441c02c51107034182c40c4c18540300d50078000c441d2081c2c00f41600103181064140001829407100b00d641d44603520a016440e074969001c40d01e0690200076111048004407c244140342c100d6802401c00d61058a049001302100d41c0c03c01d8a0030b00c2481b80d1850081d041c005051951a25001100503003403e031071540d06101e602c444c149141e02c80100803120100200c00ba11000c3d407440c0006400d0100582c804c00038411104001040300d00045480c03c19075507600400503400700381d81811100305000707402c003c40c5081c2056001107507a900203042849003d040d80d0384008480007011603511207001c0030009400c20700c00d1000c03900144400c0b0292034900c483d0301d05440c141d0341d250009401c841c60008140d0744d02c0d541c0e441a08080002c216600b102d400e5071601600c0500707080d80d03200d44c14450b029000c0c0c100c544d103a190b8011981c48c1d4045400c2212480c40c02d0081903125112400104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712589928 1107 712588821 712588831
    0x180d11011b09050307140603041b1206050f0a0b0f0120071707060507080f030a06170f0c04050403020723100e030105090f0d180e0f 58
    0x91081441c05104411954800d880342d480e040c1458200320b176981000510b030780c5c40179141040f5160902100c0c0c1040c0e000c9810801c1004c080401c036401d145030341000c03006592560244051000035000b007800f502201003040301c25151403042c40700704d800b0500c10a4009040f0403917100c2ca5801489030382503001e1082005d0100b94003c42d205030510255411401c203074034450020380890942001800050403043c00c00501c1c201290701e900c3c0c000d0003002030315810781e07000000148074400a0740141d07000301445025090515400d0103100c0d00ea80040d09106e003944540110843d0030f00d018004ca03401941c02d034003c0c00f080c9e030400c1a80e10003480c0c0e480104003d400b0100d01d100709034a80080260000450759131317005442d081c0b0400c042c252400504400c0542d4465009041d0045010580d030380844041c0c1000315641c00c07071202c200110b1000e0380c0500d07451060381007001658039482402612503 = true := by decide +kernel

theorem cover : BRFrame.Cov 712410071 712589928 := by
  have h0 := BRFrame.cov_init 712410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712410071 ≤ n) (h2 : n < 712589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
