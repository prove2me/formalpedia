-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2738
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:23.605996+00:00
-- url     : https://prove2.me/submissions/ec960bb0-6ea4-4c03-acd0-4627e4067eec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492266187 ≤ n < 492446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492267437 1250 492266187 492266189
    0x8070309031202010903090b030a062607060c05060106031e1505040c030c020c0603060d080408061b21190204060201021305030c13150f062f0a0b040c121505011e 71
    0x402c008c008800140d00032400d030b02942c002d0003004102c421003505240006081101c000c180b0703200d03000c0e00c04003044850044040ea03503265801001415140e01e0040e048004124500c03824907444001c1c403070300e10601d882e8041d07802006603900c0c4103c06285003504000403541110044011b15040003950004950086014661b01400303450540c2c0e030740da07200700044900c413400c40004d0040b200445c5c08070355003400207811842490340d003051860309075813511403030294016641c0d01801a4407812540f0600f1240c4081c0d15000303003218100f041c0310503410745c5040030781e0400d80000005030760101e4210580d064072412080140019009021001e4401c2d01288072101940841490b2580ba59500500c11a0032010780e00145107a512400d005900c81800030702603500c0040f00101680507100b400507400001e1901440303c040e84004106c0100281c0d100700001e10010420ba41c40300b0301001c0014540c055480301a9540d2056140320071840308506088102e40042c1c001c003410303200c04000b5140d0f00d02c0c1c0301c5401d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492268687 1250 492267437 492267449
    0x2b0516170c160c06030c210c02010905060a0c140f030c03130c030f030809010507050a0c03050717040e0c0f070f020f040c051b0309030c1c0807030903120201090309 72
    0x18155030307520030444010b4420301c0340c440400c0359100412000c3c4a2200d00080c00e40c0c40b603590505c64a11500da007105d420300c0100e6a01007032104081c0325104044da40d44a181a03001900012541c01d00b00e44456041c0001215036507941074844000d80ca200c1d50010302405030b00c10180c1150300b048110140ca01a074000101040b003c028000081a02e040c00c20140c103c0455014141a460303940300c0c900154100007d83e003c5000c0386c02c402c081883d5a00602450348108841c2d0784190030180b07480d000b160f00102034141a41401006c121690100d0f0f15101103107031078240e5107107040e070f21460030011043d580320003070260070900001c0c03009140c00c019200441d8092600006010300c9100746000081c0015244185e050b07000745843d0401e440c054104d40a008004c011044182e202003814244945912900307020580c1600150134481d801c1c5099083c4540300c40f44071503030303000c0e241003551005030503440420b0550202d924540100308014990ba16160000304610090040c2036196502520501081c0980c4c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492269937 1250 492268687 492268727
    0x71403010219030917070606090c05070203060415061a03150a080601030b072d0e04021303061508030a05070209010f120609170406090503010b060708030a112b0516 72
    0x403020700402000c80031810a041c5d40c4256115040e01c0c0080c0141250b124840241b41084640741c0c80038000e005666810380c020b409030483d5504c0380d48000d840ca680301202d042039a80c40034049000c41d003d03103108411194031032041e03540f03003014099404d44401003d14a440b07490031030024462018080f450a04595100083c1e510759121444165124607880c6956001c01d0306911005908280b0ba02a8040707502e03040e00ca1064200f00074085c00700344e21030100d000c500034160207402c1001034070650007a69286000c0d40151072482c1c44072955421503003c00b5009000410102c0c0c540c05501e4100441401032030715003c2c118001e4940203840040842c10b50000d40880d42e20240813040c44429038076110f86403811121140e5807519030710040c0482e1340d035004031800b0390f10b881107030319031b500340f0308202da240903041000c19085030784141d80f0700064480070410140d4031506104103803130648001c0d5000c0e000305c40401d12450310a0a0a03811017101c10050184010320151030290511540107801e80c60300014100403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492271187 1250 492269937 492269951
    0x1302060714120a0806010806040e0d080a02040b031009050f04110d02010915170c03070e10031404060b040b041a040b01030605090f071701050609010f021e07140301021903 75
    0x44241462142d880e10030014000049886100c2d40c4011090704c070740c8098a4a00701c0e40c03610014442251485480c0c003000d90b10108400c1000c1d8001c404e5a41d00a02c841c0d005868a6241d2100207166002a00c16048a0003401410300c1603c803a80101c81c2c1c0650300d24030303c907050324213900c40c52581410f91070b0380e41c012011030b10110b00303691107992924040d01e10f52010014000c41d59000520140c40d40300d0b0341c0107511502e0080340c1d24202000c11030b030055176259a020403998904003040b00e515502c0008600740341e55a81030700c010f0041d680e00c09219134025180081e0b4403280c4002d110990b900030700d603e48114901200c8503006100320980022008041c1c9001507440b4050300168000d01280d0040e0b5401a8000100b20000a011503c01d00c24101c1e5030313404072002c0320300000080c182401e0041c168082001c1c4552001940300720203650b0314055910413200d90003080c03450005480c000303044110103a00204c0c07042c4400d1540042c402d0452205030f0086103488071a09990060300c0c0d42441c0c450800d500ca500e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492272437 1250 492271187 492271223
    0x60e06070f08070606030809010f051305090c12070e040b030307020d06020c160e04050708070b0706090602160f0c0b040f050f031c0305041e03050a11160303080103050613020607 78
    0xd548040b907001d84c0c1006103c0e10390802030340725040700c1142c0c0e000418103414401654400c0058030704403680d030031031110050705000030091100b000402070160304500f441005264820b45603403e028582c1500d55102c614462028041555120b6084501a5008000010040c0c6030300c0003a1042c0d0703800174001a203c0038440022424403d9418100381c0701404034101082900c107203c20140030714820021540610380e54116580c86180b940300d0340704030f00c40074001d070004034105401400605204400c010310707002e5610145002d4040c046c2040e0b40c0c4210001d2a40c0401c0340138490319019110f928070301d0f0305080c500004507100d010140600e5002c2c5215118050040d2810020401c000158074090408034801880c01401080104ea094444200c41024104c00003854107880002c0ca030103075031780342c40c0890042050351100200c1c03a031030303050b031141c0d00c07456a12070101d01c00d60025605c039076200c600c694034500300b02d072402102401040560b07452071044001a40c8840c221611541c0c0071152415611005e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492273687 1250 492272437 492272453
    0x41211010e0312061809060c0d06030f05030a080106020309130e0106030206040b0c0105011406071101090b0a02010213080705030a03111005010902040e150303040909020d0f0309050a060e06070f 85
    0x520741d8142440082035990a80e19480c01d80c900c501000d803144c5d00b000d0034418800c08981410f46120400750040e01c003181c0081d04000050512501c40d001c0800c1c5c1541e01c1d99240e0080c000c3c0b010981e21504041881e4040d00e41c040030140c010100c40c4000c5080920b4640050780907031401140904856560045142911003034000d18011a0003c05031600c840e655001030041d0380c0071030042d82d403a51a200002c214440092032021542101902c5141010200d0381c8030840e00361001b03800c03414031080d00c00005a07480c400c0010301d5105c503254000743c0c641d4426130401041004a400400c2150040401802140c07030000d8265486038151412084980e540701c8101d0a11450384558403905040c4000800d070b1010342d40003041203e4250792115880d035580c02d4000004040b540001d90700d900100310802880000d5004035442500041072084600746503980c41e5404030f205c41c2d0490114443d1034003041140742070841d10300100500c2c1441c2d600010b40d036001a80f244501c44004150b14140c825400c280700b500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492274937 1250 492273687 492273701
    0x2701090803070503040510020a0e09281a0f13110d090309140f130213050d0b0a0e1207081605150a0c090806040209060f06030a0504021804121101 64
    0x82441981c0741010b850041a65100b12410380d803d2248910302880768501c3d200b21601e19026550329400020b080c020059503060141c110780d2038800c20070450714a2190700c40600440300181100241c82051001300950144d42154050310603442440e411741a80c48610f60744a0201d56441c0010300c2181c02401e40280d80600c8031049940d6150510020030960000c14407010341d07801c14001c2d0300841150f8100b11846402e070800541000d4148486000609a500901901701c020300c10a0040e60719640441c00c10504002c06540f004092414403600208520500d013184c424038018000c144607140c02040780b4801c03507000900d1240d00192150704454481d07030915000f80d0040c01d0380c00078089042400ca21010a40d8003404207480d241c200e0f40d4080c001c0705107408503400349000e40000d50b01c5800b0005804401090782d40c10440c00101d208490f6035000007140b080081800c0000c0b00d0805005102c80000210f049207440d02c4494203000100c3e108075034100d6444450314100500c01400c0003418050005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492276187 1250 492274937 492274943
    0x20102010e0609060402031005150411090301090f140102040b0f090406050a0602030d0b10171b04030b1803030c070618020a0b0a181508130506010b0405040b0108270109 74
    0x840c2c1c00d011082d10b0203d1841c0c0224000c4042310101944511440200c072000d40301d0f4941c4034040303400d900050800d07822024400c0030031840241804860404a800d48184000c100d030a44c10307410000c0c0801412852202d0240c800c40000c6013054140a0000302d02d110707038001c410800e0f4005c02d1f441ca0035031343c0d50000f02c080d10010309440074050703889801a40d01d800c15070201c00c2043c10310242030700c03e040c4a48036000d10000f517903c01a0741d40300340305100c81010010785a0350b00c070312507500100c0f405001500184021032003900c0054041c0f42001003408444e1031140180d0854104105000340652070310282c23041c0e07a40100001940a020410b0a110218240e1307000750424000d060020703402c2e41078030140c0a015070b143c4408100450203c00800502c030b1a00405030703420941183d2045881c4224192544101d0046401e44400481d8668920744602640030b44a0800005800e00141c03c141c0500100184207082884840c2810300f215070f1001100c00480c140c4131100540e100051009420407007180d90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492277437 1250 492276187 492276193
    0x210702030319020408120c010b010c0c06030f0b0604030320060402011418090c0406090b0c030d0209150f0a0e1806011b020d061401170309040f0605091006090506091c020102010e 78
    0x403c180411b016800042c1401e000d03510703281c00b074940c550003561450784583d88444081c0030b00e41840c405a0080c00240b4404003a02d41c3c4044104280e111980100051402a01c5a1200462a0041070000700010301e0601c0103810030380600c00141d0b0800d10b01b910b954000701070151140180c0a8894034100b540551660001c580410f01c06074403d480001e00c15640d2582e200d4844a40340d0a00300d07468481c02d06015003681c82001500d1940003140d003c0c044101c0002c0510b0304001c0c000807400000d4010000300d1030110310000304d03011440e80007031071509140c0040e20b4000c00c160340c011141540f03490060003107042c8840c200201010186028580a5865005080d0034502045003428001850f0f041c074007071f03c1d0711001000031400952110f8000a0050710400551a14410000303200c046c3c0400e0200445a80d194500882c140d80d85425951148100207044189680b91001c01010500c180c2d00c043d0041d0401c206500690b02c988180c04d0314219403004030940c440980c03004134014001c54450b035817140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492278687 1250 492277437 492277453
    0x1051c09030806030105060102070303050f09041e0608010c030618050a021b060f060118031712010603241503090f02100f0f050909060d020a08010e03210702030319020408 75
    0x5800090700343c002c841c00e400810055a401d801a640e0701d4040c08060082501401105490070b15240208003c510140002c9006010141590001800c1e034a0365041251035034010701402c0c0c0244121103d255940c07500340103d520f4503001e04044204260510600f039107403c0001c943e001607404460540040c0307003039802d00401c1c400c81d040c0c0320f40040d101c0c0d240c1410540040380003584140c403140c000007940400052851700d9990713442c441a80005e9108640802403100c042c03180180c266041c021311554501042001400420781c40c440c03040b10713403482100c60200c0180207072540b070318900e2060311113801d00103030b40d50060403c0a030b003114501009600040340c481911003d9489a4062064142a2102020b40003004020340351760140144181d000003400d000159140b0304076403440c90302c600141c510110030303444005241c29070348560b5100e03085070f0000805034041c4104500825861100e4018a078190421600013501c130310014200c19452141800030569641295045400030142c12040355054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492279937 1250 492278687 492278693
    0x4080a1718070803030f010b0c0c1c050c030a0309060e01020109080a090510080114010c03050c0a110f09040c05010503071707021b040902090a050705070f0b0108060117070501051c09 80
    0x60703008580110080c0150580010311000000507a030180fa0744018050590f801d003d022000d5420030460704141e0706c211800d4903119202c0c16841d050345051140c11010300f0046085c44c0740750007500c03000b05010f58400820400440c1e4000840420390b0b0b034500d44841041d22042c0100d02600a12201070038552340040c090561a8004190350f04403181510f1001111009031f4041d2001c00c801d1143e0002d401d03d039418429203601c114030914160f8800d04001c0c0c2040e03160b80c1c01d02e2a2554104040341c0d00d462040084000303160000240040e59400c4401c1d6815103040e0780ca100c41a00e444c8200c0341400b01c0400071511242c014866000c0c201c010038450580c0e03151118000350f451542d5443c119040d4507040603003c407821b00d405000c01a81d0058000c0340300d0380321842c0c04c030b008040040801c0c08104082c8024800244507015110506014400300d032025418002c080c2d041100680c440c06001c10680c04d000c90740b810100c0e01c8002c0324401d0178086c2e212804484942c507662000820340a00740d1610ba011020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 492281187 1250 492279937 492279961
    0xa0b090a0905150403050f0703140c0714030a082d07050d080a02070201021923060f070f0c0f030314011223030414030307050109121b020904080a17 65
    0x1000c1c1c041c070b048503d55400c0209580c00b90b841a01c1c06800504108101c1c4005840d11005041c1b01e0b210745007901c480c68408254400a40160341c4180150300325102c01c006540b101000c03c03444100480180c0002d8204e0781d0b0300b00ea45d02c030f00029003961545203000c008038800b0010080c500341541060302a0b449900d40741903500e6040c00503080b00801c94000204e40740540500c2a180e620398103030020178000c041e414036000c400e075002004079011242080c62841103030003180668030f140c41e00790040030f2a040141d004a00c0c030900a180004000c4035484500c141984a14103401254210840300d1030300d1540d00b011405019841c511183c0740d12150000521011010900c5c48100d004901995016200c805e940c00b0000d03061040f000c0c02e038401e000030b0210b9070a40480d11742801c0020122071030b040b4140d40c3e00e420b580415034117860308100d011300c941469421200c50300f6083d03803d121b491740c4e10041c1e40c000b40000780c0c0980082c1c8402400300e442d48950703010b03441108118000002d110044e15040e520340403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 492282437 1250 492281187 492281201
    0x3050307150e0304060f1b060f0204141f1b020405010f0305160b030106200f0102070b010e040201020307030f051e03010f0e060306040f020a0306140105041103090a0b0a0b090a 77
    0x11429242c09042e420020b008000d81d400c0d207850b6611000742c42801c080440380a48103c096001900c0d0211042c0001400d0b441001003d0018480240c1ca803842c240c815000031700c0f101005030040c81c0c8252952503c8c40310f0490440c101e04039003007140b070011a80d03503410071070041000020b401502e00400402c900b00200303d801d0807213105104951807524000ca610400c1d001610600305400001d1005109031401107010b00036040200840300c603d404400b04083c6040c084610292850350300088540900910550045c090300c141c2d0084a40c43c201a80002c1d0303039109030b1030040c003008032892010140b50311400480e03495400901280c1d50051005d012100d9503172080c8100d44120301c00c002c0002c1da078280b21402034401c1000401410540c0c2c1c4c1d503250420300b01d80741c1c03904903407144521001100050343e621400c40c8001c0c0e84041610f00d0340c1000140300490b0084605079011b410240100708a04900080018919500c903a000907151510740305440504a00c40d0503ea02180c02010000105d00f5540020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 492283687 1250 492282437 492282473
    0x8030c0702040c0314060f010e03071409011d07050a0c0b04050706020c040b0307050603040219060507031706030c0d08040b0406180e01030f1217041a0f01050d0b0c0403050307 77
    0x5601a003c5041e4103c414a039070b61400341c2064400100d1500e0150b0700c034420641c06041c0f0f035450100d1000002c7c1414a0354000c102c61503c08080c86000d408e141000c50b014086040c07a4161603c86041500c564a100030001c5040210014528100521036480360410552122030b001940c00d10f4a441038560225000c0c400051241c44407891003071600e030040d204065005406042c8060601043c003403a58401442a80c119407155800f42e1240b440517115401011555150f90301c1d1461480c000304540c1001800e900c0800c4164107020380ca03a000700d0084200c1074211400703044103a16150024543c01160f101d10509070012030000355407604007080c0c004040818aa1100e101c0d00d6001c0c03165414400e0001034800c2e40b240401d14001500c0c050541c19419581c1030007040107000851440b5022070490702110003280800c56100b081021400b002d400a907581c001070300320740c10180824401c0d016a40e01400d100c5003000800c41d02400d4030b00b100c000d590040301b03a0340d81e107400e402c0c00c04964034610012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 492284937 1250 492283687 492283691
    0x30602070b19051320030a0b10050102031201090906060b0a0207180606050301050111030409060b091306080c1507050714190501050a110f06010807140609060406081308030c070204 79
    0x502d04004803445034502ca0811407219006000d0b103500c41c08654211001c0038010b1194240e24000325980030060b03121140c0c0304000c01d03501c902e4207035a001648840c55000e941594010b100b10b00010341e5000c8400d043d81d040c0800008c1182c0300e410000007901c0a41c0c0540ba00460000344151000d50210b24082594445040c0305200c42151704800219815440341500149040c0018882980b050086100350040e400481c1c0c00d040e15154020102d5101e503101e06565900011200340900741070440c40002c00d2000700c100007030b03450041120340340d5420940c3c40d031160a60050752502c1c0034244095900898005c3e04640074980c0343d00d541290703061507409540c070a0301001400c0c0000c075800701d13644050351810b075a42030600032074072010386000b058000c02c48664060b002c0e02001c030f84003c1101600030406080100303d828170301240b000095854102c00b074010501000f10f44803540390141260111907882c94450825a1442c000706d4510404100c005d1004500000b4840700c02c4c031100140c15024022202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 492286187 1250 492284937 492284971
    0x170406060906050f0d0b1812070201120c0c2319110907020c09040804090203040308100503010e071e170708060a0501180c0e040c050c06010618090c0207030602070b 72
    0x4015071507290502503a8045170030780700100052150110b00340c002180445000005012003141410020043d9070149445000300700c0005540e0300950f103410040c04640c040001000b03290008005e84906100501384140c54101e400040c10010701170420710b4244020303100048031180d00514240f0128805860300102050320702414941110010b00444140e00180346802241080c8940f40f0001081500c62503014800024100e170a400250f114030310071f80c2c40b148035192011030300a1603240d60300003e020b40c1c5052424000301c0703030004070075058030410703100b23440900c0c650100070680c950190884417085001030501440d5607030000b48101034405c06400d8541c60356500a404044400910950018440c214207211074402e0b580e108001300c99a41c5862000800d0b032074040f609072408070f0800000250300080c0c00c01c44034018401b9502401540c5051514900f0b03412070308158a5860161400f0241d85030044200306008007d0580116031007081951078013414246445c1c00b0008503480840360403801c3c1c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 492287437 1250 492286187 492286189
    0xd1d0402220509070203030708070309080a230423030f010e0703211407020316140901090c0c02120c0306040803090c010903020148031b0f0b060117040606090605 71
    0x3c18038404e48065008600b1070799800000c980e10080600725509050b0380341d506201080f0140300410680320a03480c0c203044450180744590b040c0920004000392007005200601c41c5050490300045010506c01594490b038860100282c00c001a02c0c404540ca9031904891f110306c40c1e4003203541001c0b2030054041b04900c0070300400c1c8611007000c00b840c8800242c1003400c0580c0e60f09001d40a400260b001070200c1e540c040103559894010710a541090410b840c28145c100540e2034a1441c0d503014040b0708105002c0700c120482c02802d501040c0c1030080c400d4030486016810404100080d2064240c01412542c46081c60f0400c041a41d10903204500b8501441e06100355079400741000f0802c4a90684d60031614407000a1020404100074456454160440210b112003c0c0303151300012480e200340c945105202254600600141301520115a400008004500c0814a00708404072002e400040f07003040303607468500482d24007541c00d442890b04001c900501c0144011030303010505a40200c4c0c1c042000075110703c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 492288687 1250 492287437 492287449
    0x11a03061806071b051b030706020a1e02030f010f050609070e011e050c01390e100908150105010807110307140307050a050c150c0d1d04022205 63
    0x5449150190b200801003105140b08082d0318003004004240d51601c1141c550b1450f04204185a084440d410503036254215854203104200007042c40c0c7c0010040f0341c1c040c2c0d0340e002035901403010207d040d294010302182035440c24084001c00c603414500802c1400c0f103075801c0c07000030041920380e680600406030000300518082c404540b28640140c440000c2050030301e080013154560140143c0400105211036607030f0080074003d4060502c10340503448540259004034400808a80315407078103a018000040c03061a8000744400e002c1c0d031055480c076220304a6451309a41e403a801703601064140c40b80d40140b954045e200d84005041c1d078000d036520324058032543c038100c581c00c00024050840b50004c2149500245141c00c42c0d01410300900c00381c03400c001158844d2800d1443e4114199080d41041807800c40614000c5265074500070601e10542c20900c5982c8000d40e50b115540148090003040002040242c1849034580080c40006009559401c11544410280c5485130240d4484218034200030034549420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 492289937 1250 492288687 492288721
    0x2031606021e040503100e011b0207031505070801060f03090804030803090c040509190c081501061b0c030b09070f1d06040921051207050a02100e1c03020c011a0306 72
    0x6001b0305c80e0042400305480200b6441d00420720a40d0380b039140100311209944114200310f01070700540902d62171401d2040f0a01030400314000b21902d00310803c255290089012810744503245807a2a0080c0344180c1940123040e040c0024000140105002040110680045114000500c1900c04213210300c0305200685001340d800d10001d40156034900c40f440641040390344428001e4506043d643d07a0760125500740b402c041d07100c0b08025441001030042c25009050035228040e00c15480d818a0b0003516070446443c0140002410800c0d00341c046002e4090070414007005d021000c0b801c80025990301c110500c04060f8241c2400c070300c003150000440502c1c0034811320f6001500308210740c0031000e512280a11080303121100106004003440742c00300e815800200e043c4a040662502c559441c03035982c002e86410244491000c0881c181404110014004201d040f030900c11102c0f12a041401c000c000d41c080d00803410441c00541c071784815003040c1074841305a40da00c00000e0b0181d50540d2507040409580d0048 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 492291187 1250 492289937 492289939
    0x103030c0f3e1203030a0b060906030106020a0c0609030f021509040f0c11030f040312050c030307030204090605031c0f02190c05040b0108160c1e030815010c030e0d0302031606021e0405 81
    0x505c0002c80108194105081e144030007421a807a00740f0480001d40d42c1d0300b00b030b000600164000c800003401c03c2400a4000050200c03800d040c12a01d165035200960340700c19040090140036413040003281100d0a07016121100c000400600c4101d080c0201c00c070003401004410400592015625080c80c913000c02214060381203600a0b134a06400c680310094004000f204100c20000b0420004500c12401c1c000346014100c40c1c1c0d405030391646080c0c12074013a9042600001d1090b005691103000c604081d08890305403d40c1418050340c00c1001d803e081e030409513290080480050704101c41030400070401550416290304540070820b0b403000c40f00440e0090011101006c114080710b00100c1514007800c551012288034244582c4202080c5182110340241d0000846c04030b43c8030400e010341c4031810b001694800000b843c01004481c2e0684008041c3c4040d400c455004011070103084090510900c00c40300d210320038059014441d042c0e0310b001002580507851308110010b82800c030100f813040c80e50880b42120b01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 492292437 1250 492291187 492291193
    0x15060d23010f06140a0c0b100e0601030c02030d050403030b030f030c011a061615020706090201020c010203090d020d020d080c1e0102040f051e03010510090e0102030103030c0f3e12 79
    0x240004c241c503866220f01400c4d02445030754032030303880024814603450f4800c10b142c8140400462804070080903841c00900030314141400c3c81203040c0c2c541d074000156180c5401c0c0072004503032600d460400b60010140542410340501a503440344480303910010041140941c1e030301c000c02160340304c429002843c0d1400c5040d99800b5004001e035088440d0024952a40360f405050801035400e0107281c50700c01c0340c0c00340d0001c445654803030340c0400030f41d81c0600080e9030030842800503510309a83e0300001000507580d0040203224140070346051080d51230f601c40d000c903519400940300e583d400c80130122503079402c070941c14104140284200d820070a03a06000343d40c112190000d000030080d0070030007000390b10002c21803402c2d103681c0307003425040c040c0d84c0034003030140103140c00560643d207039090000440035a403d011902401340c0c010401000060b5101c603910f0703c1702e500030040140d02c00440c501550428a181c803141c0078148260304905c541c0360b203090399205ca4449011084907010a010a001c0e8804000d14064982d0f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 492293687 1250 492292437 492292457
    0x4020105160c0b0a0c020f030a02010e0d230c030f0a0c09020d0b0a09020a020d11060403260901270b073c0306080f0615060d23010f06 59
    0x3000c103048101c01d9105018440c021038482d00541c007190800c40700440011002100704055040c44c540603480581d055000d031140d0350207900060700d82d2802d00032a07070090011804c028140601a5000c1043d061480761000d4008080d80c0c006603500a1144454842d000d00c101818400304002103140e1250340c016034402030740e450480e1920080d000451042000354541159210303e64070143c445010b480000001030b140d104a0310b00918209200c43c090007402617040e00d0303692842c4001183c580c09545454200d81c138110310319040070940c0c12119507551010440c1d0600a60450640100e0b222554403085039541a002c0c4503040c0203070750008000340c404052036000c81d002902c0740c12190ba2041880843c80c11829080180c1c8610458108072410b03081d010081d03011209500d0b004090080001100401ca000110032040d0b0b112400a012110414000c507068001a2030f1b00302a0303044083c0807101000030140c510b96076102055404265450040d480b4000f00385c16003240c4010051b00c01c951380c3c40e1411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 492294937 1250 492293687 492293707
    0x9010b40060c120318080c070f12170f0702090c0403201e0f0d0302010b090903090a06051c0204090903021501080a03050705010638160206030a0609020a03020901020c0904020105 78
    0x402400000c582c02d617101d905281c012541e403000400000a1800041a6003440c0c4448000c607c40650007442023031302c440301e444010032032400c041850b50483c0544039030b89038580340300e040e0107202c2c03008000c1d008100001000500410180034200726802030b80c1c0340c0950500c921054034980000700701c443d844054110406485004075021200080c0301401c480e4100620100042c00c00141c0881100181c1d160580d0403502c0c1006414143c00001e004015828008500f00050340840c0601a02c0100a8046a882c8103041e05034090f007411703a0b00e50310440d074503515604140040d01c80100b00342c01600c175840f032034040700340e01c060014101c9005030060031869000c1c0e03030212034a90000354146c0d82c6640f07541000c5039450400c00b12240f00d2400442001458a41894440c41c400400044084110082c0062407074980080001c810641c6e044410b01e030341e135039420075180042031035130001d511030ba1011443d80071007500b548c0209a2100242c08498455a181c010003980607802c0320001e000800500042e000c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 492296187 1250 492294937 492294941
    0x4050a0f11071104140f1e0c0a17011a03150a0e010503060f06060306132a120908180301090c150314041121060705040f090b09010b40060c1203 63
    0x1c7d40d06107100700340b401e441c42000c09440d01642c0841c200c0200040c480c000603003106200051101d0f62440080e46c0d89000343c0500240c031030342160001200c000000501029100680d10f400c18401003045c0f0420307480720858801080709008503030080c0f0421001c0fa0814590101045c402c44005110a01d159030303d50030310031048145013031080c1c81c0751550249203d100752811045250507003005106012186041c0c014100c034903102c5284003040c0b900c1c40000c082200c0c501181c42356880159450404004400400c0c018000041c020b05076042146000c610954038004140c00131340310360b030300340159150b07003042840c06281030307a0041510740008a81849800c000c15280780b0708075400c9218a081c000c5100013814600c1c01c895000014000141c04d02944202c0c2410a02070302c680c4004004020900d00461340000041c05841800440824031f50022150660003071200804038483c0190040c550400c9080600034460148000300c604d20085a264484c1c80124001500141c95a0003000244000d0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 492297437 1250 492296187 492296191
    0x30705071401021011370c0213020a0306090b0a0e1b0c070b0904110a0e1306260706020114010608061f020a02040e07080a0204050a0f11071104140f 65
    0x105500070803c40034400c44d018400d0540c440712003250180d035851040711030750541300c0002480b0198484100c030080518059900400c0d81512410f040c9101000d90000070000b51046505140c41800000c181200d140c2c5504040119200140f062180b4041281044003205582c01414200080c040010301505041030400320010100d0354030908e403503505980c01c0d0800d865071b00840000000015010142e04040c800e03028003055034021b85040400580b0014110782c0b40400ca10b20440c420058001022171581c4504020034007045071804121134404201148501038917280000d00500c08000341050040c091288142d048a078038600b01c3e82801c1d025903044801420140c5c0018082c81001001ea41c2c0c0c800c0621a86283d4005251551241c07040005803010a500740140380c000500030091141c000520f40a032690403075000c5950fa542c1a0070390700611441d078010b40f40504211070362540f0305440c0002d02c1154010f20700d00c0e0f4504040c000f400f064030b6a00c080d58400c444440b00089540b282e0320b005039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 492298687 1250 492297437 492297439
    0xa060e190b1014030c040f06050301031704050d030305150909070e090d050f0c1f0203180d0504090c020a020325080c0a05120a06090606050f0a080d081015080f07020307050714 77
    0x7031b08090300c1b20520911070105400040100f0000001132003402400f5096010074004c2c611a64600f500b0000803c4c150817036180c0c000c09258698003c226400c0896001c510110405804c5441758505140b00e036903504910b00c9204100d400c828041030b80103901103502c1004100e9a01d65034603240c6840710351a1964000009154980180404208075000d04d40011401228103440581c4a051041d040719410207015105480c076480349002e10111500441607404440040c00f00194050401a050b410440e504100a5040c0074011441d19032602081102d00e4101072a11141003c0ea142c007002e6a5405042c1080c981c0301d114020100034510f8003030082440101030005513403091300070356070b400700341c0c1c24841c401c46103180c0303d520074401d900f003441c1c0d0f0300056482100e00428052030280c1e415180c58074810031030108040c4100240001c02c851091800600501c401406449034202d4010701c41002034900c0d00304102aa408201c100d840002034490407900304000e05015480c10884c045408082403600f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 492299937 1250 492298687 492298711
    0x209060a120303200a0801050105160f050f150709050d020105070605091b010f1b0c080d0f032a120e0724020a1a0a060e190b101403 58
    0x11034003045400544031500e10a0f01d02203941e007180c2654410f42c1d80f0104003a610720304140801c1c55002d5100c01024119802821300e16900d400c48005103903c4c0001080181507281c614111008226000488150025115059500c07820410001d039410240544005001800201060040e4608907c1d00e030080741c0305041c4246450700c25170b0782c002a2102120210a960401c0412181d211028220a40c14010900c0c0841d11007541d008054085402006921007500d11868001e0801c802120401e000c4e09245080707452165080714024a84496200014000303401c001144115005110307030052115608446111646a0781b1002c030740070362443c800404460b8542c4803403c44082d060110f0300191141044c0c000840c040c180c031101ca00b00044080c50115070117845640041041100448121070514441120380e8445034500c6020b17059540160900f0b824600c144420744420030300d020b802840448062060380e9403201081011000300f20b100d000f18040c1140c6540c001d200314001c1d40c1c0030200103d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 492301187 1250 492299937 492299939
    0x80703021903050712020307050a0e0303040806040b0123060a0f1812030207150207231009080f01060303051801141204050709060305030d0b01120e03032d01030209060a 74
    0x10210120205141e1140440c2d5241c1c24490b003240e20261525090150b25019891424120030040052154000c01010484403184000484c4d40a0040320002c0180c00201c2d034083c00c09090001c82004288030307411080400030032848076035080b20041000c00c2d0008120360304000d0b0058094505140c101021410000c0c448080da43c007034041c0d9403c8002c0c000301003c0d404158401c0c903020340380500320340110703914001040706819019400038003002941c1d0060705484290008005590340c1064004020b94085029036109070100d5020000b801203946c100125007244a0418956080315018000500002c0c0100038000c0c0760090780c10380041039503040c50b144c07902d4040c00d5841c0000350842c1c500101d00c4801d03201802b0501008000030310190190420402944e495903407010b07a00e2150b000c031041110349400e18071115a0140780120303031441c0c400105001d940c0c6c800c4241078903940200c13000c0c0511031450342d440c603080003012603003480c200700a02c1000340342e4296000c0111456000386015440001160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 492302437 1250 492301187 492301207
    0x3050c0d260a0f1a030c0a0302100507050a0b191119080907030501090b0406200d1a0303160506070f1b0503161506060813060515031b040c03140708070302 68
    0x1081070352001d0b840c114040b0f2507644604050406d00c0000500e88194803042042c000740ea1405400d500096441c1015540c5e907846103810340c20f010038000c01800e0750344031104110b0322241c2c1c0f00542c3c4956018071410455284204c80c8040705000d5018036009a060860640d518140907503c03c1d40c101c40104101c404075a903036a249420348048010440c1c0910070b40e014081007000e640540150910343c120350701480c0030041c910801c68041c0300c0044a200d91991210015a140f50004c65494107018003540d59400800300d40c0d041c02c44030039800711094410750300000c40031489807410450a13603296482d0000400610545070406801d11426540741c007040280c0030340c00f18004900c3c104e8030311440442c1035444c842c0c841c01c8102e9085901c2a41406412b8007001140d041001000400c2c5510500018080d11103500c1000e448800310001600340c4514400d8403110b00d0f90300344a04004400310340a00c02c50020040403000d07240e402c003080b0b68000945010820072801041619845082c9241c01410030fa142d40c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 492303687 1250 492302437 492302441
    0x3060515030c0d090c09151d09030d05040f020405010b03070f02031603030f021218060603150a0c0207030c060908070920030702120d05060907031a1207080102040303050c0d260a0f 79
    0x319250500034a84908000e0031070281c0348c60f1f001110b980038090b0070345041440b00341c803480b0315021204001d0381d540001d020403246801e070800d00c0741c0181003005103603142e890510b4250300130b0382c00c3c8001c9080080d81110b40d0307100004076000002c0e18000b4590480e031030f41e030a6001d0000114031001d142e4081c8040003681d01c03254030440c4510190f164032601d4010070300706c0c0c9041500162082c0e0194000146c2224091108000c440d0080300300c21000500400d1840f0403402c6c903889400040244504080c0080c40c0d0381d02842c20310684040d07006032114595101c1c8814104c444240c94959846c3d860740030b00761540820400340d0b1340a000c60065942e92400130b450807802c0e901114201300ca440e51345050010a007400c0007101d078800c203a81420071018544014021244d450500c46902c01c01d500c04480d112814148265001084614003c1d901c650f1a850040d0842c4c00400c00c51440d4850622007103d054454407407100c2c00d940100030184042c0d0042a07007801b50400810214040e40c8426844043c0e040034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 492304937 1250 492303687 492303701
    0xf15051e07031205090a030c06140103050f010605030a050a12090f0306140c07030c0b06030102090405040f110a15080a090f050604060f0b0f0603060d1203060515030c0d090c09 77
    0x340041030794520980c900602001502050100d81e03c0c580707000c01500c2c03030000a01008032500b50804c140c680c0700d14507184001e4628031780e50b0169a0560030000080120020b50b0508994408000b48910303a203a80900d641c54650460141c89a400800032001042c5e0f540c21005003510310340b400e01d116603115184071100c40c440c0d905c200c44480c2c1d604000c2204544411165030402d881c00c0348249055a9901c0040a0104900e070281c00d040e0b00d5000314000381c1c0e0940c11200e984078041c00c24401b528249c10300c5040c143c003110f42a142c0140307410f00404640307040c160035000d40340b8000313011000004400d81150804002848000c9840e43e0b17030b12071400b01e40407490f10151544a400103251501c1c01e842e2070819515000c1e5600806030501050301c00e0b0b03640320581900b00c40019a505038481d514000014100700502c0c2004c0d10300048142c2c41c040c00b40d407503000758003610000e40b854424412103410b4003815100842c0c0403900c504d824080b0350303c9044107401c11040da40c001c0707075501c11498803198100200e64030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 492306187 1250 492304937 492304987
    0xf02060318061603061d161110060f17030a0305041a24060901050d0207050a1b090b06070c1214030c1e07030209010312030e0604030909050f010f1505 66
    0x103d18807810710a80c0c1805400054094513017001ca09001410031007080d40310141500002002c00c0c5050302041c0d20a01110018940341c008442c910b2683c12140c0c0c00910650040c2c040905004002081c00d1545640c41d1084590040086281c01d11003a0114010700e405001150a8092810040122040f00f80c03075600401c00e40384030350320711071348a0590079103c403422020902a01c001e000e50100303682c01606403030000d0b004c40800f6985503654500203040161a0b0002001c606040da020311080115885440035110800700800c00c4002d41400c00c81d15000d14400200342c1c843c800802d10003140340c80c1c10301801520810345c1c00c00801401c94510305607001114181c0c4240d10900181000c6d4800301c111503207401c05c100c050044281150040384d110350301400003900c13032810948650615840707a480100c0720174010b4151030590400340341c020400c45c1c0c40d10501c400d541c1020003181030b40e01144103042c100c940f0643c0164405140c18003240246205111000500505004001078407200300c0a00c0e00c2440b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 492307437 1250 492306187 492306211
    0xd020d15090308060f1008130305040807030302010c081005090c0f190305060f120d0e0a030f030207050f011b02011103070204020d05100b03040c09020d0b130f050c070f0206031806 79
    0x58510113005c1c5d1403e091007203500c0f91303122602c00109242c02801e4175402c540c445038010810174507810150b88a1107a0b03803042c4428418031600002b031642c10751041c070410407190384142050f110700f400050448450700481e80c0c84101200480c5140421000030500361168401450804188060780b40380031f4240301041c0c002c2a100c1081004910300b42e0401010050211a5490700140c050ba107607580d2a00c200c2201e00f40050400440040da4484000d5002540c0c42042416140f40914009465030041e1064038011444090030301e4640d8040d101c03640c6540f540c2c42c40b4000d6500d15400450320040002c8d1220308070300041003801c0150b21140000c00300e85481d80404205414120303038503c0707184c00310360140038100010b00034080064031038030342c5004460a8140150712288943c15403002000f00c01d00c000c0c2e020f00740200d210b07040c0d0016080a40500690801009607595582aa401500c201400104194030003840240140350013400f03150040001c0a0b181004040080c1c00c0740761582c00e542c415081c0b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 492308687 1250 492307437 492307441
    0x5030a060912020a080702060d09020604060302120f0c1206010311040e190c091e05130506090903090604050415051c110f0a1215020a200303060d020d15090308 70
    0x881c50b004a0508014580f004140b010402e481c1c100e2240030f0318100a21036400000c003040f01c000c240e048507401640040c1040e46d1180da404d0f0140088d4400f418100301c591260000406002090725030500c502d4414180c9450072070f0f1307140200307117903400100510b06242e65150850814844180900081c0840f0501c03c00e0901300a844404800c0440c8030f110000c1c0e01b41f50b140700307456a21000120455400c8104d85908a080a03101c2021a625400841d00503184481500000c0040c1d005075010f180d00f42c0e072984164a490081a407244904e80705150401c40400c0208075a040690001030001000c0c4041484c40351940c0000d06590070b4038030141041c05049235010b0902c1504900001018030880701110390340c0810000c9900e5118500c507800009402c10204030510000e207007070400c3d102e0010011580c80404c0e15010704222a9460300100750b4820f80b1041c03613988000011a1b0040348000c0460500400035400c0180000014070222803074442610115580c41c010700490501910030f4891003024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 492309937 1250 492308687 492308693
    0x1401150201060f0b040b130b030415050708010627080a050604020310150909050c040e060115022103100e010306020715050f15060408060c0a020f06070206071805030a0609 75
    0x9110703541c020f0030b080c9a18502c108802c074071800858084450380100640c0303500c3c040280c4e2a920f149688019803ea000004210030480580c000e030b0b000d10b180390002c00c0f240e128610304440c080c40034040d010209000040c84007144503541413548000061250030407216454040580c20b04d40304c0f00c4111215802002444114503060048401c40581c980c4200030100740300301003001d00e4815101e0b4070000d582d10038500b010308c0010f2000302d140e23000c00f4005004c5034614080c2d20b41e41c1d00c400d00c101c407a0058207e603208041440814159601c00d03c121f41c8540c1c1210702c00343c0e010107902c0a40843c85640415000180e001d042d035664500841c055440142c60301400e041c0055498404600049982e2501040100d40d5208503142500000900219100d100510003c1a100d11880c0c010a2240c882c0e201048001c104030001000d001003150300303564003925107841751507a40d2010756001004da0000700003e10098451048448800c0524036008043d90f51000400d0611081c401c0544515407109003003028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 492311187 1250 492309937 492309941
    0xa0303240b070302010b0603100e10031e030f02011e0b0105091201020a031b052b02120612030703020d21021602030f0c030d0e0a030503211506090d061401150201 71
    0x101b420140c81480ca907181403890f11040700c0745405002e0001d002000803c25412007140303000051680715940c000c1d0705400c80c111303117001c22101e8811000540590342020501d48107008015400f00040300b0f0042410b40c00580070b000d0140c0c8040c0302c0c1007200c14881383c02542d85d503c14011000c00c54a00050341da014072031005084c1d40e1500000002e09804500f0340640c254490308a44920101c0e000300c04255213200c1260000213820f2820354441c1d07002084424181008200c06402400100e40c819030702c50304501c3d01622401001c4014015800407400418205c1c0100800c00c40000103045010070800191802c0c0304070b0b0001080da1040242c0c180500b4114101001018041030041c0d008248090002001030358030540211800200507103408224030325202c6840f42c1c4041e5034000103480d03d80c3c004e4120b1101510441030084c0d803070700b00180841c01c1019820480d0315a04c10180090703182c24001012b012919200600440f07009a50b00c0b00d407212451003000582c040c0403440003003041ea40018400070f00b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 492312437 1250 492311187 492311201
    0x30118140d08040b0a061a0c0106050f060a0c0809041a030c0306190e0106080f010b090f0c04050120070f150212070201030e030f0d091a06030a0303240b07030201 71
    0xc141d0045202001d51500210b4255000b0b50002d8005000d139241d60b900e0010f045940c0c8541d00c01034081c1e04144c20b0341c2501014008802c0780c07000800016698004001200c4d13400310300c181c0c00140822040090a208644c10000280503480c1c0340d2034000444040742c21503d01030f400048007000080b990789185420301c91681101c000f2002003034942040c0208a410300316100050007400c1d40c0302d0f480707500d010007900003100410f00b6201b51402400c105d03560314043c0c050a02c2040c480e140d42d0b0000390b5000500c4121074068a074008101e0b0519007002d0040d6000f55070821450b00c2e030b1188440c6204020010850f92020704202c3c500d1581c154502001c22030791f110031140321021354020401c9040c0f104411000d85c0d030000c0d02440c01060510114003202d04601c90407100c038218500004440e42400b0a50304440120307441034400d8010590860464401840c0940f030a940c141c00503501c00300800c0c17080c1c1040048000d0030f80c0804d0580a510400101a4070760342c002040b0702c00104405080c550284038000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 492313687 1250 492312437 492312473
    0x11710030204050f0601020d1b06020712021606051204020d021017060301020c1216051504120c020319050f030414041d0303071d0402031e07030c0e060d0902030118 72
    0x1044d40c01c2c01000071b52a01d65490004003001411001c8007100403d0071480035204d40c00c82811542c45d40301e07017080c001100101c2c031180003608c03070483c1d080d16056008440d01e048403400d58850b81402074003050045945c402400c00d903440100d030b881100250f6201c500d01032029031070351911591540307119100600070307a0050005110303034418003240c1d10042c408180003150840315002540c0e107200c2800114070701c1c024074070007400320700c185111800100009444180120b00811401c1d081d0182e21000712850b00c89490001d40503000fa00203841641c43c0b0b1f5814200680c824001e8845a00c0c49103000d03861030304182d00604211000c5034040e071150411f0320445100b914800d94202c480d80c140010785547c0d110140c00b010030000f01d0030000240f250031066009030a03100500655481c100402d50402454004c003d1108501c0303c000414000b901078806c00240954a840b1000b6004801d010001c00342c2108003103c1c1e0b60754807401c1d11001079400380328041010205014101a401240c10304858080d0403401132 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 492314937 1250 492313687 492313711
    0x21e040e0717130b04051615080c030115050c010906020f0403060501151709030c0a030c060e0624031606051e0403020f09281a04050606071101171003020405 69
    0x4060301e05201030140718459040b2a002c41c0d503403506c0c80e290b803510001007500510f440d421200402d4900c1c00c0d6007100031110244d501e0305482d07251200030048610003842292921644001d40e40b0426010340094041d01c1014000014a4141c54841406a0344070315030f50707810b0540008090040080754480c027800f40c00041412601129074400262000008815a00304600c40b6800500d0320b0a0400481d000708094406850302c0706924603014088420120040300d0345405c1c0442c0846425001a000e8412804a480461528110559410040c00a41220307402d405030101c20800001074035261001040c9a69409030b031003030b48a070302c0c101802510300002d226280c2080100f0250f0780f0424070007400c80d811141d14075144c64803410840268186082031050301c42c031094860480100d07030300c00480000c0f405010606d0300c01e030004001c201c0f14201c40c042d40c820310910084012421078400d004507828181024803070b203804100e0b000c1c01d500040700c0701c01c880981d07801c0500460501e4021503401080c10700725 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 492316187 1250 492314937 492314941
    0x501150c0b07210e030a0e0607111c080f030709080a1104181e030f14070f050c062709190e0c10080105040501050303030415021e040e0717 61
    0x10764020810081c095000700a8810110403040b01401c2c0c481d01e5000356441d08119400c28a000107899410040ca110003042032550564110700b040300440718055404a1409403040039041041064016a03442c90344206203404580700007103520303000700b00b00c0715121071180d168a400b590042003e84941c000f4003440d00061400c0c400625080a40081c0203001c51700030038034504c881c08030000b804603003202902c069841112502e84ca9606550300c45004e00036515141320040510b019103a04000e1211207036034140c2005070300003081100711482d8807148104140c03004003400c100092456000007a00240c3c003045080c0ca055028483c441c103070303d0800262003d14003442d056404901e03030314072802c40598481c0c035100014100501802180d1000b0070080c11114942a0b000d03008103a01401d020321340c026454100081018038001003924840c540c441c0d02c2c20410091406400c1c043e4115000c60f60100c00140180e8090201c040080c0c0094203030300540c0115460200c100038002c91052860005403095001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 492317437 1250 492316187 492316193
    0x804020a0f030b0112110424050a140402091206040b070215070516030918091707020319060b060d0c020c01030507051603090504110912060906060108091f0501150c 72
    0x50070300d04440380e41740801c480c2101c80c1001346d4072400501d0f4039680a403a0424400d20010400c003820041d01000044190887d225030601103001c0950088605010200d14071152500c0d01d1340007419030340d1f00940b0312940010540801487d15405540413520103840d40100019280d040040c0303100004104075600707007400c00d004090040d1040303600818003030104401030014903010790036003002040c1d4801502c40161880d441c10004064000048a0703040f526041c1c3d50104045905840441d034004000c0c00340010070f64a255420603c80800b02c40d031356211014403031142e4410016101310b20b4200c2002c1909075503900020309111042145030b05052030070041c400e1455010303050707410840001e00c24800800b0706060507108102d465000c5a031180c00d2044114003605460040c0102c0e03a01074515494085a100b6015103841086039400d4050344900d000645540c4100552600a84000f040d2001e444411720010407205441580403452038403440100250b80340e020740015811214680701c2d203185407030307030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 492318687 1250 492317437 492317453
    0x20901080a1803050921010609141b03061f12180b07080a0e070f03050606060f1207091206050601021213030627030804020a0605070f02090a020c010c0804020a0f03 72
    0x1201408104e00440d8004554450306400440501400f4002554000c0020168068809030003406085400e00c0f00406020b42201d60181c000c0c141c444100840c40003101d084103441d0801050030341e1000007100c40104000000003510038820342d56544101e60b008106000e000d0325034091010181840303268030741c404500501000b0b50009410700e04051207440359034403140030f0b045400055446015140c0001103039488640c1201c1142e1180c02650407690320f60040001d5402044140103e200f0200120b0000d4003407082c071264010700034103108102c1d42d215059050a4810004100c9410f584c400c103100082da0100700664902402c0c440403407030403219513448110080a0310004107141c0d01c0d50500c1004000050701400d5500020448020081203030600501d180026034040e07001700030f020800b203044c9110300c0c116050140c01841c90080000d80340d091000080001b040c0c01902d40d400c0c4034503200000d003801803800708980c5650700402420240104003000110340d200141c0070340044001c01c0051540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 492319937 1250 492318687 492318731
    0x70f0f2603070e1210150f15120b0303071211010f1e0905010b090f1503010218190506040807030b06090f180a080a030501091803300906020901080a 65
    0x5881d4842d5180c04c0a540d0341c90000248041000d5500380410300c91001e18070014042194640300b42c8640d0203640311480f441c4a0f82543c8608001401c0007007900c1200b20315040f440c41400054112480c140440d1289100032200812200005e402c00900c1584000240600c03500c898005c0c400700700b8071003c05e0040c01e201a07a10030701800c82e600c0d50801c3c01402429403180040b0003010700b00e025245426944545103101c2142d02c00e10351202081c9407030712400c0500c00d5800041f0000c1e104c130544000c2d50100b0a41c002c1802416211107002c400105040e101e0002500007010588000c00c1294214030300803901038002400b49015180800401c140b01000340f81c0c0f45e822a01400308900210300d0451202d0500a000401030450b07040000c018401d143d141e0710590403202441c40800c40350f1044a0003d50200c540040980041c80c21390040030000e1042d4030400803404400204e40d00b540d5107030b100e20300743d941c2040b044da90306601151020040d40c1011855030301c83c1082d4020003d0780c090031400c60f180001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 492321187 1250 492319937 492319939
    0x3010c0917030d050f060109140d030c05030c0115081005100308090105120f100e06030604110111240c040f090b1305160e1212070f0f2603070e 63
    0x1500e40e108140750103100b10b800340403000005002c1440c0205003011903500c2a0307400c0e400a00b05200005902002004030002c400b0f00070a00c040c59806628100e07150740707800005036802c2c0010011340442200910803a10040080300010b59400e02d003401f0581000544040c141d451030900080210320880b4400c40c02c182c030b80c050b050340d03202d4201c0d100495840c000c202c1102d020b0b132194414002829102c1ca4014800d200d985019400035480b101d96582d1002e0a960013501075202901050008001110761a850031040c0b62407154881440e0401d480c080190b40d104000c0d440c6c1000d403405114035030060310790003207a0050039460700d0300d000e0310011038445a100351455550380340c1003640c407503440c0310031005800221141400309041c00c112209556090000d454085a081403d507505800d001655250206d41c8802900c0e002010030003002c072036444404221401c01000c0c0c01c076400540e00c40350054055010b40d812048101c41c0040400b0448541c2488509401e030030b104105205900c42441465804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 492322437 1250 492321187 492321209
    0x20a020a15021c0902041107050319021903030f150821070209040803060a0e060117360106050d080306010f17070507150c1b0c0306060f050f03010c09 66
    0x80c421003a04003e0160300c10310240c0a003140500840019142c010386074050003120200f085100200f4001414801c809000709140c106100c426109100d88010f41303550840350041c0c034003080c5110103078160b5030030f031070701c100c000c655102c65025000c41e40740300703c55003283c2019418160908000714590746815201c4001080411209010b411202d400c040da0406030303028010540c1400c1c40e01e01803090b03800860f841c5029501c003c5000903104d54101c1d000c3d014041c1078540a40b83d02001d402c8424044004100300c8411001038046400500451040c001d20140001c45840050280c1200d40c03d5030b131070ba0f12591060740c003c0400d4000c1408071003104d030014401d00301540c1c404042c0c2d4040e11021901d40d601c0b4102d0304040d040100300ca402000a103101c6100c0d052040003001e01101240c1102d800c012040300003aa000c1031641890145030010009500855801d4681541c95540f042524500d400030301c8040d40c1c0d25010030a504103920009a400300480007842400034565008144002c90f01c80c03107010603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 492323687 1250 492322437 492322463
    0x110d0221010b0f3103021905011b030c0f061d0a031418031608011503080717300108061e0a06030b100e090f120306010306120b0a0c03020a020a 63
    0x1525602800400f001031460751340e030301c1401c0490442d101ca440240c2c05985a828119007028a282145040c3d03641610355034a1086500221005131160040440034099544000c502140c0d2190003080c01901c1410081561042e40b4a00b2031000c001501c0707100710380c3c0120003035400680c21078806404100721401064a500c002c0300440514031440d6201600741c0124a41d08012090000c52102a40ea01c6c40003070100415200f465040c01c00c0c40c1c40090f1132240144014000a2411140340b16803840b1454030345e040c06042000c4a40342c1840c0061082e800344403c0d00c83d88a04803a100d01801040107034003401180c5854104480c100f81010300c520b1000c1500b800041c982c0b00d0b1030703000401540c0c118455804a24106a130794918412501400d407102d0303010030000d02d010900141c0c0100307c2d00d411001e0f020800400032441815080501290305141c2c0714a40810001540640000d941c0e005070352403161401d24528900884030440743c041e040600402803171071143d80015070201c906500c40b0082d4105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 492324937 1250 492323687 492323707
    0x11d120301121b0b0304140c060f180a0b13060f0e030604020d021201020a020102090901120c060e010c0204020c010227010f1101060e09160b040501090302090a110d0221010b0f 77
    0x383c10030b40c119403031101010040c041808090300c4000c1140100d101180c0c0c03008a2102040300134041d101b0a810070810400003023141c88a245072503020440050003500c0d1458503120160a1500070b49880340c100c07440460208802940b05040c41d00c41c07851400c1c00074541c02c89502103070715003a00910117809541e010a220003192a0700e45100e11020101000f1512404202802070107544079504040c86002d2390b000200300f41072162212001264400800c00780186004000d40300510320a50650510032043c1105003d41c9136030000700b0820030740100042c0e9440d0080c100307010060030002031450605180208684c40e9070000681508da06042c102020780c0c40b00c25400301e01400d269040700070404d001c1c10030b101d111440001e103106881c80d02c5224049441d101c8540640d280581e1080703a00081103000d0801c0075003413080d091504585914070200740c02c0d4400c100e94100b90300181c0e502480340c0e070010312002d001c030084154200003861011b8545865242454100311400b5070144d1408644c13000403590b0807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 492326187 1250 492324937 492324983
    0x1090f0915051207030b010806091c0e130f1d0d0e1f0c0209011502060601050703050d050405030a0306080133080d0f090b1603031508011d12030112 65
    0x1003400601c0d03181c000f09042d8a19880d0b654500c42202c1c900b0420001081c020004501144164200002045d81d48e1000321042001c819050001085c070007029014038654880c040e201c00d8086451201081309152440690200c52112004042e010700c0c80e01d240c10014000300f5400e130f0000903813800e034403003d01d080006080c0c00798051000900510262010035200d03040080e036030029000b2202c59403a0380e40e070104070a800c1108d100030030050708050005036681d801100a002c40e94002d00d421401c2410050115044807026601035540350f2000c600c00d03903901da0500a0038041c0055000038880c0e4404108044420184044c5110b0200e000038204003400d05455081001007174210101c9100204218020300708201c00511400026420720f008228407810008039822509100743d21111460180c400300c0c02020700720f00c80000d048251100181a141c01d0080b6001c0c91500c1254003054240303080c0c0c19141040c01500c46541480900c01000b0302001c246107040c429811075818010600070319181300e2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 492327437 1250 492326187 492326189
    0x10c020f13090c03031e1205130f0b0105030d0905030c04020a0314010b0405010e100e0f04020d14090c0d0b040b040f021c021305010b04090f060509180c01090f0915 72
    0x2501c185092546001d0020502d070300d50880e4081d44540e601007607005010400400007003801c8002c544480316204840800e58001c80d40700d092142030080c582d2007079541ca19107c00085095400b0749001e00142b060345414400361030310401600700b07007080c945464082038540c0304400c1d0040c800c1d6804190a12124000d402512500510049400e443c0d038460540328600e41050040c070b40055a04042032541e410880d100030715915090710348403c64601e80c42000002c40c44202c8054000b6028020310450041e01d006840c1c007101e0100d13005415140030031000349440c4c00650f84038807500c040c492050118031000c1f504d980264000f07943c0d20459480b800d29041e4040c12030002034001e001300030b0800200f0281c0c0c0400048030310840d1001440045001c900c01a29800c1c0600d031408c8500300410411601154003460800160640c0460010f82d2180050285002101e80b0b10003140d040c02c42c034400040030310410700f0303032042424414400ca0600080c40c0e810003450061400070741c2d0381c00301c2c2d219081070002524 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 492328687 1250 492327437 492327469
    0x20d030b0a050d0804060212070b0109051504061511070b09090721062102090a0903030e01090b04021f050a0507150c230f0a081008030c0a0c0501030b010c020f 70
    0x40e00e0f00303102d107041c4841d030348584201001401402d081c010030070440402c54025680041c004515039080100e840020f00010b0b003c100e080a00e60201102501c07207008400081825030070240000ad000171001c0c1c080c0414000f10a0242c0201c041440402e01c02d80580e1000101a20303070040a95980d4010348450081028103e800088242c04c032038291016085082942c100400000f0400400761001030704095181000303510006580015803511444d911020404c0e0007031401041c080c2c898031140d070031134058080607500e592614080000394184161340500b100c100410f42d11004160354070040a0b4014180c3c01420041c0002d42c40e02403190500301c10800801c001410809070a00c0303800a451760030300054038200070f40070401c1015803451440a8401c16103596910500e00190f00c403045460060003021048290b00038400458841c1d400c102404c403482001000f0b10705200581020180c2c1803440d405141014204200c94070180d91000070084219410b43e074175004440712900141c048003207641c100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 492329937 1250 492328687 492328699
    0xc130914030c01021e121603060302060c0d080c0703020a0b340306080109020d0602090a080a060209040b0a05030c100e030d03090606080a021f02030f0a03020d060f06020d030b0a05 79
    0xc08102d80c041d4014001e05440700682c03503034042c4969080c0203e018400c81000c10f413000c0e4002680f0110190030001c0b4004061800060880c2c403940011110b8108031240f85c0c5e6a484040d4204515422855481c1c211088018150030f000744d95400940da60b0403c079000385040c150001141d040351304c0119040da10f40c90140340781c3c0d9880750500c03e4600e0b00031030000705001038107200c03002654500c180719810342a500a00702d0141c5030301c42c1e00d5800195200c203420940160082d4000103640700140400a4054824600540d862503600e04120560f680c61000d14841d00410008100d203540000300f420100360300351180c209030f9046480c1910b40c0e2078503040d166054000c25011a0303041c1d50507444080c0603841200700708110f07512503015543e500d6400c00e000303400c078408100d0074507405161f110500803140303184105e074984189014080090780102004a0100380c001c2406145c44500f80580c1020380824400c09821601c1c100c0000e594081c6000c0d40340a060b6a15001842a00c450803401c2c00b4150117401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 492331187 1250 492329937 492329947
    0x2a060304031706060408070519030c0803031005150901120b1c02030709060b071506050d1a0711030d020a0e0303120f0c040b09011d1f030605030c13091403 68
    0x341400c0c1491040b81607440024000034414509081601c05454100c4001d091090508041c04900f00c9120510700d100c101c04039000001500c0748807000090000c0c0400b031034030785c1804009100c100034503030052442a600441c1348441c5021160a079031a106003460200214107203040c00a00074145d050b1069003101118003541c50044c000d154541141d88240c01301d40c03c02d90703902000401c0b540d0354040d00d01018802c1000303c0120303038030120503403c40729014000034030141e882c000600e0348011a44122000e00480c02605040882044110760100c1c45080040c40402d030308590365128821440e60034001070b804940d0040c0c0500c20038001c3c6044501030102c17591303050000920703152000119080b009440e0710600282c850000302080c2c4040b0b0796070f02d41850600d9542401985c244103003011000c40c0e88408071400945907101e440a41707400041e036038000c1c0021410840203068820903000b080c000c2c1d22040e104100f40d1100d05114205000509002500464501d0300c40e500c801c050014000d01e10010032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 492332437 1250 492331187 492331193
    0x13060201020a1215170708100615030e0c060d020d09140715091a0c0102070c14040b13020903491e02160f05090a06082a060304 56
    0x40205071400b0300c0c0d1604050010092110030035501030006500d809084480100b00f80300802101c400e182000740c0507504400e80302d0110620309405030f5140200c0070307100c510400c1005c00316024011070284a20301407200d00c11003800700c2e035903a80c1b00326a28011040007501f45050105541500c2c1840b00085c010f114081301070070000b4291124003010070150064450004116038014480c100d8242a515110206850300060100c41d080f0210b01c504080400c000100c8078610138402081e805201c5c80c1c20301e40710703810800001c1681004070841c50040d1310306903100e007583d5a00004680b003102d1078000966500f01c12404a4140002c880840112000c0404150404900d904100140b0003a80304081002d07000100c46d544200700681c060401f00345260f483e100701440c0080780000044050044660f004686048000102840d510601861301d01460600051900201658000c1d072092018031002e030910641c00c0e2501034002c072400c01011302d604040319144941d1000500ca01d8010291500c80c90142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 492333687 1250 492332437 492332441
    0x23030739110f1005130306090f0501140105061b071e180c080a0504020f0901060f18061403221202061e130201020328091a09060d0213060201 62
    0x31004581d101c0003018000039508001d4116000e01100030070140c03c95241d00000d48640d07000c49004481c50000c1940840845d00a01506c107090748181d04a218081d103d0038010700b100c288050400050704004010080d994030b22082e0360300300216034440018040000c58481c0361180540c4040e0322030b1412060f480380c41d40e03403e2901003101c90704204099007a800c000e440e004c075070502e2001c0c00030400c0400420954012540440d43c0148098041c140030141c008c000f49810809070b001d000043c0060108240b03065100c8040301d052004100c44180041c02c1140141c90700ca00d15800c0d40c400d000c01310001d60000302c0e540620826581a51540200b00400d0801c5240c0300405020b60026110301004038490800d4040f10910021540c0e44407600307078803411488a5000c080d07000a0341144000d100305050000c0d0b0207588070b850b0500740030064a282071644042d04400030799012902c030301d25100e03074500701c1007021044a6203500210b4000d0703910715200e0940c41c02405403080c0f616074500250000701d0300c01c1e015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 492334937 1250 492333687 492333797
    0x60118022701021c05070809030c0909010507020c0a0305150705161514100b130302091303170405060403030507030e010e0d080c04050a090b0f030d02010c230307 71
    0xea082d5804070b8540c00c484c4000d90300c204581c1e030010340100710510110300c020002d8964944020195004540c0f500f0000b1044201520744c4021a5542c0b0107104403240c0420ac1d1084608007600d909045030302d161946600c525050f8204a09581c41000254050b8030440440d51005e641425825010080d414816111000ca0031020031440c07512002c06800d50340d00940d540b250015030124564113040410190545d00207032466450240400da000c001640c0b001c10047c0300e0304100703110300c0003a0740310f0400800600c11021041007040d100070501010881c0070035055403190700350401103a1515012400c17802001c2e9900c468065520300185a2501c81000c555021401034541c0d42415503110303510725020340d200314810507a0106186008100c900142c3c1c2001464071801000c0d003155803001b4011908120141d1000300051759504992080715401c0201e00400420404050251510050201b040d0303200203801c64084c401c6181c4519400e2810301502c40564402c078009048000c40d0240081c0c3c00008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 492336187 1250 492334937 492334939
    0x90d120b010e031f110f1b01020c19020f010c0f0b090a1a180601060207060e0d0b0c0a02010c050a080403110f07091e09020901060c06060b0a0c0b15030601180227 71
    0xb0600c0340e4440009203000d1ba580d400303030505110301c0c01000615011141c1046034903800b5554003880046122901031004800030380880c100020301294500c10801c040b04440d1815040c8424100762201180d040060403120591044181d0b6040d103940020034a80300300c045004080e50781078250f00c0c8207141465203290044206080c410250640100644d485000900234800180e1002c142080355501c82c607a01c8101c1540607001c102d6070b0301c9586560801e014104c80a41c40c104000400d412525030912942d05864200e01d80341341400c0f02c0c103400610001e0060405000c0102d151071480500c03005000f5001e82c140c02c80222640340e039441015202400e846421400d4240d09690f00410050032801581107866004101c84503680c00c010058400c0c2140304000d1300d025544400100d0594000c00003000e10400c9034890000400103460180d80c0c0342c400400c0c8213200381189680c800103460008130941500e103900e1000c0d180100c42d44681c0000c0c000c55481c0400051641c980d004541d44108504081d810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 492337437 1250 492336187 492336191
    0x20705072403050c191e0905130501051f032417150a05100f0306061a19050a0311070c050a0501020f0c0103020306010306080f0114090d120b010e031f 66
    0x48100e4090b81140e2044821050360a400c01038101850748849511015044e1400d0859104a000218001100c007030364896000c62a003103800d1102d80fa080e040030609543c050400d10240d8180f00c041b480d40300a5020300d0409003001803500d01c01c1c9000743c21100040c03044c01c15070410090107203d490091641352240c00c2a101900e401241751420111f40f0b4500910a012284129192016104018000106030564482c441c08000c2181c0c02e5070080f50005502440c00070556604020104005043e0318a00c1508038804000751003e132021700002034211141d90400d80c0e00d5503e1403100f42c020307280c41402040b01300342c0025400d00b045004085502510b0301031710020400d075201c074010f84c0e0310341404142c4a03850f44038109200d101e41c8a5002154484018980400c001e41d59400b100e20b041ca0074000c500035651501140c02c100c4000c1561158040856002800308d5290550058010444070030307090000ca8903411a0411070340103485550503140043c0803603000f60002900041050703850120345000034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 492338687 1250 492337437 492337499
    0x4060b22050a1a07050a020303030a02120c0403050c2b140d080f01140a090603200303040f050103020304060216080d0c0e01080c0a090e0c04030611070309051302070507 74
    0xb04000509000f0758103480405442c00300d0b410125003840c1c01403201122203114030031050700142c506102960291002c0c14002d610307880c1a880030100f01200500008403400240410000f1590020704e4050050064450810349500d00d4080d0640083e01d03200e43e001041c3e0716000c94204901c0c030180504008801e0251a20703054500f10880300800152010700d01091400c00500009610000044007068000c2c0000d101c2d0f90f41c3da400b0005e56a003584180c80d141400d0520b5811182000b4030204c070510200c02840c0762509010135440900b4040c01418101036000c40010704000c1541c0c12541110301840c02640880064500758220b60b000000660310a0304001d15440b5080c012001c003240300ca4161590301c40c640d140d4000345019005500120100185400002840140c1141446c081c1805840d100d5a890075800d103041620003060610300220000c001620100343e1159010050350303c2195440c2c402002c003103056010740201c0c1c1d4013038028090102d00141c120381301601402100042e00703002e0300341 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 492339937 1250 492338687 492338689
    0x50702030a02010e030a0e10030905010f02030612060c3a0e16081c0c060606020c0f06030129070803070306060e0613050105030c12131a0c0d0b04060b2205 68
    0xa030040700f1b03000021800d100d050500340c0c58140c181410000722490000740203a403603241c6a080d51001402c852980342d0000501c000c504244040c402000001c0f0300815250800340f4605080d8850300c03210450042d01c1001450310f14a15058103681c0400000101511a41c00d500f404001c2001049503038640c03055a01c44030008040034a04800c9820703040142040c090b00c0c0c0d02030203105aa481811080144640383c030000903000388203034800f40811b98014120341301c0b00b00911032040c02d02100a840355006000401038045a803945002204207003c5515540c01c1308000c43c0414029940000c00b5070001004100d64503505502000444600b42d50300340c41101c003a0180107043c0309101c5c0c120300303240c0c03070740c0c0c013030041d54020401140c000500403203291610001e80b0142000c80f030141c44c0203100d440314010000030701c11205269035020b01c03900b071400c019007840c60305001f0354400c1991510030f00361510003c4400e66141c0c3d1000c00100704114030f05039110500450002840395010031542000c1141e00c001c207803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 492341187 1250 492339937 492339943
    0x6090b090907030807030c0209180c03030f220b030906090c0a24050f0403050c04050604020a09030f021801090e0706031112090c03031210060c1101080a0609050702030a02010e 77
    0xd41c65030002d459164103544030340b070142c0c1c095501a41445100c1401c5401626a40c403d1407281155411040d1000e4100c150642817000501c82c4038440d034400d001800b45843d4ac41c00315030040e295041288065112545141c2d051140c81e0f0140c441c0340404010424900b0021480c68400e400c42c10603034820107184010030046001c14060070aa19450148078203018804d0f58500c8440c40c0d181c2869420600064841070481c0d003d41c204035011303005114400e0036030500d40141d0307130403000445080d420054001d4001300034150318400581308845070b5183d201552540c403440f41201d1101c1500e9401c2e5a100e8030306030060440706c4900f0001d4403403650001030f443e11902c0b65000711030031071441620b002e8510701510340c02400900f80d01032902402101c00019a42000100003096416541039001d103071104244680a640707601c00403d1295481c407020014900d0301d44411101c1c1c003400e202e00c0e86d031604403004004010a0b00241d412600d4141840744050700000506001c2d610350f802841240e500307003034950b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 492342437 1250 492341187 492341191
    0x2121819030f050a0c08071208090406180b030c0603041121060a06080d0c050d050c0106090606080709090501082d0d0504090c0e100f020a0615030c06020d0e0f04091506090b09 77
    0x30000601031961400a203200008144200b8012f001003032041d1515205541d1602c03085241c00e0056448000320b80303501301484000210342080ba02c071801e40c5841e846000990380e42d00e04003449000c01c048800b403100b040389148030200040700c04441315440d007003035440000c2449006002084c4a0414907411446c49a000590096881030151907403512880d02520190010001074030155290900440c0c4902640b2403800100150b85d80c010540c180008041c10080300f40c1c1201c0203c50609006016240c1d000990b504504c41c000c4901520701307504251540c00c3c004e003034442410f0303010b00014103040d5a481400340080d1903403000d08110703480f8440c0040e43c180d1054903585802c0a82c1c105400d400074056100300c0c0501140d07005032211140590343d15001c54000074403145401040391b03014000d0103a00c980341009410039000070011078850280c0601002c034408000d92284a04000d1150240c0b260b4011790010350340541c0d1404a0311040003141c01508050040000c1c8520f4800e84190720300e05640280c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 492343687 1250 492342437 492342449
    0x501030c0b0a0c0201210203040c0504060f290c0d020a03030510051c0c0f1e210f05070810090203011505010f050c0c150a02121819030f050a0c0807 65
    0x40904940c60340152140305101d401b41d0303903d40456482c1c03113251140d070000750701c21441462041241c50401013007000715012908890001c444c081c205200ea07042d1840701c40c51420302c00c412803401c0c1c148141912988d11035443c080040340150015245200d800048800f1054400d890503c8555510540008a0502440380503800031220051780d80007050194100510341c00f4100115845440b2840440c0c0c40055500c5034004400c400c04200e0301e144108512400380500000d440702c6e5500070390720000120800003000e0080c0e40e9030b00d04d0000b0011704001c07420040c6952420358680306544e015030001070a0800c010707400b030350a00c2e2162120030701c460004020344005840e00b040d8503030020000c031641d80006d080b18103c2d11070201c801540381e440b402c581c4804041804120b586000f00071000742401a900b212000080c018844541c20440c04e82c3c2c08600c608080c1c1d214943c2c1c08524140c0802202e17a54000780203d0300b4406100240072022030000002c1d03004d240c142d50012780e11110195200c078035210701 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 492344937 1250 492343687 492343697
    0x60e040c09050c0a030b030307020303130f0e040308070e1201050106170901090b010e1e04080c0d2307020103060b032a0a0f030506031501171009020d0b0903120a0501030c0b0a 77
    0x10264103000360701c211a0206e010702200d061400d60b50109145078020305000c00040350900d820000c2c003502c03000a40c007611107403038044a1800c00347e17000f614240b4040c5c8814240034001c10140220f44503d03160100380070b007440090050b03594030300e00076000032007600303400f558843d07202d0000328016130500908521941c0081c0ba00816886c1c1a0b4040d10188050204042c101d001600c0d02010400d01803494040c80c0103521203135076a1903020741d103460030070035004c124140300611300c40d41007003580a884441a200b0b0823002c0c9640b00b40f5840100d0080265401180c0ca864001c014400d000c08403985105140d142e04800944020700c055014030b40b07000f074642d400c0018030344028600790144039812441d080800601201e0018840c400d12090b40b10013600101540014644079441c6000e04010b807002c0c42000210400c1048103c1d00031070a40400228098201501900071541d00c0d072040084600c50060b1404801803420701d514098042e02081c842a80c124107000008240315a59108480d48100d81d91a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 492346187 1250 492344937 492344947
    0x3100603080708090109090524030d0c03050309070801060915230f0f030a0312051b1614030a020f010b06030723091306080118030f110a06060e040c09050c 68
    0xe000c9650b0304c80e1506504028000800083c0c4d0304a41c024540582e01e10200c0c01c80d03901c40040009058090a09040c0c4240e01c0031900b8400c1a4009140b12003290701458925a0795840050551518a80c2d502c860850341c0303481c0300020400c81d19803254840824006090401c00d40c1d541120510400e02c07a2031000203240544c0300e1405141c00840c0e100a860003520525441c000e40000030304212891000360b006c200980d1131500c8011140c80b610354080206c640d454a90051285070741860300910f540019140c521108201c140440c0350100b003900420801101c3c1d0329516801c00170f4a505003030354104611341c2441900009494001c0640303100701110b43d1060540d040e103c40c170404a40b268001e11101600400025501d0340f01c1e0100034600d4090260049500e03445c051186085542108150030718080b200c0046000a0b03028901c0d00a0b00c45a00d0908440c941c0da01600d414601203c400501040c1340c600c001403001150000301d071049000f0b280c8e0503d41e550360201d14040e0748040301d260310f401d0000c101c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 492347437 1250 492346187 492346193
    0x60403081612050c030403031b050406080a0b0901080709150531020f070507090606080403080406110a09080c030105150d0309090e03070b0a180204050c1215031006030807 75
    0x30305101c0300007691501003405040c400d01801150301c281c0702480041d0000041205154150150020300580c9840c2c0c0d10300e904a03540002c005024500400007007140003c04145241e009421000d040000141908a29652200c0840c0d40e5021486140720039401e1020000480d140501c01740d0458201404100c140c1c1c0c3c1c50f06103102440f0851050006410240360300511050303652001d000d4650002c01d80da0303921189400e20b0b915081c0264820548541041024044681d00c6450140c12030760500704010940c07201e1400c0c901521803c081a22440c17004108850041d1307001807914201c1350100c0c00d40c2c010095480901d8244c68049505000d01051010000c4d0242010860408200e000c1e01e4200051a25001c0802c2036500700c9031000360380e5101260f4601032001444005420000b080820000003851420158040c1d4030001c0103441a80c0d6800010109021081255070101003480da0703c07240d2414109950700360041c0c00c0054001d21810311030b000d41409903c590400c5d2078010306041c2c20980d95a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 492348687 1250 492347437 492347461
    0x305122a0f0d050a020c0301090503070201030504020d1e021e090c0a02010b03010f020d1112060d0c031a0403080903071a0c19032009060a0c05010e100e0c0306040308 73
    0xd0403103040c8220645030040c010284603020010314160354496a03000300e131310001d01e42888008403900c2079140c4401140060700c008112040f056081c200843c841d5580d00003c2c865240101e006008005041d000d10502030182c1c00418090b40300300c0303000301e0000e0840c020902240c0c0340b01185030802c4140300401c44062150015084426492001003a58160b410210b420356840e000f01c80110b54001c00c00380d07441d650900030100d10140ca8080300d82043d02040800482e45009019917015040310002e07501030080309402c800145030081c0b40c20281c0160700b0b800207141c240844090340010404c90103d864900048211481541c000c2280c0a403070342e1803070716404095000b401039070641008100c08030300500c0c01ea005188400d240d072800110b00121000c154658044c201c0101c2302d650301044402c20030755510080ea0255075003440d000c03a000c00189082c0b8014001d0f0301c480340240c400c40d00d1034521100a6002440200e00d020240c5030401609018541e950f002500d0090204903041c000510500c150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 492349937 1250 492348687 492348757
    0x5122706071401061e180e12090307120b041b080a060b1906090801150b18210708190f02011b020402180108130201020316020f060a020106030512 64
    0xb040000340850b40c440390b502407002c001c00c128428403103044d03042003040b040110084005929910900404d034015014644076854a0760130f10a5000c0840e214540f510104201c1c8080c1a00d070000e0b1901c2c1c282d40c1480386451008450841e0014078090380300f00c98890000300c1c2d008a0740d03000020010741001d99103600207804019101d17508440420151801c2d20306500c0722000605098445140c200e0034442d03600d0a48140c1c2246000b458107548080004800e224102d0300344a04d10000c840d01640c16030700040b480d5044030b03942c000b40c8220403030910f0500004594403040f22025812258450400c41001e00315070035441e40030b0b120714090880e41d03000d54081c4100c000341d448082480300020450b13a00040880e0822803942c0341c0140c48240041c2156007007044960000c0b903101030300e102d40c000e550000b91b6903c20301a09840510540901d9811901e038842070000a060051401c0d232107481882009000300064441512148a00c15040800c00701d22402c41701c0134010020604d00c40f000b10100501e181d9a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 492351187 1250 492349937 492349973
    0x1b1202070f0f0605041202120406110f10020d0b030c0609060f21010e07050c061b070f261602240a02010c18061d06070512270607 57
    0x150550001c00250a10681c6036803521602c80001e4a0400e4101442c02d244009803a1007950b010032080f0201920302c07415a42115a1b524054800401103c0784605012041d040003060740304044071070352008030300e402900707101002e4402080341d0100402059a41d8204030803490300460200064a414208034004140e02c03039a4917170703c0c0d1a1007103056995400b491400300302155010100d005018240707500c0c00386a0846090f10381241400880307200e00f501d41e0740262024154505e0424200c03482c40000e0141c07607903190021000c2071028920306081c0c20a0081c003041240d1701081c5554000c2220915003607881201d0307040200a298419542031012541101e407a0790990044e500744104180c00c080d00901c041e12081d8000300e22441460b0003c0d0004108038544842404d001d50140300855120120b000b0b554540c072505000d213180c82e004203800d403023200380107003d9002c0c80030301c152403034400d0b401019400c40301082c2c1c4807400040f0281340350386440ca58400b91310445c10008c079404180d02100d044401a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 492352437 1250 492351187 492351203
    0x3060415050d080403170427111614030c030f0d02090a030501020d0b04020a1d12011103010807050a030f150f1b020c041401060f0c0605011202041b120207 68
    0x34841001980680200b94211120500060140200402d0a020810000c503407140ba50906003842c194034030103442c0442140c0010383e00d2409958400150b040044034684e82406075555002ca000b00b0707140700d4225501503d40a40901c000c0500c000000f040790050351152015509040d540c3d0701007007999002c0340c0140c4055400b407081c540942d41d000c01c032200451141c4001a5030715138804010003615813219405124074414030596000c5904005082685081d283d81c0000540b05540065164858900452460742c41c1040008295144c680158180c0c0d00043c00c0303849031651601000340f444510b00004104412040c0382c0c10000301885e00307c8103030503008800411111003106020048480b801420303049842e04a5034005401d03018800b1508142040e81c051160450100414800190600c100401c1100030803000c510b192294142c0c0e116103910100521555a65480c0741d4002ca08040c405d03440703940b80280ca4401005000d0303031a91340002541710b40b426010303111607950094002100c02e1342c01c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 492353687 1250 492352437 492352439
    0x902120a03201e150a0204031109010303080105041509020a0c03081003030c060f090f03020105150906090c0901050f2b020307080c0a090e04050601090522081c0e06070f1403060415 79
    0x2075183d13420a0700c0fa1403100401a15945035080c0308803000307880c4441500441d404801400400c0e0300903e02815540141d80c0481d03454001c44034680e6162003a4001049503102281c02d2451561040c02c03100041d0095444403541d846010610f012240548070040101e092422401c3c0000c1715071f04070980c3d10f00c0b90600050f201c500c0d0340b1882c492801c0c8180460050b5510700c20003158103000040c050410303500742c51032074061404001103034500c28050544143c003603004c00e800840360321803011a03181403045c850007901c0c2c420311241e1180c415100000ea83ca1412600c0c0100141d10146c42500d1250311039a640140702c1c3c6802024812581c00a030f80c00342041444000840c108125210f0b4034015440b50000340030310342c901344401c81210740c080e100c842104c2041110006644102d20001505900030704140c0c3e640b250142150100060350405c0454507040040310740100e10041482c034894581b60319040700243c50418212049017001403480c0c024071041c40402d2040c1070550101450040d5000e00400d00c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 492354937 1250 492353687 492353713
    0x10f030b030607020f0610180e030906041d061c14160f080d02030405030a06050c0412030809010e06100605090301020705030f0c0c1f030f0902120a03201e 68
    0x4036400f02c1d00b00c00903a0000b40020421101006090360040384c0c00e00049049050000c0d160350314807171740c006101c0300382c4032200d108004c002441241da038020004d02170366076556102c05250481c03291000141c0741d0351003400015098100384842120b0428051100c40350402c850383e40b004506614508006078cc800c0800c42030700c01443c4e0b810031780070307101c0309903454219490500302d0b030b20700403001480030f0842d001800104078903140000c210961517400403010405a0300c800502c00d0602503a40050010201150600140341c2c02c01492805400100000d114031915400043d075030311019036680301c00c200240000c122440c814000f52199407801000549440c10a8440a2454201001c482460100000c813011491420010038004000948031121003210440c1300000c0c266803400b00e0401e0640300e500b50042c43c5242e0b03103d01c0c00b295005111010088440e100c41d41d8854a01c1303000ca002c0740740c4444040b45a0005c03017046520340c00600c010078140c1401c0e00b01030190005888120940e00c00c0310302c05410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 492356187 1250 492354937 492354943
    0x203090a060612020a180f06170c040921020307050708070819051002070614090102090a0b1204060c110f0303041a06090103061830090b0702010f030b03 67
    0x400104004003920445800c040c0d04030741e01d981c0b01d0800c85810111910040e00c4542016080710241c1039409203901054641d14050580440100300403881c1050129500c540c204034030800403404000c075020604100301f800111011080c02502d00e542000d101c505440c0e5184000040240314810f07a42046803c0e510765103400410b030020300803504100001e00c00340908010041c100c401c0300c8800c0190790b0240e242c054503000d0141d08039040580003e404018171600e60041d002c0a07021614100c0286008250030b8004d40101109500c2041809000111400784a0079031303281c46102c25855a0549543e643c102c028840c045100060041c0c038078a140e14054240720003000003610602070342c0d0f0380c0b400749010003031141d4201c1c501c0400c0d4081030902445854843e00300b03040da030b0302c010001403d14011f07007501c1021142c9580203080e41d0b8031400c605840c00308460580000e142c40d1030313095404c13050880251640d80b40350040e0010343c241031041001540c41220510142440d40c24009031030001c2c0008241 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 492357437 1250 492356187 492356191
    0xb0f040506040f0603200303030709030f03050408150105040e07050a1e030b0a05010905163c0507051903080712270c090c0203090d060609061e0f1a0a0c060203 70
    0x40e040c5500c2052034461b0a0b08104405203c8114003551952520743c1c00500b40c0d058a0002410791044420f48004042c02030080720301800520003114466020880004800c0000b40680b5000301d081c8028019540780024180c0c007a240d0083c4400c546500b4101c00f110295400702d5100c42c0940c03500400404035031462100c900401032000081000d60510074024141c0300060040e05540c41030300d171703140340c0b0170f5224103820500100030415030503c035089240130310000b44821a032f100300c05500d009003001c1d5030008000c0001b54402d5007628154061040080070b000d0208070041d011030300710800640c00f03a1203480030100219510000149490310f8002044a020588491860581c007400c603401c00c1c00320127041180180849070303092200710444030000307440340602551700d030080781c880e2194030420101e03400103000f0300000c1e0004c000d4a0b545900703a0a50704200c025118107000c85400200d54103800301082c0041d5003506080003a04640c04136a0702207640081e449a041012012800b40002d94a0000714 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 492358687 1250 492357437 492357443
    0x271a211c020a0606062609011113141005040e090102070b040605060f0f010f12020c0d090f0803030705041a120711010e030915030402031504030903030806040b0f040506040f0603 78
    0x44402d03100d280940480c3d000e6003000c0d0170301072041611445400d040320b83c03010000c031002002425444600c6040e0141c600071950401c0b605c00850321080510441940400700e40360148408180d8038240305001d007c0c02e4811990b0b0001d4010002070214036000390f00141c011030b00000041c0340403080e456000c612002582c0454005032100240f201c245007508404960030380441e40b1042c1601d9540001e442240100007102c01d00070101e160b2604a0003a505850000c203400b42612522499030704000c0499070f0030b0040e003a003402c0007140400c0400c00041a07038400c400c20b882d903d103414101010a4104004044100a00360040050050701d22a1401890040480340c80c6c07100c3e04000c0055140c2510030302d24074850160710610a0000aa0b1000c0c400c143e2011422811030f40c03a00d43e030010074100010300030822003051000d0148030401d60f2051411045a01982c0c4200031520f40e841013000350f44002882507404007108400c40c40600c0c03d43d010642024005000103000030f200140d810507284194016 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492359937 1250 492358687 492358693
    0x21061a01092c13050a050102070201020d08040b040f0609060f09030e0f060d0905010e12090924090c090d050a020a09050c180406271a211c02 62
    0x644440e5030081d01e10070141400300c2c000764840c0c0003480c0745680411002c0c04203420b502d40700d01142074403001c007034080490354229080d0b400c246281c5c24003074040e5200000403801446020180c1840e10701c00d000e814080c6510480411590f15141c99015594025884c01c0e00c04595a02890f0001000d40c8140009400000c0c00410039801e1413701812031202d01e482c482c060209034141640d2556080225072807240700170000141c0329182d01309203004100c0661903805902c5646032200703c061035080989000c18040740c151803c0e0f9100790140704c010241c1041483d00da001803001d8412840d09400c6594001072001c031043c10080d81c0c100050400c40c1c03404050b180340d007244000d1419400c1c21043c05018000c12141400142400700c5424103500c10280c0108044020049040d41740d9203039001400100042040c0c1c0001e49a000c844070a2030502d00b10b55000035107050014001c1440d1030260603090600200361524220b03a10180746034403200328858441602440328111540c868010b000040c0d51019801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492361187 1250 492359937 492359981
    0x21c02130f0c14030114090a021603050d150f0306090f1e02190b0f0c010f060b0903060702150a0c0903080f03010f060c050706110309090910180c2106 66
    0x3d084140c02004200e00018104018010060715000908130b440c016aa18211030350f031009a00004e0003540b2040509222940701002407543c81005401921404002085007000b451a440d80180c0103114042c5c40e05075001040001c50b1107603004814450103074481c0c180d01d1285648007840380ca158090103010031001d000820031b60600d03079892201c1e000440341a0040a05200440c400c1c0d02480d8541c80e2090800542070101003020342083c401e00312130312000d000d01901d896040c019034028043c0c4038001d100c2c910000e00103610000d0a00f0040705200c4925000b0340b01c0b44001000340101039201d0047c422048000000a001000145500c0b000e200c8081d40f2541400011601c014040c2d12540411849039049000300c0d01c0031803040b0440d40281080c59041a090031b903942180100305000e544600a00d0800031159808103860502403210300040203a120502d041c0040401c0300c4102070081c269040303080c0030800484200303804c002400f4482c2c050b032000c40c2c1c1c1c3d1402910508021940c2d10904965 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492362437 1250 492361187 492361211
    0x3010e1b0904021f020717070515031006030e0a0f060c0206090607080109051b030a0b030c042007020f06030703060f32010909150f060804021c02130f 66
    0x54141a0010211800da0a0b814a030300020040d5014942a01000c8a0f041d10300c0100c81c000c0050360001c140300e2150001013500388005035100c421610406c7c0c054901e548481903d074008904030fa10800e91604840c030128140303c800c0b4002c1c10303045d4007504684201c00000000c244410011201d261159034040750540c1002c60017820900050f0403405564040800e1194694015800505507201d90340c00080650301d40c2e01019258109a91a00c030010303001007840019941038004c90515101601140c5030a82c01e1814001220400d24901b41107840003c0403802a95002c0020055140000c200800c05042c02c800500142e1045d04c0b200c0c08642d547c1d81c2041418041c1c0384440042c400240c1201c66030303413910b11070fa50958048413150300300c9504030701c1c0c00a260b00030f601c0b01018041c50f9004011403861034a1541d0103050500501c3c1c0c401001620004080b40301b0107049105950141c1003050180301500058030301c4004040c12a40044003a49020702c0c900c00740714040904804600218001480c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492363687 1250 492362437 492362473
    0x90516050604080a03110102040e0103030509040c051305130b220c090302060d020a09030b01080d11060c040b0708040306050c07030807080420030c0607050d1218030c02040b03010e 79
    0x94051409600103002c02c01c001c00001c01c3d020050703600b504045034a035019400d403a0080c03107142c000356501c00c180c40001c000d042e4407902800c610320081d1003c00118655400c16203e900800a001b600341c0c0d006401070285041c140b4004101c90700d117044c041290304180001406c42e225074000c80c1080e0350b6119000419415500902401014900700062064155004160345115607041412074580004481d00b0852003054844004d64000c1d0001c825544c440d1101c9880d0107441c0c0b807200020f84164102c20002402041c01070249000e25034180c54203240400460f415000544103170b403282d0051000001041582c0180ca10510200c031034aa070307501491502034801c44003c1c00001c1003050207410030000545618544c540c10100456140340b8403401c83c000b03450000d205205a8002001207840030400074009052000d4490359141c05400010244d05030b011a007901ca40514406040000040400d008200d9001000d0000d000800d54400010200303081d5203500556004503400301e13001c11290a000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492364937 1250 492363687 492363689
    0xc1501090507090b120c0f0d0905491b05010204210b01140a05031207140a050a1104020904021809060a03051507020f0a111807270801090516 62
    0x380030701504042c005c980d050015900101002c080030380c001842031030001c02806817a422801000140301040043c40c140d42c40d071b2110140e4500b51120790241c0a02411102c02c5ca40301708191032284500496140f80e12500c40c80c40b14000ea040c000840b620800c103841600310444c11501070740025a8a0340740440100c80c07050020080c1c8410401000820300260000007a141112072840004616400750800242c0701c0e15541c0c0002d50503c175448081e071040114201501c051800f403a8280c0b00c044629040300d89410300042c0040c41030300040004070004036503040400d410b1201801c0113080883c3c1c600410100d81c0071070201143c00080c80c41c0100301c0d140440f00030758400b80c281e5080082d82c0c0ba5a88050340c0341c181c280c3c030803601c50010340004c40c003030720800044840104030b030101d615450403405c06080d000b59040b641405100794140f072075034005040324164000d42c40b41e91541511f000b41149002030aa02d08a84c0410100c3c11f48002000102401580803650144021781141380340402c04802030401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492366187 1250 492364937 492364949
    0x120f120f24030c0f01050d151a19030507090312020f0705031216020d0b040f260a111c0f09080c090103020d06020c01020f0c010c03051b0c150109050709 67
    0x140c504440c020b918042500d0f4061101950346200c0c0d4240360300143c815025114482c0e0034180350140c1800169105a04c1604135140d034801e8660b0100b190064500c5842070640030000440ea07038076105006807096105a134401d015262515a094a0750350b4072840440750b11880c1c005a125a844400120b0140044002000d0480040050401410050256004409078124203500324100001951511070f00584510381c00200d01c080e41c50507280606150486050640e8030b4015140802c480d050040310002c0d0b01c03000d200ca50390815454080c11550341c4c8000f803000c64503000b142e880752400e001c000304d03142001c02c1903290041800ca01309002050f0400941c40f6202039401602e030401251038541ca00782c10b40e40c066503a03c0030003d030b506202010b4450340c003803000071350710018003050304c0902000601501958a0001d101000c6069821401c1c0e0360240ea21300c4101d001240b41000d00d61501e002090b6042084d13098035440c0bd0b80c02000d0851b070800360300c40c0050503160b00804c10790b183c0c00310091010300f01d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492367437 1250 492366187 492366241
    0x60109030c06110c0310290109090509010212091e0a0f0b0631060e0f0a0513020603090a0212030a09050d0c0305030c0a0605010503010c02120f120f 65
    0x219544855032504014030400303091041d030201e10780a01009000071030802c0303400703011180c3ea1106070391b03601c00074190b02c141404003603a42200781010f18001d652410603540140d4a010240d0b080c080341200905025082e80403d40d030810144000415080c03c6034800c0c5035a0010f800c000700e882505085808120b6060300306500090744090001d40e8840c885080a90000080030349555401c000c0b400c4512415000112007a40f075643c0d41000c918080c2401c000d066554007480082e0b51410303076030312886095510124040601c400210107114a9000c40e92004e070100200303010f2442c640204045a1003641d00d4250394004131910000e5003841d01003003400b0911a0000d51400c6200c4800a02014050058234400c0750010203210a0082d0350444d103001e15040425203aa825a01684d680e0b0f80345525812120541413074000142c0385410721a009540042e50090402084038004484d0f0326484569610b84111043c0f0451500580044070b4610522054020300c9917414000b840400c0d501c0003143d10840e43d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492368687 1250 492367437 492367439
    0xe18091c120207052b0f05030402010c0b060609190302042703030b0f0a0806070201050c210c13170105060a210f0b072a0c0314010609050c070b060109 66
    0x81d5102880c81c8000c8040703500107881d003500c0e02d082410803d000096007082c01c01c520074494800f00c04c099007546101c0645072041c2140a4a80c203030342e40e010484001c0d0101c0e02007402200841d105d161007a80c060f03801491503251050794000941c20b070308007110046072204568000d0045041c248100784030000581444001c52200715400500009602001010136454600501d10364690b50000c51500038000e200140550322111110f0f0f861200b01c5941d40150308001c0403440c0d0103540402c8415000030300d041d802d40e9014880300000602000f0302900e0200400304401e08421000d0300340c01e40500400404504482c2c0c4001d11030307082d0b441c05440a0310600d01c0b034408122424045210302d400c6110800d44004e900524180a40c216440f08000740501d03804801700447c0c580d205031100141504504401400058280c00e0001c00380080b034000c10f070b09054903003400420711502265071f41420080001c20043e0b1100010821b40fa005e69181d4220440410844100b003440c44141d5409403080c6440f048003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492369937 1250 492368687 492368743
    0x201050c071e0303110d0c180b04060318080a03050f071b0209070201142e0e180a05030c1005160801030305030c130e07030c02030a140a0e1809 63
    0x1020800021003100b010300c1031a6410503010f0f4004079194000e0070802c907126021102da11010345110f01b080300004041d61101c1509500740e1220b030050703c0003903000508080c1000001d50007090200c64a0800c82e1031a801c00f40001c1e01c0d04000c1c441911607940c045020b00b44008107425214000c0d01041c01e004480c100c1ea0540c02c040d28514440503011604101c6984680f503007071f4011700d9401c0a81291510103c02c00c10603000140c0850701c1e2400348100e00044038600400302c41840c6045c000d01c0820b0500d24003040b120010080c96441032114081170f00c0b000f03c0d090b03507060715650020004c03c140c1d0b000b02400d0740d9100501e11500d0790002034442140c0350180c401100178602c45c01400003d0500c440803021900050b96081031703030901a549809000010384604030f0b4400d50303001f151503100090800c0c41860101c0d00c04007d03590420030680b1141c0007030480c0907501003540c10402101c010488a041c003624181e8a4407a410405100c00100301c2d101d04cc0800101d042040f00c4807440702001420200d06a8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492371187 1250 492369937 492369953
    0x70c0f0b0a050f0a200105060f12030315010e0901141c020306060103050a0216030305090105090d090308030402240d0e01060b1e04050307150f02070b19021204150201050c07 76
    0x408105203244d65510303046009a404008921800050800302030244400360030551055008031800c4a20740c3d40b0245c5001003010000700924040729640040c808590b4140c030100195107070383d105041c01e00001d104400481c007062000d80c0400003802d466842c04140e0304003036004203003d640e425021038000d019600030a941e0b040240001d8100340d501c3c3c00207404006590f060324400315643c81c4082c50043c00d0300b001400303881c0503900d0034000d5207048046004603c002807811455800c0e03440310b413030301c074a1a100c0102c103800007001a0307003022070907108040ca81d040b280c140b480034240c1102107840c1c011742060b1804072003d412a0702c000341c2c54001c0501004007140c060350f14900d60310320780322351285c1c40744d40c006000e0045500290301886400804602c4c00182c8480300781f00612941c4900f008116039004990705d429074400c40c180f0314010051101c01d0b03018400c031440c01403c1801215846002484401400d5010368004491258500c0d07801e400c651742070081642141c0c107002c4890030480c00f9112420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492372437 1250 492371187 492371197
    0x30d050708030601091a0706140402100503040602120a0e06071107140d021215090a0b270d200313090b130603150b010c0308040323070c0f0b0a05 64
    0xc001d408000200c1c40c0e8850150300d400740910040300d1555030540c40400d200c40d0017020084551504004510800720000c51712180301e150000c4c0900c1c00e09424400980792640060700649a56030200140c402e141040c4015600a54030728500182840042d402d0504002c40a400e0b2030404c4403040020403a442c0001c5c124082d01e130466980242a5000070000c0d8142c540c0d800002d4000c1c8030680e070501e0006011401c291500720800c1d04c601d00d5590203c84503100d50601d5002420500c035880400c3c0c40214101c80402d05070040c200394400d1005440409190020710595800010100000c00120701d0b2404c81d41c40d4038110383c200031818042c22402648412845009150701c20b99104810159692070450004003c0c1311540100180d41d107a061602c0e01a55510000c0c0d846428078845000d554820b09150842c280c059440c8440c03521a90b03421649100050441180003028200201814030402d00404940740300e6417901280c1c07031601c40d02801000c0390342d1041d1100362052007000d020329007000840d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492373687 1250 492372437 492372443
    0x70501030605061c0e1005040506060102240408070f0602030f010510020a0201020717070b130602070e0411240d0207050706090e0a02031f030305130b1e070206040512100b030d0507 79
    0x10030040c0019145c1e03803070480961604107480b420803040c0401e0010100300280144001e0742611420381c0d0340301d100c1e010360090700c802203003091000e400500460032160140031500d10603106d481c44060192038000c1680c00a88803000c41c0c03400c3e500108111700c0d141e81021a0030081d8000b52000500d1900048d440b00020301c6038070b090901500c0301e03c1460130144143c002030501d918107551100c41c4040b000282104e90301400d0098400e0314408206d09003003140b000d108651005c040f0028080180c14014806900d980c070041501070100100100c0e203105015000f900180d140c0140c8465180c10190301d40074081c1d0040c0140040d08506008a100e9494900d510003145227000d0382c0d940752a40041440c0342070707003244c08071002a10000302c10164014005e10818081840401902da1200e1003200c1a06c100b100c2788501c1e1000d5076103070b00c41d030807010094445540010601030809643c0d1020601003a1249480c40d0380e60080602c803010f04281c0c1c03090710030700c202c01d8000b40003030003070140040e04500c0360030790103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492374937 1250 492373687 492373691
    0x30601020d031506080405011103010e070908011a0f1302031302010e0a0303090b0f04030605071e0e0a151403100e0a0905120c160312020d020316020907120e070501030605061c 77
    0xc1c240b11007508039030f19000005c00e0603075070bc2d0b9403001108041181a2122000282811000141180c05000c1e048904005060110542043c00100300359912a241c040d60002c030309402c4030103044018030195100d2a820380c1c0a1032444401d1000400d00710b24035003ca0b210b4070301d040c4240b022a9100742c20a041e40d44182025980d030124403168005c0e03000c1c3c5c1d84010035460610040050b441c0e80400b545104d07400482240c00a64103e0360240d42c107001891a46400136403e03a8100815016400b02082841490902080d051140f500d1085960b00480b8042c0f6090f88002d810810120442071040e071008440500304102c80da43e9540c0d944401104508400c0d80c400440c01c8101600d0038030075034602c05211000c0080f0b070390b035070f2800b640d049250707001c2040540607002074034000c0c500200844071a103280103643c16400d902c0d5420060410405850300c001c004141c00c00210035441c0d8843c021522661500901085203404001020348040340c03c0140642000d01c890710f2042c2048200c9041500b0340311300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492376187 1250 492374937 492374941
    0xb240d0b060f0313030f0309032f100b01090f0f030222020c15130f0611090303040602033f06040b03030a05090f010903050d2a0602030601020d03150608 67
    0x2800074007482c11030034501c140000c144113000820400120307a041c802e445070321148251072826000ca80740785078061b000c94650910042c9100c54480260450801580f05945589040e600c1c94a062000600004020b0780c0b00b540380282d68120b4840720003003403c42c85000d4010304204409031130880078440207011354101002450600c8108054046902c941c203411512421000421a6030b05092140c60307010700310300030201d50300bd00300400d4556500c0c3c0000001039007117000d40da00002003c2401005c4c00303a403c107006c0014103641c10310040004203c603900650311400d22102c2c0d1007001403a265865030304031030306201d0461216030150460440201a0135840a030b0340c2c44000c50094051241c009a141c0000075010b0440ca4004018100c111016102210200c021400642e4003102ca8000a01281d101d030b05072160307051103448902d80078207020000c1c0414011004080c503982c90542000c66406401004000707065904101035450988546011300452441520814864a250240700c0400803c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492377437 1250 492376187 492376189
    0x6090b0708040b070f060b15040b1c230702010203250201090b010b04090b0906030604121116060e0a03110112060e180d050f04050d02010c05100b240d0b 67
    0x82580c00401801c0c01d102d60354246441c2100740d0b1010150125056840d10340011078a081c04400d038205030441d01070191819062a0307042220f50002000048a241650416101901078cc00303000308103446401c0c500486101c640c40c084851000520031411a8818410852580501e145400d451108940340b4031408403400001c030701401008001401c054a40704c000158002d100c4004c104456480200304610f02d00c40003041543d4a00350f6005905501001c003090100301d03000b43c05680d2025909090800da200300e5400c6080028019407120208040b49080100710f401542030000d90344100d41044119055030b40ea07403200c00300760366120304100c00f86c1500d103a00c4103181c2c0807801030996841e401180c0e10308140d142108480070444496a4010170030b6207809240100c082d1003440405461080c14207080006120800365600c100b81d0400c04600c3c51400130a00c24420103403060341078040030400c51200c40a01210940c0035500941400c40320a00640481ca8081500c820303050900c8041a6100900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492378687 1250 492377437 492377453
    0x622080706050c030916140616060f050402040b0d0309350d0e15120403030b0d0302010e120c1f0b100207061403061e01121415060406090b07 62
    0x3080c0185040c0c0340400f40601260000040c1d8421120700c82141d90b4051201000510444680304900101070b60304c4403682c80f03281510180c181c0c240701c01d0a20046042d07540302c1c0c0c825107203080051003d0650341c0013440150300709030082080d120019202e1924203882a90700525405140c426a0304d4a508511480742c030751a030141c00f400880304501038081d03840080f6400741d00c071074450980074003007103084444c004641801503040300c4002a50380701608003050310034a01426200108200c0c10140d484e180c480741569241100305199000743c0c0005280400d20810354a4800081101e000c00a414020a0685100090070326106800c1313136210221880302c00051800b40010a901940c000c00766031280b0a0302ea40018014219905580e0f02c2c801c1e80007503e0b5001c0c0034803007a00e240d40c00074620036520798641c1010301d100000710b80c10708d40540f1030754401c00b010080302c42010310100c55040d00014010540e003514900741d036180d0111190351402d49045409840e00300c03184215034019402107514403e0240c0a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492379937 1250 492378687 492378697
    0x40e0f0402131e0e0106151101091208041109160c05070305060115031503031d01120213030c080c030a140a050706050913060e070c0f020612060909062208 68
    0x244003400070b01d00d01c0080f02410030061840303a14080c64030440c08484481409200219564050303882c00c1901403110881d00c2c1070f0034010459082d074841203203000050034184002030108050762016082d007000c1c6841814001c005814a1140d82c0981c144000c1c0700801990090040031803c01419428040c90060b0500c00d199101400c03601a01c000001d01c28010582281d2520199400300301e20048001821800c1c94640800b6000400b810b01a009080c0c2c407100d0000700e0101410303e038118203001c190100030781c4c2c071a40e81c071207801c3c241102c02c00030050444a0300000d401c808014188200c0d0401c0880d503601011900a828040303209441c18a050091203020b06e480d800400740e13904035072580030142060344460100750241607860300c2c0c0003581140c1c5c13040c0c0040c0c943e10640d0460f2611203002c11215643c08540a4502d0544401c0c52001130740e82100600d440308510354080c146241c90b9040001e19030009040340703070b140c000340300308000c45102404640040c03050030390f04a2039004504207a034a45c00307a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492381187 1250 492379937 492379969
    0xc07110a0b0c0601061805060a03020d0606050912060c1603110a031706030303160518040204030f06060611060a02071a1f091415010e270606040e0f0402 67
    0x86450301260050094008001540e6a001110401c1e42d0f03503502241e004040a002c08040900f001d01408285000c1d0000c00c42c41d0013030325003d401c1428403c0d61204681c407503445100440c0703001414000d0707420b040000800701988100a0300003450704044030001c83c401c140c1d600050302a4580720000b00360240c01c10081044004080710030f00255032402030b05081412030341b100f501c0c80f5040000c2d0750340b03000000c891089668111080e03203403200b9041a0f90b036400100301586d00c5140c40c13003640c22035221440a003005500502c0c20106084050404a04560003500148100304c10200e502c16406800201543c1051060200581e28249401c1030344401d080340624190b4004c410003030012101d003140e54003001e404030400200002c0d9460029204589140314070002002e01d5000050f2000074003104803000c0d000c1070510191840c42200007401c20f1001d04152000102c01084065005080f10580d5a0100050390f40c10320f00750070981004140e1100802144500400000003411511102801032107510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492382437 1250 492381187 492381199
    0xa1b0f080a0504140d030c1209120303051608010803160c0b0d1d030c0703020f0315040c1401020d17190f0902040b09070903030507080c062502070e0c0711 68
    0x110490000b04076902920a805010002041544107403601c400c8041007240e0540741c0ca8040051507a0700e042c0c0520100104040c80701540c0c000641c800710340b6012080314400d9400003600e29042c0c0c92551820103212110081025200c01803205440c00012540c05a210040c00c21118a192074001504041174228021640780440d20034280381c01504165240808551207240031f414641e40c2a580740607100c0e0f81012039204031070170005400c004410030808800039050b2401100d105104a48801c41960300b00c0b4ac0d411600410422207070300680c1c20302400c400344003034241440510340060041e21802c8258130540f40780000308000c501d1003000d154000450345010f21000145158040040c500240240d0013141031000310380704d03442d0a042082c4140d9681e103031441e200d4207540b42202d00742c006141c201c0c0d000400300403050101d00e04203c46481900c1c1400e0141d0040e6403801c252114004924520096600c10641031004d403181e44081c41d17000d007a20300c005480d103150b4100441800755000815030054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492383687 1250 492382437 492382447
    0x180f020703171b0d0b0310090309050307081507080c090a061d010c0c0e0c120a05010f05032d01140108010506090f0f04110d0618030201110a1b0f08 65
    0x1a000528400c940c030307400040b64020f0b51a402003004842040c1e010030000322040010810340b07041ca0307004070f060860103011908600c15800010007181c807840400c0c2d001c151121020040c5160410029020380050382c0035101001c118034002c400c40030068040000d0124540010f44c011074010291102d07400c0c0284139004455aa00002c0c0003400040d02e041e01281610182e28040e5009281d400f030016404446005400c1c90002e00f1818801e001e0401101840d00b0420701d12403003d8900910b00654000c8400a229450301c05110480c070015440325000303070003c1820700c45405c0b80003010344a0b980d04605100d00200c644482500404240b5800a0800500000402c2c0048154402489110280c1c1c030701c0306580f2040c034514150201240c00e200045460400a0001001000100241440a030403d00358650720b80e501307070a9542e0501c200c2880380a6410000a1660900880403450004081c1d285082b090f1040103054000d10440e46000030f248803640410800d401c01840700c0c2c1900003148070340318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492384937 1250 492383687 492383693
    0x607030f0606090501050711030a1703060906040504150c1101020c030301090608121e090603070e130203060d02090903070c290a05160212010c0c0624180f0207 70
    0x142038008409102a24001011400e2030258110b081030b0ba00c16180e0904140481c2e0341c2c0300b28517011416441e00360041060310400100c50f0000002410740a14142d901c0e440c00109210140000800781c5210f03500b02414080482c00800016a00380954000460b0081010b0401d403080300c45000c024203d9031001410311071423a004009103040e5080380600740301541da5002460341e911681101903d17000b400300107194130345210407100e1a055560010060500c02d142d80010020b8000f00c41800c04100c00c401940c0c2d8501e071561446070f6650b0303d050304605508260000c95000b004003c0000c1c040c10745072021603456641042510072480c1c1c86120708010640720084500b81d01101200c540003940c40100c0720008019140568240c80890f41d81c031070408054181c400780b103044005081ea02b001b03140b000d1034020b040070301415070041102e1300d801c500e070061482c101041f1080c001031901080845004a2240124a004a0700b00c5d04500c0142403030a031114004002040d42d400706640c2e48ac4001041010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492386187 1250 492384937 492384941
    0x60c1403090109031b020105030f07140f03010e130c0611030c06011715010e07031e0e01240e0604020f0c010c0207030c140d02061e07080306150c0a080a0c05060703 72
    0x4058400d640e8184e41c40c1d40c0385994117444030600c0000380803440500001d070910248110241c0c3c05055442d01000e00b02c40c1405030a0b04e0307404160360b010703140300000040c4481d10fa5401540d4201280c000308100d10010744e200c0341c0c00034840c0e001d0f550811010406a00b0681e0041054900200b120401c0e40c52659603003000c1e030100620304941c1c00c024050b84a580c0c055820301080281210200b003002d000700d9490443c201d00909030000700c202802c02014548900006500c980700d5440d00c5500009030080c0710301984440d40e602c600d00e0800c2b44180100c2440060403c42840341c00810942d80541c40c0c040601190700c242c082c4005c1000203600c0d0451083d1450b0b80001d0b800110ba01400c140c00b5000d49401c3c44041d090441d541c0c05400a041c0601080141062401460691001642610304c06141206200e0300c1d0320440017540d0040001c011710610b1b1420280c030b80d0900c000c00d40d20710300c1d0000c824401758450f600041c02614618000c900e070b403c4a40148134074446135a00c10251003e9250142001d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492387437 1250 492386187 492386201
    0x30a15060f06020d0906200607030c0e03011a090705040e040339030c080c07060c1202011803082d040b01050a0b040302060c15130b0c040f03060c14030901 68
    0xca601e60740040025101d00100348503e00400c5940d855031403e00340402600c105e0504402c0441c0040c5540c21520000000e000329070045800ea80c0c0481d41001c1c4080090104884040c018400e915190800a912541e200302e005c443e00d003515848005e42d030700041502e19010f1640004001c1e0f022800300010154820740700780940f8200041284003840b04032840746031521154100400c2c407a13101d680c50209000b100c1458140d8032540b08507103800716401c0c51034201081a800180403560300107804003008107040076030101c0d92152008001c1101e40d04d4041191408111001d014019107402003070031440d000220031a084002c288807249060450100810300300d084074162a58000c4d44004211403600714100380c216840c0c1100a4200b0342076800308a5180d00c58801e5158134400d4020280c82400c4020401c2d215440c404d00e4090244070030b09155a846200402611200790101700c1800844c58442504007136a41082001613100601c00040d1848410390340d002c0b21250010080100d10007054011803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492388687 1250 492387437 492387449
    0x3050606040f0611060a1a061b01020d060617090303010b070c030611030f0a090b0c21040507050307081522021809010b0604230307030b090601030308090a0f060b030a1506 75
    0x41d145c2e580d0101102d044400b20707009950120341211060101d4504400540780f040022000c0401c01410ba440d030501b244e004040d02c400726610b4003800c1181076040341004681e0000f50320140118508520340d03a03140d220501400002c09c40114600c8144004026504091a03002c102003180b4a14510501d0058008840c0d40c00c00c02c1c0c9420005110703201c54040d002c027080d407003101015142c82c1c2c0111401c45410041501e0800030400400340a410182c1a1407401507003e040680b4025090001b458242405504000d01a03404404071001940c8004103941c2e2040440040c00c40880381205070981c2224442d0020794010200000d040701207802100b464003451800c0f00070848c42d80400e00b0700125008078131a070200c1121260f1450700c1401c941031004480d000040550342d00c662a07075561000340200741c075240c8050344402c006100705600182815004070600307001381910342e01544c2c1c000849078001001000c1c640c03500e031446075903102000081c0750503a00100700000b001441d102c8900508581c421a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492389937 1250 492388687 492388693
    0x40c1205031e07030804030e060d02040e1b031618090c03060807062c031c020c01170c07150209211b130c02030f070f030806100f03050606040f0611 65
    0x604903045200b0110350301142e268840010360b6485441c151a801e114008143d00180d0802c60f0700d054150a10003000a01f81d0590203851600340b040d1000d40c0d42d00c0d810510314480c0000c00600c04007890707010104c44200c0c890310f0102000b0b00c1d850182030303101c400c0303a00c01c102490401d411180455056001481130f41c0101c0e080307605543da9120110342c400c40c120004202036000346d00d164045188044806505140a02140c13002c6009905002c40c203c02002c0000050b085005000d01a690180c81440102240c01481c040340c2004410500c030352180c1d02004004800f41155103000c400d6540581d001d40c2c0b0000c201070001c0f010304524028014800c032001803280900031140080030551460b46000c0400a42021010240b00510b00024240107440c0000d500c414480031501030700000c0205202441410042c0402c040c910300a0f1002c080902684d2154120850315150540d12501d18075801c6800d240200e4162106c201268452059401031411b4005404020507002e40003580740005c9c00101c021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492391187 1250 492389937 492389977
    0x1302190e09010f060c060b030609072d05120715050903010f0608190f081308010b0a0b0a200601060306170309060702040b0315010e070210051e040c120503 68
    0x1c12603060700900445103054400b25050240c030b80b14a1151094600c5050005565032107140000c2ca4031004541000c0f242c2c0c0603903000d0003d15003071061460041200788250460302c508042c4010082e03401c1c01118055907055003a0400040b041002c0b8009240c0c460070002d01c80041c00c0c00a1455101425141c000e40c01e012aa070100070180c03184208490155000c0c10803040a08950f01401480950655201900360703800030104131200c0c000c18500c040c0f01000d80140e403a0090480c2520a090740442c49003038050810412035107604101c1c0d01041143c9030030740003100f0324080b5100300c0c0c65501001c1c90034032600001042c0c2d039030181d205609440c40200101d01400c1d840b00e00365500c0c03041403901c1c1d0f04500300713210803001810150055040108010305550001542c500c6512801c6401d905c4994105804000d008905405000310795064003403010521241c9400594001258440c500d1500c011047c00006810b1100b10010303900503060b01000c51000c5001418030319a290001ca4201c40040c03c0526 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492392437 1250 492391187 492391189
    0x22a01060617040b06060a110102040603050a06090e12090604030c03140f0d050909070e03010906090212070e0103020d02010504170102251a15100504030618150b1302190e 75
    0x10544629840382c0504245e9543d03e0510849170040d00343c100902c02400e000640d1064280058000b0700841d5a0004080c5001840c501c01c0d506241d000c1e039011032800414007409100420b0040802e0004000c26561f03001100114040e03100d5944050300740c1c1c400740408002c000c82e41c00c50301c00c007140d00d2044030034050710b1543d01d0392141d43c00d140a002240c400c01400300a401d10b1100306a12845508244050090f014040790940354a600b04072016681d441c00c120452500c81c04454400715604000c126460500021109161041c00b01910a004030181107045a00c15000c0380c0c0a403440d40c2c1001c60b52000554001d020350002c1c60341e41980f40c0001542040c68083c841a032441075001105140c100710002e2a0003d0f14034068251001c03028851001c400c6a22590311209403100280c3e1072513501c0d49141468001c03160021288035010141041c2c08012844541c0070a03c4d07141030201c0056451900c00014190300311003500c2c2007605001062000c440340042848c114904001d4850070707a0086c1001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492393687 1250 492392437 492392477
    0x81617070503071401171e01171002160f2006120c030402030f030a050a08132a03020a0b030105011e020d03090f02090412121a04022a010606 62
    0x101807070b905948510010030501c4510070399813204000604040403010b2070030384860013843e400c0b544609501100c030058241c240180e0141c5005280b050800e00b0390020300b00480b40c40b050504071250261f500401d40001300306031444c01a07002540b059420604900a18100c96000e518101c88040580001c0d2585460300f01201115030000c0500b03c0044165162180d4120640002e0070603a0035220b40003d41c01c0310103080009124110781a1101e03034842000700001003064000400d940d0a43d16800d200c103000514111800500300015910f80154415a002e0f6a00c4082981d001035404841c201000801164400045041c3c4800380e98100144d0f811510080e0781c0360745c190b2000010380c0920108003c0301d04c039501c0040d0042c4500c030700704451195900002d4034588290760580d0490310b12190030301050b400088520a100386800240010440c4a41f0034a008000800c5680296000200803024a41048041440b0082500c0342c44504050018882c0240500c1c002c020201d9507403034a12a24240d0301f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492394937 1250 492393687 492393689
    0xb0103140f3429030f06010c1a0c1909080a020d051204120c12032f0a0b09010b1903110402040b0c0f06060a0b0301090c051603020109030f050c030a030c0908161707 72
    0x170f4a0b51112a0711030b2001110207003006081990040d981074452071040302d001a005014103c003407943e548400000100e805182c84c00392520050054110040020200c0031030111041501200e0002042400f030810505114a4084059800000050100b07008004160404010340071708032040d942e0740c1300c994040850b184a00d001d40400e10307100c06c002c2c034020f0101d0710000c0c00303070780350320503200960700f40315545c0b401c0d041900131641d2112030410004540c5092049841819040752003080c0074000001801e1600b0346804050301c035580380c034184076803500ca80d0100c45c010702e0f400900c26900c24842c99a40e0b100d0401c010301348094025a0086030b250302d0f148940f4000c0da0100f40b0024910b03482c03d0341c07900080020040d1102401003d008030a52080803041c0d4200f20b034000d03000400c409200d403800808050400c5c0445080c00420b03c100c0c404504e00000b07a9950003814107000909400307480c41951400607643c4800501e1150070250803804815007034401c01c0380c26580e841400d80c201502c00545402036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492396187 1250 492394937 492394951
    0x108011b050712111204080f070b0a0c0f1a0f0a0615050d1d1c050703080103021e0619030b10210908070b0103140f342903 54
    0x502c500000301e0021141003814403800d04204140c480e00340b00e5641030216648034904071600200b01000850010b10031000080d01c840050000141440400c48040c0181c4051804024483c80031a0421400b030010b0007600e504090601d0301e1011140301d4036a80c0e02d08980100041e034060000c9000d180c0280580000d8443c00005e4074120580400100c0315078000c200702c1d015054072094212200c500810400502d400710380050440f10740074240d200c01c9551144600c00c100b00d000c0081d50042903101080b1030560358100d03006e1144007405030b5000b140f50401e04005902c070200103108a9190819400541e8445583c2c8007400710b9011401004543d420850440011075118111110440d1403084070b002c7d40c402c04c01000035071010680390003207243c00c9500f044400414820040c42441101c1541655142c104001410b144041180c0b041d25031000c4d1190b8142d880782020030740e20440500b41405a1100d440810400322503407a01c02d400c00c1900c00040da2001803142d0030100078203552400712072091034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492397437 1250 492396187 492396197
    0x30c040507051b1006120c0b0a0e0d03030b1005030702010b1207060516150f0b0d15020a020a0204020d050714030702070b1c09260903060103060203060f09040302060108011b 76
    0x200807855003000d403e04100b120854011402c03084440001880f895014000c0e1400c0362074000d007240b0342144400c4103a0000c0c2c81c0620203105400b0340c50751021130800700503800c3e111441c0b10f101a02e4158050030070882e05550050818001c080340b26801009988100c240764002d01441422500b80561381c142d00b01c0003051074000d00d00c18071915003d1f900502000d90314510006840704075407240c86910023a0061742c000c0356203d910340140b00000e80241c3e080700e03108039030805131540ca503a10074500031a10f860712007801d6000f240b0250414000d0102c030b035605030060825580e078051002c2000052100321810400305144d031346050703c8001ea90302968481c441c150010441c1c10b003050800c1409800c5940c808407444505014401c413944d43d400b030003038060720034510041c003050f802c4841c2119540360440500244018030241d2501d03500000d1050450381c200000503035988851010901000c4941c0b409600048a2001d00041640c000340450489807003030001c000c11008030000e449018203078420000094 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492398687 1250 492397437 492397447
    0x40c0909031e180303020f06010501030501081e10060902040e010e190b060f191d0d0b060406030209040c08150103021f120509030702010201140f1f1211030c04050705 73
    0x11407048801c401032146400c00c544509a2510740428410f03103608218016080f5240203a00f41a00700021360140c8800d007020b000b550b062116155640d000d410070040140c142c12408541004148105580d422a50700240b00345500c403132a80340a0340c494440c620045040d80000540040c4090b001030103a0186079080031102030341111034024017440d04440c1e5101b90304002c40174100000d50003d054503044005840c858a45610700a0814946a02c01e03035030282080a02262550301e686400d91000c0e40302e841170805844043c0490010040d07604000e4004045409000600c02400342101c00c03104020102c499250020302d00c804602020303c0001e400c400600709505803000c21810100034071803d0300c0c1982080c030384250078205a4800342d4103180950800140d40741036503428041d007410840074218500840c04c0040c3c0104060500410301c10300030b4003119503501c404007440d02d0f2134000c01c0d0a4449819600190909040c540700160100344284510780b001c64107400e182c040c080c40340e8486d8480500303003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492399937 1250 492398687 492398717
    0x418053d0e0a092609060c1c0f230d0e070f09050f10050306011404020702100914010306080607030e030d060609061b111905090114330703030e01050f040c090903 71
    0x182d00081f803022468011900c91492408592400007400000c59561050103103012401912104880d000c11845080d0254081020780342501241c4005142600004a0301c220001950401000e50410100d503042140001400c0500307401c15402401c080d00c400105490b8054a044020401d1007159090340204c001000f144010382d10320311002c1e1002c0c2c409403800f040ca0740002e001f10707150308981c1c2c003091f1281010300c5419121240d00300d0140303003800d00700880d130308002d40706988140003028441055200c40e03004d55013500601c00e80b03102d41c0d41c079001400304035140c82c80078280c10b0450094900090460325102c03101c1e95100859205141c0244500220071500814408100c24003000c0c0c0a0740d42c3c0848001840d611840341c218020309240440d040040c405504000300039000420351031602c0c6041031a100d1031584040b1980c401c0d072180014540d10708681c902030b00070b0f0400388060883d039441c01c0e00700a41406508502c500c034902c40d07008220601e407920406400c4030b441e1580500001c0e034165559000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492401187 1250 492399937 492399949
    0x140327070f0909110613060e01030b01092607030605070305060a060f03270b1506040807060f0210050f06030f0d051806040305030418053d0e0a092609 66
    0x101034051070740408900c03022000b04101e030707210702e20b031b08200d0140b110100031442e030001004089840034078041c010403031143c0c0024100c51841c006c0c11031403011481f6405441111003460011080c1000c240d4000c90b540342040001440c0850300d00c1d0110b030804002610b549018280501941e44545a0341c8451140041c124020039040190748a814031038103a212000c0c4180c1c807100b8200e4842c1500440c0392074601008540c0510500c03400307001e540c00b07010034440321030003252140c20b8a40f0b618001003003100c1c1070420ac0c07518880c481e800d0742c83c616200c1131211802074144202e04c500e400303030105d5102c8003250f82c1841d5241d488526410004105220511036070702414100c803081c0e14000c00320303030916890351902401c0d9880b650069600c030fa1510704058020301c0a02542d40d110500d2040f0303801c1c1e1040c0c41005484102c403183ca9801d1826501d4102d00100403c2c010407003e4614401c1a00302c5241c60040719004003000002a42c5800a0015607000000601e0051074030003071607440e0900384400c020034880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492402437 1250 492401187 492401201
    0x7050f0403080306010c140f0c06130b0a12090f1b06080a020a050405040e011409060c04090e0a0614090f0c030a0f0c0312091a030402100f140327070f09 67
    0x410006c5200040001c207201c00e85060807614040c01806910004a0003240b61a8214000601901c0c040c042d1218000000c1e00460032280301e03139082c65503040b5032402101c030100b03a03c03107403000e40d8508070343c14080c0140747c0c0050000701d100d2038540b10b400300010501d0707009000a01c210000500f5580005403ca9078603000f40c003400b1410f003070550030f00d51078100003026a0442250100c00d80c0d580c24905044000310312000c0d4200290402034405030804400701070310361281c0d0240000c0302c0c3e11a42070080303c030703c00c110344020b240d0080d104000e5080e80c110f0b1528502c40c1512400d03054405c1c0c0030440109000401d42d0403581c1e40080003402c1108555903800c001c0303c2c845100341c402c4000070b8400004158270a0101184290342d0344d4000781507081441d1401100721f0030700401e150040134010400181c89158001d429a0b03a5401e00e4881c400c1c00c0401164402e00b001050002c0000102c14403a0f807044201c004c0b60419058409062400408038aa50b524943d40c03040c6045e40311000402c02030f41c100c5500c681c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492403687 1250 492402437 492402439
    0xa05010e1015090503070b09010e010c1e0f060903031e18022404330c030804081c05040b0618240604080c09090c010c14010b04050702031207050f0403080306 69
    0x103008140d40b44002810714840d1f502158500d03200150280844d0380c0304d00074109808007400d0494442c02e80340c5030343e40100c2d500d810780c01c40420000d074818103110350021035007581030744040c0c14400b080c01403078000c0217821410402e1132041166040300388062800d020f42040b48454a9001448098036000c01c01c0ca2103000380981440c40303024030b54007901000400108043c114a4843d255001d200094404881c4030480031900015504042d03190807650011840880e2501072426080781e07251818031084d603110300c1042c3c542e03c441c0c14446c0c1c5520b041a8006910550217a1401941a0396400a10642900003070390080b181c40400005440b0782c02c0103050b203101e2240c01101c1034042800c040030805643c001e4000816560100d10703440a94540216003540c01511100548494114000082d01882407500e0041c024230440903c001c20b10760941c064904c01c80000d005201c3c505009002944903403018003100b105034050400101c1050040d03044400c02a81a20310a02c0d142c511f49503401642c00c041c10039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492404937 1250 492403687 492403697
    0x3061302032e0e0604020406050a03020307020c09010602010c110604020105041721030412031109060d021e0408060c120612010e0a0c06020f011a06090a0f09050a05010e1015 76
    0x82c1c44486030120540c0040a400b1065400d042c02c01c0a50254a500100100d01c210b004000a12071254042c1c26621110b509003805070712511540d400342c0c00c1100c1403007601c0d048502c0500020f541581500040011a01070700c3d0b1300140ca91007103005440b82d40480d00640420381c10042000f9a01c100d550780c540340d9081e0b000b51240101980210340e070100005180b001d1040c0c0c040184001e00c4291004241c4299080c182002641d15200615440d0b0003503d0560744a43c3c004106500ca1008540403a07240d0302d40300107406d0345440c0c1c40700e0380055600140142c402c1c42c805e6170005507100000c0011140f0003880c09103101815038038a000c0006040e8084070540155482e03800c1c1054521003008407038002c40c030450280e4121030070405c00a19040c0c81b14580070700c2c2da051030076850310700000d00000145c10710152480c2c0c1d99800c1d0800442c0b084c65507603126501c501819040040c44041c654000b6016181e000c3c030074082640d0728041c2c0c3d140341d1400e4030b039204005035002d004c2089803543c9010515500c254184 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492406187 1250 492404937 492404971
    0x509010c050a03030506010e0d030e0f0d0b010b03010305070509010e0a0f0204050d030e0111241e13060b04050402010e0d0203011b08010f0608271207260306130203 72
    0x201c0c1c0c1040e0401c0c500701c2c00720351501d06015a644e081082a007032000300f5621180262140e4800030541003030b0803480c501441c02500021829221b100060b50000d401204d0f109095a581203000200c0e80248401c1da000d02400c040401c0318079090300804d0480701d0b0301d0707000070140d100c400c079a41c000c0400380c25403400c0035420400054552181e00303c0d2042d4034041e48842c0203840c0c24a001420001507002041c80c10b81101514545d0050903900309040c0d60302d104141c42265440900e00c540340c40b0301e90030002e98114201c04201400d004104a2000d02c1d00c2100b05011402c417443c10302056071001d0b900280030130a4942d813190b0a060203460040c100c2c1c0001c2c00030915425480038009401880d0704013100040045005200800340310303c0000003082d0520b070400c418540050301100007004101041c0002440b18481010301c00700b004006420012005038036034038501489c0032001840c404c0602d124010881071a051f814906206a82c0724000280003c000c03214a001801c00942c4000c100048260007445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492407437 1250 492406187 492406193
    0x100c121d030a0f051005072c1c0201112d030702090c07141507051305090c12010b1207052b060e0703060b19050d050a090b0f040f0b06030f010c030f0e030c0703030509010c 75
    0x18000b2740c81d06182161910324031560000408030301d0b40c00d038034400d00c0d1700000c181c0c50590211003d6660341e0340700324050f8041021a080707242c25442076802c080e5222101205011642400030700501205100b440c1c00307909000e0300300d206a202c40c803c4d900e010780c03c810100000c0000d4002d400400c030002035503442d483c141c0c1e180e00004000303582c04d03101c0d8044860f003c10108030098030b080c8034030b0140c0914000309091480c29100760100c240014980c504200c00400c602c8810181c20b0107031910040c050300021511115001990003c0c116407103054403d070030038408030303250502070b114860a4600c0f0a02e854a4000000d0b640781001034031100c4002004005c10800d950800c4070310071301d401098950000f04100c00d1500304880c16079006040c4500210104052100040070000800c0c0c09544c40174403401940d640500007030030035a000c040d00800354207180c11440c42d550305900041c01c00070485010441c1b0307860740e0b005c03650302e00032010006050790054506001090258020b020f9500c01454049415a0190703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492408687 1250 492407437 492407449
    0x15060e01020a051b04060902040506030c0702130606051201061707030c111609051e010e060609040911030f07050303120a06080d0e100c121d030a0f051005072c 70
    0x441d80c4224050b42000ba0341c4d00d440c5c0760094600408901005604040c10b010003d0070610000c2c200b07031100c4000207003e0b02151207010b5500009612108100000c6503284400303040c41d40000301c100416a80500046207040c012500d400084451814008181c0d807200c01c25002030400d1030f140828064150200c40300e18008022500074800d1a04040f5002441c00b0503017000d86074080d003286102c07a10001040600c02200700d0090440d003a11048074800d4682e070300171501e1f40c80b440c101d6030340040c10b1000c00f1061203003503542c0c4203240b0390030340441706900741c006035941d110491800740c65410b8004102c10280c1031440e41032140c006200c00343c00901a662a05030500e002e803582d1008021032a1840e21550070701c4c005255803040c06050030280c02c48840ea60760b5401d10100807800100340101d103003071000300004200c40007000500207070407607410109900b4004d140000180c000c40c0d0303501c180c24440000c2d80360350140364014a40c94070f03096942d01c1d6140000c003503440d0241c18150071000c4124105025a102 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492409937 1250 492408687 492408703
    0x509070806092d09010f1509061403030304152304021002070503030f1b03070b0405100207030f03020a03061e05090105060a080615090303130e1614090103020715060e07020115060e01020a05 83
    0x340e109107c10a07e07041007001600c0b41e40d8084800300b208650150080e031004001c030b0f544241d0180010088003580d0680c1c90040031602500a002d582014400c90710b02c0304004481d028900885032072110411340c800407030352001c640c011150150010702c540032065204201400c40d05c0a078080c2c20000010f404030329442d64110b500d0a9540310600410301081c0101130145c0070f4804031389081549889119100541038110405050b23040650014041c801ca61184d44405d002d8054407000306490120140d0305448090540106449940380d000005020700d04901282e228171241e4681d0240c541d5080e04000b1310b20819041c02c2048642001103050329941407004140010f881c5402901c3d003410402d08120174103005040706803508142e12200d00c85a005070414105810a0020f195925003200c01200640a10711004290200c0c14a4603087c280c2079400c240140d4800440320f5500d035580d00700032400d03100300342d184490b048402c002c03c2c007440d441054854110310b01070040720098800c0355240e030301d08581e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492411187 1250 492409937 492409961
    0x2012109150b1c0f031d150a02010b06041a070203030d110a17040f08030606090406030f2d080d020c06040507080606010306031a060102070509070806092d09010f 71
    0x50b40c0301d00300b00e0346015074400800340e40d18204400610510395403103055106036040039080c010035124400300c0096210407030510b9680030300074400c012902c0c405801320350040c44c6040e0265080005c10001400c0030010b03074044400076015890020207176200042d4550003500d080c0c0e0580400c000c0200860454041c0004079140c0c3d80c2d64554685091030010b00311000b4105440b4101e404005110100e900015100740c070355045507031950b4944849000580c14441e50b020030380c015040170000800c2c0840d103460034055034080c0c1c080010079a01400258001c58195007141c103d10b20280f494008180d2185c090500c2904070700700103140101081c88a807400004650403189a0b1009070706200c4c0c040240001c40e0840c5c4203080c103110050850342ea240a05040300161124003000d0350000d04160f2007040500c00501001e4125010740c103041500611404c1304440d42c500070400c190200e400d4000c00d104c45422040b4003042d03220700b1119030409000a00300503003001c04c60340d280c5030010048078440c41002c1441e64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492412437 1250 492411187 492411191
    0x4080d090801050601080f0a0b120d05070627060209032107050106080c130e1c0f090b190302090a050405010909020306090f2e0f02040303020f06040201210915 70
    0x1180103045800c2d144010b04e083d040007480c1c030502980c3c00c0d02e004115004400e4940c0821002c1d00d040216a19082100911040b4402c4a9640c0f14a0750800010600076024240a0040c002d02801506140c10f4660a00c089680317840c0ce5030340442c0c0254050200300c0001826980154907002280590072081c012010405c540003c881080000134401d04005251031405441c2003542c3d24001241c402481070405011912a42c00008141c810f0080b90b03c4a11212054044804200e100030f02000000e20020003040030307600d0200301c81c80100242c0f501113443c4104464006c400c042c08034065042880f4050300301c0c142c04008116955940581e50103020202c400003800369590041624051010301503680c0350f0400c80c61400c4400011424050a041d21610700c0d001131680898290b113066403014420500c1d10700b0051002c0810030790001c1048074002d03400c82c1d04c440100c090076500c03076406480080c00301c2d101d00038202429207403e00f11018440300140c001229841c40e103c20703942480a0914800d410313 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492413687 1250 492412437 492412439
    0x210c01020406210b01050417120307090f0e010e160c050703080a03060b0c060609071404061808031305090916030b01061407080a08040c2304050a0209220204080d09 72
    0xc0010080403c100d07455001400300b43c2c1882c00281c841d1141c0c0c000c2d29100d820000054810040030010000d500780300c0710116546e8506024010b000d0003641c05107114940e52000006840d070000300700c0d0360585120680c16000b9490b4201c10382d030f04e400056030302c0c0140011564030300c011610134003a640045024584c4507548848002004084822940017007260981c2071000c1c8259000004031107500000940301c188080d1941036055813106608500c13111005030004000c034000d584140ca50001c066141328003002140c44180a645901421111001d0f5214100c002c100900e00154143e40102c0e034042501d040301d00d94440000c5054040e002590040c0c0010010040d195110100c034284010b08c031403081c2800c01580e110800e51140024090400c40c01c040458140300e03ca11401d0020b100d08c0254000c030030080c41101410044841d030541c4a00e142100054441c0960b00071a034001900a1070740240a800f224103c5400c4058181281c0440e400e11011034080c000700300d040c0c00000c0b0341d114900700c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492414937 1250 492413687 492413717
    0x319152411070807090b150415020106270b13060b03090c0117040b2701051806070c03080901020d0e06150102010c1d03120d02071b0305210c01020406 66
    0x159941c0885501d40c0124800c100501c0c2c0481d580c0c040d9200d20b20080b940358240800900b8800300820608141b1500140010300805a000d0005620605400a0040e680e48080468200315a240d1502944102480400c6122810750140310f40f904000c080070150001c03450703d5011902d1a40100e10860400020301a070802c1c10850381160300400d01c0d00c03074581c14100c136504540f0040500300a2441c8000404600c051f803c40c06141117202900c110191138411000344140a44020740d040c410104510055160903040440d802d0b1041c0c0d81c1d030700d861048140584c4d04071104030000f005c007a610b560030b01c165170403290355002c1e40c405050240001c01c180c0c10700e034a486000c207004803175082c19a85000c011848a60b00842035240c01e510004140100d2003084020900b03001d04a120606000c0700003810044404196000e014101e00034142c0801c103520010301081050300c02c1c00003500d0750b0320070751400e9880038030416010410604419081d0421101c203034070300d080e038002d03410800200b10000411015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492416187 1250 492414937 492414947
    0xb063901150f03020d140703151b0327080d051501020609011b0311090d0818030309031002070f0c060e100f0804020f010203090a0905060a0b03191524 66
    0x10345200d401c0320190a1a540c0021000007158178002c140d030941420402c2074000c14480c280c003c580116100144140c0003010078014805059051429950103000c0b04d0b41c503229119901c14030140c515404402c8083c2c072100c81d04401035007800c0703450120070040c0355600f4060380660f5000d42071069000504e00340e070740c001a0600500900440090380340c0203180d18540c0c00b5408140340405542400624110224140303000c1d440780a064035006a030069610080241000003404d07441c44000042191924032020580c9a00c510b580040c0c3c5039008100c0802590751700c0c1d0040940c54415070722103c55041da640c42002d11201644240c000c218541c0000c105402e00c0b00e2000d214013517038503008d40c400102c280003510b541c6011301f01a0141040f015038000a9000f001150b04188004000305210344e034509015002c3c0c00d0031106940100c01c0610001200d02074002624021f81c400c0740c40488007200066224000c4c1006c4100c5542d0f41103020002405003010408010000f03842ca1500c00110795808010b05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492417437 1250 492416187 492416189
    0x1020d03152c0610022e050415060914060402180a1805160c140f10020c0c0a031a1009050403020f01150b1b010b040e0a0302010608010b06390115 64
    0x4050307031134249a18050384c1d021031009048100001081e200b11241015403080200c849081c211603881d2070107000c00e2007144111034840c06421a01400b140c0c0d150812402681d1200c464642c031885a01c1c0415101c0c070f49030700640f142d0321424480d60000c0340c0d5038000138503400882d44190056000300381002480b26150080543c4200380070703030f0414000030b030b6880185840405100600b00614a040c0d40e2000003090203901d02000051003291b001d0313100c1e00348800003940848030b03141c0a4424285030060300d0914001040440341c0240110007080718508001070001002000b50030560717940240480e0001c0e50b0710950380224003960003001e00068030b2405034210344843c421201c1108446a0410441c0692000c452103901c1d0f41010002d842e010a0b101809450110019680305080c222803180400c000200462410300a41c001e00219a82d00c114600b214107042d40282c001400300107150503041003008020112400100c6403640045140001e1080585415840c0b85a511145035011242007842108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492418687 1250 492417437 492417439
    0xd031109030724030603022110020d0b1906020d0f0201140106080a0f050610050a032702030d032a18060818030405060901030e1f020a110c01020d03152c06 68
    0xc0504540024502001c230411300b481d00041301c038600c0c5e0f131500306128441444014036000d40d03c039004012b504000d0541d40d10150b019103060000c0350b1011070412041c40445903d034024241c1c0c80c42080044404442581d074040c150340d00d680140d100c4500d101d4009000f00714551b503400503410210b0501043d40c00e11100e1080042c101005d1003500d903152504204e050210381812079403203020b818280e01415082c0c1d83c61030140b03401184045807407140407602e94100d00c200d00b50303000d1450201080c0c08a60240d46504071403040040d220f280b0144079650711a00084504041419000b200c011000743d07041034010800107440282031107110310080e1a0b0348030007590300000c1c5090905050110301103025406800d0b04041d15041e081c941c5100c14404134420b0610b48000b81c6034211070703080c8040a580000c40102c0000c0741a2a007440c41500843c1040130b02005074060050344a25103000c03005001d01c2800908150f10451000880320182d4001d182c41c403031051a01c4848904040061071450001820a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492419937 1250 492418687 492418691
    0x32b020703080a0b0109090e010c030c170606070201031b0c03020c010914090a060e0c07030813080306040e030903030738040b250804060b010e030d03110903072403 72
    0xc100025007006140d503106243c0c440004001e621036004860b881181e60208861038984604442401c4040d0810800460345403428404001d01c090104d0310228a0305a40402203a4440810101c1c50440010309140d401494049a00d1307000c0380651101c040503427420b02c0421401d042c1c800070180c040c002a50310385802d09160f10103d240c010000c6549010341358440c03140c02c400000070912251540400c000d85480760744e032001840d14900e50140c40d0300190098022406031000144135001c040700829401d540050410706540342c1c041404040c2101c9074103880103010038801c1e4859170324100301800f00300b4007a1300072220b5070340720300180c104019450694040b014803030501407800251040340d45e03401c240d008241110700d41d1559906150200b00000d402040c0744494055420f056002180e5070103240071b80020048034140c00015a41890ba050826806410200c03016892038000d42c0710b4074006102c0b0000c1450440e8400010341011001c1e0001302c90b480c000e00108041e0003c6110a00041c14030f4241 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492421187 1250 492419937 492419947
    0x7020106060509040f0603050d08190506011d0409050d09051e01020a080c190606090e0c031b0109150206100b03040c090504021306090b10180521032b02 67
    0x1000b040ea03c1a280a00d00a98641d10002203112259202100039030300601941c00a400c441d100030b0541f10140c484901d00303204510741407100724951050500650b0161202a034440d0f1b4084240880c040031a03009500950300e4a0403401710f41c040c03189160005071990360301d190b90300b01030400c081d0059411001ca18900c080c0006602c3c0d9800040d600419608030080d59120514911660705d081c03c6030300b1480140492150cc3e208000454100701e042e10440300082c800b551034034070140d658000707a03070345198594015854100308011091148510070018074103000d41c503841e010801e0880b08290032181c010781c4410100554103a460003108040c0a46140312031441c10141c1714101001414014108540d81c0e40000c50700310f5460180411031070501250030b1100650b10038100d0003c01031240800d00990507803420a003c94032401c00c40030700c51481808440c00c11700b02018002d1f04540c88442c541056403c4006514082c01000178001030301c00d60f804481d080700844e00c0710140d01c011400500c109801800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492422437 1250 492421187 492421199
    0x6180213050904020d0813050a060f0c0201080a0e0601030506040b100303090302150c06070314130839010c0f08010e04140c040f0b19081e030f04170607020106 70
    0x18008125041103030100c01c2e94860740006503080c5107543c4002c1410200198100e801c52445042d10100d40003200c4101c1c0c3d003551145c044e984041c00804400015203aa00316000642c01204140d403c04512080003a615401854040c0303880c030207030010340395940044100010864040c041e00d85c002103011540c401285544e9000c0c04c1c110007400028880d688c02e0454115000304602910030100c0f01c14121103143c203103c2405801019a44004d05000c1424400602c00c242c03000c1240319003a0f481201149481e4011710043d85440290410030311400105e40308800e00300c44030361180c2d0b4001c44000006001c140c003a6010380681100104401806443d8004101d810100150194003039002180207040c034800608207400e01c0300c0342801030ba00a142007952404032a859000c004442d409031030748000b4200b0b5141072800165584181d01103540700000f0703100d00cc291030078203089450f1441d088a0070005010f140642c1c68000d600007500100002002801e8040108621a00101c4071f0000300092401c0c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492423687 1250 492422437 492422467
    0xc090c020c24030c0c010f09030c1502160204020903250e1e070c0f0210050a030b0d0c1206020723010c030908030a15050405010803091026061801030501061802 70
    0x100514020391340800d101c1202c800c207403c81c00703800c44400001c00034074032185005042c0c0b0b85074490684685c00c06c0f000c6031074410402e00c200c60441c48204035600c1c2c407038110390820010354000c030030007509802034000e00c0f0701d00b81911102809007a4240090845513041400801c0110001050b41c412104199619180503d1480d00c413034200e00d02d031400c418206400c0c181680c224034550b40094201c40c0003105507814660100180803002c49a03501400b0b203100c3c2d081008001965070b00c0103042081440c0040181c60f80041d81042c41d584141c00c003606080181c2c0302c0d0080d0f081e51071301c2e2040d01ca00c801d1200380da411013840348042c4102e9034201000742850a13211591140802424005610341d50712802d681500344141480c01450001d10500896031505480e076229002107041038051040c58100300801030040030104e8030526000c102151456080b00d0441c040200508102e8000d8031305003020f8488601a010b89019501503400883e0b42444c1041d0034598000301150340700f84034414041090041c00f04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492424937 1250 492423687 492423691
    0xc020c010f0801061b1a0412020c01020c030312071101020c031305180411030111030c07020f09041208060121141f03080307031401092403080d090c090c020c2403 71
    0x101c2525207641071900e0241401c401180c0c0514000c1600e008110030009902358808642d4103d40c2507034000d01c510345c01640c0c2e03107002031504e0703626802c180a102e000c01c4d0490201907001c5d480e85410351030410081155400c981c0301c10106000c03500001044050640041c00b243c000740000c0c0d0380c0b510070f0620780b404581180b0002d000141a6040343c0103d0050756401d42101507070380500c5190580d00e0508201e0300a45a00c005000c034040c0842040b1260300d403824864283c4100d401041554220300900310480e4001d5008280c181402400720080110300b1015030150303400382c030800001a0141008802250220000300002c0d002502400c010024a140701141c108a07544a25441d03185c2d11000da0239000b518031507911b030411010480000684031465008590070343d02040c058040318045481c240ca1856007400301034a08441004146000030441e406668500c0c0150b05c4081002d840e85e80c00710a0700c80c0c00041c4070040e484400c0303801c000d18105014a00d628a8000300220380c12625a50240d14000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492426187 1250 492424937 492424967
    0xc01053402031c09020f010e03190c12030c1703010f03030503040503160b07030b19030f03120c021006240c08040306020720030d0905060a11010c020c010f080106 71
    0x410044140d814020003d68000364500d2400580c103091941c20440140000f480070b0b48074a0184416171010f5014101d503401d0004040c010f00b85d180d4256901c160504040c88040301d060740c00b0300b00099050003100f107113500d241c4a42e64152010520303003091780c11a080100f00c407050350700420041150102e0b000c1c1c440216941800c00e035450744d8603410320509501031101d01c0f01d4807200e100d00c41000c02c040c4500d05803003400a61410001c9259903403c0c07060328121900c11201074000540240042440a074044017040d04c60b141000020345050b6030740d01034a55501c01a809a80940d500300d013001498014440900341d50201c0c186002c0c181d4800c080e62150414140090150103510f8609002910301101c1c05103800003010355581c03142d85080050460b054541150f00302040744050034910b404a2217840507e03550f501c10841c07030300344010400d6590000c040e4005101440303020101201003805591504101c6402a1090700008130014080060341403a040412200c1d070014042c0d82c0e0401018002c00704 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492427437 1250 492426187 492426271
    0x16050c181b04092d0603030e090901020915040501090b070206190203070503041202040501060503090a330e0601050d050615040216060b040605060708040b0c160305030c0105 76
    0x2a0300c22070000144103e401508201d03080c414034181000f1030904010103040d90034014a100d01058000808417602c9001c028000740443c050042c442c5400510b194021480d24001442c091070903000603d03680c5040d041c0420b074540820304000355038000b000310000b814160155803070001e40f580050f04900ca106110400005840c4041c0c006520030000c0d10000b40d03108080b83e64503a03c1c1c0c0c521031610900c14000f06c1c0304c0d0b1308080002c1034a52156044d80c0c0602e210100400501185a89481d000042144030400715069059000c10701c2c0c61000c080c015180f00104c000a11044120340c0030300b4404145c210b00c2c0142503207140c00700024030010701158843c9610100c10000c1c1035001c00940a8070840306444c48011082c16032906214003603002540c0e40404583c00c2004a907070300305100700f9004804001e001c80000388810800520650000c1c40d0414400082d100030a00c071040000601100c1d80040d181544041071903844030809116070b5401080081c52000108002c04445840a0511076207110502c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492428687 1250 492427437 492427471
    0x3080a05180708010608010b0d120c06020f070f051002130e060a030b09010b011805151305030f060114060405090105010c060f06090c090905040201090501050c0f0316050c18 76
    0x80501218404007560103400d803042d0342d5a480081d0302a168034005c081c4c455107011a108400d02d0500508681c0541c0440c800020100c0414165030306d1150034401c1d60456020000e0802c804004802072030183d118060403140304115041642c503000c980300c02c62040c144100524001c0790805000402210341c05080b000903581c3c5c01001c01c0c070240d031030b030301c001d14981b819070034010482019081401703160403c0e0780d00c509172414041400b202408512074160000700d80004006659131403002480c040c1c1104005110044d998000710749040c09614844403990071200c0140054910030500840c446000ca4042d8105410a400a086d1a80c18410345040c8115418410200300d8590007000101e081c02804001403641c400d1440054000d0b802400f0010751a400081040f11603407082d913016070340680d11340308107500300f2005454507402030b415205184181a0200808081007004040840150000c401605803c0ca40703103191644a0b80c0140c807510401e03111100400341c40400940c0482e00e2803d0010706 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492429937 1250 492428687 492428701
    0x70215091203040b0a0e0307030504080d0801050a06180f29091507050a020d03260421091e0905010b0304020108150607171e030f04020f01050c01020703110c0d03080a05 74
    0x200380c6c0c40612030642c0808038100b410305401c10040c0c011141d040c410f60301241e0203030200f12140c40090140e07641c025405041481a58802c3e0500e000c580d503105c01088441c0d84600b81004001c20f0fa5200c0303032040403005181000904503849400495140c0c1081a090010349000a005c001202e880700d69880c00c040b03085420b124041149000d42900501083c03040340544c00d0050030302080f0031048880500020340301c1e00d010031083e1030a21503034010105003041c0070050035000070410300251050401c10f103a0001700c1c09200c0b40c443d10200c03c02c8041a40d003080e00c1c1c00001c100b03640c1c05901c01c0035840400e00403c0b000d42d8101000c15481407030b04031010402d491a20014165006030440035108000b1200c40684a503c118010a0350007004d900d2400c61110407104258548001c80e0084a84001407020030018140006144407000301410150700b480001841107003260065402070300010213251401c1c0c1801010b100d1219800c809840100c1d8911743c6e03072805030008801a01d00c01045030341c1d000207040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492431187 1250 492429937 492429941
    0x8030c19051c0c06180c062d11030f030702100b0f0409150204060e120c151303140a1209060906050c070510020f010e010b0a0e1e070215091203040b0a 66
    0x20980c00213040280302e04c001e50b40c0d289000d40e410211107050211704081034860103030115041c1c001805254240000b08074102099040588565005020190701607001000c014005020301000c1c4c01079031500c0e881c012600a107811403200e4100c0c8140d140c08401e0030507031100711405090311410303900425010881c0c41c0c6000000c1c4001c880c0d5101910105000c00c0d0140c0c00f0002c115401011244620070360000e070641912980502100c0750b005210440d01c10000074600064034030035841700100e0101c00c0d42ca0f142c160762150440440183c1c1c0d0420103a88041010a0340c041005400720315148243c02d007000800380801c0701c0b50095205100c400300344041802002c00000c0c5c05824090103c0c6444d960904001c0e40d0703150000e4a01009500304a10031400704014494249061001041c00024a141c041c02d1560850080c01d40d42c44808403075040c241caa521090f00a00601d004d0b80245541c0307891482c0741004010150010120b60401501602000c0041d07040d02d4110390041004d03002134580c00b02d00300c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492432437 1250 492431187 492431207
    0x7030c060e1606111e0703020108070e210d0807080a0b0d0c0914090c03060c09010c060504030810060207180e1005040b04020a050f1503090f0708030c19051c 69
    0x4540a1482c0105209034082440340c00c08200108462524040f07543e501d800100c0c0c21902d1005030311180c02040550b1007800c20381d4010420741484090300c4281d0000c901d0203210f848400e00c082c007050b00503001c8034004105480040500d0314104046083c1900004c00022004c0e021814064641e4240201940e07190701c8000b04691008110800550325a008006080140b403a100c070713140c02d00d0000310341d8034001c1160100703090018054000760380c841d1a086626000608014100500c0e00111000105070f0f00c02e0070700880c06078403440080e142444540191207020340107182150081d2070100810801120b51344543d6841100116641040c281017030301c0c1c4000c030122445414241414081030014010100f40550300a4440d41841a02c92041c0081500140e00458120450325a8103124031280006113802607200001c1e03440031040020401e01c1d0800d190092002030b0070004403140941410015808003440c9501d0042501e605619070ba621a50500c035a048e42a40b0038400d091f00c05c1c402d60700300c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492433687 1250 492432437 492432463
    0x507091d0108010c02070b030c0d14090f1002040f0308071712040c09090b130203010b280602210307020102090a17070b03010f0308160f081e07030c060e 67
    0x241440840000100000c4203105041041d4a0322007034003103080c800300703541003541c0c01968103034030f1500c0344050407090764842444003040a0381da5005000340074214000703500a024000041c5600b4030951030007070500710403150900c0c4c1c4074810082081706640e10b0340c003081160342022416490f62201c2c00c001a1448090101400302080000d20840a040010310301d8055800355a00040c1e41b501c1d0b07480e403022614a00c80203061104030705c00240e41942c1640c4000c0c00c15102400100c0d149503c0000b10b55840b01c2c085801e0170111580480551403540d004854008010354401802d40c079000e124040306a40c04080c0100740b80c0c2002001403002c40c000d4044411046016101c0c00300e00b03980d40e902c0c031041102d4020b003500601495000080c40319055084da4181c0d00c0207421281000d1030343c2e681440359800410034044c3c400054600c500402c0007000c1189645000380c044035900e1098468141400b80492001241c0e40c40034403060011a500150066503160700107000514100720000c00703498550310031408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492434937 1250 492433687 492433709
    0x70803010815100e060f0f03010c0c060e0d08190b090c1c0501060813030207030206120f01080718020322210305040f0201030216080c010501150c030210050709 70
    0x15103090300103000c00b01c01c10105503a0740a500c500d08101d000000074407604a061040700042041e0340342142541c440d811005000c07000050b04040482e09454807200742c0e0300400c06405001051101c10b029034203c03c545000501013900f85040003514030301000c1d01402d0012054034543c2d18420700c50380000f0301c96100502c214ad007894000314803c0f0700d6000d407000d0444013603c04120b185000c058021141680c0c210f0f111041130f6661005190080342c111401681140b083c40000005616044000d1a4603501d00c1600e8680f0303e040f804081d81004180d1111615901140d0200302600e001004400c40c05a4980b0150352501c40703903561030006032202c00b01c40100605541260030448280700b07008205120104070441100c50b08c4007070f07007224412038000d4501d001441c8032000662196005004500c500078110003007200a4403400c003e5004040f503020969510130061090400b4120300f241040200c0c60080c00c207050a60f0025103518090501043c1a9251001f00f61100d00994020010f07284080390 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492436187 1250 492434937 492434939
    0x26030a020403031e080105060d06180f1d0709021b010c08091902091b0f0414031b180c04150207050f0108040515060d023c030703020909010207080301 66
    0x800035407091204501248610452090340c09103509150344100b440e40320b180641c2e107081d06006555000400c1c4490185c1d40b000085000000c414079090303048071f06880000d009006600e9001141c0348258400c10455554400c80c940c540002480c1080d500751103000f40e2141e46542c0d042034085040a003100c003c1d400c06e0340c0705404d40c0d44000c80c1c0e0301c2464540d0403034805100102018140d00294507001c1d4014406200040511031281128070032002040625880c0c022009801d00064201303030443c60110321040720b2049140f60421000c100c104411050550310070001000072601406400d12440081c0c5650004003184c1380d1006840040280c01c1c901a2440e0074071f480291109030f903005131442035105c80481300c02940f10b8852588102d9100004001a407039921040d880d6500040620340d0059003a092480180c07600940711031743c244206003001003c4100c0c000c0c079890045580e00c00c0e42c00000c0c00310003c102e40c1e000034031104894054400c103985490b401001c501900c5100c502603c5041c0c0000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492437437 1250 492436187 492436201
    0x130203070306090b011d060d0c0206180111091c0512120108010e060c0706060b070f14010e1908090a120203060a021c0e1e160617042603 60
    0x254428142954100400394680d01503500321929012550300080c5640d41c16024403e0402c802c03003c62030014031a504046251010000fa1400c0308480070061300010144903000441c800d080488414a50083c8000134055201210034096008828030400422480d00c901401d4080401035080c1c20030142e80e02304014583e01603169101602d00b070b0941b40319a0000030106410b224900207002d54030081d0015886911101400c1d4100007010b0300e00701c1d80c0f103400158580000c0005c00c0501d104280c40c0d01c4c03502003820303c022a41e9103820314001c2c990401e0740c2012400c1000c100c035881522814051001d09a440c2810352040c0161040309802041c02040868401110250040302e54030841c21548036940e541c0c12130050b801038000f641a2111070100c00401c80d4502e40103a1a94003903181220f000000600403000440c002841c0302d40710f50407025200100d07029060146001d040142000072100007595601255984000d002030314140303124001601e2031090240880696641d50341480e00c07400c00701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492438687 1250 492437437 492437441
    0x2061c020c1608030d0e1212060a060f0f200f160f03030507170c010203041103010b1207150c080f031006080103153215011119060b13 59
    0x20701040c81c4501c81c840516034851511141c195050100a1410f00c1c02c4121400d0182c56800400c04590040070070000f8070b450b41c84060100c3c910a42a8001582010002e0103101c1d0f600d80c00c80c0742002401009004199000800102c50002510300300255160b8100a102c2824070030341d20991502440d03000c90440c5d90005000480840c241c0f80f03020441c1ea0340c10115800703086030710000300411002d220f1000880c0220303071001041c0c3d0054014516000b0751181c0582268003c460894040b000d0107041d810300d0400344200041c3c0c08081e5003500d80381307800300b281603071314482842044a1810100c80704503480c2e10072541d14030183e81c404207580c0c0f200020801042203810441c0e4480100608800c0090000d1043e804ca90480c0e41200340c00d1600c040303002d116405000a109103d0080701422948850450016050f20040307560700c424441a05000a45000c0c40400340d00e030504001c070112410b0700101e0701094101e0f44201884d4001c03180255071074064090407800a415520504180d030b03001c0324034055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492439937 1250 492438687 492438697
    0x501150b030901050915070f020109120309050c0a05011b1b0803071a1006030506030a0212070e090303101715040809100c05060601050a0917010207030807030516080402061c02 77
    0x4000d1150f5645e40b44040c1e031701c3c079940d0f01602000c1800c4020810042c020440700c60032010510003c17880c42c1c02038031840413940c40850380b00002955030746900c0a00c1824018201ca45004a6600284d2441c29000070300c2c6200050302c4807001c0000904e80e000300005200d010f59100c078100f0b00003032525520740c04652250000b00c020b543c0340009141031000306032510340c000e00c240348102c403a400d80c1c1c1c2000700440082000808940d010b21030f050581c00541ea0b5076001d45001c00050004281280c00c4c4200e122000f80b000d440480c460b442482400344410399140241c0035070710a140709104c00d107159120a8540b0460580040b284c6400b4002e0100f0303c0a80c50040448000a83c0c2400321040e082c03008680c040c0c82c031000548103403c0381000c1206507100721300810500c2c18502e0103052003a00d070710601c50440c04114604030160342c00646003003019000182694810014103040100d440c00782100450039204480c1c0d5402c10460000080c1103641d45825620001e40321000580d0035184110b01c04000c1d408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492441187 1250 492439937 492439951
    0x6030c1511070503030712210f06050d0b0414190c210b040605090703200328081b0a11030f010207030e0d0305160b0103021912020108040501150b03 65
    0x38000203403421510000700d0b03000301e48018005600d007114a8a40340c0844420840c88002c1089464074440070f0f2018007440385100c07801520010b082121000c0794002c4680381e41c4003900402110070220007107515a10940d91254000403e4a95031a003084030038100032071907003802101c440f0721030031406120000c07003020705945115520b14440004c00440f21031032100d40340018100d0020000040000d40d05030409a0000c0707140c0101d41100fa1250f6882d03180c00d525880041000c00b0301c20703100055140400c03801103c00c0d00003146000c800b00c40040e00e0311149503000c003d8110107001500c0c415800d820b50141241410381e4046c0c641441c0a840c2079520480c48000b864130034485d6890400160f081031007128100340d0f06031540070f511407a0030140b00c0c1d21194202c00f0f8090080601c00c44400c001c43e40c00328205140301d405000c082d5030552040041d20800c6c521010601c8910400a01c260300041e000c41001a409080c02d0307129644620b8814003401001c0700d07c084200b010840051302134081e04c0a180070304e01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492442437 1250 492441187 492441197
    0xb04060905090f15100e030a0302100b01050301080a03030b0303040b04090b03010c030e0d0c020a0906080d020607020a0309092004091e021e0c1c0509031c0806060d06030c15 76
    0x35015011480e030907042d2084813141405941041d00c0e0300d04202e0b42c1c03588940314100b407501c418540000a0070200e009000343c001d030704010144030081009204020f080c2d10242001402c55041c00071040e55a41c8000005043c95600e0f29800314a076002c10507100140302894030707503548a0301c0c6e480721001740032894406030003507080c070000e603030303040d0080c091000c400e44504000c04036440f16940480304100070110036a000142c10300e0220300d0200500076600900300c4500200601c14903da0000d1800781c004020000315040010340750002030388001540201da4030120b0210311203103000400b80490a450014510312070001400123000b1450703400020541d211410301c100756036910211141030b4400d07220340b0503280480400c4001100c3c001e002604940310340702d00f00c0d61302c1010101e006c5418810011000045500460418180e07c1c0800010042c43e190a47d000380414020030b001d00707070410141c01a4454403000c54000c40c1c0e200700d50300c40313070095400c00481e813041c0da51040c428805000c41d1f075031080050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492443687 1250 492442437 492442441
    0x60b030c09010b090d031103070803060319020102060c0c0c040f0c021902090601030504210e0901050402070b0606210f072703241a100905031f060b0406090509 70
    0x200e0180c1d8500d048466441c5100c0c0341c54081803c12032038840c004011014444009101d80513070000300041c0403001d03c601070711984c0c0e003021b00406103850410400ca001d0310b0600d800c5840180d9011503100d40002c00b0200340c81d11401c0340540d01d42402d604501c130580082c6400c0850b4000c1d001c50b0040a841081c0d90240e420b003002038a8680c0741050035000294102d615000807131440d51190303000540c0140548100c0c0301045002440154948401001200280c6442e1021007145884980f06004003000c44086150614603910103481050040400d0320807040803d20b0307403100c0b00c0c00c0401d030b000e00c0500000c0b414070300d8019005008414250360030000148804c448a05511a005540e24880040e03020003030014616601c201030710541080c1c120142c4001100a07030401241c1c01100100400600c201185448541c18440e400003050b040004001fa0b1042c108100d44022803803040d0400728007103011006003020040d00143c50030b90300c001c0700401c0000d00000c10395800b0b00e0481c10b0724401c0f01e807601d080d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492444937 1250 492443687 492443689
    0x70603050c04061704020a030803100303030f05040b15150a120e071815090903080a0b0405130b18030a021c020c0a120501060f080a0507051801181503060b030c 70
    0x182c00b0750b010340b001003204004042c070340056100e081940a4401012400c00903184d5031440e03000c0d0016100f801002d17482c0041402099018000c85513403003062101040149401e4440e1020300c00068404512004562200c0703145480d120009114850a00301d41651020034882c014000c010800650580341d10705040041030308400700b143d00486020086a850b0ba20500c080c0d0002446c0301da5100c440c0c440005030000b0040d04500849061324000c0c0c4503100c0914020510fa8144e4000c00010303407003203143c0b2042114614104800e0120a50412889141907694441340d1190b035402003410429840007040442c1e00c0741c0e00042044004034011003098011100c00c00c00c3c0c2c0d803001e600d044164006a0017174180100044100e070310028600920020035510740c0c5111240840c3e003150850b07481d0382c00c1004400103100b82042028018441901c0383e86100410303c072214031404060240e030000a402c0c03e454483d003600ca070040c105100d508e00c103105809640e45080702c001c141002c651806401101019a05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492446043 1106 492444937 492444961
    0x60801090b0402010e040504051c020a020402030103060509070b070804091a0d0b1803030f04021c12170a020c2e091118071713021207060305 62
    0x180b0300b07040c0001018003003000314640c0500e0800c4140301c0040e00009010019001da0008403441c0c1110300d104030305000c010312010358020f0000c4008070030b01203030b540100e000d0708a0400b241c001e03580e555215880c0e40208800544040c1080c8401c01101c2d04a82000422480c410090880c0d20110000a41d4178524107005464914070003042040c0f9a00c1c405072241c41045100081d403d61030098000c1681c0d040040009000c3c4002003039804170031450400140300300d03622150b82c4100100d40300000308090030811041101000d0701000ca10096554400c882e0b00424030405440341d54041d50380e040c1041d0019007444040203402d4000e1020b0141c2e841110581440f031040e9110480b4404100b11681c101502c459002100c200f013400000358000013600713a421b07803507a60200583c0c0d401c0100f00031007032403000194001050701c2c0d050424003404a41c10302a907003a034508000c244c803004090b0391 = true := by decide +kernel

theorem cover : BRFrame.Cov 492266187 492446043 := by
  have h0 := BRFrame.cov_init 492266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492266187 ≤ n) (h2 : n < 492446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
