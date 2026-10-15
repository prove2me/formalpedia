-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:53.893863+00:00
-- url     : https://prove2.me/submissions/ac883750-3c98-4e01-99a1-41bd00f1eff9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798201438 ≤ n < 798381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798202688 1250 798201438 798201461
    0x15061715040905150c09010f110a0b24060a02061f080307080309060f040c12060605150415030b010e09180a05061807050303071217130b060105070201170712 69
    0x80022022600010303404600c01422041030400c100880000ea81c2c103e0b4500c1401c2202e0b24180c0a0349e10211030142c54a0000c0301d018240c07840d02c40401081e400c240c0c80c039940c03602c403841801c5216040341060000034020020380ea00513030401000940341c00c4030409806072200340d000708054100d0751810041d00315440f5100584400c4000410081d80358410004140c2044100003c0030b0a40750944481c0741183c5c0341c0c060994003001d458200780a100d2685c101e80301a00c0c0082c821101c2d981c3d102229805684107102e08112010540c18105000c0d000c0e2041e401da001c01030316224a001c44d0541040340001e0000c0015010100b4002c180b00341071410086084000c1c80fa0009002c40c0c01c001200403402c4010b02030304200366003c09000c0c059a1030100946020a80c8101080028945580241c03888507101607805d0403a18004204442c1513160b18841c0390342030040e2540341d00c80c0c139180011141440345140c080c1c013091070200203c41e81244451010351000784d0349000d03100c82c0c2d414414003003641c0e85d0b10000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798203938 1250 798202688 798202693
    0x14060f03070b0706090b0f1e1e01090902030c0105070308010b03130501151707050303040e0907051306060314090a03120b0402130509010e07231b060a15061715040905 73
    0x10354100006d070f04886401800c5514800b8161510408000b04080004000c40c1038601c0300020644c02c050290182c11000d807068078601c81036841c0c08600300200f503a47c1c03050f842441032110b021030550084044641c0f003500369030303412040c0e0308242c042c90032035001408144417118410300880116100b0f124a288035401009030300c0d0303100d2510080306520b0118003040c2000340c0042c40100134a82c0d0000c121800c42e818501c062005603070741c07000141801c14561203c0e401c40d1012a100e08800d003654002c9041d15001d850804c880c0071f070350303014000390541103503c0700b000c0e4051150700d0f01280c00f60402d400a580c00c1e0380d01003103440001010038140d8214103c1f0140001c0240d02c14011454460039950244c001114262030034500300f5002803001520048440c2c0d60355003d81b205050301c10100446402c5c1b04071804402e2400c030b0900350907a684404807440b0b02064645010b6190b1741294040190844420380e46890304507500050548841c00c2c0a80034580c1d182581c8028881a02d990080111a600031b101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798205188 1250 798203938 798203951
    0x121a040803100602010b06091c02090705070311030a0905010c150e16050301020f03040b040c0e042406030206030c0a050d0518061503190828030f14060f03070b0706 72
    0x400000302c0120b80109055904000d606807494031544143e5412085c11110b2200c1106400c45020b12403060220280d0408a981c0800c8881500b000041241c40d101e60358a0003180c4401e48555164091503100074002a0a80400c015a61140300707101d50b850300a50300395440001c012072000c210341002907600620307000340440e480d0402035400342000a10054000b589803088a5103001191300c401040103295040d11004103080c0442004440040c005075410b188a0f800c0c1410f041c40d45401c13100800e03110b104400020f180c2c0308034a001e80001c803540170b8407650940c0c0b59501440038682006072600200a010b001840303c0f80418082c880c010120100055100203a00b11900e0400500030104425013960403500b8000751000640e814110486400010540c50715107050145445406544000b26510b00714500f0358024200c20182c4104050300c08001d03402200240a0955084d020252220400d0800007142e40c18072458810142c1c030001d040c1c480107500c4142500054001020a50f0025540d10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798206438 1250 798205188 798205201
    0xa03031a0105030f04060e1c0c060b030a03080a420605070818040e0f16061d09070302090a080705042d0c2312010b090a121a040803 58
    0x10082110140203280c558070f58680300503008003050016000520065481e0045e0709140400c0c0141c81844282c06803054002d05d000d0001000f0aa40c41415a105860562040e03100c6c0750001d141c2000540c161200b0031255260046500240711040010b20b082296540070064031041c9446c0d40c52250000806a01c00a60383c160749070f4100788c0340c1100040c808100550400b00f0420410784e170140401a00b0039045021600118000d003410304181e07a4036214078000580f040c2d0000c07401000700b1030510707005942e003561a4000c50340840c160340060071380f402c4015819982d0424109942e403119803804d01500c1c05143c0c101048030050039a1050b811600315190901c001d1030140a00c8148588049103030003400801d850542e014a00d014605600942d0b80080c0c080b41f03409020b170702c907481e80008000061001400c00804540d4003458510000340844400419240705c0a419190342d9a00030340300001032410107441c605e00145810080d507010410312601550a0140e10050380705600c80c20010342c6a0410a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798207688 1250 798206438 798206471
    0x106170f01140405120a0207170307060c02030f070b0615040609060f140306100905090a020a030f06080a030804051204060c05010e1f180203030409150801060608010e07030b030a0303 80
    0x3001d12002c00034550074400071540008103c408030142c1c2c1d450325510318080c0000c0e880c00410351700c2401c841c01401c000c901c42d00001b1014094180c0106014041e0621801c0202e84a105505aa00c040c4c3c7c01070200b100070450750208a503106c80060080070032003988080c142011340041c0e000c80c0004044000503c00c181c0d22052020500125080180c24090a00121012800001c040d58015030104100d005010702c101c0c0064020880a4101d880500740601403201075849401d41c040403a05204018552041601c14041100c0c0c104014210740c0d0041da408071824840580152528842c0d10031390030382140c030403000307100420158668000017003c900e07007142510200064503035140c1002003016442c0d02081c41f040d019106001000903200300901210a14403102c00b80a90180300c042800301e1302d141554442c041c5c540502d404151047e96610405080c2c13000c1c1e00a41002916200041000c901184041c0350400c04600300459880d02e0100417a20f4240301c0d200c00d40c0084e031603100b40b44080240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798208938 1250 798207688 798207701
    0xf050f0f042409080703030503220c08011b09030b06060304081b061503060f010b0c010608060f010504052d0406090f050a022b020618090705120105060a02100507020106170f01 77
    0xc4c00c044c00c103480c95518081c00d00d01008000502141c030307241c455280f800c5c0328801c0e007a12503809000c0390106501da03811540200245403001202e030f000301c1342c020380150080e8042d07004c90b640040250251380d211420300180e42c101400440d030303080c41030000703540d035804407582c00c5a02c0020900600303503860170a00c40c02480d8004400107010703400c200709102c4804030092aa0f81500e04255455503035448981c5e5550040043c0d600401c164081e000500c00c03640d03881c105d942c0c102d0340125410701803516a144101c0110b8585151014645c1e64031400344d203140107840e00558058011000010010015200e0342540d00e08960300312941d4125a1001d000c52401d09007120603001414400210b0400c41c0e80c02c215030030744540011344980400320b0000d140390700f0542400d00050001d06050001c0c00d1500c2c015140713401807400c10002c000a41c1c00402d40382010710680c0d03032540242e0b00030301061b42d002c041d5030010319003d403420045540713854021440101501c0d40110490071080146034803010000b01d1400c6511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798210188 1250 798208938 798208949
    0xe0604051608041209050a0308030603010c140315010c0b161d0319080d1503060c030c0909231302120a030e090a0b030105040606150f050f0f042409 65
    0x142845074200c46540001e84990003584110101890250740c08140c03600003141e48507941c001c03a00c650102c100b01c844c5010b54082d940c154020312181013407000583d0490100c0404c2c0807255000e00010307602c03139a4034541220394401030401a4016400d074a6034103c0e00012581e000c620070a84220016059100d5000003c0ca6001110461030440c0c860000707454802065070003c4c401d0b00e5002110502100707a0031145280c8003000104801029507400400804d0544015901d035454000f0001c1241c2c02401900d116007096a15408040c0c2412903003001440e200420354050b035600c010b07114030241c451500d02d000c0c1e035410301100b2043d5078a104100c0b00d134400004800164100101003800690000213000307000030103c81d0000541c0d07230114000001c000760790300c00d9815800c1400b4403050207400c0d4403010560752a83d00701036585c801c4120030364510031408001c0d00014402c21000e00031007c21000f520f0000301500141d880d050b6a40b05030440c800150b07080d18105d00340038002c0791289411804460003002d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798211438 1250 798210188 798210211
    0x512041d0103050712031e03061701020301080c01080a0f09061e0b03060103080901050705060403080403030f050609011406040513061d040f080711030d030f0c021f0c1403010e060405 80
    0x60656030f0702c41d2548401d00c64001e07280c05426002c03080600a0346042d8181008000e415404108901e00a0180075a8400d0700c00914210401e02d0300845d0600031030341039440c030500070310040711100011294004000c2001480e207907600315001c0130350407a0090001040c0034445c0881c1c003072105040301e908103580d4960194036503d4090454060313140440c81e541102d8102044540384c0d603980005a81c070f4800e446e401000c80c003c40040008144c2c0010500e030150f402039404010f00e0851103543c01c11a0b509940300380e800403070000104100355141ca0194541c150240849003069a24401b040226002061803040316890340014025200c80300d2420115124400010103241001e488802000302103200142c040c42000030120f0a100c00e401003041c1da0100542120b20755a15040020001c0103d102a640070b03501303003140180c0ea64800198174520038a81a542c040c082541d00c0340000804482c8114000d0040f500504007424400501a60007842454010119407a06108210403540c00503c128a0b90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798212688 1250 798211438 798211441
    0xd0204090606140109030b01091a0d080c01140f0411031609091101020118080f1207020f1606050a2304030c140301020432121e06040f080a0504030512041d 68
    0x20f1f1042140e02c1c1110013003100003409815021310145c0c1c1d610210b25064100b44c03c9807150040043c1070000f464072100d4072008102c101c0454a91001c4002c05840050b01c41801c003003c07c0115901083d0400260710040449481074007158801801c1178460740031b04003050b4aca10340181400640c19070b04c00e84040920080000d002c0105d402003a80d51b107030401516404010403103000b01c0c4d8040c0c04032011103000e41c1d40050345103810b0b00700950720414807485254a0181c13420408207d040642118155145500ca2034200210782004442002d003c220b007a151101c1400018515860600144041c60290403114609814026803a182c800c400460601030ba104020030003011189060240c0900d142840004101d1041ca1038150846401c0782070550200b0825809a030f03040d80000c00c1d07000c01c01c1c0303410307003000d1030204411203500c9000c100c601030080d403030030500c0e0fa0000c0c020000070f00d245072035030074220306141e00c0740c0700c05190052200d84a04105030000b0b080c4840480b03e94101c4080d02c0f0350030809000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798213938 1250 798212688 798212693
    0x90b0f0907170c130b0a03020d050c03040201260a02070503130807030308010602031201090c1115190603021c050a0c080105010e2d0603100207051c0f0f0804020d020409060614010903 80
    0x204c90591203288812680420f142401620079011282400107111007030005003000741c03e941c00c0d5402070780c00328086040380b060050f40d21f2007894118110442c002c1e50745c0c40e0313580b1a52602d0103580510411035490000700044003000515a5040001d081e1030001056140d0841c94007410b4500c040e0405420b6600900032415071035490045c182c150390700500c1c0480c0d90400d800040d80ca05010002d4007080d402401d80071030003094034100052241302c8011480032040300418100045608600011703400000380c1d4035190180c3c0340c507110800c0c0c84e4402c10483d40c40c4c548517154401c5c8000305801c02100d50b5100c41c01040480200b88182c0d4214103601c00340191160500c800b90600c141003031001c452591144009040e6550900890b42d0784080380e5000e541d07030b4065107406521601c201038083c3c0c1030408000604003003440b0300c0c0704003080d012a464042000d2001803055a04040040c812a4052502808040140c88600803000890310458004c14600d08026520090400e0810b80d00c2c101b140301c9008101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798215188 1250 798213938 798213967
    0xa0605060f120c0118080d030c03060906030203030301050d0f20090a06050f090907050a141206190b2b060e0d0f031a060a091d010b04090b0f0907170c 66
    0x700703c800d082c00280c9001000301908400b40b5580002c03080d0003043c185140e0160507400150991815550400400d0f848079166000c42d00140800b94240d842480140070034204800000e42990041c1c2900942480342c0c0c1d10701900325510080c01259403548041a001070428403e941e070081e4103a0390074480542087c010801208014220324030039024940440c0c09000107101840c05090080c1419100e944c50309000c0501c1003c00d0079660040f044070f241458940400710b44c0718050b500c5402c0140c9060040e211103006011003000340740c1d03c2207540c0d41401e1424401e03481840c020054071041010700846061000c22183d42c0d2748018001e40090f00b041e0049d070fa004051a5040000e030900107003600e10f0b0380751211042c150342d542c2034120f4000240851100d800085920441c0d0324826040200351174000032178400c103000c2c880d01003007800038001480700b8030307194100d140340210180c02043d60080850011f040107a05584680100c1d8074030415000340c424010619500581410206141003920f090100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798216438 1250 798215188 798215203
    0x40e0a060b0304030e01030f11071b081924060510080f071107031e1502040315050703090606180f020913050c0c03030108060133180302030a0605060f12 67
    0x3030400c5403d64070700c00309a009a2103a205d035204100d080022710080c20240c2c1c2c05070300190040c1e5a0081c41150070591450410b0b41c0802d41d1b0443d4040c00c90310718102d202e15042c442c43d00701107862500c003111b65091400694021742181e2800140440ca03585044240981c06543e04042e5040045200811980c0f4080c0204d564020312185000020001d070740320040d08100382c41c0c04c000c0080d0780083c80340032a49401c01c0008042c5000c0c1640c4001035507440700803000c030300c29844014500b42c0128160348007104244d0160b40d021000e800e004c510041c40d5681e820484035503400003c007100301c0f202c802d404105288110484042d4240013107141c1184100001d800c202c419040c001d2031525980011750f483c0f40c000507151402c1d00441100d4483d41c4910149440d11001d00a00340120480c417007145d00c0905401ca20220000f1004480740005080c8004651440138220744294200407050000b0050f00c0400c0943c92480c0101000103160503d0400c10144201805a55210b2040301c259007000e041c0109459 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798217688 1250 798216438 798216443
    0x40e1f0905100315140109091b1a070812092b0804060203040c12030203091c03051b280506070302040503030a0c0f060c0206160908101d070308040e0a060b0304 70
    0x803411003034900711309000b0300004510710a41004a80001411101350f401c14070900344609841c65010f00c800c90030080e01d452a00c00c0001c0103003070710807000044561200400c40716010743c20041c80c01e2440441803d040c2000e4030b40b0351159006900011030030045484c03140301441c0c1e02c142409401d00c003c0000300310490180010386a80e0f40003001c181082407610b0b10304000d041d09101c4440350000b50074080e440741c004004182c0a00d22954410545000c0000310750402a0705481d11424100400031003000070340c0310000c0300090f108100180030800c0c10011000f5a6448080000b00b6000e0f45181c06410240081e0120090600510040c8260398011045d14490000d520f4481051041d071b0405107400181c425010380f61920303080c018000c2c3c075070108656100e036050000c1c0e9031070060204000c503100b5910784503092250308040203840e4030608903008002112015000340020001095a160034003a40341e108481400c1c0010301045954100301400d54096040342c010080141303800f146000922000380b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798218938 1250 798217688 798217703
    0x41a0c1e0c0a02130e1504110319081605070f090b190e04080f032403060c0301090c120c02012a020304060c0201031415040e0105040f17040e1f09051003 67
    0x56494518417580030456803090b13101100c0c4e002d0003101c41c1035a0442c0613201030703c40b10705819000286083c00180142e075201c6070b00c4200c01006881d21080b1642d001818125100500c00b11164046081001400050140d226404a149181c08181011101c041140c1c50044911a007100c01d1054140038110441c2d51200388504543c0e1207242200c07492040c440110380040c0d000c01400300c419075040c0d14410040a0640480700c000c005010169503540440f20001180300c2000144505d02050b04207103030310001c60410f5032400c8481c2141400b50f80c0c102c401080107039034074041003144407803486481c03100c0c041c0b011044a6113130034008025124030550117002c041c00a5840c04100316403103540070300865460b4035090209414074400c00c1c032190f11800c1c011803141303007061002d1502900600c2114080d60340841070080d100d078103945010904003904002d000f260790038070000440c100e40380455031180d44480e60442d041c0001c5080d02c5e00c00350458100c100c2040c07801c0d04000030003100428a00c16260009030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798220188 1250 798218938 798218959
    0xa091a0306040e0304090e1c0c0f02060903070b0705060618010602030a050f09040e150717181204030506040314070b0f1906030c2402060a05041a0c1e0c0a02 69
    0x80c020710310b200e5540700c140c546103015030ba400c18881c00704205280b02c48da21200704100c90f200c54201c802c0b00440c08050070300b48074030a90000601d0910010502090b025099502c0d8940e40d003441d00303241d0084072007512560440e60822146117041081c4003464500c0302500b440a50520300300075580d000b150203103000c0c0900050303a03c0101d0000343c15038800f281d0052080c000c000d44046403e89500f100a01c40d100d07400010080f44920b070290748010041c60301c50750782c0c00c6039960b10003805603e0b10880c041008030340a00749518003d140e00d50000c0c009140034400a207803e040c94a8020808040400d881c090700c40d040c8031840018001500c442e81200e40c5903421001034440081e40101080c1c3d03034900c0a8458906075001080000403c0e03c20100c03000401c440030b82d503507006602411406a405000b0058108070b0010f8641111540100e4005008081101a02c0101c4800560070001520307660729800000c6000d014110b0f00410802c4860b803241c80f0076081111b51420203544020505000340b142041c200d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798221438 1250 798220188 798220211
    0x20c100c090f0909030e0901060f180b03010b0a1103070b1512010c0f0908010603082a0312060f010309121b0b0a0501170307020d14210a091a030604 65
    0x28450142040101400e02c0a60b10019000209183d40007200402e40ca03a540c84c0c140d203010100d090481d06907890f03e03401819684011144034417012501c8004002589010650101d840e01448c06800c40f2104d5036a42e481c1c08401501c46503907503103d414036501c2042402700160084806642004904003510014150385000900c03c840100040b415507191011a5018582c0600e440000d030700a516030751120358440ea03109003a1940380c00701034040703101041108103020400c0c2c2521900c00ba201d0641d01c902c94480e20030b41c1150321280c5201b8801c0e41300e009001640c688003590310761050f001d08041000682a0360703403112032000d0841c50303c140544480c0240710180003621405a09078481e4101c0c0302407620f118850700400c428041c401c48a2022158000e0704840001200c03000340d00100701c1c00701d00300c0d02e80c0c403020550b407904120551400303040321109002d08101046845064802d1020303071100800080189000080d9204200c00b1200c0480c1c420041c907903504403130304a01c00f9200803e03d40184e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798222688 1250 798221438 798221447
    0x102120708040521010903180f080a08031305030f0307031d070b09030c03070f030b091f0b060904020703030504170909011e12050f0d0801081902030c031509060703020c100c 76
    0x2183d041100d5003059140410540e00c2401840d140c210b58114803c01625200702c400384280e10302601c1c0c10b66000956800100d4403c0333000d582d214002000c50088401c1682d1418150f400c00000694422008014450070581501602c200d4400700032000d0901d0300c0074800c1540d18441441246542100010b03a513105440074000710298140140c12201c0c960342d1010320b00d0201c1900d1005440e6003d0a10200d030900f4804500359680140024106800100f900d031040001c046111506070321860820048819840e9400980541030090702d0005042c0780900704180c44080f0f000045440140812002e10b141d0740301007001d41540e5811845010303048001503507021082d0260080b50201c10000e10603000c0080001c3c117003454140400544050003a105002e890210b002c0c010320600342c01c0440000110600e0303c19108402c0d00041c116000007014030b000c0b82c2045030440c02070420010450402c1035610003000566003100881c9411450a011154510388551000c00c0c1d21541c1601c503500115898800d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798223938 1250 798222688 798222739
    0x305120402031011030a05010501140d0c050417010c1112120406090204020408030c010b0603011d04050a140f071d1306140f060306060109050913081207090501021207080405 76
    0x81c6010070012003018480586070300111b070380e00c00b03150800001050551140038044510001035948500704488918183c01800544400804103c018440014236243c141d030407108a001d150000200782c0c075807007801031525206001210b180d5000409940e0f4200400c002c13074500c0d40c1c90f8031000700e00b900c2d94036081026003403582c000b95025001040100f1004400b20003400107a5000001704044600c107800c4c0480b0f4082407007403d03452402d84882d441c20202d88504194018810407c0ea25170300c0480e51040c880d200d2a060b0700000d03510a581150f4000c0040000740094000b03140030090740e03509101601444a401081185d540340c41d0422081000f96a4022074050604120b0a01d0315140607803881440036000c03110b0a01c02e104030804030320254012000001501e8000d402040309a4070801444642011030320201c1d03055404000080c000720703441d074030315010751041e40e1180b8541d460800028030300100c1c2c0e100020072200421040f130003d91268100c42c21500c0585a241000c80884d090000c241070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798225188 1250 798223938 798223963
    0xd082502031603020d1d030303010303050f070c23011409011116090b0a0506070320030c060f0f0f0f0601141c0603050712030c02041812030f05060607030512040203 72
    0x10280c400b10101a0082444200740c3c150741e40c0e101600038408110302c1000c04035000160550000c000502c0403d1050006081d42402d100159260901d150780325600b4207001e0b0f000c818044910000d04040c3e4400d100d42c481000f009281201903a21043c00c100034511950680358103000b540d06000322003c00610801000103400c80310414020303981c0100310003520f9003100c064483c1d014400c01140c1480c2c80001d0b102c40c1074156a40d201e0340c0910155540540411700d244051500c01404420101e11040040a10030032403020014440d040021029500b0740d0013a10001180080c20208582180c2d80f8064aa0040c400d103071440070f040f001c0c0c0c20842c01d44100a000d059030f44003240203c190034004c0d0844421240f04808035401940d0390005000c0881d010b14004001420041c04000503180175004050070b880410919100900c259030b8020355401c9004081c004641c450000f075009605602c02c45611440984501745020600d40e802070291003803d002e01c0001102801042c107644040107408214003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798226438 1250 798225188 798225217
    0x140a050306010e07030c0507030503070804030905040c09080111070f0809012303041401110904020f0909090a05070614040e04051011040f0b072f030616020d08250203 73
    0x16100c0302080c6410204484c2103002c2410100000f0600d441903040394002070b007540e80c143c2103840360802280d00000c083c005030b00704214072002140303560300e911602c604245d00d500c407440c41c00d190004583c25980540003003000c241c014030052010850340d180c33000c7d18a90109050399681c04010051705c10f1003c0c00908500891201104100c0c441e2550066000b50f0007400300043ca01004101d80e820780c1c80d00030603822030483c1446011217604098000e030004011001d42281070070300754001b00303507000000ca903200c0c030580c071030044001403180c140030b00b00c09810316140004481c038100510740c03524070a521400310300c90380c402c0020302400018041928901e9001d501803145100380104a4280d03002405010290501d10b00001a010000700c110740c0711a910400d003d42c0c3c811306050140c04400005400341d0000010703138005185980a02540d0300c40d56010851040088003000003c0ca06200a251a01405078040078014136103501c1c5104104050306404810f445490510102d04500841543c0030648 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798227688 1250 798226438 798226441
    0x90c27010303030605010e2d06070212031b07050907120207050d1e0201050f060d021503040c03291909051e120703091509050d120e030a0b01140a050306 67
    0x183d050700400111035090303a814121207400c41c10421244501c41802203c00e440700d1054140d010b510702e2141001100810140c01c201481d00032480d032000b03d928040e00b540000500552041c0318060800b4010070480007015075070b081501245516002404170424080074080b40e03400c54031140c040341c06059001d01a90074211040c80050840c50580c0719011210307890803001d80a0600c14400c8904c24a044284568640c845030280002140f00103c00d90708001044080c41e02c4011890040d80143d00c0384103417141c041c0c65401d01c0c1907400c4028444940c8842428a00c20103142c42550194128007244a0321218a1000200e00010408420002e00500132a0048081ca5507001c001c8006d40c8a86010b0f241e0502c00d2401c00c2c890b510031464010041a1902018410203142c0000c0340300b070030340c1d60800007900b0303031a8000500a1000c441c0111500d400e54906504d19907030201c05020000d600b070b4000d0030003004075520096003100500858001c090018081161562052074010080c01c002e400d48009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798228938 1250 798227688 798227693
    0x204050d05010f0c0216030f0f0503030f06130b06091203210609061203071212060909111e120a12050a02071a031801060911041d090c270103 62
    0x6400b0f401004000f140ca000c090000050004c507807008040c0c2c4100c0325820150442da070341c00454144107002d94140d40304544070030000b003040006501882d42c400c02d00d5421720b030500070041d12602c980000c071421814650725041c41c0e01c031802507504402080b911080d070742c4c04004510745513000b0a00794000a511000d042c1800c80003a00080d405008182c8403011703566a25424002d400907100c0d086850740c0d100704140f8011804044448112904510303205500300c150b0301421099030801d0300f1003460142c4d1810100b0800848020f425400a400c0c2c030b84021380950411241903407522070045a004500c8030184905a40007800a415902c1c3e000e4400c000301007503200d0041c400d07000189600007520035100302242c41204200b46540826500144a165a075403d0004008421141a545003036403100e41c0030406410902030520b1007840c44800e29191441d04451540e9000d82080404c10302d002e442c140018103201041103070300480140c131602e150405518264844c5d802065071100c027550303240d002004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798230188 1250 798228938 798228941
    0x70b0c090f0a0605070c0b0a1407080408070b030610020c010801060f090e0106170a0506030a0f031808030a1b050316020a0905190e1605100210050a1401060504120b0a0204050d0501 79
    0x1510302548820440ba912240320982601c1034020760303c0404d43c40d049600d83e500381080140a01cae84904111400d00395aa20384501e0980c098000801204021040101da8100400244491003d1344000c15000c22190006024840103000c1c80040003110941c2c81c01c45805101d03410300500c4100c000c1c0c0071541e0b40d000003c01b40070804582c480c0400301d10020440540141c010280102c00083c05840e1240c0b140da01c03060380191000088040c0019407681c1104040310082040c0280f02c1035001d1903647c000e1201c001d000f05640020f9020f85500c4c6018200805e0000080c2e0352050642d6200040070701c918000a902040998480b1501070704140c200490140c43e00048403035169002010310042c0c01600c2d1468407120b160000030590b508049041205180c4406140c00032240c0e401980c090701004090380c0291002180c40031100d58449040e05110361103140300354010002458040c2c2030504146000d4900e440480303014001204080104107a400644c0c102d80050000038036904401c00d441c0b41590 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798231438 1250 798230188 798230197
    0x11e0c14030907050405060f090403020f0d02011116111e01030f060302130c110f06040b0f070206010b030903090a030b19051b07080903061812070b0c090f0a0605 71
    0x40092140552011040d800d0800c0e01d000c1c0c081c000c068640141090240401004020b002d960301c01403070307aa050169120203808a020368082e40c0582a07288080c0030291402c0310103001c030003c5a02d403000030a5442086820780c3c00b0903407003600e0b401d0903d0321400c14601803040aa44154018815450340e2052000659498880c69003a201404000400d1511400f22003003884003030f40000c40c03561a80c2060000e61701869004030b035400d0821801c004a40b403a450540d08100401c0c155102c401400103106031b44a459501416010b40003076079107040711000b52120810310400c0213908010021554500050040d2400381d480601440041980c904102c0e07646107007918580d80c20400c01c202d4502c01802402058443d4110340a00c1200c00f191600c1c07030342d195101d0b8a00391014a000e000d403181036642130241d03900900c9000000b102d0702c88000341c0c407400c1414644110035001020001d4500044000c118903911003808074070a40c45000d1a00450b5190540c1c40c072551784851803120200b000c681240160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798232688 1250 798231438 798231461
    0xc0c030807081009020703030608060705070209151c0f05030d090605060301050403021b06041d041406091c05130305010509010e0712060b060f0414010806030102190e03011e 76
    0x101065100c0410a41d2102c0041d119082503040104090044403880c0c0c000789402d605c240b600040d4141e0f584620740c1421401e44a000006078005a2081503141081600e50440b41c1561078103080c4220800046201b901c0c00386181c2c64161050342c13641448480401500d203280c10038150303aa103080072050b2070010400340703500315803241c94100441c0150405204543c400d55241e002402007040c07050350100b0100381d03c1e0080358455000c10004c1400b07082d02481002c3c0a0440000301c08a007054945860050301d00320980c4155030141003049904080090b802d505505118442c181d140d01031201200c40d0710801e425020140140c02c0000200881507005602c0788601c6002001140c44d03442c440c07030300d03101140320b0f8101000800c1d28600c042851503101d01d02c13680c0001c000c580340c10f007190b5908031150040d034021202c7d091304040c802d5840d604020441d0344520128000c624081100e4281002c8441c0c0c201c4d51400c001040c407611420ba142540040024012a0300c40e00505443c0d088041c0a0803014264 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798233938 1250 798232688 798232697
    0x8030709060e0904080d18080a0f0503251403040c06020c0111150a0b0a03030503060a06050319090602090414160206040b15040b1215061002031c0209040c0c03 70
    0x14409204607400a41c21800030b25002e01c82d180c0743c50744845d0750480e000419805645090782010807444110070300c210342c840c41115403900303010760016100c140941c0382e640910008000304480051140d020710720109003180703d845003074008070045400480c0c46190108901c0004144024070503011120380c101da906500712548000c1103001114144500398606444c0d90101c03418403043e48842c0e81a40e4014041d407400030b0150320f0500004c0005055034416004981d000045c4406424003404040c0a004142000c5156040c501c04c0807062803d00702000b01c1c207980e14203200042007082e03012100c0ca0034004005000364182d000ea05526180305850030f050b41e4480c0c003680d05031a8004a0054403481e000702c1807e0017583c034085045840c4452b01c0d04d10758021359440e40b41d5810764540d0805214821001c00511a12540320002c40c101700700508005e2003060f404104e820f505031f00104071380349100c41c0744040c2e240040c803580000c0640103098a0f180c0c018204449403a14030b500040c00541b660007580e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798235188 1250 798233938 798233957
    0x3070309140118030e030118150506150702013218030114180316080319090203071802070b0c09090f06030d111f0e011103010f0302041116080307 64
    0x1400c030b08a41410360703081c2c508800702e85900e002c68025010409010300140022840382071200008060007040c2e00205c80001d082c6500c05a0990381c0d01ca020307401142039800401c3e13550103021461042c010410002d04100800410415230321545c1c805407054500707144100c02111018003580381540082407000a1900010f0303035a141441e05024070050000300c01c407c00c0c82c0340c4800c540704142c1d01c400c1c40003000f01d1204200d00c95030070080c40e034095403040c09070284030f8890420018880201e042815107511840c20040d203040035a070301180d248121018403810903080d070400360340c03400139018450029080c84208000c02603040f800e0710051002d958200d40410113643c0c1c681108840c48402e48920b900341e40322544d1500c015008080d50030710501d810b4200c90300d094140c02c5400300740200740b0428013800e80b10110580403803024084d011140c1840c0310003904540c18a02801004083d911000e8401e94a40c00e112450b802180c0c2252424079902c4a00780e042e401c1400d180343d5560050707898100180b1600c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798236438 1250 798235188 798235223
    0xe010b04140103170714030910080402131509110c01050606040f0e0a110a03140604021c1d0604062304081c0b0315042901150c0803070309 61
    0x32603551092280481e20003a42d007561681c41c8035807500140b00e60200c40030404400490030800c0d000180301080001165100890b10511401d4410f9500c0001806150802c0c080169a400c40102d10307034444000000b519002100d003141e0079103180d4002400c0304d15020488060f0114a802010b21040e60402440741d600e603a01440068821403180342c940c003480c0181840304003851042240c03c800254004a400344100300001a00ea03c00801b45c00031903034035480d0200d248246c03442030750320200440341141040380140600d0220041b07030350200407082c1d0b61081d20f444d40d103003400120b46420660003104e00529251404500030203070320b1417400c41d071106000d403d5501250540c05a12441c1e011070100d04144c43c0000910400007a0350300541407039120125100725440812404881300402c00f8082490700b4a030030510f0300104816104076421792114180c40000c410092601c0c1140d1101103035031414903042400b21034000a0b0a4020f081c124008140006564560810302c84180148814a040fa0089 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798237688 1250 798236438 798236441
    0xe010e010e01030c1202132a0e010905300f060109060b0d020714010e01020405130501060f1128051b01020d030f0e0303040f0b010806070219240e010b04 67
    0xf440300602001115409112501c920041082124405048801207440351444001a680c00301c2d030118608122004040e14036080e240007000004141c2420082c07081c3c501c00017403558505003e100c0c003404e043c01a80120b101708048480ea281500c2c0d03508141040000426900c4107121400e49180b8400d840002c50761155a12440044440414016103003075039048002000e5000b24009484031005070f09000306400082c001c8400000040e000141e58904203000c219400d0509030405081619050051000b40c0d00010400311500c00c5090001b030160b51040560314180038282d10b044c1201180040c0d130300c100200f4119800181c03161058581c101ca03544a080d140140d8082d94900680c84541800040c0b07000b03034407020075084018004542c2140c8041c04502c0c50b40140d80440b0720001d0300c042041840001d800c15409040341001801e201d003001c110003560303224201100e0301d12040042050301080380486200c03502c0c002102800030b0041c44124003000030850203a00a09950070549240d0003860a07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798238938 1250 798237688 798237691
    0x708040312051314011206060203030916181d0114100b2d040305010501030803040308060a0f0b030c04090c02060402210a080c030f0f03091005150d02190e010e010e 72
    0x240003c40781003a240c02e00035642d01924001030f0b170621404004d40d0042e207415000e21005055035030003d503500d08014000030301e0002c40c0096901d20050019040c0801030301e030090039820807200140130411111501001700c03424912591900e141d0301c0c00e0107070051900005c4500384500a0303000042e40c000d070750324981600380c031820107450760145010215540b6190b10304c2140400c07461101d000c038146905c80c0d03502402c4035000e81040c1e40c9120040704000030154481c0e001c0c0e40c88101622240040c0d8581303c10700440c040c2d5400b03a05101200400055086401d074000ea500030000f114007407100d4048a44045d48640e4250307010b030700600701d8500380082051611030b1024008046c5005010340205d40c2c44030b07031003500280c0d1212081d000c100455030441075100d029144901c0602400d81d600e00303100038060729041d81054540b02c10b50510301040144801d210311201c10000c1602c1761b94070f5901c5403001403403200d200b0040901e00c00e07100303501040c01410440c00d5070603510b11000688141c0d0b00c403403071b18035030100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798240188 1250 798238938 798238957
    0x6040e1e0a0c1e090b12090609070b120402010e0907030219110c0609030304030506010f06022107110a03080a030f0b0d0203060711070b0a030e0c0405060a091a0402070804031205 78
    0x551186440e40764070300d00d542800f526014905180311684640802c9001da01c480114440d041e54a014040d1980d42403000c550030001d080000c21500e4a0050040e07514050034a0888200407802c2c0040e082d07902402c081c81d04000300600303a0f0864609014040e00030f4001040040b40b103000740401c20016402100c030322186d20358500050840d2000942001041d40c04400c032960140030a202c000000341c02005100d02920000c0e0010b41c0180c10114028a0a510090401c0e8550741d5010004055103181c2c04807600942c002c00c83c2501041d290b1302241d0fa4001f030340e00080c001c1e60000344501344554103502442340c140b441d0310f081c0a41807003907040100075480e42e80301035416002440402e5245004090728201404540d0603540300ca0780c3e41c00f40c048160801c1c200403001c86d032584074120105805100103109107034215010041400c017440070548024441c0540084ca0b41d41e014640e0500c2c000020b2170105603002001596a03010a10b041001c9822520007104c042c2815900340650900410903100a02c0c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798241438 1250 798240188 798240197
    0x5150109051e0102030c010e010b09161d0f0a03050c01170c04120f0501110a09090e060417070f0f1205040e07050d0603050f06071803050a1106040e1e0a0c 68
    0x2000c80b00207402016401d882c50640c801040f40000c421028021400198104000042e60750180c10070300417011170007131584625145200304d1201c0550441000c90441090408031110035a1520108804426006520358007444400e000000c00ca40000c03007090401007aa141e200310400e050b00380782c25207000c0d110140191402d05c810300004403920b00c8070169600841d00b18152500a07143c0c1c1c0e0031205036850f4205040000121311641c3c0b50080c058400400365400c04004403602a02e11079101d05028000801c04041580230101107102c0720709859801382c1003c0005900c1000d46451100030196500032685072002c82940a0071034022030071707102201d007070101035452591100800c0703d0951003010a4a100b42e074031640407001c900c0402c000b68489060b0b0000305400e06046c00041d1211213894092410304400c08001e00000e4801b080400c00c10b5072010544000010450001e070740ca01442d00f00100103a450000c201e005219403c4640c1040d03000c086903441c644a2110110544516104203800315 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798242688 1250 798241438 798241459
    0x83a090302030d020d020405100806041506021902031c1101110304030507030305130c06030c03060509331012050901020708040b070c05040e0d11030703080412030905030d0515010905 80
    0x4090303600108002600030384011f2400c2d84460009480340c50300401540003c00900400640d410240300b0301e061f0308002c8103060305043c03800c00b0003542e8280012080030031061219501d011503e041100e1881ea50440e00e107601610001400185003560219480102d9801c00f00405004c0c0701e0101164052278050361014503080c001d4a0079030140030085c0c0750103112240c40c10443e01040301c4d0348100f00980b0082c1e401158140145000800765661504045d202d84070340c2c818417500da68403004c5100400c00d40c98004103840001d0710256030500408841917000b0031051200072103641c0c00030f001403e100103001c04026644803110a10300706e006d9503000a0989030100424001c841d0700700090408584201030080c60f454031440440c2c20359520101c80c1190ba0b21140d5a241039507003040500c080e4811810080d03051501d2614000c1a101c8090700203802e699400d880740100b0b41c4641c000f054a1038001040300d507a0990f8465480c002c140488503c080c42c00351003244007196208400c404100c500060440310071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798243938 1250 798242688 798242707
    0x2040803032409100e091209040b060403021c0302120405090711010b040f1a030c030604020108060a030f120306050906010c0b09010605360c040e04083a09030203 71
    0x600200c0d510025a0380c0d8030310080701c210f0351890700152007010b0f01c00c3c1141c1003030715000820154003805001d06c00150005414041c60500d803000385c0300620b00486011900554103c085032681c07186c0d40000e5007001c000044000302a403074080780241103200382d00b19a940403008540303203501c3c05607010300f6901101c0000402c505030700c260000020481500000608414181c1c001801c84142e0100940020340f5480305e61402e80203075814140c400c1043e005010249804400280c07039800060009062001e88404142c05840701c0c1603842c055903228a942c40045441d080c59045110b0329a80e035400281440d4002c00c0070b0800d041034900a01c030607181c0e043c1c00346203907403006c0420200501045a5640e105000106a520700444094044c002c03400c1140c400c6e5074900030401c21107007408200000c02001c083c041c1c3c88600008803402c641c0042c1c8500180e440e0740c07a240b07015200c0c02c00703840001880c152241c03403c0250300c1c0000b0201850388055441c1c2000c007050310b03c1030318402c07800580940c10038801b1815 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798245188 1250 798243938 798243961
    0x10f090b0922050402010207060201090807080d02090603090c041506020c010c05010b0a0b0913150b070c1203051206010216031127010603060e0613020d110313030207090204080303 79
    0x2400100030b0009446801c0030a1081002600031251881662210140420f40d42c0501c1150084d001c6031009114030011512050603620660b0f000034074180c2c00084903000350310f1a50613151142001001a552420312980a5a0f1000c250781319900c00e0385410500c41107584071215103004c41d10150054101c500380000152480c405c86e1000b40c0b0f040d5202c035000c241c585d940400d0303500075108082d11983c480803600c052014400c040a00400584d244c0100d81415038490302e164421600c0146000342e4502e000c1c9400c000042c601d03400f010403414250080810140c00401034243c0c110411181005551407000480c1d88480c2c440c00b14400c001c0d403d03000d00c00700f40411011600c07030402402c8004002c24884000103840b0f405681f81940c0c003608001440019810b028010040c0038400041e50700b81012000991000d001150404129034000748400b080c1119400041e0000030500c841c58491030200700b032010164000d44202d0040c01004004900b400030342c0300399000d8440c1900114219500e6403410700c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798246438 1250 798245188 798245197
    0x305040201120510030314030105011b03091d01033f0e12013c09110406260f03030a0b0604080601030507090b030a0209070806130603050f0c010f090b 66
    0x3810440c2c112001900b040460268601481c0c2801c07640400e2851070500a0018002000103140b440080004214070f0b0703400b13070502d000c04601d1400c483d0700103110f1030140c0784100d040c1d1094416100340f44c140b002029076141014101d034003900d0f41e00d0491007800450b40c01d4071011800b000700c044844855034140d1240c611035800d150701e581440d0712441c150f0000515180e0310007000c1c4500c0ea441e400f00100329445403040c1d6926249804007c44800300041c2c1d0f10300510f01c24120300614650740d180c2501403007080c1880e90003501d4068801c110300c544483d802d810800c03c0c240340006010a000800402810002d100b40101440801960642c1c032101b81d410080e201c41c40109a01001c2440b012030080380c1840302d40e0080d071080c0001c0c100e1341d19003500b41064410305200c0c18425004a039407003001d6142c040b4015480406403404000381e40d14500000d08176008503003002c040324640030000c000c00400040c0c0c107a85040c5841110001030703450004480c201e10141080b80020051941001501c95040c00751 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798247688 1250 798246438 798246443
    0x7060318060e0606011b08030403050307170405160b0a1d06040e070c030906170a0c110d05040302090c070510020304060212160f2316050a0b010e09150601030504 71
    0x465042240d4030785009a80c02c9091201c060381243c400d101040da0001000c11140180442d0410107460940381c2c44250702000301b000c0d00340080000050540791241d01c5140920300e41d480700d0340c80c03400c1a080c110340e43e00000c2c08000309450781d0309020403592450011b13601e904900307a0340d02010700340994210f0307100c0c680d8104850b0410000d1001040900240c19820301c11041a6599103090000b070400421000c0c142d8031140c28040d80c0004e00280380c03141500180d1180210201144184a00a04603809507100c2000320803400b4510040c40b00d1079000000f841202c2c0200c1c1c036201c00e5200c000c18414070b0b01c00c03007a00600381d501c103040714202c0e0096a009140c0c454051080107080c0004c48280d2200784808540010b20441c90812490b0001d070030049907030003c0842d01d4036158410b202529000e108900800314101080003081103220490030078802010780341c0c88402c3e00c800c10340c0380c9481c415802c1c00f0301811107100c03c4400060035004001036030300031001c050540b51400d0b4441400540c002c25024009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798248938 1250 798247688 798247721
    0x20409020901031a010504020f09041805030a031406040606020a140c09040c03060f0b0922150b1c020105090f2709100e0a0b0c0403050114150301050405070603 70
    0x180980d6680c94214001d60268880c03141c881c4141100001c400f20513008036200d28814000003510080b890103480b0148000d80d4009240011348808c400c1e8143d26460081c414440010112030403a8589c1000700404420400b42d050364a0300b208004c20340d070081c0111001a8080d4507141e0100c2c52055800492040d401c0075502120b44000c00b059549604880a4031143d04d07461040040000720300ca02210710000d10000c11004810070005800030030007801760740d1407070090500040d10360810040740003a60f82c0072201c181c1c10007001e44800054590241e00c0303031091003050b034604217002560100404c0c1da91b05a580c030b8502141c600800030ba6054000c03403641c11140440d07040203085486280440d002071400c0b0080020f20784a40304c14640642d0003500d043c00c5042c08aa215409000140706982d59448a02d01e40560b4900d004c000090180b5440030340690b003403000c40140b0401c080c8406005105510310b81c07115152680c141402d035a0300707072801484e5a22a41d010480350b403082d0f10035018455103080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798250188 1250 798248938 798248951
    0x30706091223030a090e1e04020f01050d090f0203070602060709180612060608070605070203100203040302192a061b05160803030a0e060c0a05090d0b0403020a02011103030903070f0204 81
    0x41c07440c42c0d134100200550102d816103000340000ea882242c40307988002c114031103401046000e000041c0749040508024041c1210b403440680b643c0c02761068500100f10140200300c0500b00c1d041c4400c2001c00008103a010340200d0101082992020443c07034401d8255441e19510b040c5407600a40000c3d20495000c10301c599a210046460201c114024141a01a600204070305041c02001030030811903502800602900b04090f5005803804604858804458040183c50340d54605099080411440322544441c3d1840b02c81000c004007000080307001400d402500e60303110790385120911758000c94004d450110700c1032a003c00d00c1a0f060a0825045849007041d590100c40c500385010340b401c030301c0c2c001240b01d0b00301000700101840c00b4498014501705210007000c0a0800e40080b4086116541245040141c000b0301c1040607240c1d111a03200340c030361004041c215450b0904000f92280b403030070300403400524005212121100300209a80c09a0300c00d2002c0e500d031880703a03664410054512002207800039206c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798251438 1250 798250188 798250253
    0x12030b102a3f05030403030b030309010e15040911040f090c05030411031e070519051f0c050d0c0b0f042109030501140118020c0a140c0406060e0307060912 68
    0x8a101d44440b107503210140c9a007000e1034040d040d5400c2600f0a0b010754414081ca0341203130ba00240d144005d45094610010903200b80da24038280b44540d4029103903450411421120b0a07102d28001d104460100a08601c60380d12a103041041d2100d040d03c00c40005c0050003c03401040300d245100b4080080101180d038400d150681181d08214911015003a98112000400003810070200c40a4100002a02400880d040c4400100d062110040c0400260140c183c4441e04034010001403007565082801c943c1f410b0001d00d00281200822402110404c2c41301000c00e540c50801003170980100d91004080340a6403800548060a01403580c0c03000401483c440b002000ca00284201d02030601d0a48003004150304141c4041c0c000c0f20b50410101c843c9204011074041c11101049400c00c0561000b183c200c150007001041e8030b00103a03201c00c1ca80c01460403a000034842c2e0840b812003081d0b00b058065902082d503802c42a2044200e5100340755040d1803114220002849101c080038154003080c006071122035416 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798252688 1250 798251438 798251543
    0x923040c08150108040b0103080c03430f020402030703091e0b070918020901030b0402030a0605040b0406030c0e220b0108070e060102030712030b102a 66
    0xd1001001081c041400d00c01d90b240c2e001c8519107003403001e081c01c81150500c2c2e80c1d240400441480b0103002d5602c081622903a2010603c00c5501844120132480b02541092507030807201c842c90f8110090148500e0100c00000e0784520007100895006068040343e05240d03000c0c040030703500082c418400c240d59904031000081c000390000c0402280405100409000d5103841d0f003941c1005072442050041f800802c00c078079020b4071404900c501c2c2850f009a11050b080340107078041e001d00032a1039840b4ac00801000b4454045500510403103808031000d020341c02e06001403104030b98071400003400d000383d010401d10500c201c1c9402c03e13403c820040074080300e540c6410885148070700c040c4011241c7c03550020042001000401c00c0c1d0010b480380016001c21030801c040040d54920134132400401c641c00c0420700600070340c047d611040c0c0072400980810200000404010a4003014485806040030203030a1072205601c50300115400d00d40c029045603041c8016128a80a01c051110a00501000740388a0883c40d461 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798253938 1250 798252688 798252701
    0x50d170f0c010b1008090a030e06120f090d0f02280b040b04050105060303040f1701150b0705010e0304030b010b07081303032a0809040e0c1005070201091203092304 72
    0x78036000103014082841081444000c1004840c1000075000a2004e03000300441d80c062105e9141c1000103080510001142c2030340541d01e80c4007602103072202000000c0d0b5144688038410f4030150103451256404d400c0a5880100400604006034011040084100030b403c07844603a9903607440c0b0280e01d6501680d501c055000d02194101c0d10014a81d091104000007401100d03048203049000d14103242c10080307046502d40a40c80b44400c0200c60290080d5072100c01e610081040340843c0c08101c60645036801691180c2c0904404c58042d86015500c0c8900718001c4161000e60741e201c4010a260303440d050300c01405420400050f1130180c0204812604502c1c207000c1c400085201e03894284000020406018040900c03600031191a40c00d12589000034094a0450742030740030840c1c0000d100c80c9089072607460802c03080c0350580c00c00c1c5403004017140030380c0080190085501c00d0f030b02d04c2d685989555010341050b4117903e000340450090740c0b0901c5034503400c01c1c0c007002254644010b040c51101c880d000900740c589 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798255188 1250 798253938 798253957
    0xe0d050901020d0813150b19051305090709020c0f010c020706080a090f0803221b0618060c03050723010e0c0102150411030a0501020d06090501050d170f 67
    0x2038124941d40c042c442e049000069003000c0020b4505080c0c20000c00d04001002801140101c0c40d064818940354071800c102c034400b519984c604445c10346410b00d0060303079000b0244904101701103079002c46218058580b081322514082c00400740342c00c035140042e4010041c041c00da801200c18511a0724401d100d00a064116079004259040c40c258000d820b40c40090600041e190404048030081003c41070800503444c0d1050055580b40e0b1440b021404d40e5020138140c0c5003901c2a6803c0405210700c0d020705058550f0341c0c441c0c0070310303072580c400c0241c0303540d02c5c050035052101203200340c00c102e81405244002c0c0c00b10f002e410b00a10300350140c0d454907442014003120040a108100c1a1078100b00240315849503400c41100404403081c7e4180042d595054046e10b0008106d40b04001a0030007605084100b40000094202c94108443e464502d003c0e4100210307040300189407110004085c140c501500e03040b40c00240c1105601c1695450310003200b40e1101d03d1407140b03c010007124103812000e5004005040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798256438 1250 798255188 798255197
    0x121c050d0b040608030306091510112407080402040609050f07020c0307060e120f03040e180601050604030303022a0a02040b090103230715030f0513081c0e0d 69
    0x2484050103000c503021011914001ea14140c000e00400320004100d039044101114071096a13542d2610712659501031900c000d41002944c040c10545580010b60168080900c00989003142580d010784615034801d4246090802c1b0406c0101e40098020312507940c00c01c2c0090404103140b034a41700620300742c0310152400162520078100b0441180d030f040c0b2100103c100c0480240c080325160071802403880440e407c2c1548100c41400d510990550100102e2010080c0b10703040da40c84550350036015aa00740e0840761080c41c440e0070001c5d442d0324007010801c0c5041c0c1c0d100a000a0409055403001c0700290880300c001002105807160600c0320002415003e46031813020b0004180b0f0443d148180802c1e903801d003400d107004a01000050000403103804203810324500701a0500400c2503400704092a04d08c69500071442075403880d06007481243d168200e5001c00e014540280403a440345c500611030f01d141c111002c1d0000c3e0040c001303482c8110304400d07581611412801c003c1080020500b03000e0804c03340115000204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798257688 1250 798256438 798256447
    0xc080f13031b050331080309010315180903110d0f030216050a051011190c0317040c140108090c0603150603010b0a030c05040807210b0921090f121c05 66
    0x882803085c070101c070f02441145c45510304025160f0707900030b0003940750505845000701c0110818060160700201481840d2751124130f46060340034010104100700741d0000c0c500340031184100704001045090141140d440090701d80801b0000c400a4100d6620710000c0c480c42c2401401003a81040102c0849000384064102d9801c3d2800300400c5400c80c42c500d40e030600060040481c0120702600c08850320071903082c0010724040350320342180c15aa445001480c01c4070000e0030304c000c0c405001e0701c000c01d036035041c2521005000c920b8015100480100c41e4262543c1c0120408240782c100040615017110341e0a4041020801240000b605034200f42c124115440021900d01d012661500540f4104030042c100145041e040c05000c548130b04c00c5009800d540d0100e200120450502112003412507071700911454901d0912410180e00c078034220100c042c0f80c4000d881222030f5905010225001c210000701205403450384001030024001c0320560518590103948000c12100421044100c0b00681550b500d0790f46 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798258938 1250 798257688 798257737
    0xc0803041202060a0e190204090507150207060e0603040609080c100b030705040b150309120711102109080702040e1e0723031608010c080f13031b0503 66
    0xc3c00d600418000344203007440a1805008400b00e414140881c180c003c2c044402c409002260140511100003001c0b481110300020705500700641801e818401c7d503090b030756590b07612603080b5070740d5080854281c1c1c007007010000710780040c045500a43c0303c1440b17696641d00307010381d1465032420000da00b80c65041d078a407110542c80c410300d8148040c0d0041c0c10211002c0281d02403280108060040b0801c080f07500d48400030110749522401c0280700c461101c0206010f80d038449500c1c207100b0402510441d030340070385072820311503549500030450031001c40140743c00c41c5078801e0340ea180d01c00604001881a9040003007000040c015843d20301458038585c0e04000180b141c0103141d113059401084030080c00740d45400020041c4205107048003050300f1748183c0080a00b2081141000a0425413a04000d094000c940741d00021031040c10340021143d03c0c0240c440190f07a9a400b280e010440b00d040701c5004028044400c50000a40a0901e0070f00303181c4845020340c205005941c4071032640d805118404104400405c24000c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798260188 1250 798258938 798258943
    0x7060902060f0909061c0b04030509040c0906020618030a0c0f0506040602041502010501050f041a0904120e01020a050a0305031f0306060e06010c050601050111190b09240411010c0803041202 83
    0x5c0009003943c50082c0a2502069264200b0703103410010547c07200f10300070078289840b500580c0d6013414020420080d10301d81072000703840481d1078882d00d005801a480004c010350544104030b2509a00341010714580500741e03000311032003600c40008495103082d072111440401c0e01000114411031049000607034480c180910700030422140080c0c24210780c1800c0c0148482e0300d5112022102c0d640645010545031203040000001d1012440c00d1504014000f040205010609800e8880c03000030f9207484000b0a03c0c0030049841e03114100c0c01030301c640d0100242e1800a44660011a40600c400c10598100c001c020401181c5003900d42c81078408a4035101e083c03001d091104c1c0d03140e070031404c01d0800f103000d07a55030398829880d140d051280a06000d00c101001c04030100500802e54400301c128000022015039207401e25420070242c9075000c1d640f1601044c2e0100024064803080c0c0000321084001d4155034954803e17410300c0c01903001c40e04015011a40800044040000d14000c91241060740544a281e290007403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798261438 1250 798260188 798260191
    0x20708010f0e2a0415031e02090615040b03090102040b04060c2d0f0204020405060c07080c01050c0703060f0b330913231003050706170c07060902060f0909 68
    0x80c001a40c29180103c140c1110300141e04801d0548000c00d10b0403092000210380440b65001030038156450114407080d0002c402c0398035115100b2185103465849000c140f01c0d841070000c03000c580e00d80e8208010b2204403280f0000d198001c0c00b2000252501307890b00ca210f541e5170803d51102000c500304050000c1008080456981000d14400349409049994440d0030140c02d8040d1000e4004d040052002041d91600e40440b80982005010241d035003100d840441d90b103080d43c1c81030000c1d0303018280c400c134084e601c12401c41c1d1a841c980401001400d0543d220a4028503404102806140d9a41c1038261661110507070344640806010041442c4036041d001514100c0e07041c1c004500c801c078100000c2e85a036564032500c0401e110f0a5500051200c01944044402030402c4a144060007901082001c404860398289050760712030b00607140400d5039408191141c3c00c0c030741c2e281c42001c0604000140241c4860028007400360081a001c0380c05603154003c03408541c0210b111118080707002074032001c1404e1842c2290b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798262688 1250 798261438 798261463
    0x20319081914040302040b01110706050c1509060408030915010b070b090703022412010b07020a090c050901030e030904051918050d0c08120c0304021302030f07050a020708010f0e 78
    0x34000314121030032540c0b151107503000082c4030b41d07035480c1400c80607403089114101903511441110a4203885da0350140043d0001c00d210311702c40c41a0300d0344642800100700351600480d1100c00a01c11525240d80310201c0b80c00040c00400c003445250a05003032580580b001134000c0000d180c079169940514100aa000c42c0010152041e0780d01500f02000140c4880c000c8c64001c80701d040c0d0303c10180540c0f0546940c20b100322600c12400c41150400030138102440d400a1049a10890341c3d840c040356a18461130584507400d1483c0d01040d024400aa40d55001e50801c070b20000c0c0182c00d581c507040c405400a03049400a4a071104658400342c0311602105861107000401b9a0507210600084081e41c3d49650711a0000ca0190030059429600002c016030402035960300c0a078500413801c03a00d0180c1020800303402c00c90781a07225241105030300e00e406685100f12800340380200d2400d00d0b40d0352900c03c11341d0643d0080e9070f0141144540040081c08000c20320540805056a98000c13070f00840b40c103180d034900503a0b82d040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798263938 1250 798262688 798262697
    0x27030d02031e01062d0930060209040b0a0326040b0705010f0e070b030c091f080403030c08130201032403030315050103062402070e0403020604020108180a0b040203190819 75
    0x7104100c50b0860144001ca501482c804202281b01410308004901c00501a00ca0949507901060408c806071b00600420030064030104814000c900c01c0041d105810311026104203130700001c600d1021101c1604816000c0d00300e489038a0281d80780c18001c020b501210042d601659103034086000c034190750054070350100b00ba2000340055810601005818403002d40440005500000c80542c180c844424541411100320b0b420040c0703204460002d89460700c00c030380c201d00007403405841001c44c038003510304240245007001c0805811105a80150010400c82c4403070b80520310056031010b0b1440311001840046c500c00d64011506860209030300c0070828607600100d061600f86103040c450f406240c0a416940c01c80e0320a00110440d08001c02d90402074986c00160030021468200028160005642e0307000314402e0341c6030149903545000c215040c0080010759442a04003203222000b0400c0c544450b60402c0c00101030700c0c9500441c030040c450b1340c0351140049035510f40c086180c460b012440d25003620288480c1c01c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798265188 1250 798263938 798264017
    0xe03070c091505030c01440f060d110d0f0206180901050f1c03050910052221140d0207150509030715170f27030d02031e0106 55
    0xe004c0d83ea00314112101c0449040e0401c401a0410381c0700710400c03989022200c0c411f468000c100c1c040002c211016400300c001440401e03003900f0042c03c1c222030660020281500b107140c2e107041000c00b0360201400e81d00000c0c409141c50240c1c1d104401040601384c519002c014108144040c0310303d2800503070206220703c3c0c0d02f1803c40f0503900d449500c56207250601c66003601250007482c0c1500e01c0d000e035401c425001000c10b40040c40003900030005281004140e2080411540f84030200f00036240345008040c4044500c04a020050640340c80c0000f800e84162007e04000303005084c0c1500c0c0c801440404401a03004400801c0100d42000b070405100d503d51800d14909010304011a50301e10051181070115014400303480d0405d4442c0407206489561210061520300348103046441055095402403050903001018003034904402101040f81c043c080d001d1800c041c00782204070000c1d04001c06610714980300ca644480e103480c200741110302038100c1f0303290004a01031074200c0012140c01a400000c040503200f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798266438 1250 798265188 798265213
    0x28020c010e0a0b0a0903050a08030103021f090b0a020c030f0d080f040809210312090d0c030806100e03150106090b030601051b0717060a050a140a0e03070c09150503 72
    0x30385401d5a00601e0070f29030303403034842c5402c5409803983c0c2c0c0b015110780543c5a03104104140c3c0401181224000c440002680f4201c3c91541170500f84481450701180c1070300d600700400018072010b044400c0301c90040d100c0c9840024007090401032150101e0700310350401c0341084070b802c0d041801c0a41120740d03040404420f2520b0740d51030040d8400d048626124172506d1141e62404040007200d0803a0034110700569440d56540d82c11656100002e4030071103901c0c0103050305241c00c548540603464142d83c040c0d81d80605511200c05000000c050021000f00700420b00c0c0c04040140c030f00300811a0030303401042c0760740711540c90590000c2843d0010340200d0300744c080c10402d12400760b034004141c0d01021168900c3d01c171b107150703106007040c98104c02d41d01c40c0c0b91668150b141c3c3d440038900425850b2080329541020300403903a401e81a2000c0302d00f080741c1d200c12031a80e5804075030251a5980400140300846045a1903c030940d1280b45140e030580d40240c044640701d642c4402c4024561603407000901c025401040030000700c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798267688 1250 798266438 798266449
    0x3030903060f0209030a030503090c12100b100c03081815011a070c05060d0b1201020c102307020f160617060303030105010507050a1e02090106021b060c0328020c010e 73
    0x4080103030400001202040420b4010310105408000040895410f90cc87c00021902c030340708441c00d240110301c0e2800384607090401c0d441124186030f039966585d4041d019640c0c182c81000e0041c2141c4100803038400b54a81c901c0e001c12a04060200c25402940c07190b140c245d600a502c140e100c1100d0180320244510310024200d240d0503c2601c404540590b2904a038180c03a800401445103c0399010b00745500f07181c00c401c41903008281283c3c0841c05c0e180c400e52418918002c0c0e80c00d1600403807000c00c0100d4920047c0c1c69500407036030440094819a4100e514141c500d914003002511180901c1481ca5820010700790010340001c042c09848820922510703202000079140d00051042c41e041c8000050703400300308002440100c45069000c4c02860110741d031418001c1c60103003103040407405180e19000218005000042070400d0124062200c0c034001810b0b001d0001582110030200184c0c80300f445070034102c1c020700c90340103854103000310000141d040241009141c10103150420381444421580c00049880e03a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798268938 1250 798267688 798267703
    0x204120f26120a0e010603081c0506090103060b01110106060810060206040b1b09090a06030204060803160201030c0e041a1318080f160c050901090c0e09180703030903060f020903 78
    0x2021101210b039030743c144100018142c034018503a900e519046010080004010240102440810049080020300586241215020754035903500180d0780004000299140e006440510018940450243c00c5020401d0a46140e9006100400c03000b408200403908500c503c00c00502892000b000142410380301ca4141140107461940781c1030400446030182c03007520b400ca403071500001c6c05904661800102034001080b09000480c810b80c01d00d900040c0c4a200001a10380d1401c2d10540c0c119002c10a034015002400f5401415061000d00a05c1c01720720740d10f5215084241050419000e0146c19000820800b6948440390328042803402618403031074032a801c0c0407410303540e0243c0c4a580d280103400800145006502086107032811011a2000b00114040000100c403c00c0d0384084082c1d8866200c00706907240315408500040040718500e0035894070401040c0c2009110413982054114400c030f00b820a103458100307030302203500b00308100200189849100950444060b0031130800c00920300180c0c03240d01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798270188 1250 798268938 798268957
    0x10021603141c0204080c0a0308040603021e070f060f270206070c06050a030c0512071d0901080a030207050f0303030606070809031f0c0e0a050409060204120f26 70
    0x100000d0481c0805807150842e004001e104400a816000c1d100810010394450b001c2c551003030080048141c06420480b08800642c0ea1003400a42413604200044009401000d10711354004c1c905c440122462980c000100002c43c000c0b184089002079505184040ea0340c103042c080a5146014058100c41c071a501151184a00c820b441c0855074505000007407142c040c00d4400f41003c12042c2c0d000035044d070020000c00c007800658900f80500b049030b14040c1c1e007074010421084040c0340c820700020700c00c070320401c203250740300201c1e420362f181c0211600701084076220f090700204169444001040b060680402c9000c0040200b10b600707280755000480403e03100e000c0a07003d2070103028081040010000d80b10182e0f110400054100d880e8038400c05104042c0031100c0300c40092440c0341080343d1003910f10503041c442020002400e0700040d40d181800344002000703900b00030384200f039080c0000f1694041c80440d030518640607000d642054403589c00c0a41d42000c0442c449115085442c1c0d4141e130b0f0008082c03c1e590b902c02c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798271438 1250 798270188 798270197
    0xb0906060405150904021b0f06040c09050711010c0e0f0604120b07170c0301051e01140a05070606030b040c170a0b131b080f03091e04290310021603 65
    0x40f02110010b05800790115440d4003038008140d46004c881180400350040034030a08032424440c0c000c1e55070362101c10030307140901209001c0c1c90a1107690b8080e0081a0072022628210030003501c050301c0982119641410a0006000c3c9a228941890020280c885d030700412183c0702d251928017014900e15012401c0010001e241d140f000030785c00c60085002800307020f001d00001c015460030400c0701c010341e4024000c0510428403880d80240010040e00030b00c0400c4030603140c100d822010903402000d00e401000c0c1d042c04201e0100a0744001072680d0040000662192032030700107605162800c4407400407243c0110703400307100110341c0da2441d04001464840301c580100c0c030b0075002e1321404802c00c50800040b001820310303040d00300525410022081c2c503004640006082c3c408130300d540c2441c40e8482c882c080c512540318448040d02c00541c14680c0300e043d00e40310000c1c0009501c0101442d13501500341065526040d044254080e8503081c201030044079041355841c1001c51404024041d5001e00340c00c1c0007000350800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798272688 1250 798271438 798271459
    0xf0306040507050702090709031505011d1b0f04050f0319030e03010603060c020d110105090a0b0a060504110d0c02060c030c0309010b0316050301150501020706050d090c03030e040b0906060405 84
    0x29800fa0b0210f0344142d070003620743c10b0149440400588568001d110440c0c400103010001003030301c4024030030315042e0307004502c1b01c400d07414481028010701d01d005849203904410a40d03100c50507100c3ca0700240141441b0302c100740e465501d400104040e04008204c41402030b0840c03442d1840d5a141c022862007a154141040c8031400360640220703005000301d8000519403881c00030550740e00340d000038919034122030a40c0c4402c405810b6210301070030b030b65003a21146a07a9002c90301e6080000e00e04036089078460f03050403000482c281e1750070010b0251030001001d4900c00c01c0010301842c101031303103018050101000e40020051400e01129091140c840140034039481c603400b0011510a180070b4110400c8550005c00b1141140500500e00303080303064912495102c0e619100000c103003401000c007118100e840503005032100514004040e10664800401c1707051543d0780f01c680c1c00014000c0e20782c030f00155000f42d86a0703a103145c1300824401202c40390713400355208032244020010300b682c030361088a081d9501690f040300c2c81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798273938 1250 798272688 798272701
    0xe060c0a140c03210105120c01050a0f0c06151d0906060402070f0501150f060c02060a05090102070e01030302060a05010905161206030204050c0a09051203091c02060a03061a0f03060405 81
    0xc500405101c40c1600c44e80030b07500202001d501038403d058441c22101e1540c1240070700e1a09503142c401c14142d9010520600600000e64013841c46244a042c0600b04000440080d51303580c0b00300c80401407140702c038008c032507014070000503140595600c0e214a2000c0384104d040c01400942e4034030008042600c2a0b8000881c84108180b20904038090359002009110703a00c504005a01d0410303160141c1d406e2603000e4030000400b940314030414051035401034041460094507040458113548001c01450640c4a40303900000d01503010305e001c900a5020380d014002c0c43c100424801300ba10410392000d580340c1d041005105500e540103071900e07600c0d0242d0904c1c6503680391803001240034104c180e0010790701600c1e000030400c01240100080441462550311203d005440750104006001c6030178031203130650b10074070000b001400c146591390404041c40d200c0c441050a60380c0040e0b02c0d076100c01070040009854107400c109694640081c0c1c5040600f159403a400c007000b00d40c800c0101d0000411051080d40c958000c03407003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798275188 1250 798273938 798273943
    0x9141b0d090506070f020c060f0403060506040908030c0316030b300708030408070509041a07020c061b0f0d120b06160c0f0b120705030601020c0901090e060c0a140c 72
    0x1c086034031005807081498504005032104e0840210840035024440b03100a41c1d10301034044514100178100c250782081e0450b00c0707140c010140180320036002662442c1c00d0000ca40004041c43c4101005c01d4565076901e045048080d054140c0030782102454181110342c0b1040d0344a80d0b01c40c01100004c0f90351130041c115401100c11500320000c114885028146010404c0c04010008005856000b011030b1919581c1d0310910003011812100904003d030440b02143e400c9203440c3c00d0341c0e04040940b04507001c1c0025100014600c1d07001d28449030351100320b00c42440b0b2100042c00411422031034003014204103180500054201500f603800410703503d41c1c2e0002d030300c000d03503410381a21a055848291075107080304034501b902c3c0f00522030160208007058440c00041e00f00780b0303c00703d03003218010601926098a4107003041d20680c001800302810750103180314240702c0703442d010758150090100d000081001080520380c0340c07c080c0013604001c05050700300080500c8a42180c69030000c0f401c00e05415580d000e06007031450 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798276438 1250 798275188 798275201
    0xb04061704061413030215010b0912010902100e030d0c03020c0d0303060b030f010f0e04030219020d14030d06080c1813060c02060105010e0301090c060e040e030c0709141b0d 76
    0x3c0f1a805040a01c604562002102e14405129800316000b56800540f01e2015420901c039410b0003850030020420079041032000803401e00d2564001042c40106a400914ac009940310840005000480017440f54030301001112180702c220f0a0401080c10180c5000f034813040750030300b0a03006180e610690340400d8800c2d40024002c02c61152107c0d22400e020f002c801d42c6000c20320418a25208451000c01c0c0a4030616115014507072540041004640d40406903800500074201a688040c0102808020884d2403011003500c80401026594801d0601250000c40340030f5003086001742d002c48040d20b055280c051013140195030000000e4015500c4a112702c410b80c81102e4010059070a083c20074503d03540000e41541610401d0701c40620204140d01458202c810204015024406013601000301501848003040301901c05400460129880d00c8854550ba01c400711482c070951040500308168070540c4100c810114015040211500b841c01c5044081c20903c040c1300e03001c500010340070103829500e61009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798277688 1250 798276438 798276461
    0x40b06060f0d050906090d0212120a0b0603091608160e060402190503060a120f0303050601030615170606070210030203060f040603060c080108070b1813051603060b0406170406 77
    0x900072031070013a005030340342d0300d0540c0c8050603072240d401468480c80c00401c1c860070b003501410005040c4958001040800740e1b02900c0c8003661540c1d07a003105685c0c3c580c040154401d400400081c0800502d840004200007150703800b00845800a194090320049060303688002c4407950000d5003450340315000014002e05c50a2216840c140c02d80e604013400d503400101640c0311310300c100c44aa41103652244280540e14103804000c0180181440c0d110019000e43d2180750413410604d40001d80c69240c0038200141800c66404101246800000c2c02424100019096203d030041e1022818812141d0228a4900301100344105042d000304c0000e205440d508001460742c4401271040c0095952404d05c440148500c91658000031100000070407071003000284401114800d03081285840342c061100885000e1030040c40398070041c200701c0052802528082c450142681940ea4504203054940160441d202136100340c9080b60148000c1003010f03000b001c0d086031810300002409980c1d40e41d10b0010002d10071602c80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798278938 1250 798277688 798277691
    0x1a090402460e01050f0a030923061602070e0705071a0915090715020c04020a092c01090203130f150b03070f061404150305041a040b06060f0d 62
    0x500000488040c850005100314241c15164008a040454208011101082c0440c000b0005c81083c010610000d00c0e40c0302c2c3c549400948003061740c1e08c038071a40310101c081c0c8510703120307429070410080c10501c8407903000504c10101ca1102c0d01035280280d2030f502c00d0310070b01d07034407499840020301818041d0040313502541e8000d4083d10007a032803c0844840000c252501201403291851300110361000a061501601d0b00c0002090230034038101074108480500100c080441c0601c1c42048a5601c8900140c90740380d0840e103811003110b0811a20010600c408824004c0e1030703210038101c41d031098501241c181034415290015a0700c1e0740326110b044008030743c610014000214132050380d050182c1841411a05041450203020706c0c030351b8104140c0d50352454040c00d01000142002008418002e0002c03504810340c00007018100740ea1090700180c040500c005004c040307600e5404000810082d040740c41b4040014a03441192410140c0f0b5a0f80354104c020100350040600080003000c032410f038000e031401d14001c00f10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798280188 1250 798278938 798279007
    0xb1801060801020a030e0109032709090c030317100e0c07080c0604060c03020c30120402011e0819020d110d050108030c150a0204030210181a090402 65
    0x226034000d6000690071400a0303d420542108181d040c003810100c0e42d0195154a0340c40b01d107002850302401500c00c401103062b070011000606400350b010310002c1c0b901487d1300743c40e450300e503003000340801041940c46a886101007003000701c00044042e540060700d50860030b0005543e0b45000d0081d80344144075028144c41c4001c100781d01c29800002e5842d124502c602014051419400c1c0254103070300400702c401c4042d40050f2400c48552203081e48100b0008010401e549031040f26413003401255020101e41085000404200f00035941c000d22685100072800c503120720540c40b400d00c001e000c0100038208056820310324101c601c80719a6034041e01c82003410210100071ba005e5100c0c202c0e4190f40102c4641c585581084000900343c01c0102c1902c440d010110041c110340c00a1019010b4450801820f01001560a104c0071016882d184505840c0741d0f0140c442004031140c03d0750210024240e42c1c082c08031105924a40200060f141d410740e03d94000a80c0e02580701c0042907080c500c1003003800c9800748000c0441c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 798281438 1250 798280188 798280199
    0x303150803031b2502060d06170111090d03110a060c03141f0506030c0f0403060b1f020c010f0215090a020a060c030804140109020d08030718120b180106 67
    0x80118001c0103e0032204800c0000554024414043c3d000b50300000c4200d4070f0740201080900d890305045620040044d441c2150044444040b0f9110344c000036002d0b60102c41d0450030031400d200c0c800194005050003030400300d0600000f2a000804900103003048907032a4a40e501c1d42003082000100e81c0e000c51300f03201c40389440780010000c0c03204a0109142100f1080402d0701c034440a0400c0c9094400c4240e11007080c2c0c100002c3c440140d0015100b0212200204020104e01c4003210103000594440d0b5404509d103020380c02001008228401110005048100c1c01d0f50020703000100ca0341195001c0c201482c030019103000c2641810391480342400c000d254038040200600700401c245542d28400c9941e545130507100d07402180d0400b5124030003004908124080350101e042421182c1c6c0c410a204c0012889210990200d00381403821941241d8a09020040c1311000f07800001480120180f110688142441e1034005956403648402c06080c1c4801030b000f0424400d04560391001681c1580c0003440010b5644 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 798282688 1250 798281438 798281443
    0x6b1c050f0c01050c0604082206020706030f0b240c03070c0e090a03021b060c0d0804060f0209010c0204020c19030c020901141f030e0106030c0e0f06060d0903031508 72
    0x11110080c0d0040c091006500c2d80100c00392074a20f01d01c14000c1460f55103035510040780c5d41c041101d00349070010180080301150703c40c00c64031024150590180065924151018080d910380c0340580300264203000c1038070f60a4032100f105c40800c1c08182892000c1c0c0c0c00409401d0721074403c00544031007a001c00034004050240402c52314040361a1728010744c020365200d40c0015103904600c8001001608010528501c0508042180c0240140206240c1c0b400200c000054030384843e840b1003001040101d0200000d000d414811550081d401d84415071801c2104d5000078208011014001d2289501003900020034000f000089032450a000f0341d201c06403010b06025008a4081c00124800d005100002c20b460f00b159498120509014105052205400015101200400305d0000070541c0d11409058070030b82c240941c10055006400302c6004505142e00415401070045c50780c00c591078440e090055a1300d43d8011030384505a5001c00003030241d180e00d012406080752550041000e1101c85000c0703a03a0101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 798283938 1250 798282688 798282703
    0xa021308011515090e090715020f0f070506040519030b1314070f0b1c05011e0803160305070606080109081c0501150c6b1c05 55
    0x5041c1d4000b0550b540c0c00c42c01c0c1c81500e01021100143c91120200616030f0313a10041500002414299400030385c50781444943d029070711386458010380c400c01039200c03000c40510102d048070096402601180d0709001c0070448c54440d500c1541e0190450030039603040b0781c4409441002441c0c6c010400e0030581800020040c0343c0f00c013148140e600c00020b001c2c10f41590800903006046500d610883c2c110f60345002c0510405800409007030000f144252585c0804e860f441c400d840c003800c0b01c800d1500b2401d680b02d5015201d0102600001c81640c0200102484280b024081650382035140c40c186680d440d1a14209016290b2507000307040303960a008914080100201c0944000c080184200b004203c3e40910070041e244280300b68281803510307414240c1418842d5003150304841c02540404108581c0411030031442003081d21104440f500841015079044060940e0101c40400d503d103001a054902e07541690301e00c00f44640d50154054000700c0c642e13074807800e80104010741c00302e04000c01d140260420944031801c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 798285188 1250 798283938 798283961
    0xf09020102070e1e25030e070501180504180c060c030e04290d0212070611031c020a14070605090f1f09050c030303090304090b0406080c090a02130801 66
    0x5407160114000402d0a0000d1003a2800045407045401c940319084013080090420540c005922905070700b40300c500e4040804401c02a5000240e410324540401d0030400544c100f03a040214104d00e1503005501520b001044da2b40444000910080346540f0780102c0881c80401009901000740003c0c64580152604161034040d0715000003854280c0300300800c440702401c00c441c10201d540c21012201a08103000090408043c0003010800d800303800103002601d00a18410085d840103106201c1c80394803a00c15000e00003c80021400d180441454a10840f098117140c140300b503010800d103517424481e0901411036841d0b00c440c3c0d0340d9184903041040140200711a80d24035440346098052141c0800182e40246d06a18240341011080c4101080301802c10840d00765824030590a1600031070b50240000c1d40101494030042d5a960f1408440c04191402d01c41c0300c510943c506403017080519400324400c104c90000712a02041a550002a400203015411800704240120580442c03440340550001c5400310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 798286438 1250 798285188 798285193
    0x1b010507020d03090b0a050a0204051804200d110a0905010603020c0f030c0714060408030a11010606020615010c17030a200304260d0906050103020405060a06080c0901050d0f09020102 80
    0x82c04250b09030300703403024a41d00510003085900001c604000340ea21140e0018041d11000d0302c2d1a588000040d220502d10001411120f1941c050208000585800c5c01a0080b10071000100800c140300003101c42c039410001400e004416405461503682d01321500d4064129200c0400c125610390400500035004859003120314800e08000311400c410010581d002548040010940b682c00c000c074515a640c01e0a0440c2c0e000303c0c042c440400c414501344060140202d465840c80c41c4440115203050968400b903120300190340180050011900030785101c2407034014207081110400f0a103140400c1c044528440c40346447c4004014405801c180e50050848030380b2038100c201901080b444144250700c0247c82c000c120350b204001d030f00710004031060310303082041c0c40c00c0042c0c3c201a00b88180e0003e40b0403d0404072010382ea940c1c01442103107031510850390031540a554140d190750910501a00d05072014000750790485003c01c4149079a07101301c2c221002c0802007041484181841e030300400150101070303012070150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 798287688 1250 798286438 798286453
    0x15090506071e1b050f01050f0a050103021804150c0206100e1302041503080a2c220908120a05060d111003023703020a02211b01050702 59
    0xd40b15140c00c2c0104550685000e000c1281c040c016108070a0308124042c80d16038501e41080810000d0081c98410340e100300003c1014540140000000403000703024880032441c18006001503180d0340c46c602c14800c1000d041c614180c803541442c050101016443c84c0413181804080f20f005940403a040e80103952040c00c0c0d003402900c614031180c42d234008469541c1e5843c028030594003d803600d03420464207c3d14000303c04007210307181e88030824036920100782100400c01c1c20b030350111200e860700304111211080d00039500050f104440005c030815030b9400039030394042c017040010300312007a2640000c0442ea402821a42c0d9240a0a00480c0c5060304481c1c48020724513190000340d645c00d01c01003000741e17640e0000344000c1c0c1e071110320100621040c0050f41041056400c0c04445007030600a00700c64242036900d25043e41c00b100303002c08622030403e0406c1e100101030045c04214580d9800040c2030084429080c4110403042c005004003a41c5d0041c07099405421000000d59400c0800640c0818060f24641d826103020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 798288938 1250 798287688 798287701
    0x207061d0f0a082d0a170304080c06070507020f040b0105120613020c011e0905100e0312010303050c0609010b060f0702040902060a090e010f03120e03120a05130e010812030702030715090506 83
    0x1d80d2140c81001e022850b0911503586d202500000440d07000d441000b03c0313070a0404129965280c0b0b80111142c1000c41c0f030025809082d858203e0b001c1d01c0c180d000311030070310118500c000000c1c440e005401743e040c0c640b9030003408925141d403083c1402060b0301c0d558000b152501c4110005074040d02685010070740d500c032010080305101c8a14000d80c00c145810038010111031406001002c0101150448003045000912034080c400321414440c40c000c0d8000c0c1d440540b070f0301205050701e080c0400549041080d070314041c1d001010361101c005a0b010031030038400f05500d408090012030050f01182c48025803107a800140004681c2c1c000909605442140466410980e00d400e000c44201c2810b01024108046a2000d4000d4510904001000c440050103803150000c025198801e5a002580c541010410100d421212100b0110450b0010244c0201300c0309154940071110741c49040300c02284001c4a000000a8a4140200b04440d1284d9105044904041c1c241182c40021704150b03000321941e011b0200400d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 798290188 1250 798288938 798288943
    0x405040b0f01080403050a170106081f080c010e01090b070303050103050d03050c160f1203021c050c1803070b0301090b09090331180209010207061d0f0a082d 69
    0x40403441a100d501c46a19140c85c1a182508514509800c02c14007100c0038010191440c9414000e007002d440b4000c550424400480c0814054896040080d5101070200b0000500203581c90402a00303003400522031a030742c4c3c0120307082d6410390824000380700001940b80800d941503110504aa0040303054800b00070b5071040441c181d0350140d40d070703010f543c2d0280040300d002c440c45445003015038880e00d40e8081aa00580c0d40780c4a400c3c0007000701c80440c1d80840e5140030286d4041d80e004c261840c1c2d610410044c80c204140e81458015003a20341c088260f000181c00144c0c5081060340701414a11190540b01d60356185648050855982806d00404075540404c449400000c19582072010744241d1001245a010040000d442140c82032030510402e00400105010000301d64083d0100240015940342070003c00a860310703c00380e10400030403c0d808641102c28220603c010088401240e1034160b10340101c0010f10362204d5500700380f1a078040c010590310101c0c66200c2d0f9a03100151140040a10a1102ca0064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 798291438 1250 798290188 798290209
    0x1115161a0906010302040b0f09092b020307080f1c24060507110a121b060e0109090c050d0e060417040819060f06060f020f0303150409050a15020405040b 67
    0x112650002c0c1c014401450190800901c2038405000f520240c252900061010841540c11040d2030300b00d5030b144412004020000154100014041c0010058082e0300942c1e0380310307419011b0503d0001282c0d6001d071120080c21035030480b000701052006e402c100710101c4024004c00c88070008a03600d411303201445000ca40441030840e11161119810f002198460702c4803650000b5059501c160180008240d50301991394034084c1501400c06120b441c00c00c1900c44039001110b411030700078000c0042d8440b2207a80c0c4046100d050300e0102c0790114401800020984081c058048281600b60038902c14050455000820703074410b601903401c0f082120240c000700c0140b4402c5000c3d00c02a5041142c900c0c01d0746180c02304a416040c81600c0002d98000800303282c90407260307150014800502e044811070032003070b4104465100310090402441c82e500300900702006201c0c0c240c00e0207010b140c960348100140038003884082c91041d0040d0450f9003c010b2841404020341c01405040e01c507034903210510f40e86041040926 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 798292688 1250 798291438 798291451
    0x1141501030b040b13090c0803041505070f020904240603080d020a02071e1502060906040308190f0e0d05070b010506091903060203060405150d1115161a 67
    0x1400404402401100907003903010000760003d4403024407030516111000240c50445150000180b2030140d4600000310b00656440f01c400340d0300c244020310181e8010034100001d2070050808558503545032904040c2d5180d038860181d80110900c0800050102510342c1e0705036414500c80c010f480003031501543d41114110702010f070181e1010700510b074072480d86500625409405004444411340e031609014019065902104154101034a00300400105040301d8004421240040c200b2868040e200c103640c0c8d03030001c00c06070800c42c3d9a0003040c080350301800c90220b1900ca65070b082c003844da400c4007808090085800400b015224001c3c2ca6205d503440788040c0d5584651101c00300305282d20746020081c803504401e50059201e95003244403a008c1e0f1030500e405008500c11034000d40c89161003010413048440081c05130b400108001080031099480c0600d070940702d540090064181c0e0700700400300b0024010308080c4080c0144c0041c241d00008000760110300712500c998110a0642c8107080c0c0032000300b4087d95103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 798293938 1250 798292688 798292711
    0x604020126060415050303040b0a090e19020d06090c02010617070503060f2d07081e07030903120c17010605040605040e07030b0607120e15070b040c03020a030c080114 73
    0xc41c10501c0e00b9044952011440c0c80106205920b1764006821a03101d0b602c82c09a4083c005100d82203035401a902500074070380c10103924030500d080b00aa1041a001c0c60500c41004c1d07000403082905440f0381e00000280c0420340c0100001c41e15840080e009080600501404603003281004070000c400058500a542c409000b400b15501c034800d40300c006800180042c1154600f864200ca43e10300c00c061202024124045800d51505001201401030340e809000603d080000e0919900900001d13018150401d000b464009540c0d0090304080b100b091203000760010340c0341000c00345140681d0002560814144040c1c011416981c2c40f0000e9500784160f200300008a03d0501082040c203640200d429840070180c2030104001c0c8503480012420b81c044902150a110952250381c9226403280301d40c80380358000d0315000b0340005031710454005401341480003403005032010006010072070180f000e48011a4050181d41c0e8030703a164a0800c01d288500d00a81c02103600c0d241810740b1140b50411960700840000302e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 798295188 1250 798293938 798293941
    0x6031b011808060f040c050102010501050a0b0a0c060f0e0c090f010302090709080303010e012102011d041803030b01020f01051b030403050c2a01030506030d110f0601080604020126 79
    0x19110a0458061003100340307034030100000c030903406200c1207204140079044103015143c1071600c0a0f88802e283c002904580c5042c005000c140c8803c0ca00400303654202c490340361500841001240c07280600c060041c00c00741408602182c0e04c1c080e0308801c8031001c0035001d0303480361040d110a100300d0742002c545034059040240010000350529001c56500100145004828103803914031080c03942d4000e1703003c1d200d01c0035804010805903c80010010002544d1010040da8556a0b00020301d03044564118900209115540c2246540e503944030110600c03245251809050036810043c00411041407814054060381030751103803411040c404c3d18814121300040f440358805c00d40d1112503e42004008400b400010807454110305803c01c19200003a00707120341200e02e095a1080014040c1c1c511800d203050509140500a082d9000302c0c04442e03200c450f2030314150620341178542d585050f600120042990050700300101d80000089a454812030003a02c503040f20240210030015003411216203458040c00600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 798296438 1250 798295188 798295243
    0x60906030912030c0301050a0b070f03030c051b0c030105071b0f021302070c0f0803250f02060c030706140c1b030d1a03010e01021c110d02210603 64
    0x20051900000040c0840751141c411500224440d0300036100f071340b00c14001000400c8545000042c010213840701c005500e050004659404152a044620050038075855459082100340b00e1400c2d5151082c001c90f0010480b9568400e45071205401d0610030b020b5401e210004400b5805a608000356041c0f010f214912400300303480d2103041009241d0126444a50303680181405200b90001c3c2812502884a0f0300c05139290807a04c05050109a000e0505038100780040c03100c480e4803e221100c400c94120940b01c00800d10b240c001e90340d07143c482c1c0c000d60145001c1b4442007175000000107011030b11302c1500c04100b0210742c00c5e007110030403404a80d2014040313001c00014010741d200c10b01020072000d01101b16030a088103c2e0a20003500e0400b10410035145031040c480403640380901503001c0c2224140021850200540c0140310100054009000b04946540d003100340e03004041700315200d903560484115250600d140e520303010110072070600c020542c500300100311300e840d000c00c0c4c4000010348682111014503088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 798297688 1250 798296438 798296449
    0xe0f0d0f031e1d06070305070e0906030c04050f010f0503010624030f0f020711060403021c0807050627010b0a0519050a06030c021b0a030f08271e0609 66
    0x540405048060382201094007503814011110411400c50000680c1046032243d10b24000340102440b0816003841c0c140410070740c20020038500c00e04243c600c82d1840c3d403814086440d2046038240160002c2c0750408002a9582d60402c0c1810b940c0600d1900e44000d607a00101341c03d07100f4602921048800d0300b0441ca54010000003420b031000e80c94100451602c548001c00c03811903001c0c1c0c240644054000031114104054040f051042c1031003203815604060541d00890700d1041c1545140851020201d420014090540c05540429038014116001481d180f90408089202c0580b1550940140c0515481110043c000d504070700c0d50141050500902c0c000070040302020f00000c0c00780500e40f00b240840c0c6030b111120480c01424480e21f0200740d41c0c448110091900c400c21845d89006494030740421400c2e0359118040040b00d81000e0698071503255802c00441ea40b2a00e5a80b003c030810550700d600b20300d1070707444800b040c2d0002101c01002646211480b0280b83d14811031080d4007000c20009441d041c80d2a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 798298938 1250 798297688 798297701
    0x3120a0509010b1503090106050a03080a030b15210f15060a14040308041d091515180105030f010605010c080c190803041b3210030e0f0d0f03 62
    0x401d0000c90f031406040041503400c1c2074128041201c140000070851000e01c240503420080109440701c4800070310710348642000c0c3c091404200d0825440b02d018030255510801c1d01110441c400c60056943c02c02e80e00a80d000314500c1c2c1001500003072140000d20614900c0d40700910070ba44103040500e41c0c081d0101003284030780c042d010a00502451a41c80c03054650400003400140d40301d21546a5158101100b0406040c440d06c9507501c0548410b04100c10000c0105800f2855440c4400c0151244c0715059111072100c00c199011360003016240d07901510301000461107040316015016180940c404a0310203081e0b0b542c501409020800742c60689001600c00401044242e1009040c2c41c003503204120a83e8481c50f00d588142ea51071400b105004c14055019407032540c84050070004100c1a181810b14080f46203141410b0300e030300000d00c8000003401543c000702c01070250011700c041c00e46500410040d0003840c5041c4020321610515420b4020340e03c000920701d40344115601d81760162244040100c024121 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 798300188 1250 798298938 798298951
    0x10603030807030209031506031c0207090f1e090312090b060405060108070e0d14030a09090b0d0210050c1204120614040206040302060f0405060a0314060d0c05060a020703020d0501020a020d0203120a05 88
    0x3880039202030a8ac00520354140940c070341d80038248c41840d0080c0751080d2099003808190051038054040b400c01d04200901c0c1030715068003001b003424800e60405aa800c18003e401c041d04034100240f0008110b0b20b007548078450002290100029140d180044034807001c111082130216038407001114007403621400903082a48500d04441c1e10700116003100c0c0c00e40d041148603038041030b9440c4052250744200d014440b444082590159103560b0b20345c002a039102130001c2d0502c1440b00005400420030810b1286005407042c0c2c0b0800745e0b640e075444689182041031180140c46045c9049144440c4180d1090a2409190020b101030308103425074003040391503408000c01c1d1154440400c0b00282c1074a9480107822120301e60703140000c1c0401ea8000c0d90410401c0140303000e20904d070303100e101000900003c0d10714054400c26582642c0310428003406030b02d401156000a91b002651154840800005400400140340e881c0d080e210b0006076000709030b98a0090f040380b4419080d2a00000f0f030662031940c0301950091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 798301438 1250 798300188 798300193
    0x172a040b22060302101701060302030c09100503150306010b1209030d0504050304030b0c03190b030a051204080f0a11010f0e06071b1e0302040515090901060303080703020903150603 79
    0x240c00c1c0341010828850440070110302a1100000c100390700d4400c00078a09070740d6a0500300c07140c00c0d4554020812003014044c4506059021000c10030b10103c090030707030306200e6000e859403512501065000d030854104842c04909203205100c1d00949040100b034090403108080e0f0258107050704904076a20350340000700716103e9407000744240752400d10315000d924001c0c0d0040001e5541c1d01d0650511519005000344420700102d0100309101440d02e04840f591f420411f11400090540401c0001038107080c440794000c0c00c140b06800045220b41d50b400c00400448941c40c08a4183c040ba00ca2480e841d80c056000150452021085c000348550060713400784191400352078101c9544001400042064109040540350b20480440301c0e002003510b4112032010b405104884404882c800c1110901c0c10408c1c0802401a0346482c0480e40f006107520b00145000002409072040d441e02c1c4001a008080f184010740c005070b0424042406503000c0d200b00d842c0741c0e0020b00038203800d40c0d84c1c40c402504110b010b0556905032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 798302688 1250 798301438 798301459
    0x60209011707050315040203010e1f1e050f1009170709020414010f03421701050a02031308070c05040f0605030105010b0a09150e030106172a040b 64
    0x14000c0074216071091015482d5141c4904114000d02c02c45000c400341c040c040e40c41040140b06000d00440c1d16a0302c00142d40160085c1a640b090941000296030f10001c01d4001070845450094400b2100100b80e6030160340b0a0b81d6040c0714020040b01d482c441c90094042502203c050116601e01c00c6840701602c0c40c1c400710760100e50b0700c0c01000b0883e48117034440142d0030b486424056103580c0c090a8107641940d5031030107103c402c000726403401c4a0580f0003940303054000344030343c030708012540c101004c2c0300038012645025100380d0318010307024402507001c4084401d500c0c00340001c022004600c01d40e07009240200030041620065a41d2941e15446654251091028003800081540c1c543c00b664000407213042000c500c9d20300d0582850b0a484041c3c0201c40304480910036080b550794085603102c1195004100481d800e00c45a1050360a10030107415680c055080000c0407a45c0c0601000e040d42a4401c00e04803840c0801098002008811450055290010340707040321b240e07483d03e600102c2c501d0f100103000c41d411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 798303938 1250 798302688 798302717
    0x302091b0901111c03230c04060c060b090414070b0a020c0f0303121503100e03070602030717090109030e030a050d030e1e06010302030c0916030c140a1101110a0c06020901 75
    0x4034411300390800c00080e26211400501c0e00000f141c600c1010030125102100d0616101240d25401035004500401c041c0034004014400c054015810034840500260f44504041c140100210a030100300700d03403031043d5000000c4e07071414403046403590324582c2c0c0034110114203801000028408450041c0d410720080c03110342d450000c24420707603001d0702007038035403818901c000d83c00e0504201c6075030503140683d440e000c2c0d01015a000401201d5406900460050303a039905d00301c0a032240c03500240ca140708444103204004000405521140d40d5500a803200030a1501140425586050011009120303810002d201d58042d8007039000091303030f01c005005841c0c500c00c2ca400078040b04a204001200c9690040c80104107600f4240883c5041860a032565402d074030317042207141803400201c0820010035030340c1c8081492061146000002940840040c542d603030389000c3d0002c0080101c4c0004100d5546001d1002c410803140c4400c0ba820070f610b07074483c2c188612035521888002d41240340d0103818032103071a01d100301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 798305188 1250 798303938 798303973
    0x1d1b0925020d09060512060603100f0e040c231e032b08040f17270405150a06110309061201030308010905060603040b0a110a03060302091b090111 64
    0x364425540c002c01500d002108001e000c1d505580c4030f0380602c4001c00c5030b1201c8140310b00075103600084c10744600350b032525802040150142d2540c400400150322620106d1161122181c050185028030010b0030390383d840d882809503040505e10118910301d005c89003140b950920b0403481a60000801e4400e5907214004042070511042c90690120b2180c2000ca078031064080100e03840344000303d4604916189001d0f0b032400c61702c1c0c82914000c1c1519114958081b642c802c044100e82c4d8041001045c948020b0700390b1103031a0100d40d1403240500c21030401000900d20070749000b00701c240d030704020f210310300152410000740c903041440148101180410842c10185480d501c00034800c40052104600003503255050080c0058810b8120341c20b1141040e0a00840755100410b6941141e004802485c0c2d0b03403104c4120000410b000807080243e40c01c04608200c1c1140c061307200c00b00b2170340250703480107060340c80d40e20b0404624a0540d107492040020b12075403489511444207903150441000807602c80349078030000883e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 798306438 1250 798305188 798305251
    0x220b10050904050f1605070c03120e130905100e0a0b0f1b070503070210031d01150e1303031104081605130e060703110906030a1d1b09 59
    0x8010420024403200141050701c2210b034413480c4890b07101101e081000781403154420440d040c1040020104424041c400c030400b40c04001c56024180c055030030009032010b09040c242d00500c5200302d046040d900040710f500d0103001c0c00968400c002e0200701d40c030103a80c107000340701040e0030301a01d10440c0364034000500101c280c10700492080b03075018200d10f000c540d0a110100c100b140d460094106000b4100061000015101070507411651038040c85820303101103004049003402000c0d004002d502401c1710031019802201c01e15004280070040a03114041d03003401c04400d4403202041f040355941940032910943c450501e032648510a149407a03aa1440c0d24540412036502e014110185003042103d440e141c00f1509404001031020312040d60081c40d01da8958a0090030b030307020b0507220a8002400f0790801c0440d81b0100005103060384030300b0300114600042c003004410600056041411202c031000002b68140200c400c074860058010045040c805242c0e4040c2001903854944802507144d1250084082c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 798307688 1250 798306438 798306469
    0x90f050303060906191802160c0503010b06040b041202010507020303030a1b140d0b04060914041b051f021002072a0f0e04230601030b0f06220b 63
    0x11600d0341468020808184800b524103881000c200d0760b21209142000802c5c0101d4491281c0070340d900181c042a40007030702c9175108140151400041020802c19202d0004099030010f8008111103004c220500501d0310a5000300d590400c418032003000009030204d5003840c0944180341ca2428240591b01091441e0030990300989104d481e00099411202455440d0301c3c2000c003840d200c06078090455503031a070b5100709046030f40616120040b401a58445400c4640204aa60410001c4810144850440000a6808540707060904001c09684440b018200e402d07160020104107404044103101c0c100f000c08440c07000203502810b450a228a1070a201901d900c5000c0d080b15044080300050f225640c0c0410302c4c100049001c0c03c542070050900c107000f01404d490407104540c145444c0d90404a000c0e540c070701036148a5010003003003d03002c41c00c0441c400f4126031080401034003603158240d031404070f244120340c0e81e41c0020644d0581590021070114132000e024410900058800c00f803030100e81c0122011424 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 798308938 1250 798307688 798307693
    0xb0922020a110f031918030b0108101409070e0a0b0d0605070f030c050301120309080307110307121127101719170409020406030f0b060c060613090f05 66
    0xc01010003e005003e064424030014500d031841035400c100401c0c003900301c0c10080290341c0020408041c0c4566004001e15001600d8860b50340e0340302c03c6d1950350802c6003903168810b4105121200c0a1a55482550103803040301d010380340941c10a000740b9001c0078010000300800341c0320201c464481d1146600d900070a40501c0001c07606241c441400f13442000b010650004040c58154945101c60703103c81500d0645000c1002e184040c50390707060031241411140c20001050000160300020440760f81c10703580341310000741d059881c0c071581ca1a0300d910410400c900074000511019040c256450030750404004951907a50008100c80607024010540c13508440e8071040710080c140900401d5010110140e100c2e0703103040100f50781e07020100d6440c0541a442d000800e50307041030844014450403e41900e014241d56042151035503a144001030140142c0e801c8201106d00e01921005c00c0c3c2001d508583d41880e2800c01001c0c15100c14040c840b07100e0f031043c00c0680540d030300c01541c40040d1301240320544a80c0036000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 798310188 1250 798308938 798308957
    0x30c140a180b03040201320c030304051e030a0e1c0b01090b120316020411120403080c040b0306010e010212040f05120a050601090209060d0e03070c0605040b0922020a 73
    0x1c4040070314026030804690358100b40100401030303911101c44c0c52a00b40040c0040c4208461502007050311040d032440c3c8100703107808508000d2030701001014600c12802a0100c0f000c1e0907210113a030001c880311500c1204142c0040001881060140c41c00c0946554054800340111507a40d210204c6911040400c0710381b0f160365070040024003500c2c01407410341c54084a0048000023041100d44d52840b400454108025004920500350b42d95a030000308101200c660003541d620740c82c5a52074406008a40440101d05404041080340f0406000e4070140c1d25100a414599140e5000640710440010102811840b4030035085408141000140c0010901c440c003943e02c1c03a04142c00c00c0710008200001c44403a07030108000d100032400c00108141102d05005005a440c000d840100c0c1d900d11075400303103002d03181c00e00c0845040341070008003c040b180d01950021141c561140c0c0220b03068415031048040c550424840032107949407480b8502e42e100c82400d8881c0c0304418401c0454280e0300450101400306e4134104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 798311438 1250 798310188 798310217
    0x2490507020c032a04021b0a030f020a080a11070305030c01021b0d05040303080406091a0f130201080118271202030a09140f03010f2c0607030c140a 65
    0xc2240c0c9918201c016102196200704c4050f010300790450090b0f110a000e092030b00290302d996045480040b04800101d642031000943d8a82d01c8015600807000108101240643ca42c40400d40e4581c29600c2488a4540421207a0844840031040b04000c1d950280d4400000000d01c100300500d04030440340005030b110f030103081102804c4040301c1d03580351180d000580b1101c100c0340d00c4801c440030760b43e15080c010440e407280d0402c02c0003071088060017492640b80d1400950444e075410b60f103e206907910303a026450343d40c03851904450010440402070106040740c00600004a2a541108159800300d00010360702d403c2c4101c00240980441e030100507491120303911002d124240a001c2980791950006514104e0102d0b0000c089030024850414100b005403415000381d034420440300c6454000600a018001c00c407102100200a0b4248100310403910505030003500c1e0514400844072075014015000c00e68a0030800c0c1d010f02811034000d000c0004c120b00030901ca002c800040c0c080d01c2001d07910b86a8058802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 798312688 1250 798311438 798311443
    0x30b04140903070b09120c1f02070c0e0901141303020d020601030b01050d1112010c090522020a0201020909010b0306090106171b04090216060605040249050702 70
    0x480e0000d0603040300008110280000100302e4041503841111000243d840809080c28402c03d0000e0030a59040015a01088840016260400c1c680c00c820814481c5405001008070f12400c00001c082030b00c900c104010b22484c0054060b4441d0070300002003845032220b8118400c1c90300171117410300140b40e4400d9081c141981041990280710050005240a50554494219010051040f9441a80403400c0c200c1000b00d181d91540d4242030143c0b400103000ca05020b41030280620052080005488000024082c03404801c2504146200d0f6031048030115140200006136000440b80e1081d07640800514895840750701416009000a582e481c0c0c990800604020b900b44060f840041085141e51181202d8244101c500750000030768074440602000e000343c40005409150f2001045601c042400c0c07800c105004c04000032244076400800c00c0075100d074100f000700e02454044484d03a14000c01040301800c80880c4c0c1c10f00400c05c05002103010a080c40030140714034007000c110b41015032684180302400f07404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 798313938 1250 798312688 798312701
    0x3010e06060304031d1302030403170606130501080604110c030403140d0e0d050709050112060b180f090a0f0311010b010e01080703020f1b01020705060a09030c080309010f0c030b04 79
    0x1203800c1803843c1810346001703003440c0da214404421002c0d26402e43c0f800341d99002d61111503034011a030640d01c0740b906040c082c24140301100351006120290700016454603007241129240304224640c4050b441c100b00046400c00700040603a03800076599140125042c0010001e80041e940c018000d5945500754546140300e1000304014400c2a803024110030801600040140c03441607082d5500850341c00642015490420950b0180944d5440c050000c100c5114074144404018043c0c6e100703000d0345048030b00f4042216031100740e4100d09017281000c00c14041201a4107904050140c04440902e071150304c5c0e4440301003035035508a0224000e0030f1040340c658000e0003096034101c000d00b402c030400441800040d0282d030000303280400701035001400080c986d169009880c01c1ca810702c103d00560112880007035000358425030701510680f181c04001401c40e01c4500034410340923415928030500c44070981d180001500042c010803002d5407295189669035220344542c0f2088086a50007007005102c1c42c0c28007088800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 798315188 1250 798313938 798313951
    0xb040317060d020f0414240a0806010603090507030b0c0405092413021605030a0201150803040b0a0302071a060f06162a03120207091e110f04090203010e 67
    0x800400100da0742e448030512a060301a628900d0410401d8006802401c00c8904074420310103c2052140608804019095038030740138840076507030502da4080016010551045180a9021000620100344240c02029219101750704407501c460b1a5540c101500d03004559000965402103405c009a00d403001174a03802c4061035a4145001c0c40004c098030910f0f0100042900514880072000820001c03981251240d400f402c1d60a030f264800c0b450260f460b90b0245605030012340c2042c00320003140c0c144048113401c40b50b204006514080c80c02a03420003540100c8406418140d00780000c2002c20882c10b0004200064111604803910309a01040f41603200d07070f21740070300a810a0218000100300f20480000d4a5000b12002e841104550b1004040c120251482c0b48000100170000040100704d42c0300b17a2035440349400f50381c4d0582d1a03e10500440303414880c13800c07140318100500d44a400a80d444410000b4100d0b12251400e1030352100e4009980c4140c2c4440e854960001c010000940d180380240d4101c0ca = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 798316438 1250 798315188 798315227
    0x50709090605011b081309090611091806030a06020f090a06080903180f060403050307050609191b0911130f060e061809100303020f0601030506070e0301020c0a0b0403 73
    0x2802c01c0002020b050595100940c1d5154451144c02407101030001e542000f442c60326a00241078558003c0700140c0b8003e07030301300e0b00707207081c50516416003c00209680400c20050a8041c610503406020000450047c03d06c0b42c01d400340340c0414000c26880c2c001061048180030400f1780c6ea6803400c003030211070f4a05910900c00c1200c0300d000c1c003d600801008580c0a044200d811410040c036100010740c0300031062822640c80840000c0000c01c210001c8050241c1d54000e4054070140e50750701180580301c520301a200100fa11098012800003106824824410f90002103400100c80d22100c2c81c400311440390741042840c02001c903138a1030346404d00020f9005000078440c005e44030340ca4000094070030030500a103a8819800803070034003024407546ca0045007140c3d00806c0c541403418a080411000c3c541c600040d0014061903034a02c0303414900040d0a4100c035448401080340e43d8903d0300440c1c6040000000c0769265408100310710991004205403c0c80c0740c040c00c48032282d804c042c900681403050071410b00e890203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 798317688 1250 798316438 798316451
    0x801080d2307030306090603052107022b0605010f1e0b0a050906071a1b03130b070905030f010e060601230f040b030a060603060b091e150406020105070909 68
    0x104a45140d0300d2108503694121600e5002c5881d090f0040c291a03084000030a191000000034400c00040e034010f165600d40039102869415a14190b4030720a000700a074119444441010400021003580d1056030301a040e10350351801e02c3d688a10565000384d000d890070140b0400d041c04101019400100350001c03d442c0d80c09218a0810000f02c0340c0030301e032204020301c4004220700d1541d0315904207d6404a6001607180301d10002c00c40040760b02d00341512900c00500c0d40d9114413108201c640c2c00c490094108010340c0c04810002d23a2202400c0c50010420010001c20b040006159281004143c1c0b000d04c01600100e01031112540c2c0600d4010002c03c59410051400d001c8400c580040d4481c0080301c22000034aa51103d01e007040c074240e84036a50082004d54000010450b10701e4241d4400300075a40a5981400019a6048030040902403520900d41c45100c50703001c054582902c41d2114507414020b81014614840d8800e00b00040c4c000340d0000340541d44603030800c83c00301e52104904018000044040002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 798318938 1250 798317688 798317717
    0x50105041136060103090506091b181305070f081b030106061209260a030e031c0b040b040203070f09050102061b161b030605010b0c0a230a030801080d 66
    0x700720601c2400c6441c600b0540200e042644aa000000c0c015000811206c0e9030809151082d9941000e01c031b00400c50007500c0402d075203890040b5402081c0382199051200c0e0303448200004010000c500c0d0704458900c01c500d00081c2c0360300a0306041c0d000300110409880c3c003c0c0c040c0511052901c0c3c500c041486645800c00c284995a081241086c5115540400103482d01c02403914894000d1009102041040100b1a4050101c4800020300642c00399540900508845864076030380d03405020001c41c050329030034014819031100381e40543d8a200340100046895000746001c102285d005484e8400014852541c0040710307508548003034010301081c4001c0481f07281a020369012031040b49071113079a04100261113000b21800728141140e0075049401400d04070541d440e036000c1c4070075a03c001c541c1c060824000050100710071046c1d44c85c0c1004500a458108400c2d44e900e804001042040c081903d601615681c50660400029100c50300c00d4441c81099410254604e1400e1440c500340700422a0398a0f12410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 798320188 1250 798318938 798319009
    0x908030f030c030c04030506010e0712050f15030c090f2502030f0315101e03110f030702070308040e1902090d120507170d0606050c0d0c08070501050411 67
    0x2409a0b6a0704280e45a4030392140c03214952150f540301803c070744910800071809130188140e0314007442d1341c0d07211031050300340c1d1b001248151001111024181055800080c001d800410f20103a8a80c0d4010143e840c1000c4103000686040025610303105465080030801c07028609080d80a90401c201100c001070f00f007032100300259a0b1099400c0c0805449000c00815600b5044282e00d1103514402007103508043c1006400401341e0f0041c0d010080151030482402251500901c0342500216445140d07501d81030303038290340e030916900c05820301045215488001000ca001400601701500707105481c4203d80c24207031141c000c6003050380804020b01d44104001019540c0d0500c006c4840ca500160305561880300840544040c00750200140842418408036003858881e41e00501e000c0c144520308204054545408032142c0c000c8158442e456440800e0341c501280c010180704480503c60002c0f6850011241d40c0c00d800d445081da0101e0f429648a44400c0f0913280c1101018420806075400c51100190030b050201e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 798321438 1250 798320188 798320191
    0x14180907060e060d090f061802013c030b010e0f090f0c0d0e06090f0705010903110a030609050f0706080c120c0705070e0f060a0308390d0908030f03 65
    0x3449000d600142d079546400d070503900c5400c008070041100400302c2c02c0596031400303102001c0300c060b4a003808c6800c402240c000309040ea0f94046c1c2d90401c25509041181010070940041c548000d881d030b610410198480800c030000012041c1e4010903203c4c241400034000740100f8644502c04ea0042c00b258043c0d0702d9092450741d000c3c109a0301c1e00b025071107440140703029211300c440f01e09206050225020031075a001800750b0041c485d080480d03442030619203600b0346500b06130181034000341401104001040b030411001f8480d05005208a00e056541d9482c2030803155506400ca601e50080140080c5083d8140040402001181000002071614003594aa1407103042800c48840360107502190002d03400c00f041d54030040c0e000c0101c0b28020b80b541c0180b50424000c4500c00c2c20030b840381000030503504080900100300c951040780141090010304254415507104100ad429101066440201e1008000000c03040c05006102a0020710b4901e40c0007403920304150851b11442c2e20811481200004400449 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 798322688 1250 798321438 798321449
    0xb04151103220312021602030f0636030715050a0510060f0201060b1201030b2230090503070801020711010309140706020c100806030a031209080414180907 68
    0x82d64003002c600e42038842c0c036203110000e04c6291000c80c00c50200c80d00300c1c5054004a0086040b02c46e070b0013201c499660b80ba20100c4410020707244107034940b1072688410303181c0c5200c182c1c030540c106c103040c125100039803030350700124002d58914000308844485000184500d81d04488981420f01c020b240c114010941c00c1c203248940020043c11050f10309480d4403e41c81000a080070001403582c455a403100720072201e2003808152906840507010880100b450400800e519031020030f016401241078880122020703004600a00ca40c401d28242128880c007102c0c0034003085c680d601c0c3d0300c0d149400c08041c10700d080043c2d0803205c0c0703581c8104404404201c0349290700305952800d03e0003058031600c901e04066007404a17440d22040b03114410340411a2a00490100329155050f038001d170a0b0005000700301c0e9105030540e007031074140d005804000003007071082ea1303002e01d018100e001c04141a079241d51070960b55409079005042c2034481d19000034041c03800903058600140d4220705481a400c108980e182c80d544144030381c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 798323938 1250 798322688 798322741
    0xf0702010c170912030c0d050105010c0b0103110a1203090f06020705010903170f04060201061d011203230a26162a0807021f090308160b04151103 64
    0x308441001c02c0320b4413080c07041200d400d4481c01e06110446c0341e0f401036140750241c1c5040030f00105013944142c0d84005926003001407030445910319101e00301102d5546000681004010b20081074500022080c1041d41c1e00c00c0e66000001440d00d5803856140752607412031400c43d0004441040240c0e070140028054030303040079160350b81044d544080315a42c4104c040644810101040c000795031901940080101ea4600e032003142c66006498210042e20000d02805042c0300c845513100d40400d00c10388440c07503154039100d1180c46404040c1485100c030f07007082c0c0c01c44000607110501a119000504054011300742090043d038000e04250804040c80c3e010090007034104502c882a4501e8011400804d002d08209000356a00c0399215060404166000714000c0c1d020b0b441c4807c180885080780f807540700420f80f00342c0c4c0b040000303425507440341d8295108034031020480e08111813400102d045003900368040c602c03400c0c9a10064107d00303000d03420784286c21146d0352240410300420904410a000400c244080c0800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 798325188 1250 798323938 798323941
    0x605091305061801030506070305062407020d0b0a0e070503010e0d11030f03100905060d0c1404090209100e1515030403021606230c0c1210140f0702010c17 68
    0x1084000802500f1481c00c0404180000140100032529501640d0655800d0107103685100902c81801421840d500588520050040820b017442001c2e040c1c41d84002c2203801444081d465002010038190b402551107aa1a11108017180c0100b05040040200341c00a0001380e41241078503445803000e01c50320003402480245080488401c0c000c07203290760008402e4507280d0421004d04424040d0a020300c0c1001880c003008140030340741003295420520f0303000003500c0f14541441007030f11055264801194100ea2a44030820041e81d600302e881e03206440c1203100e80801d529015010f100c0003c0946480101980040722118649944ca08500310410704010503070f898965180481c5801035540d00c400381d00300c040b000810a15404a100050130701c5100084413503150f206000e03031280c4036920400c200c943c000d1003031a42d1400c158001d40c1301194060140c0e001c00700000d0b03590098400c0e2a00c00100140d00c40200000003a80c00d000341e420151a00c001c0140581000001e4400b041a050036062400c0000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 798326438 1250 798325188 798325201
    0x7120b0609060607060c03050105010f080f0c0c0a020a1223060a1a060d0b1f050d110c06070201060905010b09010206040f15110403150209031002070224130605091305 73
    0x4100c40d04c15034000070070170841c9070709a4001d00501e800c5c020140010f48659000e6141d501c11614035024013548247c2561944a41c0c4055145038418031358072089004108865000d0ba0350048014020100b07600602d00d031180d2031412045055140260301c5d0958032621006032120b80006807079903c56141e9070005070b07a410002c80050000c1428156503405080040c003116101c400c2c3e00000030050b03003138441d40c03500c80f601d121401c0c1c2c0c0010a50307207200041c0244032100c13002c0c07000d41044c0a02d101201c843d81c50000441111030411000719900c101603919030104100b0a441403007824018901154000c0c200401000001e484a00c041d001800e1440034800e402c05020b0719002c4007030b1244008000701f181d204012503440c10b42d0814482612960114040300d4100509402200c1003060018050f01100041c3c0300c20500941020b43e087c0e82044418014208140840410b0a1030340e40c00c840c0c0c240c030303090031208681c910304d00e54008104100c828002d08150741c80720107031380f0341035602c02d600801d07180c1d2040e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 798327688 1250 798326438 798326449
    0xc03050307121d010b031b042307200c0f210106120516050109180f0c0801080c01110c060d0b060315130c0206161b050f07120b060906 59
    0x4821403801603d00524145201c0000c0c2c0341d03004400e400c9000344050140c0104041c1c07105191998040c070a8032500c14800d05141c59804650303e041240d203104410001c5a81500d0306000448120010400c1408040200741c682e0181080c61640308000304008006035001c254a500300e400701d13074000c0c10341e00c44088258500c7c50b0702d41c2600310100001c0003542d0b039070131a04021142052056540b40104640c1042004441c103000c1d080c0c4a040c0c4480d44d40d10b140c0a08003034150b9005c4201941945c1c0c03101c658041d110203010b40507451340d0a0342e0324405541003d144038146080b6050650601002559040507420045403070f5000440448045850380c2107811303030602600a4040559020000004101d0030446250044400c100160303140c41100384007001e50030440301e400750b140703002d6405040080c0044079030103a074100c0d458140c80e1003038904001400c0a2489a07800354101c1c1c0079000040300c2512520100300782c50040100e40041d00c040c101c0c544401402400250010380a5412200000c0039034179032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 798328938 1250 798327688 798327707
    0x405150901120f0b0a170706141902161d07030b0105091f030e070b070204022503170705040e1b0705030318010b0d0b0f06030c06161509030c03050307 66
    0xc10b8003441000c421007950001000103042e103038840c240400010070100c12a404158a03070100400404c855410070340241c0718080090142e5101100801c821020401b18161044021802e6002415401c582c031440c1c80d407851041c0c01804040b0b008041032070880d60301d48115a04822141000505440300380f00498040c03007803a0003d03410007032891908402c0d00e0300150001c00e0b401140d40030418807111844040d16a41e680c0700e4408507080500050001d450254010302c10600c4500f1202003000d401d00032300300070154080c01603010520000e50040a015048011a8001c205183c128506030820900c462013000c040c00c4100c151964074141c0503d00c80190841f80b600e50020203c03a01d0385008136004400b00c5414640c060305500b009a0344105050851090100f00d5005028010564420040b4104180010b00e42ca525200302c0c41100d0054407444000d280c109403228000200c0ca2260a0007044c2800700e00864140624140c00e43e004a0b600040d142e13030850f85407038220756a480d82203049420301c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 798330188 1250 798328938 798328967
    0xd0606081303270b07210507030c1205040306060e090c040b010912050114010e01081203060f0105090406050411130f05010c0212010b27060d080306040b03030403060c050c120405150901 81
    0x4050307060280310304818018a003000c840d100c2a46c500401114280641240100404c0342102c02d040060307582c5598000004c903510b0014181682d03900c0b0541690103c2e400044044845400d225400748244902040d146080e00d05001e00041200000c0002400b885032075040b50030703c42580304100f82074102806a410748564103229584440307005007198800e00c51381026220b0011081c1c1b1900003039040d00d104410040a0034407641c0820015681a4030022805070712550b0b600e00440d6a94991042d142101b0159060310786900c044503286903a1441508802d00e15410820b003002260b03440550407003025410340e0b44034044407074284098090b00500d80c002d5800180540941e0a03000c0d007540009100420706d4503100d00d9240d00c4148440311640c2140507080c0e003070400006155083ca90096240340c030000d4122850955241c43c1c140480d400216060300240c80001d10341001e0404200100720729080b05182c9151918000c006030305207110a00c001c030b15000219115006078098502c40c0550035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 798331438 1250 798330188 798330209
    0x2070503120108060a0c0207060804020d060906050a140408090105070f0c03151a0d02370e01150804320f0717031b0703080d060608130327 61
    0x288165003070000800309009594052140d84001280c4d14490f001d0145032413419005000e516003000c00c12104440018070070380c2c11400c40c4045c1400510701c0c1c8240550715000b80782c00561400c2c01c4191505803041c41d0144a4003840c41c90a0001185800080301c074600001d082079a65080c4514061640d502cdd0424041c0a05489540020600009141c10034009900b0742d410840e801c0c001d200e0851685860505540010002c8425001428600c00c006249404a0b050b1101c40c585106850004028440b40310703a459116101008811218130380305014088034070b54800c036403000160003448624003c3c0080c0020502c0c2d45004181d24000001c00c04046c0070701d40000140322480403599903006039804410311480344480000d00d0007003440310628054418805076180040201e00b11642584c1c08400c00c1c40c070b010300e44000001800484c014070703141341819404141d071458078601404800c0010040400001d482c0e8020f000260302800880240300c0c182c0200c0010101240d03410140040c9400c82c11050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 798332688 1250 798331438 798331447
    0xf0a030206130501030b010c0f031110020c1b030f0619060510030507020f06090a0201050705011104150806010306031703040302010605100201150506070302061b09030106140906040605130c020102070503 89
    0x500d507150b091802c0e924203803000c0c0814140130300119440c01640c00b0191280c0700305c1c02c818000a10a810f40c2003451140720407941c0c04404036140c1c504036440000314a0040d884403d02d0204180360348020b490804084000e4110b81182014a03529041d00070b2a601c3c1640e041c1d100c8554540c0e0592001000c2c1c03130040d1000c21030304240c900c00380040100350f03107001c054440d440c0740d64507598000400d903100d04450b50280c144152158011348858104841c1110130b5525486100741001d00500940000c102c00840414040c49a900c080e001110181802c1d04040c01c0c0401440410030184a103c0c030074000744d240960740d07611410308030b0040c01700342c00c20365010014103e1240034984c150411802d1049000201030241c1d96082005040d1268000040140e00003200041e1001079890001403410110034000345400300c500002030844445d03410100c80064071000060280c01e000140d0b030340c040c10a030340410185040c80c0004414071001030980e10340e10784031788035031100910039010b90315400d50000880b07444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 798333938 1250 798332688 798332707
    0xd050307090e27061026010c1707030e0318060c10150b03090c240715050901020715020c0a0c0905180619110f120106110d0801050f0a030206 62
    0x102c081220340e260704440e407243d084112030000b00f00903005184920b06001910b180030869140c0d0580e1420910090540c01c8100c1064802800f841e0f1001401c0d6070350f40a8600004a07924100ca405410041054907244c0410100703c2c00000320362010541d00190301e50010740400242141c42400120034184c02810305414980c25a0b4104030f0072940b10040d0080031a0f00c900c2140c81d035000464000826600903400c40c0071508201c2c41810400e000354400a84c03040515215148a5002c5041101c4c4001c0304410040c04051601c5400d4000300480020362501c90a0340300c950f0f04000c3c0f180c000080315400200c2d000b514204000c0245007540c4141c0c04401699038102c0d180041200326410041107141c2102d0b011003501c04980148142c0c030f10302494403c001c00854170401850303d4128403e0844040010758200c191300c45c0503155008440900c56410b60401c040201300c1d8180300c80141d182d40c070562503440502c0d08110b409055038411743d0074034074100040000030800112580003139008030f000101c2c01e00707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 798335188 1250 798333938 798333961
    0xf070e210d030510150503060d17040305030703030c03050c271002010902090601181a160b0921180d08040305070608061c020409020f27010509010303020d050307090e 73
    0x800c0101d03a214004440d81e030b6480f040345e0705d0014002d50016400300002142c1e46041d8034822507590003040700110031295142c4100f49507200d40c105a46551020601504144e498041d101480200d49402d04c0b4230b0078113000c0f4581e02d00520071400700f15002003490600800c0d84080758108618000e004a1310344441c028081d0092800c1581640500c0c0c400c00055030950095007110004508444a245506d00d450300010b00c04110020240060804200f10700400b400d4050780d0784e640d03000300181180c03402c01c2c407441e529007442d681e0100c40101e01c12902c2c40410102e03d00340e81c10640000c156000c1c20320507200081c400c9071290402828200c01107000701c01d00c4000a454030540307030b40d42c8582c00640c580e0000c01015402d1240000c1442c18801054001402c140d04079464443c40a40900110f10740c0000182002e109422056000000b5030b80d4007200f1f0000c030b81940d00400c0203a07089804e03541142c800039221202512403a040c010000080b8088034400d440f5000142034a020444103800c0407142182c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 798336438 1250 798335188 798335191
    0x2130b28030c0e2809080310170a02030d03090204060302120304031505060d03050a170a050901060905091507090f03030503060907020d0f0e040f0e07030203060f070e210d0305 77
    0x48030940c61420200308103044644070f501850702d0421914210950901c071025054085181c40101da4403440c1507400501c040d4061801120030448000c0c420f42801d03d0f03102c8427460007180310031075408200c6c580d0241e10041440720a0899625000ca03a009184c00450050715496100a4000712115a00386035184088098026240b01c0c01d41804802c2c2101c038a40150b840c00d58006900940007610030000070302910042c90044114103242820007100080950466421200b20403055211003c100c5421800e01c500d00c083e1400c80310030003050400355110740e0b84034070281500d00103070003a4011510031801080c001006142090340808140d49030300d0028690317041034070418000d0f0f0703420b00414146400880e0703501c000c002a075910341c15a80d407400c084031481e01c0d88100307076001590340c60001015103442c000c490741c00125a004200c1c0c1c91a61051507c0c212004210032080e041400600c00ca0300d44c807021040e4250b2040f01c14189101084071041c000e9031420352003540c907104000f85040419055000207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 798337688 1250 798336438 798336443
    0x3210020c061308040902030403030608060411030105071b0f0f02030f0102180105090315150a0902031f030206040e0a02090604080a1a091002070609050102130f050d02130b2803 77
    0x1641140c4480c007100b00b03190440600200081c42c00d000501050072a80d014591050080c07030040f50701c2da0707a402c501d8104171050300c003541c213541e400b5a8000c15040074003410703801205610b0000d00e030130660b518000180c284d851f002020003150344180000d001c2c6440c00c40d64899001005c0e50501a20b240f5801d0003544080c2132844081a135030690304203580a01c082e1460050041e01800c18a41d08910200c0d640c100101511910700e0180c0c0b090030580c03a02c4100102401010300c00603900d040c415008009118054003510b000d128048080c40103031aa60180e508503003290908918070b88401800502a004503980c0c1e980050011500142d90500000c00301c0315a40100e224800f0001143c0d4006180c540855030403a243d0310103403915859034001c1c0c1c01001107501440002a400116580381426032780000c903001d8280102d06d0090021302d500d0a4441d0007400201ca030580c41d500303198041404202030303401c80c68190f640c443d82c0c4601e07501c1c0c2c0030361050300340400110100304c5550004034103c200030a0005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 798338938 1250 798337688 798337693
    0x303091518010207060c12020f0f1006052403070909020f0306040f0504081608070c060915030b2214190b0402040503120a11012c0a3210020c 62
    0x44460b5002107111419603255650b81ea0a202580c1c84e402c40408040f01000114401c58030464007842c1c043c42001280008034019081d600079011202c0b080c2c0e8525000280b05404c0005440b441c03052070702008240c441c042100e142c030383d540e580064454140a034409040180002000d070184900140103620480d001c131820400c002c1c02000f0001101c0c0125801800b1072010401001d441c2601d4069146540c4125a1280f804489640b0895107000c00d13408100805d8000005103c0c0042e205501111002c003460100120b18041d000a9281401000d41d542d0748100300454000c1c08000b80c01015912185074000301c12420000c80c043c411072003020382c80c150b40d8501015a00c4a01e000c1c0200c0e01107900c01001405d20601001844800350f004003605018412400c03ca00340c4c008083c09480c411b1000354005c4000e200700c607000d0070314003024601040a9508020360321800160030242c050603032a00700035410702070150400b00ea801d9895500c031b803628601c40d022400351000ea8940052004462080c10f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 798340188 1250 798338938 798338977
    0xc16050718020711040b032104030515190f020702190e10030c051203130609030c06090b12060f2d0409050a080715050f09070b04150e03030915 63
    0x4246049010f0488000c00c07070303c942c0f45010003901d003640148945a01c000e0035101c00d5858200202815040628001200c20303020804000307000c8180458041e601c1c00030502c081500e404005000300d411006c4600800c40d0391810b03008002680c0b641503c113443d43c0030700400c180381c0d10004802801542881034a00c0403890030005200001c07005544011641e220241010503810101007000c0340084078111a02440184114204103900320540002090345444411045081d4100302e41e0841d0950080b00601403050000c104c440e828004032040e10100d44c006a0907500c41000041d18804251421a889020a150400780c40c5940000f80040b1500c0b02d100c03440f51842509001c141e03000b260001d8456088285000c0110720f4010082c07011340d100e681c0d6140c2c603141c848080c0086950a8035484070418403001005040501041214040e0901007022810a4a40040068014601002c0100f04044040c41c04202d44040050b00d0b5001c200415100140c050301700b403040260061407200d2110380e52440e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 798341438 1250 798340188 798340229
    0xf1d0a060602030a0c05030d02040b0304050616081302010917010f0608070302010507240f09030807030902150d0e01020f09030d0e03070501210c0e0f0f0609090c160507 74
    0x3003804219042a009142014281242500d00c10410301042c0e8960000304901b1031b1328038061000307002a06100c40d880c0d849082c40c0c14414542400104881d05285034405c580c41340c50f4000c2c4800b58001800b004074414207603540f0040342c2c100c040e6802650900700c0404d00014420041d00302ca12900c940200802400303546034465139444c5c500d4031020f07000c40c0c42084035002040c040b2001c000a000131021447d10a0440c0c40074804031038040800c030601c51391780c5024208140e8002100e1741c1158031841c051140145030380028040c50940c412900e65a00d00244500c84041710b42c004e4010f03942964000c42d11116891903a600c103511207000c0510034081c21020028175030041c02418003020000e00200f215905203001504e106128010300f0f20034262404032545285441d00502c00840440da45410012001c0014460045031f4400c02c41c0c8140d40f2a00b0303110305500c0b0101916202641180e11810036200c0c200342da1a40d1103640c9000f81200e6507803040c24144000050b85104441ea00c020201911045c00e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 798342688 1250 798341438 798341441
    0x50405040c1e030b0102030c070b04090c2c010c020d06150b13090209060702040c170a020c1005070e10020f1204050d060b060405100c050f191b0f1d0a 66
    0xa42c20180c46669452250641442a8003428542d00e041c0100c0386010f2400c040b0300d19219681d071040324407400c001014070269480d03004003540d10405003001504505c08018000760801e1240d680f100e44011800001c400d42e00c01c0c56109d0483d5005043d2200011032402d0441c0500108501351603410142080040c002d0803140c2101c03603991084501007125403d01d110304c00a580911010303980101c0c00e00820340580d480344143c4442002c240c6606000b0301c001e101e05c0c01c0c6103800800035918640705011502d0000c0000c00e40d40c210710080880020a0f41c1c0e048001e0320810550706500f0340200ca8040300411007600060030004440d0360304c0440305800001601c802c09880f641c020700c0d03001180d442008000481c50342140c2c05000000f4003240c02e06840e03801091207502450480720020310150603480902c8001e00412086c3d5050402400c0f0718410810805044d421a41e4018000103110a2408050070360b10341100103811400680c5100702d40e181000c94100c0c1d10320040c1900d01807550041500007000c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 798343938 1250 798342688 798342707
    0x150806090f0a031124060901080d0212090607170304140313180e0f07090f0504080a1107031e060b011e03020f0c03190f020111030a050402130c050405040c 68
    0x71000305107100140c0e608070b52641c1c18060b541c02900c40c4000c185000c0030080940482c20200d8580c542080ca000c000700409650180c0c0301041903080444941007041d408107108401850380c009059071200c0950201c0c0c03007445251400b0349411510300d01001100c055000a41c00360740104050000c0c040c4101c0010317181d104e1243e2020311034800100070010054200e03040c001c410110503000400c0240001814202040d403482054903800401041c0300d40201c030f125613226481c1c0c030300341005549010381d1070341c44900c1869211418011340d43c01a460300c2d4020070551024561010b884011141102540c3d24a000942401c43d0701a08102523205254407071511100c04440011101c1119043d48405800940c8491905219034008002e28001c0d0038042000f400d03041c80c0c0c01c40705c5030341c2c2c030801c040181819000b990150459060406980342c0550090503686c1010a024000540d07490320310005000740c20303500711f0340f041c80d04041140c0c01c2c094015001d8400c032142500c0601045103c0b64046031210039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 798345188 1250 798343938 798343963
    0x9060905030d120f0e0f0f12040b0708300a0207020906060d02090409121115010621050f0406050915160318050a11010504080c040f0f15080609 63
    0x1081e0040b07550300340b04a0364103450751a01e01000a0380500d0342c81d40f40548514482c1e2240d541e000750255440c610301044420a03401306503006e13160300da0780504050002c0c815445030f815600c4020510606206102d000c40384080040010450701c20300a22640c110984182c40004005c054280061191440307802107420303580c3d00801c0c0c0304180d62908200240b075000107020000d070755400e1115001a468604c94800980d0140c3d40c01c20001a0100c0000c005403a0b0645103549504502d58644008034601e4400341510450b09084075130030312041600050f4180f0300b0404003000c0c101000d000500003800b92590007940240e03c140416600c2d0303482d079541d600c045020036414200d148001031055030030110034066084281b80104039289000d81e00215408160740035105504098081d00800001c851003c9140000f82000303802d0504d03121040c0d85038030265030b041c0c0c0100e03141c400342007015075240d10184c03c4030f01c400e41c100060110307405a5440c80c80207005034140c07481010f02185160500240b00d050700b29 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 798346438 1250 798345188 798345193
    0xa060c02011b140d030e06090a03090e1f0905070201060b0a021218041b031b0e0607051e070302010912210e0301090305070b160824040f06060906090503 67
    0x1044400d41c20100880e0380300c1500c845112040c09510340509000755141409a990041116a203020301b40e8203113500680501d00603802420103000090700f1a05c1081214404042046241d480d05064001c14611a400104055156001042100300c941c0014001c1600c1c0d802003000c243c5035425100c031842103180900160b407001211107115412400180b07424402c2c0c00740d030710301060501c0104055070308489045526100f00c00800710819854800e21000702d0800840c00c122110104001e0102071102e807000c0d005103000245c400501c40204401d4118140880c5100c10070103200030560384900d41c0b804200d0006260610018110f1140d030001c071005600306030308421040c40403428107038060b043c3d80048240160003050034061782e0203100780e800140c0240c880030f0740d030001480c0c615070301000101607041c10090000e2070050542c1c4007070000c0d03200f0304200c00101a10100400705030040c0c190f280a941c000d040c40d4040a245085401c410125030b444e480704220103883d0391007501c00c030400d401600d4050303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 798347688 1250 798346438 798346457
    0x3230c090607141203010302090f07050910030e0a051c05090603010501050c0a0b010902071703090a02040e0f0a06092d08030406061e15111506031212060a060c0201 72
    0x10700c0c05000504002d40301d400b10820403c440c0c900503003041e003503104d812014003000c4010021340c1454818a80e00802081540c2d129182558000e0321034007070203114901545d0b1001c00031158601a520044403482c031001203a0040216280c07490b907503140085090050107455800e80025030041d0291107030ac900040c4150709580c01c05c1e00448007034105100845280c072444c84c1502c0461540b00c100c90207840d8400d00940e5411003805d0008055100c1005460b1201d8200100320040e5008910301d0382d1079a041f0340c045082004040303a10310700102d0b03075440201401842e0801040007629402280c1c614031403441085402c000c0c8a200c240d1601042200c0100c18074040c0f9900098082030066034014494280019001c1e2240d541d102c0a503c80182c1c0f030243e0004050500400c03ca03680a40120640b0b841c1034400c60907100f82e41921040102c2401d503400242030003080c0c49503014042c1030015840741031181d84408c101c4c81600c8183d481500d401d40250005a800b0a4080c802d036402c400070764060316588000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 798348938 1250 798347688 798347707
    0x1902042405061e030a050105031209061c2c0705030115090c1e120506100c23120406090e0c0a0f020705040c030c030f0e060408030a0f020a03230c 64
    0xa07a40325543c02e003121040c1a4800310901d10200185000f5203040b0000904d540c107007400d00d031925900c1405c108450b02e0510800109940e468216500c4144a46006150203500b11181d005032031070103011800341415041c0c04074124035003042c09141b64a001c0464170080ea940081c542201e401c15246541c0301e00640d018011514190810071481303440e854051540005103001c1040142202440000918070f0701c45604008801c1c06030344c1d0003900c00c40d0300200112072a00c006e8601544030b4802014242c090381007403071500540040004444001d07095034225003c041c0500c00e582c2c0107004030000728402040200f40108a404110320510302c40d86d109181c940d81003001e4402805103000a07085119001004c07400303444034000c480e44c0081c544c41c0401d5150460380058140c95000310744108251030801441203070040007a86c2078101c0d411900480d500e84035200104040c1540b4100c210f5058000103100c81e80c0c0d03515a006e00001c40c03844041d840c42000a041e94020170509641c0d00303408a4061180703085 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 798350188 1250 798348938 798348949
    0xb0d11161b051e130b030304140a15030605030f01020313061d10020a0f0503060d06050c071406061e0f01081008070306020307030b01020a0302031e09031902042405 72
    0x895400d11070304200200c1d07440001400000c022410315a041005860301092410208600c00c0d084807044001e20040c44100003080e40c1e8003039031181c000c824a0750107625549445003000d85026001c2103030716541c1c4010031080580900418070130503000348940720218040700818400e43e4054914243e0058440c200e640301c4070701038420030342c4001407202100d50207400c984080001d2412100040700244e19000710140161144110340c501d1070038003170100104460703507030340c039155500035640b040d00000c035900e40306480703441c80c001c0d607800414010000050b94044600040d21510845003198001e001c60310001c40803041d04800080a070700300514094001c015030041161991003071000222030384081d90340c840b1600e042e0240d0300a0f80c42c9030303001090000541d414080c0b81030314038082c0001c102c0f580d10f40ea402540e9120f02044400d40d507485000200600d03181c0e00848500203002001c4030b28500c036850f00d0104c203801c0350904030712a52401c900c440c08001c401041712a0094000101001c80d89404240603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 798351438 1250 798350188 798350213
    0x140d0507061a0d060f0b0109081504050309090c04090606051206210a0b010302100f02060c0c3301060801050a050405090a0f0c0f0501020303040b06061605070b0d1116 73
    0x1e9007642d82400308203940350004002e040d6401014041100d00300e400650041328007800e141c5040000403035081c0412100001c03981240d10440c8508a0180d0b82d40c10150b0940c082d00d80130a512444403000d000d40c2080d4540a00161586a40c082000c80c4e510701060b1658420460110000b1862000181280c6400380e0040c00e1084040003010a09604410407400c005425908a4481c28000014402e6081c0080f580f048560107060501d0071411094010350342d80e0008248070f103810800a0600030f000b0040c13102280b403d03c59507000ca00f181c90000b0100f08210369800d0039101f40c01120001030014815004a4125000513120315000307820002171001074680200b450341240f0440d440c9000041000450b58101401210343c1c038030160802401c85140e1a0356407115046500a10610002c240e0251400781c202d0070495409903212010b484410380100c20000140030341c0120a40016901d8200703000300040350805d4410003192107180c034080598003506400d2803079900c07800074000c00600c040c0c2043d07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 798352688 1250 798351438 798351461
    0x10140606160c0b0c1501050d0212160608041509080d0c020102040b03011d0a05060901060f110f0c1011030307030c090905090d0f0201020a020606012712140d050706 72
    0x9001e2100da6442d0051094543d600c650915140040d032034080742c0c1c00b40705505402e00801d403085065490980000ca4584207940064814244443c0c403802c139000400c42c2c0c804c000340d0350103400c43e910fa4411f80508884030440d41502c6018444c1d8010001030070600c1030b441e4041e440004203042407002c94408000746960340c00c800556600300004108592208051030003000316402400e141158500301e8400003202409a0780711a0820f014002030b03603a003401240c1900e080f071504030071008180c10100e41c0c81c007100d9070030402c50050307854082041402043c045403203a0b068481400a4181c40d00c12240d024207216040c00d60b800c2840840c565a200f0b8012005100304ca240c0b0701c03812510b030800079046580c117a894401c0c2f98403491450881d550041815211540540000c50030050302d454042d440342e10040c1a04d04203c218404a01024005441035002440d03841800020075287d01001c80b0000c440803060b50300050f0350b00e82c0c3c440c041d0700180f10703501409550740307150902d92155a000060301313000f00e00c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 798353938 1250 798352688 798352717
    0x90403031a03061801061d0c071118010504050105150301090f02040b30010b1204080c07030b040b01080a15090201030f050f07030605030106230301150b0a0210140606 73
    0x15074080c0c2c0d0030403290b8050070307518001c41d5003803410007419800c4600703d40c0070304490a08035030940406010029a507600420b503030111507070703405d40d454884c105800c480c144c154026907000c0207000c04954484414160782041d44c0030403040c2d8a40c4200041e0160f400c0c100a1100303420801846103800d140c0080110340006180541415203035400c800d81500644007102c0e464004001180a424561000a24070411944003c20355410489100120711907000d0b100204a508400f290812080e00202c400488401c01503a110b10703220b140c0707031035a0002554151072140203600041130412000c98044107056202c50340b40000c01c08071081c80c0242030020700590602d5502d07480c841440c9050701655210b1030006042c0d00301c9103040640079086078080d800081c0660316084e81803004101184180421101c203500740301205004200080c09001c490b500701c060308000800010345002904054201500781c0d07020307241d441c0042c28550301100c0c012009c00d03111341c442002080e01070600c6001800b004d56504103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 798355188 1250 798353938 798353981
    0x10506091905120d0801060804020f09130606080a0201120e06070f0c0218090d03110a05091207030b0f09011a1201200301060207090204260712061b020c09040303 71
    0x4003101c00e030f030708071079000c2d00180703400d010302c981c0f0141e0b60b8098101401e10803200d00703158010640321103000c04610300a20700c1c1070104810400b0303c105403c00d41d61010050100350b488401c0710341c1b41c0700508800c0780802e0b0203240000101c1d2150180c80c594040250003040180d694600c101c80a2800d140042d041c0b010703041016000d40c54841c0b0040300b0040b05c2c994800c01c4c0c10000c50840c039008104000c00100361074aa250300c810740910048070b06a0080e0301e0038a0b1595071b148001651075901044801c4944a1755000000b0856504149440f541408510440035070f11404000c2c203a030b006020000301c0786000340102c00180313040c0308001c5e1201280c0000040002c1d40d0f400700528090854103008210502100401c0700960400424001d00007460055050514110f012112040406842040282041c40c1100056810880c0e00f00802958004200904d00d9080090003006000700798a00d0140c0400c64000c113a0000403400b110300d00140c94000f80e0b564940f0110001e006c0d80003c403805107007010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 798356438 1250 798355188 798355199
    0x2040903050d140f0702150103030315050d06050603150c0a080411131506020f030d0209030a0f030c1a0f181c080f070318080c010f0501060e0301140105060919 70
    0x125100b40d0b407660142c504040e0030001812041d220300103105c03600f1075001201400c42e03241e501110b9030440c0e515040c0424031110b403d08a1402c48065004a900100c61031851000d010031070f00014080d42054060b40c2c940e030a1180300d06c403115001c641200b03002004002071311589100350340303a41d807041c020881072189140203000199480340007054803408a454004044103403401090fa48000c107014001000e041c80035108458690090007800300a283e4003040d0800395031014055070300900d0b8801d087c14004150b034070b000f405120480409648414804059180c86a10f5903000380c0150340302401c03a6619961010710100319040004c044103507024194140a00e0001141e10684011050f1a00c460750f191025100140792001440c0350201810013044c41c9203441c003061100082c80d0003050240d40ca00c61600094007400c900031038407001d145028000680b0380d03440002e814141404400a00600000c070005180203402809060752116013089403004034901256080840381091005034500396581 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 798357688 1250 798356438 798356441
    0xd08150a05031b04020d090602090a0902090d0605100824070906050f090d0519110402090f01080c12070305040203010c08010b040528080303040203330a14090d03060f05090402040903050d 82
    0x703d00c02c40780e23503401040c0da0314036181c0890104090401080118200081c100005c0d04801c00b1440c01f804850742c4802080848008101100140428104071100c000d51188541d0025000c420324442c0c0c840f0710008507901520400c405421605581e41e442e090a583c6603a007521980400307451a4844119084035001490502211401d4035080c41c0b09450031030141084c07048448108402442a40304011003209650b80040000f268030081c640b6040f9a9582d14034050184140908000e110141c8020400240d9254002034407840c4241c00a1080001900c0203803120402801554440d040501091080d414120b00da001c0c14010001168105440e1500e042094581e64120b00426000003041009500342003003070b902214295102158a520712304186494840000740c00d02c000b80340b802c0030584481c15608003010ba01c83e82c0000391100d0426480d410360319071018a20310007081c109000000e84c800d821006804442000e40640035655075642000020100d000045043c014244000544c0d6400c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 798358938 1250 798357688 798357701
    0x60a0218040c030506100e091305100e0c0a0e04111c0804030503040321080f07050d0e0d0305090c01120207051203150913120309020109080d08150a05031b04020d 71
    0x40783c800040d5030500303209212800c0d680224600501c18410010324050b00e44071040340d844214941e17046a41407031850b00038140341e020440001d202d4140440304246040c00b04603001400d104440302c3d0701c4195a18030001c20610206c4010300744900082c1d0780388090074020002c0031041c0180e40340114190865864101640040e0010750b060f40c008641401049900c034032001408147c601c0e05025a02c035400010f01c20000209075072080703004403010618041c0950250b48030078540c481c003408000d50801000790355013141031808000900300303404540070400103d02203070520700c10303514801a04205600480a503203d440d08032124420604859000c1d488500070354010389003120103002401e4000100000300ca406014905090111044030002507480307a012180c1c58120b01780480c1c01e120500060322014090340c4203403498050400b120103c6c950000a50b4412024401d12607049002841440012180c0c1d006072070301a409800c2c4810b280020905504090308000c1c80549400384501c541026284e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798360188 1250 798358938 798358961
    0xf0918030a03061a040513110d06140310050106020d080421120c03020f03010509090a080417100902060a081b07240b090613140c070c0e060102060a021804 68
    0xd0f141d40502240c0b0008040120341c04101007240d04003401e18001070b00e17001c0344507800300c00607584d1020f10050203140003c2d150504c20384441080120740d1050b006403d5407000200c02c1c800d01480e075020b8600c00562241d541030320a6580244404c0070410420703500e40e04003800c1903c1e8190342454080c2c50050b002c0c00b00e9060821941c0c0d00c0d132480007055501c810b5400303000b0018180b5005001d007011900c01c0b00182c0f070444400715807410303081c1c641903034090412014040250814200103400304501404c80b40300748a904000b41111082c480380c01c1080c0c200c40504900a5022504100d81c0580a2103690b605d41c0041c680345a0908000a07101109009e501c103107021551481c2c4080c0f0051214032541c0034600a500000041c0300c036040200c0059a507020081c81b984c4140826004410040803e5220500707801407041c0d10315441c104203a01c07045a8101100071614180e041002280c070012442145000c0d440c103030010a82034503090512800b9400a80f48a0b07520f2071700c18001c0300030b543d540c02100001c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798361438 1250 798360188 798360191
    0x905030d090c060914040b06070209040605190e060c030903131814330a0f08060c0f030408090409120c050c0102010209030712030509090103210e0f0918030a03 70
    0x7507540c905070511401c0c1e03601660034000d2aa07403c108100307102110500a041c01c42e40080c44c070300d0400c001100c03401240760294009070345604010812540d0390195004042900e0040c455a018500c1700c1c06640020101d800240c0184022030101c2040780c001e140c01444000540f41494042a8900996240c0c0d070302200443e414070700300903249001441107604040c4040e441090600c2c0c5001c025071a012400b151032131310300c9080c003841b10b100c8824020070401e140081246404541d615140c03492030800b40541d00c401e010b20808074481c88030920440b20000c6100358a0b504641e542c0d207812400760810702c2c905130429151031003400010101c400d0f1104134002078449000b08441c43c1001d51400540c08103041c1036a104100b554081d59000a124040b240141039140384400340d032904495a0003154201c0b504a0003450010007003102d18400047e440081e000c40c035840e00110401140c1030002140000d810555128100710346051510310940e0110709503004809503991320002602d180e0009180c1d80019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798362688 1250 798361438 798361451
    0x1c0311070818040c0c0b04020604260d0315030809030a1227180908091f030f06060915111207060605060c0d0513050a0902040302090a050405030a030207060905030d 72
    0xd200c1003804041e004143d80400011311483d4020348100c1c4a980080c000005640010f01150b0b10704d0212000351200c01000f02c0342c1e0000540c0000b480034201c0b07030b5540502404600c0c80010b48244149420141c00210210300f80b071841d1038482e090b900c1040f2168040c080d001c1c6500101e00260b86040c2c040040e1703070312440b202040c81000070490100e82002e01d9036034900d420401841c41902c60a000600d612240020302e01c64516040886115952040750845400c180c0321302d05982110320f442c090a1907817814411441003841d10000c4951030302441012401080c018071240007548034441500b41035080a00703101030303824a420b2901034049404084928002240000c00c000c038042c0314010002620417a06041601c245a51606410486602040f1020030b414071900400c5584a00520015080c40d88054035107042d14065441400f0a0b03000705921800b20321404820310506110301d421038060740c140000041c0450195120260603201907440340255800b2a00500c000d2060100010340013800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798363938 1250 798362688 798362707
    0x70c030315061409040222030311190f0303090606240c1a0601092111091509060a030206030115030c020a0b280509010e1605031c03110708 61
    0x9665580c8150342410015080810080b90000c80d01c000c500d00c3c07501c8441e191007203400454001d0160b03020051118036080d5000704500080090002641d00941c1c8000200000c005034542e10f080611241308801020002000800c03840080202c0c00b521034a00801c030030f016522103000781e805a40000c942100007181c2c904206405810a040260681c1000100c1e52110b8491300340d0303080d1809400007540304400000b80d1680c03207043d66101a1490845d40d1041007101224900810044501156400884005900c003840c00556161180110b1a4051080380544091110009015040382e8100f8003014001c00141e90300c1d070265010384001101010000c41000008066030524039507281075410090745500490440c0d0700040c2d100809042040758040c4040c0c01c0311100040c064440d01c2c2a1810042c0002039a064124080d6104a081120207603445103040c0403c003082c5200e83e59041d03015812040d0100b003006003c0c40110100c3c10300040c4001d04c4da0a454495000c40c004a80000002a0b296803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798365188 1250 798363938 798363941
    0x50906153d0306050f030c040e0a02220b09040f03030c0e04020f0c0c0603010302180c0d020d02090901080d170a150e0a1a0a06030e010b03100b0a0803132705070c0303 73
    0x20324007221710f01284e41188001c42d440345180c0e214103004948071101a4007000040100f446a2036024107403034510400d0b4400882801111005800e800e41010300cad10b0317058a400032000340201c0d0016044503c41819030b60660091a0850180091040c1e000802126541d10f00c040e02028245c114070a0b960a0000051400e00c1882440544a44414001030025803100d0003404040c8540200100c826201c1d580c408945000d0103104182541c00000c0c013200d880d1054004d4039018000b03450b030f40e03001d980310541162602110b507000c6000500c0c01c10200514072400f100707148c00c420740800004880e144845071086061103a000a0804480301082c00100310144c8070347c1035804400c90216528906480000e031007082548941820161105560040500300b07510a8078950002011140c01204648010019004403218a44540c0d1250760004100c080401150b18201c06100d1a6090a0070501d25070111301e4002409441d0300e107a003d42d080d02d21a00d11030f80780182e9040d15004880c01d01c6107002170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798366438 1250 798365188 798365201
    0x6070e03070e010602070320060f0c1507020c0118030804060f09092003041e150f02070f02270c1c1e23100504050906153d03 55
    0x2020700d0b528010045103501003241000d6980c0200601d4440746170101d20190982118880785d4442c500145450340c0c08030304402018505248415a60301504001700c0e1740103404103c1e03622001da003244500c09419841003208403000da500300005003d4907140d40707403401c0580080d0080000b040c08e507885880980c1c4c00105480081c40092014000d80503403201c5a013040150601314894000040041800c21030361880e02644c9500080181c45541d901d801c1007001c1d00701b013050307a84e80d20b4a05001e0541e0800280211100c20350072800350798034074400740d09209100701c640366641424005103246072010304a02c04000d004404009140741c40d0b20019040e80303100c04422681031680380c80c1000350744160f00b141190000c0d41011a030005456401c000d403601300c204100f8110107000f85441d08101780c440188480e6015644192030400c150b564585856550320816a01e000e13003a110000141c2e00c0349088010f088809030401d1014648213100c0c151060300103400d5048607031101449000140c1280e16102d0003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798367688 1250 798366438 798366449
    0x10b0306010605041509171501081603080c0a0807030305010501031104030f14030c0111070c060c05030d020a020c0a080a03121a1903080c07210b070f020f06070e0307 73
    0x38025949001c4000d006031280d8810021600d11204205405d140244410320041000141c900c00c0c01c02c0312604243c60b001c800300300542d8541202c002282202002407414030151180c1d00d619281411611519041c0c2c10200034401140f013054030010004004402520950384282c03004070b0b49504110014081c0e07012602007480c00700f4244410000320705440040c46503190000d2080c100343d5006422107045205071792400c801d070344c01c100c0d0401d1408104001010554003441041c120f40e0740b41d0310b04503518580b4510107001d951083c0181e040110050340102445549401251050b01c0200c0100b468094280e01240382034000110380800d042c1c2221131004030015245040042d5242e03d81c15540394102d208605024081c0384071101c800d03613a4841c03001c1c069030700a006151a6814503c60503500e003118020310007024200c25004803075000480301c5068560340500d09440d66071300d401c2c0440c0c0004d1001a003804501c10f1001c100b00000040c0314050040506070745224400300700400345464082c069020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798368938 1250 798367688 798367693
    0xa121104050f040308041406091b0f0f3129030d0f020a0203120a140705060105040c0507120e011409030a0f0203070f08010504030914030c12011e02030702010b03 71
    0x4001458540b01400da034032030341c58280032809480302e0405119444038103958428a20400b800e0111460000800303a400300c0d038401a803444e60350150184100c502c00d068115410400d5503016442174502241e40d08000700d20748030b00d0130140e141001e00038682c03101480c0781c0454a91720300300512042000032410410748000c1000304d10f072410742400700e55640b8400c2015000c01542c0070321072403254030900542010a030010200c605188520005810715400000948d001c141685035426190003100251011583c120b0f02400c0940e04c1c110070f210203850300000c50b07801c102080040c903002a00c420178521000140d035442c0301d81280004005030055000000d03000f186030040c80807207103940e8000b414201e0950710511891001c1d0039403020901c0e29003180c005000c000c030380c0c0d01c0200d0108015481240b2860081d030303c00003074940e50700034107030101c800d071400a41640250180c59807505022003006002c3d100c0b4800014030031101440120114110380b400d240054000050000c0c00768240a0711402040c00c502 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798370188 1250 798368938 798368941
    0x1a030a17030c0c10050106020c03070308040603052502010504060f021c11211b030403050306010c02151218070b03010311010909090b0702010f06050609011803020a12110405 76
    0x1500018818003020229001100000190038840303018195036040d007400e012619402001204200540824001c680061184030115866480c0001d240307000c0380c0d004600d00f40b41a044c900114041d2070002c002078040c000c1d410f40c000d41024420a442400e4409034000102800d040c87e0940580c1c58204945541e0340c0180700380c0e034610380403c04102a000401d02c00007031a00d401200c826a030300880c0c2034101c490b0300d49403001c80100c00005055118040d548150861580345c25400e4040d80020f6402030001441800000c0c40d95000d5001441c6140c0000d050300358071040312405148603444030100305a1400b0b540305004003a10200c20392251100c904010301821820302100042078041403002500c0c0100d01c048001050b4058000c020207010941c10500080c0c0141c1010401c080007540d0b40c5005600e80103c100317039110700744552801c1e500f004280516042e0380f6001103131a00164004800a80200100000140d40307281d11400200003c02414401c04910308181c89036181002c042c6000d68103140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798371438 1250 798370188 798370193
    0xc1811130b1e0714120f0702190b0c0706020c1014070609080f09030c03070608180106150306081204120807080d06270b0f0d1e061a030a 60
    0x112034056030159007031a511072040898144078030900040500300c84500042030800c0c072403090b0031407188800080807640002d00b10004000c43d48100598442880340c02e1100100500c3e15080007051701d1a400703420706184d61250b41e02d606541c020381c40e1172125072140d0002c10a44c1d40610110304c5004007140c868064402909000e8003410411182200c0a080081c44c10300308001a404074485540103100c998a0782c924106c08a49544450040c42c80381c450041c4007105860005608800c1c1c5005541d0403105403036410038180d01318840204210709549584002c5814501120142081301482d940412100d01e81420182440c0107031000072400c01007044103000030303940c0e10602400b45a010304400d94440300ba062604842c0034184800c0c1d0304500303240c0d0010303c40994440400c0600810b0043d401804d450f09044001c868440207025002412550310050310f01d8051000c0e00e0745800340910b5089400c0e681d111103148001114100e0b003071540c07920401100816014004041c2d0780c1680201412100794 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798372688 1250 798371438 798371467
    0xc0f0306040213111603020a0213051306050901091a011706090d201c1b0209040f0323030a1508032706071110080c0a050a0c0c1811 58
    0x49000c41e00040d2146140c038030151401c01114403003092060b40c071700d1341c00c8946002034640801c88000c0c0d1150858211159030071841307224a0f80a82c06900110842a41c141d8590008d410018141c401c55562205800041034103c00150321204499401c00751540c14019030006c0032120f103500407040d5009100b041286080081c000203243c450f81462000c4e01c0840e10340da201c1c03120b40c5180c25000c0c082c0703542440c4900701d0840712001d0b10441d6229000e2912a080021001203030b00000a54880104000f04003c600d1030910514410f01914001011180140106084880420490008000c00002c1010120751383c03003684400700f0024800c0689524107d00150341c1e008032442140402c010041401e2030050f00c0c041400000405080c440d1240d2180c01c01e000c5004c1007429040c01890f4400c15150105e100e081c2e91440b400c1000c0c1d0b01414508101800c035910b40201070b0400c180000324160002050300980352a00034043c6240600f212070020340684155642c1c1092799245410910090700706491b007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798373938 1250 798372688 798372709
    0x1e0a0203030a0e030432060f1c020f0307020703050c1903020105090a080609010603020a0b09010801120c0503010614030f01090201020735031908040305070204020d0b030607020c0f03060402 83
    0x8000100d2090b00d26034810382540310380c4c0c6c0099440341c009060f100c54101c49200144c89022243c00c0100343c88491400d0002510502d82d401104190801c655002070711020100c8a402c2810380005082c5034541d192840640e105070b0716480940d115490800803c1410403070600503640075140b540132141003485039605c80050b80802410301c000805c0d01c0e901e546804600500070300c810782c2111400d00b84140300300e0092841d40016801001c1c8600c01056460555049031011503041c0c0d40d419160b0700e8410f40d0650980b01c9003007200e400c01c82e0768001032030b070b03400340240809405506074010510400000b058601801e101d49030819034140840080542c0e008100d00b41210034131650301880e50600308001210500034002500c0704031845402000400000010349900c450002402d50000c40d0201c0c10346808a003100e000300012010042d5100504094012704901120300070049800b8501c0c01c0002c1c00d01c2c000b00c49031001079000c806440e0366450a5001e101e180350701540500b4079420950041a0316442 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798375188 1250 798373938 798373951
    0xf0c03061e081b0d0b010303090f0b0f040b0304030c0803040c06030f0513020f03150411010f0512010302060d0e1e0111040302010c110a08030708031006030507020a060528021e0a020303 81
    0x1040751011011340c44410111103855400300c0b48010540c2c42c0e207000380940c840350013442d40c00300c201c600100c0c410601d07408507800c00e412042c4090529240c0000200240e000a000300c0401c6501c1e1412800103c005020394020340c421910308162a04058004085418803429006618100010b004030b001418040d81e1900340c050755596003a280000203c3d240180d04507031686903914800401c000d00c40301151001c030310b0394246e07102c00840c068000c2c1140c03503000e0064000c550b11003007401040103180210050032020b464010204500d008510000c0c00c0c601e414011040380d40f84000d01b03048111081c41080040040c4001a03401c080c21750700000d2100c0340e6480c004041d14146c004928082d03030341c000100002c08014044036070300c0d008c620303040049800a940f00502403800b1034020440c1402809410320804d056030040014504a0711118040c0201406c004a9100e0144080340a040c80000b407000800c1d8110016070f64a01180d1800003580d01c10380c10f2129100e0a00945140550100482e0342009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798376438 1250 798375188 798375223
    0x2106060d0f0b0604150602100b01050403021005070c0312050a11010501080c090a02071403070317130312060504060803040f050603040803060907050408030a0306052404180f0c03061e08 81
    0x79a4400404e0043c81e4032892100640300107500022600c1d400254006501072640042c0180c0c0c1c2000010b507214000d5000084d8045604448503190900c140050843d09016100920ba00d07907498072051a9072800c4071682002410006181c045281c00440b150070505565000b00035030340c503010f10700d606da11442020510900300e01e8049a00103241c0c0d0152640c0d00d0b00b0191201d50b1803c0001e8450b0769070302c03105d000c50214514401010078650000081441545d61004e580682d00450f034089400d100c0d055080303082660f40313110100f0243c0340c5100b1903001d040c40c58021540c484c00d185050703c2c41c00d1107500080c070881d403c07c20040014140300550b600f001065402a420707072183c0005950901450701700d1561440b011940b41d8881e58544c203e4011101c041d200c011070a0f0315042c1239142d4503021101c100c41440c04010801c11001d03042c2d040c0d02e25a00b0b00c1c0340041c150014602410550b008106000006911160f09200710321480c0b07050700d0001005913102540628000b02540c56800c822141c41a50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798377688 1250 798376438 798376441
    0xf171006030905100e0d111603020f062205030f031303080901050c101d0f061501200a060612030906120b0603280e0303242106060d0f0b 60
    0xe070030401d41c0300d40740103500c4c184003c1c01d041c2d8070f01e40e446401c3c043e1440041c0340704a0302c0c036032841e010485c03c1c04c0361002e8548458003425902406443d007102807051350400020821400645004580c1c800c00541c10724041c41801d141404040c07400441e80d0070b10074150003c0114000b19030015003401e0480c2e41c072140250305d8129000c0161858061200c070341c2d07428060078080103103403003442c0d10004512040905040024120340b5850395114560000b10929030b004c0404100780d982c10b044035101e1030318140341ca404403c21214000403210208090103100d603010326810001c1164901515011700f08040064001c4d020701d4130000d2281e0f07014440e120038806141d880c001808416005005410341c080d000550b2420000382449070389030032114484850b0031640c83c28018001c075000301c0031b0b082c006070011825602c92090751100050680940710342e0040380c3d44401c840b503d42e18050307170700d00072401000b800c00c07450b1542d480d04103100142214490141140311070002001340c1890f2031990740250342038446 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798378938 1250 798377688 798377693
    0x8072a0f080f0403031706090a050907080d0e03061324060f1d0c0313150204150f080106080105181305010f092a12210f1710060309 58
    0x8622030315102a000c2200003940480c072a101400070402c480c400e80ea2005d2090700d0b80ba144010440c1982d45541c0120098082042d4464940280b500243c0740010f070380085030303201c51325840d00384c02c4034009011881c40c0900211518041c803020f5801450740701e02051072032841c0d4440c000141400e0050341c0143c008134500c09650004c0d4048000f416800c004803c2c0c682c1c49101651400c0116101c00c11b8540c640000280740f0f82c1d6080540b4018482c400141e00314425966522009000d148190701e00c0c0ca90034080098005e928501292410410341c0740c000d22407a400ca0f0050000c00160401000c2c03118042c0108201d48a0000c017103071030140260624007585640d1900d000e0711840c4c00b0f0140003903003801c0072811003060701d903c07503d21188200c4181101141d0039402c51403140c041640c0d241500140041008110600c014512103c0d1050100c1c104070b1030103083d803940c031036100225100064104408650400d030000385001075441041c9403070300c192800700400440d00b4014000d10b0304050b11441610304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798380188 1250 798378938 798378953
    0x303080c0a1814030d030b090a0c050c010513150c050a031a100207140301111204021c0c03020414161b06140919050c0103050c0403080c07030308072a 66
    0xb00000580000c0d40040d50b92003401c40081d801c408840c400e0140d185a9981c49009120307590300c415002e00034820551310000c00c1c0004001c2e01e0b1903482800400c00051201d10300a00c1101d118200801d05c050803400c0500704109a00381c0a0b10000d25245070850451409403c5030503140038002500c1c01050003070301000460803020000d841c254000810045890840b50040340c65400e4030015100f0500c1a01107200705803c0c0c540096000510810800118200d0480d0941c40e5500c14005000d082100e980f540e4094600030140c1001d45024410301c00c180114503260141d09140303696004c1042c1c0c5070500724541010f8880c2000d4800c14410070282d19274811035003030784034003003e074110070100068000c1c00100e0348a43e20440f442c12090248000310000081080700500c40d06400c18003c0001c0048200198000c220203482a540c120040c00300100203009103000f444845103140c05030000034607600d0050302c110b074090441c20a1040600107404000c48019654181c9070324104454003440c9542044203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798381294 1106 798380188 798380207
    0x50c01031503030e060304081201080f0d0302070209280e011a01050406050301140607080c0a200d20030601080a05120403080a230d0b01090e010303080c0a 68
    0x680c2d5017061400b555119200f44d60365840d04186d480310030701010007648000c5403540304410341214a44c060102010400b4182820360600301617a0001e0550f4030014070f240c1d44000b0135400707000342c50100844089007103402d1600300910210086190b020300003071007010655030600d240c1c0444a5201c3c82c1200c00f103520b83ea54070703030070f50b400c201c05540c0d841111025140e004174144000c2c4049521840100700200381d240c010f2121100074501844055211308a00c035503c14404440e40140c1c49151070070901682c070130201e880c1c0302c00000030f03004c1d142c1d43c0300081e03038140c4105400170401c10000a42c01340907500420403a01c06403601c42c035101ca00c1c0f050707000c001d02d49201070100d40c44040c004c0c202d1b0502c80b410200c00d8420814000051006034010041100c005901e80c00340500558006008401810418240240560454078003411642c40982640d03500c01c000203d0b40846880703080c0c1d02e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 798201438 798381294 := by
  have h0 := BRFrame.cov_init 798201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798201438 ≤ n) (h2 : n < 798381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
