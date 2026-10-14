-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:37.354976+00:00
-- url     : https://prove2.me/submissions/85e457ff-b7f8-4cbd-8b84-82aa74aa7283

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389748201 ≤ n < 389928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389749451 1250 389748201 389748211
    0x160b130b010602390919060501020a031209030302070b040308070207120218060109080d02030408060f012601090206030a0905070b13050909011506020601241e0e120d1403 75
    0x1842480a01d04204a07140c00f134a2405005500f90804d40165154404080c0c01a400c8000b0785102c0910341c003000342036074681c0e0070480c1190f0101818001103a804003454100210f02040014242c0d940e0400b1006482251304c040c140715420401c2c0000c041e484901103100305000c0d82998141912041d98011460f40240040d40c0b003001c19911042000600d14540e8212505050505480e41ea55038020f09010522100c2005600049400c1203100c2050015540c0a0704070b640e0b01800390b041c101c0c40b4803c101b1040a903c00d100c07400850341d00c4101c09600070a000c40c0c00501ca140c42e440e00003101ca014011b040030885090083c0100003550507146030603a0249900c9143c9492802d05000038840c0f038090081500e0141e64a4040c85400500200c9201c406091103602030525503042190700c1b1641001c41c118240c01881d06003075a2042039000f085101e015115981884d4011031002040f140c81e08804811540074000840810fa10080091601c543c0c0003030340c03150005d0711404a0102c03414041114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389750701 1250 389749451 389749483
    0x3040f150c0806091e090a03031a03030f130b1308011a0f0f0a051e0907020304030201020a0f08071a090f010510030210092102180417160b130b010602 66
    0x101d103652818030101548a905e554038a610103007040c0404240100c144c4032122541c200d00c3c8443d05142c2c2c036024424000d007a400c000900c0020603404240d5030301c291810780d001500041150540504100030070001041d56800c0c0517100c42d180c8034640c0b0a590f0718402c001d51036103024400c0e804c41405003441c0c1c400c0c41000f004461003111034000d2084940311007900507840004100041101da55503003004104010362988030200c1140b50090043c41800a0902030541d40300b44030800050381c1c0041c1100c1c501342c1c899103041662680c1e1030322040c14014040d00130000000c8215105540d10700b4a1141e104030f2012045548070b60204001130b088030343c141d0700100c08101c07291081c00981440007260600510710320b08100c21070350f241c81d50a036105103103007142c04604843c031040c004c2d881c164500002c0c0701058141c00442d801c10796200c59038105100503541a150021403880c007040e0b80c042a0012075071b008890030669107400501c517000e0030018641200d50403120800820214400510302000d4819030b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389751951 1250 389750701 389750717
    0x60301050f060415090e06040308060a03050a240903030f05100308120705071a070818030d110c03040b040f0b09012c10080601120c090b0d06030803040f150c 69
    0x301440061310f20102081c40952588800141d40d010324031a5555003400003001d8030480c202450000c0032005e0181002c0d03c41c0015090900100b440811040a02540580c1c160b12070042148561050300381401e82043d110300d000b4590040c150560842c2100300300e0312404012554074800044090901c0740401740072000140001400528621242c50f00043e007410314034103200c52583c0d01015092135000d0041492401e038103001100d034004000c640c0201c06440c2c0b48001c1039145501540c1e901036a83c0c40000d8944491010484801402c00c90700d45a08074001e41e0b0b500d54a0f64503007540b5911511605403c0b2151301c40020314000360304159400341c0700594034465070040c490858904002c0c2030342181007891812900d001c1a03035032256148200d02c0c4a40707902415203844800585000d10044220000c0c038200303403c440b041c5501400389415070b80d4480005440d000041c1000703006200c0d582004080010000038072042c000c140d5800031509203d0340d4000000d00352510204251818264010089213180c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389753201 1250 389751951 389751961
    0xf05010309150501031202121c051003020a0f0e060409020a030201050d0212041505090a33050c0403140a020f04110c0a1113050c07020d150204060e09060301050f 71
    0x790001200207004a02141d4100c1209004504031602a03004481440302c014680843d42c3d01401019200003a101c2403070305101e400400030480e0001a29003880c0e45a039030340022450000121001c0103503401070000d224142d242d601200e602d5025010f40302e0f2040300c010001e0b1140c07030035004520700550301812403000e5501d158010f4410f90803005041d0001030f000c3c41007030390749088401a60b100d28003500c40007005810300390510040b113071701401182d00ca400074139401001c521841006803c8061b055101502091400d5046200c40102c580280310142001c003440303600d041040261054a00448090b0103d0400003401070b03a6203400d68009410544803e440301080c9426800b05480b0a0b620351410318210341c0300102400d2048022007102c9000f084591208282440100d202100b03060320420891802c010111440500070000700900c1042100108420020104900c1198070380e9401c0554540e615100040c05210417040f0f0b49015007110740018040340b90500039680600e0179914011801c2e161 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389754451 1250 389753201 389753207
    0x6080303131407090f0f050a05151e090a060303021501030506070819020313030e0a0509041106130b0a031a10031a0a0b07060f0608030d0b0102150901020d060504060f0501 75
    0x407080041999005070740f8000380c0380d0b04500607a40070b2180c000340000e844610044040032a200038000308541031605040049160021214181c0d03110221214a102054010390401d803404e911100740d0088000014000f4081040c2c0114050301d2198003030740e80420176101010030f100002d102c098941d62102c0d010900841c01042c003e6000300085003441c01900000d65804107a9100f42e0b00080d000b07450141200500d5400b0300790f005208011980600c40c0f51518001982422000d08003501841c0c44049100441d61404100c41c100524419441e41195a80b201c2c1070702900151142030200f0308184503c00441d170345000c2050070b0280100408544190400d040b0020100198000f0360042501d0a10380c60b603642140480c000e015101c2d00940c1c400c41840c000b41610200e05042d8400d604259090006020120a8035100f80001100003411203034100101c0c6031124900230010051020400d02c9003c601c10f4000f01460314603440f080c40080c2d65613041c8400c035a06031184501c003c540f801c0520803988 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389755701 1250 389754451 389754473
    0x1615090f030e240d0608030c150c04080105040f05010506010201050708040f020a0b0408010c0e12070b0c100c1d030d020c01110106050301182607062c0f010608030313 73
    0x110150440e805850351a00b4a07410090b0307a0380c154070f01d14002c130b5180b4010005020300c0c0003400f1204043c1d41018020080c103a51610a440c4003002c100211001800012100f4103403801422544000d0045040c1400c1c2000e0001d03601006851a508020010315994014061580505460740d5800d02c1959280c071103d02050a04000301c0e4800001180003a000340e150001c0e10150201000000e4448103802003c4c04400200d4500783c003803814912582009003001c00c11604840c0041c00c0c0b2562031103800d038600d0420589080fa10590b600d403aa90001241e8400c9203201c10090445d01e80c21515070441c20542d84000c2a614a00140e011110b603140070351062041000d110301d40000422442e45403800a400d540400344501d01420301c03000310718180b0800c1c0c106101d264000f01030543c5112180d4124450b41c0c0300d081005044641c40d95031020401229113060040603904644400032814982c403415103900344070940894942c00d1040c007085c01017000c4100c0740500403481d40088008240d076181c07000c0203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389756951 1250 389755701 389755727
    0x60c090f04050a090203010911010216030804090b030f0a05010603060608030c060a0b21060601140a050706090f050613060507020304050d1b0b04121a07120506030c061615090f03 78
    0xf54a5440120061b01c09008681c0c0d124440e050060800c00d240000902d4945203884044075101a800e04002240e440e908440645681e000086003103030316500800c0c075108180d10400ca05103d0710030f82c8001d025040d030048064a1080c0004e005c41c95032a0703442e40d60b80c000c0070a00740d4ac036000000030400e400c0c101c0d8099503408101805028440f4054903040c00c906450340f80b1490960080020884290380c8600d00100e00008070340c849080c5042641d0051450103200801032115a84002c850140703d0051b01340702d0b500303621000700c40d11031070700d0b0b00141d4000141d840300300e40b40d038140404102440c1c00402a0f41c15258043e0844e4005c002075100d100162821268480780350708030010118403420383c58014405490a104000740d080224503146d401941d600d07480c20303000d410700c4040c800300ea988031598400b204803401c0c0c007003255150880003904120310039880c240e01c0b80c00024a5010000c0c80b1120080082c010070021980710a01c19400081ea0781000d0014030045800307203d04000384c011004031a101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389758201 1250 389756951 389756971
    0x105270712060909060203011a030403090b0c0a06180501060f060c02040b0a080303040b090714011e12150602160e0412020f030d0212060a03120f030b030706030509060c090f0405 78
    0x103142d4903103148040313881160080d900c3c03580000040c0f2901c00760407100000380140c80c0340186140382945005103031034654058001405e41c0050384c2a9204020454061000d070005002c000b03d500c018400403c103201000100c500b1350801000042ea0700800083c0e400320f58298492811924483d400c0000600d4281003465000da8000c0012841d40e40c10000345106601c182c00a03170345400c006902c185800d540307034031079100c2e8012100c9460307159900100c02d20741c111006408a07002d288684040c3c50940c840e8403040d2469160240d003075007900d4070381c10020032107086809031441c03410003a410101d040110301800501c0110320010800048030003401d141d44101c2441628403c41c061b20130b190440e80208802c01c14581c01003085480d035030840c3c0000c0e0708401e04582d4110b4051450b56500c3c4800c1d0b4000d00042449160315419002074013a2702304402402004043d202d03115141c400c0940109010f590714100340c0f03d00c1e4005001445800201e51413140002c2818880511500800c405000010241141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389759451 1250 389758201 389758211
    0x2100e011107030804031404060e0405042109090e030309071403030d050406020306040e0c01080c0c1e070303090501090812030c04030816020f041406090c19080105270712 75
    0x220000d004060301d1150720a0751141319a040074107000f002d084081c202d06038400302c2040200400c980080c102082c054050350040350b955540e051840f032007a944c200d1850110114008110601d5010310000150380100e0002c000d840c421884055a80c04103c80c1107805900c105e906101114207400d81c0780401900604991500104c44e2091040e900d041e40e04856240c1c010091000c1d48c5413a000e80b0802a40410041c0540d207100c070b0008084160241c10005a6a000100d070b04a00d41d080c42103036049806084118070081824144942d2880a444154001420113170041441e62145d60040c0489240344018400032141c402892002d80c0003500d0b10b010407000300070020000303040b40c025000035260148840e0b800d14190040c00110044920614440d82c94001003a20590646070015004030b0180c41c5d412240c0d5501e04401c174a8400c68040d03048140c45115a2a4240c4d030044107603042e07030b0054640307103105212408210054402551048407801c0541c00060003141b0801814000055504012039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389760701 1250 389759451 389759471
    0xa0f08071401150504090f0209041104020a051201080106050d080a03021b03090901140622080f0d09080a0308160212130914150915060301060e03060907030302100e01 73
    0xc00800d81107201000ea5112019040d100d84860316000042005a4090207016481e5403814032140000c80001e10031100c22002c00d051000f6042509002c4802602c110b5a94515250181c0070fa0804030000a50440c44c1d80081400c0c3c0060141100301d54015002546440c400d540da05a03a801c80285070b400c2550a00c090f480020a03903031844e02d60004007019650f07585051040c0140084141c01c0602600d030035010200ba02c0e110041101d0340c8807405d0481852070031042417800c0b9024041d5000030000d128000c0c110f40b44000120340f03d40300003415100c080e102070355104400e4a40ca8802000f4011820000005e030191600381c0d030581c0c031010b41d031040e00d50b124008010544150401143c40818800e814000e2103102c48612980181c0031843d0700d00542407a240300c15048060390a10b82500506e401c402103140e0300300d9141051070455006050544070740e1a480014001444200503910a00c5007a0204004940100e0040d050344d81541c0034207906400004007a000e011880c2c040281c0350b40c0d5541d190 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389761951 1250 389760701 389760713
    0x9130c0f0804050c03120c060a1b11010e010f0e06010905061c06200a020f0307020a03021c0c0b09130c3e0f06070f0c060b1c0b1602030c0a0f0807 64
    0x820301c81e82e01c650702500c031092290b440745800e07002480400c04a00e810300c1b049003001c2821208250080358540940500c40b4160053301400d04404c05840f59030034000e03d0a2414074540064030b50741ca80d00120b4403e83e0741d461080b4195101070b118150080719200700d0310020400c804a40f030f002ca000c0d000224500c10010b00d400a65075100d03440390341c1f060f008200c00006590601c9062464800039000b142802459000107082c800f07540b10003480390720000c00505c80481c1d86514503040a80010b090380e4880c0d03039080300c1c0c3c21990183c06554400d850b1190307074408501c843c0c8101000700f04d242d510428140b0000340207a400b40c0200140d014840d00d0400103502980c595880c10440840040280400448407130011b031802c0d00c042c11200a0200829584424651040b20108002e80269020a642c1a0780010403543c40c441c2c4000c0d4001d266921620091000e202610350282b0036a0941403480c04104034100c1c0c690185020071100c1da00019680d0012070302d00e00c00340c6607081c01540000d01d0314020356154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389763201 1250 389761951 389761963
    0x16030b0402190c03090f180f1401080c18071e03060b13030204060e09030a050f070f03020c0906010302030c072a0e1f0e070f110d0509130c0f0804050c03 67
    0x10300b0000e41d8040c505020954402000401080301e281b00400a5041c59149003401048014040d1925500c850030310800c80c46030800c0350400381d0a4039603c0a542c46040040c0c039840f81440c600c1c02202c03601c1003488090101410140701d2043c5540701a4604a107210007028181824019820580c40b0700001c603440243c00020681d4045d0310300c2400c0d02034a1481480203556169010610758001e9504000210300003000b00c8080840700e04d02280d40728000d124103103040c0074100e805011400c0c60204141056000109541144004c46040d0a40d03600c80c001102a4401122001c0b4402002d010100010300340c3c100b1008115415903d40050340c4603812410440f10aa52094003c061240705100101480745074004040049400300e080303241c00c209011814034006002030041040c1c110749000f0442c482d01400720300300f0f4403506840d1050030429000341180c102070042482101a9000155030820b01e1248541e04801510f4408070282c0000c01642c00c0c071001002550700f4010280100700b582e5080c003007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389764451 1250 389763201 389763247
    0xc0f05070906090506060c0a0219180204030302012a031e020c06040c061d1e040603140106080f060c030601051303050106090b0301200a0203040e0a0b010e010816030b0402 75
    0x90b2032840e00e4030110030358901400c85070146500f004007490620000c1118400c0e545c0507203140c401550301c40c00095034007025070b0007450003146c4002c00c04d11404040d00184101d80c040d500034000d000ca003104101c0340d407000c20b00b6003044940c45149845400e0007900080a0300358180c400300c041017000543c141c1039074811682c1c8030303850300828104001c122000f20404082e01d158909191104c0c80c203092500070b0f82c0700c1c0722101c1c411405808016030f81884940c0440004401074001e0280319582e1908042442501c9080c640703a50070940042a82d110028442d140b6990b643c00600240d110340710740d02d00c030b03a04c003900e01810010100200143c1020100305d48006501c1139000040b103034507004850701110b6840c2d81052090341001000c210018102800000d40d001c016030280d540e00c80008164a10301c12a4403030280680c5076000c01a20415079800403041c2c0100386ca601e562100150011a101c06d0b049030104203911400b890242203a11030f9019561004010f00b00514012400c00d84068401002c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389765701 1250 389764451 389764469
    0x121d06040812130c030813080a03020f0105150a0e06030102070c0e072c0f0f12061006080408040b161406041505070e040510090c1101060602120a0c0f0507 68
    0x149411a0a240c00d00d150f0b4801c4030300e011180c41c00095660048035608510000d0030490700480c80c00f1424a6515282008104c0c0000300c80d00d002c0d0524020303444000c0c0c90080d001952818000030800a460001d1007102c550080c00e80d45820309000c0c00c58901d641c0a041280c00d0340d401d2143c480050380c0540f096001e0134040310179030901d10b0a688018641400c0351007204006c04100c2860002141103142c407000d0000071204100d5261440000c21140c04070302d12410344c00100021401d90380c500c08504a8040c602074010301c103042d40c40e0241036034440400c1d02d004042480810080000f04a1000a0404c60000000f00360303c2c0c051985450540c1d01c0c9500e0f0301d10b06600400c1c103000422401c070440d0800901e10079000d00c000e1034207540203010704c04070303004145c05542c80d4000106078514150700d140c00360101076000c000c52402660000c2405107001990070380c542c0f0b031250200d034040c0005004500d20640105842c602883c20108858112120500f00d5802024030310300070000c1c40500661001d451040b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389766951 1250 389765701 389765707
    0x1c0206130911040510030207020f040f0b01032a1110051005043606020706061d0702011a0616060c0e101704110312040b03040201120c121d060408 64
    0x420400032180101d2021000d002c08000c01c1000d922054100d01c2c4510080c00c0c0140c890000b4000300365090f03040017446510601d0041c00f421052400c1e8003541c20268280d8041216040070216042c03012050601e148180300e40101010242c1c0c4226044100c05800106645020a40c412000c050318030656007000d5004003100c0c24006e500381032180d018180042950b0702d141c2421a204145852542c10545802ca034040749181d0500800d501151440399210b42e0130030a40d40c2d140ca10900d00c2041ca0003070410020000041088603105000b4082030300006444901c04030119000c100071940420201d0144e03140280114001c10860b200f060342203140354075003a1045013104e04020a00e0302080c0440280400c000303240714641c0c2a2404d01d640705078441d4503a10340c2021080041d145c0318a0084c1c40ca24002c0014012034011050b0002d103000754400e884049010141c800054240c40440c1c44843c000385100903002c209448540000b0402c045400412941c02c208168071400c0403002c032004d9403400000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389768201 1250 389766951 389766959
    0x70206150303190e0105090613060e0d080a03020d1b030603051c050313020a030b0c0d05060f130f0608070f081002030702060c090a0521010b0603151c020613 69
    0x12120a50032000450107945010210145429109100d0518004000c040c500c44030746030f40200304072480228007d068944034552071800c00d07810749041c020040047e9282c40c02000c00e0030328085450300c070303988105244d0070082c400c01c08400942112600004c1c03142c841c078846899551102e40600301549a0b500840c0242c1103040440c94010080c040c0c0a00844c10010001d145501070140da410446902d4110903405150000032040d02c611303003028083c007000005002201c01e082c0000c2210550900081c02599107030002c10030314202003200a41c00c0342c48081d0391248030849a200c2d211500c0c080c1c600051198131891080d00c0c1044940000054034900380040c0b0a511003045440450501c5110075807840c03805d504000e40b43e42d00030b88001d61928001c42c8840c844d50343c070220440a04805000f0075030420b103021042844280c6205102e50315482c0c00044d144909104040b00d105007603084200070017060540038410b1000805502c5403001c500da00ca28401640c400380144411080309400521a50074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389769451 1250 389768201 389768221
    0x10201051b09040e0307050105090303010e07092106141810090f081c0c200a050c061b0703060903110c01020c040c030b03070b040f06170609040812070206 68
    0x8050041d00728030010a1901251020000c00c4980c81c14066a0114581c0c0750442820b00e940140c0340000c00719420142080644c8400001442c100c030034002050750b039038585000170b4584054501403030031241001c8410710640c80b42c0806484415100e21800600b0030704180c00e08500040a80e54288080c2241d408402035a00420580303c0c4d18007010801c0002200070381d292001004100d030001d0030600701082c10506000181603840c5101050201071008440102006000040c031070b501c81e180881c0e2a02c40d040348a4002150720419520400816034030f00c0c03e40c20010150072480d100d07413015031122444011a5014002e50000f14801e84000c10030018030725000d046280d40c2c52494006030700c001d00c01701c01c0303030380c0010f0708600c4000c1039800181c50380b0300100c00c80c040c3c00d100c0e030003a415201d030341000500541800010b00c1250104e0a0305410369468203400c4400c404090541f10b81c0440040c081250b52511000d01d542140c8580e6071240f40641220140303c03c1c4408036074947c05038003c40d0400841d00d071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389770701 1250 389769451 389769461
    0x21003051509161407080711102f0c031b1c0507060c1e150609020f0f0a020c0a03030822120f020708070b1c0528090209010b09010201 59
    0x20040301c440704180f0b440b0409880c3e207403600e5041c000b0040010a24403003501d40100b1100c003190090b071103035510041410081000440000301a000e22521865004000c0c496403c11040052441524900c0f180701e02980304028400c001c03e07030726405080c01c601039960b000c004003552280f104072024815021b8034200081c42001020384100c001c1c140a100c4c0002d00c0201e07101040d14624100101444150b041031007002c17141034028010b2030400707200b1409200200800201480896000b030201a890b5280d0b0402e0f405140e0305d8151140c0c0a0002042c00810700c00684024902481283c0d400311503c0000f80450280758420340118802a00340b1103804500f08070310809170140304895034178002a42d26111003008083c00d003c00c103c800d0010818241c42400a00e00400010046508a5490360407200065200040f1108003c801d400503002d20400c2d40109407045030f500d40100c02998040c1400364200301040318880041d0342d00c0c1480030040e50f4106200f40a084152503803511000e59400290031a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389771951 1250 389770701 389770741
    0x6120f07051e01170403090302040603030804060f06060c0803040212011404060b06030123030c060c0f060a0504020307050108090f030a030e0c1e12280c0b1207110a02100305 76
    0x1800080b004691340c00600000384907900c0e0351244000d595034201242c41c50070580001758000d06045c0000145036019030060300a03070080908000d2540d4149283c4129a503500c6600081408080340d4000300c1e4003d406180c0c081d0014000a40b05d5100858642c00c60f8040c040c4891906a40001c0c401407003110f101b500d2030b43c9429690a45554100807a06511030811107403151034503d0602c03c50301d0b9460034400c0d41c19102014102c03e80700c164109c00d0a8581c5601c0315011110f1040c2d000107440704210303002d0240038a030098041d140b014207050045541c2000244000c170707940b10310743c0c0c00743c2d880e4401c0004102c0c1c039029a40001d0000700d03003492a410109c41a0302c0318070a480070000c2c074100b088003c094032100003003203070f9543e5080103540d1182d08256009201211009400c00ea041210700c132440d990103183d124100e1000080d0b101c1c0460304250181c1c01001103558000c3d4005040c49006102440e001c448400c00c96402e9081d50340001c0852266415490001e40c940b001d02c200b1298210740c1001003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389773201 1250 389771951 389771989
    0x6080607020a030801050402182d060f0405010807020304030506090606090708070938091009141e0d0318080307030215150604120302060a020903060f06120f0705 71
    0x1500b80b5203006003410381c103006180c4a82c0e8001250161281001850481c6500141520800c0444e00310440c0c1c01070100e0240040c4c054681c2c003140c0b4076103085000c0750030729154101400d00385420040112414503004140c038040d07100400000c4042942040800e1161407400000d01c602d10342002400b01d0200701030a4042408604014400f50030380001008054448401d9402c0100c000c400c543c00c0301400c0942c80007030700f9003c1b1502041c2c1c2d0078008010540000305440664540003076044c104c403440d050b4442e6980060645030898150325040f2a120300100a03038110700300380038030000084d81d911403401044012840d2034002116145400100b00024280d000c0075600780503807030301c001c0e44603d0b690b0f1140b0318228000002a94840311702d801e442102c40040d00a41d00c13140c440103201210035020109402521035940064600022402120b108090245c00342c58152070b40750784001d141e4000751010ba84410002043d20500000b00076441c0e02028010017002c1e92440c0c2010310909403000030320b80c044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389774451 1250 389773201 389773213
    0x20f0906010c0b041704090e070602160303112103060109090b3f100b0901030f020409061409010b01031413080a0e03030a032c28150608060702 63
    0x34581e001a020301c01d064201c071121040d0380ea28030f40300030010304c440b48840ca0000042400306110311036620041078030200404940038036440b102c05980d50301004003818107070403c0301c500303000103441107510101c91450744040718000c2d0007401c040606894003e12003440703a0000b0080000541c0d100203042c00820084008104510100c3c01080001d200c070310500046100c0002c43d2030100305043c4002c40d1807131060041410401442c520b8540f2002d4640701c0311b07071450621140c59174501e48507464504a0340d000e0268040c40f00d03282c0c00d12028010070403040e01c2c500d548201f08007004600e240c0d014401d03800724000044080640002400f1580600c1029041904c1c00e42044400001c5d124540540742d00040030382c3d00e070020340c8811903240240c0c60017035405000100e00450341d030fa0141c019000d00061b8400c1ca00d82c01601c02d82140d0302d46508541d54805030301512082038240c961300e1610895851030b42c500000540240c54441610070b0201000c1d0806560b20020400304006002060700602d507131001d005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389775701 1250 389774451 389774461
    0x506090405120a090302030105040804030c0b0f0d180f0b01080f01090b062107080a0309060507150c03020d02030c0c010b0102060702071e120c0e18030f090109030c0305030403020f09 80
    0x103520384210070368241d601d00001d100500d0138015030341c0d90000c0d07034000c000b80504d1605151425a64110b032000310b0b11001107810200d110700380705003590040c445a00131581130030800503908000d003525402c03c0b8a050920341c040004100602a0590788901809160955525200406203008100d0449010a903d055109400102910341841d0082001c4a200e4180c080140c191401550103c5a420741803091100c000341d404400f040034800e83c0c0c040d4070740c518841c0d42c0f041d081c0d98078032030702400030319944645020360004e020992041c070340d2040340e00c0c00505000e0340344540e404a0b88140c0e54000183e00c00714041916107800d0041c803020810030b1000d0b082604100c07034041c3d42c50005004001c040c03141019001c1c01c0303c0e42d121601e80102101c502c009541031540c14807040c80c003800e0154000040f1a0030009141c0d042041792030415428900043d4039085240402c841c064005030001810401c0c01000080803404961961018500603405944c0d181c0c91481044000807030304000700c2c058004003007000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389776951 1250 389775701 389775703
    0x130b1b0403140105040312060311040209190314161511010f0606091401051615021e07020a05090105030d14130f0e0105010804020603060d0614090d120603050d0f090b1206040506090405 81
    0x1004050304be5800750321145002c0009001c01c5041e82d00c1000800c6042c000002d00542000d1880598061360a95034140c0e46115400c50410081c0290503106080c1d01810401a204040140c1c4010080c40002003010b18040900260b41403a4016000074241c0e2100303022400d40c070503400c042c00b0700908104d80703030150520341040c804d401444040c200216291080c01006020340460780071802040003005012000090200b50ba0440c81013680100c4c0020808142402c0910100b810b0b42c1c0010300403c506075010328201c52140168904a500920600801c42203d040703c40050180c48030008211105041094000340001d05a2055041181c060b080c0702c056101d03101100d030403903000c0e103100c1d14000450a028010308202e9030308409164948040081d42e03600881c02d00c029440903a03e00321850340c15648401551550b02004d005600010700c900e00c07050051110408640217030601a14103aa02c4452400030b820509030802c01c03044480400100d0700d0309100b070300c0d0f00c24030844101e40f050820762202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389778201 1250 389776951 389776973
    0x5012c0c090415110424080c16020d33020a09030609020105120a02040609090b13051906090b101b021c0206130608130b1b04031401050403120603 64
    0x14104401079103908125000c00c2e000803070344982c4441c20603174599882c69490340102503001107503007206030b4000703001045108040c05802005034081d41c5003002c0d43d84403050750200515408903404415800c1a000050340d03400c6c0403881444192038448410a90340c0c40b081c80f044c2581000207082d10412041414a4001408c1801d8980000000a031307181030b840161802e100e1000d01c0f8180303030504400c003d201d02c0c01d034008009071081c0307944419040d41e4889184090340c14012000b6448410455420300d40c0320a40e0000d039014182c0c01981401c8641d1807246006c81c2c1640d0017007001d25440c1d601e80450380c2045150614003c04525000c070003038001020941006421101c02885001c00620340c1560310000820310004e25002008141c1c2c03400042450b4036201c1d11403080501049a000004000036512a0048422a0420114004c0c2c0d51419200e54051540b00c41c0058118030078003020001c125410140516041403400014403401c09080140803001c111810340025410032109200190507000d407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389779451 1250 389778201 389778203
    0xa180e07060c0b180f1e0703030903060207030e0904030513120302060a0507110d080a1406060a0e011209051b04020c0c060c030c01020a08040308010e01030c0302130905012c0c0904 79
    0x401c66181d110244c0140703056402c07010000b0340d486040e5602c0c00c84200440c80710a02030b8180032280c0580404005152a260180b1020380030455206003000401c40b01e07001070007500d100303240c2650f0a000d104001145804251070580002d180400c5102d91003030390300020405881c4c0109044850100340c2d50007580c5e140000d001d0342c0303855186c0000c10346840c02481c0e1310040128600c2541c0c1c820490302d400401302d032021100708030800d0510401c50815800d0300080da0060502070082850080300702800d032105585030310001d0421006e18501c0c401e2506520602500070b204001500d03200b103180e009410030714020500c0380c1c4114410080e440320341100041c0caa4040d00c06440813030312198010225400c60049540604040d4000124a81e482e0350100304144241d2094541075002d903255144280c003504d003401700600c0e210300381c042800549400801004010b090f09400b046181d100c0d03541c3c2d030035101c006c104860700600741d4480c02250803c0c6550041e1f01c1c0ea50f200104900600c80c80007856096010340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389780701 1250 389779451 389779463
    0x90308090c0922111f02070509040c1a0904050a02070204050601031b110309120d02190c0303120f060f05031033030b011206060506030f040b060d020a180e07060c 71
    0x14043c08000c01030344010800b0000074000ba080211a420300d00410314507076120801401030720808211485c101240500540d0800c0308a0025400e1016114101085101102201c1c0e01440350076030710364850040c00d2003161110805078075001144140002ea800240015040c141400141d4000f040d016507100c40442941c42c1030321306001c1580d626400c511401c000b807034011041c2d90136140301c140001814031908469500300d40003608800702d14480080040c1000300b1080c940c500c204040b038880e03190700342840c0e80f0f00c03400581f504600c80541c040f220b50340c1c06059503a48504c42001030f481d01b40840ca522150006d0300784038071000591080ca00c20000c90074983e600c00708042c050402d4524070003501c05141c0c402e88200255850300228100e0407806d01e0202c4070281000004a01801d180050764020320300075070f422402c1c2c1c80e40c2e603822420300d1000b030121b9000300e0070002950250380e44106407801007040d005001240f00481002070180e406e0140c4c00e5004d40e128000c10050a07a100c8260500704c0d82100d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389781951 1250 389780701 389780761
    0x606080106030c0c200405040606140a03170f1603020a020f06092b08041202030d03020a05030a05040203010209130207060609021c050408040909031116051e030c0301090308090c09 79
    0x700d885d407400144a451035005840c00003004200002c960220b401d135610104c1f800b4a007603000301000890388240c04001c040318001403140f14442031174009071203500c108400c1ca500740005902d001c00c80382c140d818151700581c40184242c00754107110035030b80c100080070740d641e03440d1a4115001c078040240206000d000e2000505020318160b20151507501c0440c0d008100707960383d075a05c5c102084031204420341680309000320b0100d0000c080c040e00c02c94180390700701c1d00c0c0c803421599811640c0004040041080e60155000c1024125940ea10403603501104104800162615598102603084610f607400002c205031040054078500301c0384004024a4207140074000c5000c0e0f0b15480c05041c14001c80c1d01044c1042e0500c0031820030903400c621150000303940c8000320390702040050fa2400f81c0008610034550041d25100c4084440140d0301509880060081c017200d0240d00d01030042802c44010900c00e4001400c00028040d002c1401c0c030240c4c0c3c41c02c0c41242c4240c6541010102d0514400b1002042d6861903003032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389783201 1250 389781951 389781983
    0x9060d0902060309070608010837170c07050618060a030b1005091804031e03020f0a020303040c0803031b0c0f0708031c0504050d0c05120307030606080106030c0c 71
    0x660051180c00741d000d84440d80b41d08201d101c40750703112036500034a004620b003103002080307612002941506030402c4051400c0e441c40700e140901030580c00c0301e1041d500e00351002c0700301e008920780e910040e400350501c810b25952a500c0a040505003241600410300c142c000300321003429004100300b6080e901c14200c403407a5481600da002036008040460120350400c4a0200702440c03103404c1005480c801400303894455003109141c00c4c4900d050002ca80090105148c20f41c441948138050024000016513400c00515002c0048882c403456048440c4280041c0e000208120400402c0070641c802009154025410342c100640c0b032445030308241400289152010910b02e4041c2c008114100140340c8100a8814090300c03400780e15142d074003241030250007840d00700188900c0042344c450248203e42200242402d82c40010381140c0d5440da810041e640303407080c06265a0000c031480010f50103407855840c00560303180303040f0000e0044c0f02c1c140c0c007103001e0514003000c81da100c03500078401000e40c603800701c0e02b02004000e07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389784451 1250 389783201 389783227
    0x30b220318050603010e0f0c1603030c08060607020a06050d0b030f06060f0111030f03070c15060311030c01020a020402161b03020109090e0a0314360409031403071b0302100f0e030906 80
    0x2010781549e8a11114405a030170326805501c13110121480b5a51207034907540d04010700201e4071812600940144d540c01041065a07c54405854011001c003030100c1c11803c030070700183ca400e03000d1104076004c4d0070003803d124242c03401c01c140480000003030802d80341420b421020643c0b24043c0c050038007240b0400100280318140324510030340c0000d60115844030313020461411500103100c1c90000f11000701d9a042c108549180002c5e107448079030f0b0140d0040803194490341c203001c00f1390004030241e0aa8811900a400001d64000400d5a002c0309910b0000c0c15030729600005010301c51035440a000103240a01890940d000440c04444d115018100030701c030751480002480d0706106240d008a18440072140911120540e04418520b01c50702e5031441003403004450070002201d0001500401280c0003660000244545002030742d44180142800e40c00b40404030788503140c60b04010750440c01600b2500841c03042107424419440c0044840c00104040040c031900155284120380f0301d507108201c0801c06e082c0d800c0c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389785701 1250 389784451 389784457
    0xe011707062d17060303161e020d03022a3006100501020c0619140910080601020d0c032003131e0b0f04030b220318050603010e0f0c 58
    0xe085103003501c0c0182003a0005000700c0f4200c07120000000381e0700102e25189400404d030340254901d00f444e400c51281507610f07100200030035082c0c2404d60308113940034070140e40d49400110364a40a44c000d000a03043d800c0f10800031303500580f104010100c0d05143c0482d03d40362808240d5803400e01d10420802440305071500074441d022104c2460340752040c40d00b000551070304601c1090440b41c080c0c00311014225a01e007001014040c0d0700e0b030710703400c12400c14a600829210b1380308041a204480c50251801484c8400701d882a82c8801c04c48000c51190300c1070041c0d65030b04110950742c010b02841c0480465201ea500202400c0065000502e801e820140a408144090045030104540c1080119440380cee41c554060050701007464a503a9a0b000b90f400040c3c0d51554011a940d6152441040d498641035a803111070030300c000703018401ca0240c100115200c0740c0346210200092800b030346030b05016507203051042107240e100d0741103180219010f000400400d96040601034100a401d42e400d0070503503c2c0440c201c1140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389786951 1250 389785701 389785757
    0x7020906011e090524090105090a120c05150c060601050307030f06030b0f010e01081f06032f030307020f042f130504022104021306030c0e01170706 65
    0x382d11400868501c0e034102110904584050703964507021344000c002d480e0011200040a400d00c1001c2120943c1c035880380b4000c000d0500014101c940c182e46901030000d8600c940b100440b0000d4010905100b6032a2250080d80c41c0c02000b020940fa01740b02a5245440d0310011300b20605004e4040b0103d41c1450203030308083c0142c010903508109880e0b40e4280040caa18003620010b51510300d0100200c4d451510881d00d80c1a181130b01c00034600750001c9a07510800c10306030721111000564550002c400a111000c100d04944c02c07000444480540208280401c0985a240c00388254010010240103856507401c03440b805030304031000140440c480340400c3c0011201c1040802540014050340000440040a4200c00100d00783c030040b41307502c43e0b09102c00c921440c204090900701031414032181c04e14444240390b1051016200301e1143c2200e02042c0141c0d001900102c408000c18401031111700105030560f40140301c05103440303089041c1c111940341c60b4201d034002c440402801c4421102048440440101030b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389788201 1250 389786951 389786987
    0x60209030a050303221709060714011508010506011403040606092408060705070b15040c03021c0911090a0908030411011805090a1d1207051504080702090601 69
    0x2035607440c1c40c0c0e441398011240d1181075244ca45407803030100340c0b500c00480340307650044a02c03406020122140350203400070750f1115442681000001c1c00a10f40d1184401450659800400c18514a080c0c01040e80240d42000f41980e24005c10030980e40e030304c2086803400c80280480303a9a29140d40c03d10300d0280225400c03001d03a00d030034120030352070740e2801500d05e0407aa8105049003050a464448854964406032400c40005400307018990210f600c9402c0300e5003092100c1c8200303030b034104510080b506480c0c841000c030000c294089100205041c14040d44101251155410032001007160341f40d4103950a421105801034030b5000004100c08819807168003002d410651070b94a9207010319242d21680e6410242c140007038041d5030245104880d03d101401135034001020780a803592404038010081c13001061194604401d100d2a4007003203018440e036004a403150121582e00c50307c1d0b04045151044c0450901e4080764a0030411002c078088006480c80554110798000042d11001c00403200c41c0e100c02c45001034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389789451 1250 389788201 389788213
    0x30e030a0e1827060106020a120201090b09210c06150a0305060c070c0603140a0b0307031704060906020d020307170405061b01050702160509040219030b06130902060a0c06020903 78
    0x850f07000042c1249001c2010b40343d00040084144280b40c64420030b110784409a80000320200000b00344030790000c0b6a090b184000101d03100c86803920f1109000a6500c03646c21b4110b11500031620340e0441e840c0c078602031101403441c03521905840d030540e64072006000c4425440c4114a08640f9070310216901c00460300a03003282c24606180840550592100e60111030080500e5030020701c982c06805540702c0120540e140c0c6034a6902c0d001c182014003070480b1810340c58001e041c2c0120000b21805d12010080c0d8880582603120740c180300001e0461100c03504031005551003076804007180c56000003294922036000c600b80d501c070807003581c80c5512401203030042c41d4090b4010500d107540d200c1d0011218205c041c10310081c005502e81000603a1988616140c3e0154180c0e041814003207030811046454005d88054806212030710000f83d41c055038131f000d80080310070894140a100f00c40c50200054402c00742200010491011941c1c000b40b41031041c916010b0622041c1c0ca10710060040710f0b4141c1318199406420b03254 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389790701 1250 389789451 389789461
    0x1202010e0f03031609030305031306021e07050c010e0904060f0b12030d051f14030a050303070c05060709050d12090807060c1b08060c071110090303020d030e030a0e18 73
    0x24482c0c10444e504070401c2c25901c1c030046514400e800c000300f100c2e0192141031031a110b02d0070075040b40c01440310035504a5020803031003a460801036070400c00140844241c9454195a2400318200000d080c00c0c00e040002000b02640941c1c0c0e0000302d141c2090348000300049410030030030100017500d1200080d0758401034402d81c0006004020004200c80c2407004010441c0340e81d9000c3d0301d8241d032008040c00040f8440c2e51014042101c4030b44504102c032800400300d8208010702c1d86c5182c5194000c0700c030b01c40026840c008404c2000740c10001150484800d0134044e00c81820140403840750250380303a0150a030284060400314803030040749140007a14012081e100381c1d5445090240c58200035000488440c0301008000440100b046002d06c01d481c0c0c40006070150ba02d0f40381a422a94200400640303400380d400e01120200d03074440111031100c80c040d803a883c03600c921310b00700a4107080c501603001061500b8134245000b072580c044200ca000c41e80a04150380c14000d4540843d100d400c0c10200c5035004218202841 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389791951 1250 389790701 389790703
    0x180b03060106090306050a0e100207061b05121e0f071709010203010f0e0c090f01200703030f020d120e030c01060306200c0c060711042d0e0601031202010e0f 69
    0x3d058902410f02400700740c90700201101200c00c1e14041446a80000b190200034001c1e9070001c20302580221804030b0050440341104000340d600c120403101240f00092078651100050b0940c50303008121014500c84103210224000520400408c11085280c0702c00c0050030040c051402c81082c076400207074010782c0d8903003a04218000d510a004d444815402417400045042c1c84044061040c17003607005080c2401104418405c0b40d050410811341405440486010010b00640040b08900300c07000c000d28481d03140d800c01805128004500d01c00715000f003404e102da80350304203598100c03814400358000b6111140150780e03419400780311000d262039401c1000020600031790703400c54514140d804104094141c0c01103910071091191009116694200440c80c001518202e005401054099000c007640781c28520002000c0b02c0180010380403014440710010140c90081841203810300000c10200071001c0c1414101c1d6580700e05101c01801c00c5036030941001c2191007900b2007818810b142c02190200920b4030002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389793201 1250 389791951 389791967
    0x140309070e270c030c0d050312070504050d05010207060501050616150f020f0c12070f1106090409081c060f090b04020d0203090a0b0c041805130b1005040e011401180b03060106 77
    0x1113101e071144000045181c0351030811603004550010003107142144000ca0f500c40040d00408200900409001c0010700d03880361004074035483c2c0b0940005075243e60a15058040300c0041e04614003030001032102003000740342040410078072a0040b01807520040c0940440000d8a040480541298004115136246221711800790400f5401401580c0840c80c01c0c0d90780d07070028001c2c0305024010300303003202c1180c010031401c1d000c85d0307060480540580c1c81c1111080105007503400c180411145400c0004421000728000a10320903111644501840300901c1e240c10311107404038901400580c02c0c1d5443c00e030b0f0001d0340d03180d040b02e5440d492aa015501c9103054421151104820a001e40e1207002c000c00040702480c20400311401c1c0c1c1c41c0c140a0260184403040054014031000300111008404110010041021801194404c8046030340d007040d064148000c3c001920310307040390a480c9030705016001000f00c1040b151141910346903403600c900341c160f11942202803c41c0000e066010f02035480040382440e4014a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389794451 1250 389793201 389793223
    0xa090c180506090108041b26150412030b040207060908040305120307021005070c0501050414070b07080304030e0a090908091018050603060105120a020703140309070e27 74
    0x803800c585aa10010b21410784514007034540096400c800103400207000940d6000040c0241c41400e0302c6c01d450380f40d503640c000c8d40310b1106c10070151505000ca903480c504010b00c00e20104500c0c0f070170003541090394070b0240d8080e49000c018140360300d80740b00001b0342e111581611400e81c0c020105000304592801d0a850070340c8180415503240c01010ba04240360340a20040301d00898155000340100c10281c0c005070010880076088030b0402074641c03079000218009008140c02a0701031070300b0076058003080d0491464404168402000c8000c2032192034003203040c0d1000d0301c1d0b0051709030600d21b01034142500016001c005582020b080301c1e15144d0944140101503010b060810010f40c0d0440380010220001d84404254807603041e20708181030300500807803c0401c00307142c200c10706041c62420003411040d035884030764044510401c9190301086080a140c0d100c5202003040429161030361450074407845458a4502c81e00400840558030004152417440344202c2c000c5080034444088034001172100b61540f52000007103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389795701 1250 389794451 389794487
    0x22203060b0105031e04020105040312030506040b0a030201120b040e07091b0e0919022109071d0c03040f061404020f030d0e0f030f06040b0405160509070c020a090c 72
    0x1070307402654040e038100d03030141625400340d0310b429292146030452a800100100d04101c0284400000540d200ea180c22554803a0344011a0602d0680d003840100c500e0b08002c1c5114040030030007080980d03041141e21000201540000c916280c2d0900890050070b42c00b00c04580030b00c04c084000882c418658485e104e60f41290b441c40a40503549401124112108180d11b030f40800e502c2c021039003031140347c80710002c0c6030300c040ea002d8100fa28500700c40c88181400512614200014005c01c21415028403111029088810b0301d41020075102d4401e11281e0b00003403040e88002c10000100b81400110001d94440d10f038011400d001070b10070341c044800e100b202503804034060a000c0a0a0402d45000b0032080c649105c0782d42d0350140c6c4407051041003405006201c8040c0c05025014403000c1109091019600c581d00543d041c1d01c0f1803c240c81c5c885e1510071000751005514845007003e0140c0c1d0780d0301c1c0c80f0350340152161608080d00301c41400081c0c00501c031a840045403616000c805281d45030040c4002c000c0304900c03e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389796951 1250 389795701 389795711
    0xb07030207060201150b0a0306030c080a0201090e07020606090c280815010f0e0103090203060703050711010501030201080f04140607120b01091d04080f1602040501051c0b090102220306 81
    0x34030b09a09032030951030426090020303004148444122034001d080c03030144510f000b0400e81d940f51a25a151001c0307802030003e6400075142d0000395600042d01d040100700d01b60000c1901d00e0110300003501d460015008611446118010800324046801598100340c5005002d41c4840400d05032000c10102c8400d44002060510000844004c10b03150386011031241a1682400c0e044000e80c1100e11400c101985410f041da030704800340241c0c40c1006594483e00d8143c60008850a00e08809080030388028070403030b500d030b05210040c00184d0340880c9450704540d40c24140b0016440d10f240c259905400b81107103018070300c600e00c10402c0450740000c40124a449408042043c030200d800110b400c2406405024003450b181c0703c6c6140c2034280e840149511500403940d26042184003043d080c0300b5803102034052407a42c2440c101d041949400d21403980140b608a400b40c5102408151383c0c03422170740441001d072017200203800190f200042901128010046400b0040b0191594a0400402c070704501058907050310300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389798201 1250 389796951 389796959
    0xd020a200705120a030f0302032215050121080913090b060906040c02190201050c0307050606130c0c0308040201051911100b010203031909302610030c0b07030207 71
    0x403c2400311950541d484102e1006c0c034100a5010790300250034807644081c18041f40728410f0100c0c05142105e8031a0750f2240380c40c8102610301081c1e0b8010303002003400c9400300b00028441d0301c55035030503000580c0c400e040300e071100204c8000a02d40c024100c1c80750410ba0501c0c04641c01c020010003034030300c19102207074400c1094803030000384000c480002c00034801503800f000305001c4900c01c0f1414885018414036146252510300000740c0e0a54000e160304484550005050040714a006048c1e001c004484982c2085143d850b40c000900c010b1a201024060010003404a015a44124115038180d01110703100c0200041c00400100281c9510020740c1040c01707501850303401581e641c0200030f11103c05900450560700c5000d0100ca211580017541171501d9600d84940300000d0611320341200ca10101c03101e045519003d405020740290007a52820208400d07040030011240d41d5100b4031200c02c1480c200c00c22196680e0006496001c0260805441f06030707840e10028400041a00903e20507101c0d900b507611807560303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389799451 1250 389798201 389798203
    0x501090b01050403031d0d15050a0c0509010509010903020303041d10150f090f0b0405030d0e0307091d01021b1006060504030f061508071401020a080d020a20070512 72
    0x14a40e1507000030030810040021a01c602042c0c15003a10404140b205d4410000005110120001d42200e08044190b9428406140341c41a0782c2c3c48840c20030f0510003000c0402e8010f00380e11628401d01c0c10311002013480c200c90f9128101460155030b0181c1126a01c68665001050240900394440b41103000725002403090707031040c01c1d07503030071240b00f45500390b43d41c030aa200684207041045014010440228400201c91380e1a000e60802400c0403644d09a81c1c03801c2c04245400d1452121100d000d01594200d548026140021150101c9030001d40000385103407884d07048940100408401072445d070000c1507a00345182141e12a894824143c0101d5010030700d45030118090b20428458400841d01c00d11042000c504040880c039989031044500096041003076401c02c10344001d80e04640b084d548031000030b002482c5c006400d118201380c01d000810203000d8581e190701d00c41c86520f03102c00025802242210070380b030040d80d10808880c8200702020100048c6c03202240d40f07038030038402c5900c10901d0384901c0000d000c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389800701 1250 389799451 389799461
    0x3050c030c2706060708070309050f01050304031707140708040e090d0503041704050316181404080702030c1810120308060111190506012d120203071a0c01050109 71
    0x103180c08420000c0c0b81c1480d030380941c100d070050200703400180820142c00010300d41c0d401040304a20030340360382c00c4003420a024031402c85c54404209040c400100140710100e0b4110301d01200d500070b2070070624030710342e074040f412224076108940f0f60b090600086087c2c0c00f04200070014200752a16a215172840307684104080c2c0d070721f05000d507a0702c3c003242041011801050704413907036501d0030344680340540c40c00303594402291824110080e000c0c00202c4d02c0c0820700c01c0f000f0201e0a03524424210000b40b10041d00c030700d14180c3c0c861000e0002806180d00103070300b41c00c5483c11f218010404034020000212460040740e0400d07182d2085a114030000050600400c007154440e000c0b084940e00755a0f05103080c1c1e200b00040d500d2461401c601c80c0548606078440c98440010001d0340b880794807820140190b545416554210f012040c1503050100d03545040340c0510a04000c004800c40d42d4900308088488294008a4200f80442e00a880b0084010074550790201d00306c0000e1804856100080002780c0c0d845c28a00200c407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389801951 1250 389800701 389800729
    0x4080703151112150f18040201182102032104080d030c050901030b1207120b0114061c0204090f0e1605130f1407032a0f051b010603050c030c 62
    0x680c3c0f070f0301251211004000342c0c10041d8000e0002490f18030f80d840055009060f111413009034107010320402045503800f0803060211203000c000303c030116013800611030a01c40007845081942403804d0001080d0761b002c10008419810070300011240794040b20a141a41e07009004860651260318a40c4440501c0380c8541c1c1180032003941c4290400d4088001100030300054207079641e000d8181030350100180818000400104a2085003070484041e500d004004080c0c140d01203a2050012060008280c65103c11107040f0380c0100c4250050100300c244083c020b02441c2c22180302a494256104c0207200e80da417010400b807001301c089400c0254000300b0304e941c180b21400b4590300031404c40e6035400019a6a00070b607203070264070311000c107454400c481031542c941008c030341c1d5100080c1c4581c060122003650114900202030801d2100890080e200390145c04040070940c42c42c100403001410400140d01e02d212440401204002842116943c0c280b966a074100d5802e0b1a04c030b400381d40814a07442c9881f5510795220 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389803201 1250 389801951 389801977
    0x140301140f181506010f02010b09090d030b0a05030d030c090e0103030e0a23040b010c240606050f071101260a0e0d02070b070524010807090b01120c05040807031511 72
    0x1556030b0b1130044818003c3d9450740400d5648031b030b004001d25075070700156610414103400280507960801c0030081c06d42d002404264020141c2c480d0a019541f8040f88030100b1030000c2c100890102c0300b11a0440b1018400c2c3e01508000001c00008170815500106070b00402d0340c101c68280303100741c039038140c901703100c080a9001c05513019159060145042c0340d0403c41440005040003841c882007901d911030440c0200d039060308050800c031100060311a40d84151000ba0031145001801c1900c88200c3c0a07541c450040c028112104224000c08103a01c1998440d80461048500301c444000307200f8400119941514001070040c141000059011800960040030903025801040170078500315208a680e403003103505442c9801a942c07040d10108407511850446203001e8110207041d07150600c02c60800038039400c18038001e8180205034605aa1100708c0c420030480103d00041d2401e002c04054510b4421b0740d002603194017620400201380100c4214a109680120f0001d1000d0040e9158031050f070300c2064828446 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389804451 1250 389803201 389803243
    0x3060a06080c0d02041b180801090503070813180504110103050c040b030414030406091e0e0a050a0f0e100b03030408120a0903051207051603050304140301140f18 71
    0x3989840750340c5005190020308000303201c94546c20304030783d10150101580042030000149060381141d4210000080118000822160344c41d96146a101c0c40f450700007410b005004240c1c09046481e0b10a254003d00c848950094440d2540b14004080d140441e003e0300c0700c42c01102184059402170041c41c0c800c0c14140c90142c0781c1418402c403400303076070000ba1007a03444c00c04492559050700010402030000c2c0c0071075124000e06920b010006041c80761007003d01c040b030a00d0b07248100080b094032007049400c21201c400104003590b07000c04603070041000c2d489240c4180e04043c0b401c032010030007107219041030304c4840d07003031000c1030211050503a2840345228444041c0d10031200007400c00d403940b01510100440e40780c0207090650301d0f15414a003060904200d41c5001c00019284204241000307486031030050000c171032802e41d1458607040d449008a2241d400c04029692515010307a40a60041c030038028010301c01d81403420031f00425014031504413000c1c00d40460011024540104c00210924049141c0a08041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389805701 1250 389804451 389804473
    0x60906090c07080409060b0c0601060201020f030105010e011704140d02010e0d031808130e090c030c0108070c0b0c180d11150c0303070e0f0607050a08090f060307030b03060a0608 78
    0x59164040b80050300e40c901e0600012480030003500540000340014001c058407040103880c614188003040c0c0c020402c6d0b80c41007000700070450080301680c0c1141c0003420050b55440c0310f440180e45106503a03585144014412007084204220964181070001070007040710b0321680b1042090b0308030703006140c4050059000d01c050050b0317248650401814014480e802225030900740c0d41d021136541011200462902001c54107001c1d2419251040303038001030700340040800203001c138040303611100707402c1c0a1810402000001051a130050040c0802c140d8001412940c0e403402031044285500030500840d107100190107001d06515203040c440741701a800c03c0381701d20305403039410812035240f0641c1080000c2030f1092001d500e100c0c1c03003440070f50710a48081d10b4035080c4040f00000c001c0090403401180c0d200d06014409070740070480000721301c0710144d404003619944001400c00601c1822041038041c0d40818008204200941e2541010410300010707401c845854840c41c2c00241a11b00d00d00850700240d010100101c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389806951 1250 389805701 389805721
    0x70b0c03070f06060302121c031a040c020705150403060f151401170415050609070507081b0d0f021203040218150415030203120403030f0f0e03010f090b06090609 71
    0x580740780f203030b00c000034010740e20340c08210380c146c40384402c80c1030ba08608a201030000e042007060107516000d140401442ca2004418190505841c8656019a603100c0f50100c60138002c0005002a14004209000e1000303c02c0380c07066158440d0104952440c03c0014842c0303580014083c080b200d50260300118045810b00b01003d0403000000300c050704124a0000c0c52141d500680c000d540a180910400c05048040c1110102901c10140490340182c90000401c10001d41c40026280d960798011501580c50140c4002e41100c80a041042110340c0621452540000d410060303401c2c0c2c10030550240c400303101d05801001510b000c1210065000312116400c0419503207030008440e802183c030300040302c049110340041005c82c0e100b6950b19001da5410392041c007d5140802491030b1081440d1145403a107070a42d50010500904120001d007488104144100401e0181c810034110900103002000b08115540ba558090400740e2416a292001d83c004540a4204140387c14421100644900c40986600c8000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389808201 1250 389806951 389806973
    0x206041509080409450c05060406080403120903053f0109062418080610050f0102010e0d0e15070c05041103011406090a030b07030e070b0c0307 63
    0x30248280e9500003800004081102400141040c44400140218040d01c0710400c0c070407280f52013032042581180005c100b0104103c0e02e00c1d4490300d00105400c00d2840ca40b03024004443e4100d1603110102040c04102180d01558407031241c1d0088d51185074100f503004003101107840001e03004d80010b2040202c961260300e440700314071610440e60041000c0f0840440c10480301003604540d8039031080c0c3d110040107900514000e80c0c0c00b800c0d20341444400d0340b22040b221131000445001031800d001d03118084900303e5a10070345110060545005032911481c11212200903146540180c51040e001d04c040c00f4003030351052040c0c11300e00103403000810104500d00815182c0e0350a141c03d031070380b00c0c4404a455401c0b1610202401c3c2c950300c546102c0c400903062000b08000d4500409042d14420f10500040010305603c0c01000035015054919564410b008004030f1990000303030b00301a052010756400d000c5c0720303039140c0d2141000a4902040d2103da5072a154107003420300c1100c0e640e540d242c1c4284016400300e0003074250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389809451 1250 389808201 389808233
    0x150f0302030712051008010609020a0504120525030605101d09030405150c011416030908121608012306130906060c0b01241d1903020a090c020604 64
    0x21001000200004251013080b200406000d605040400103c102401200d0103043e0b480c00550400f10890001481805207206820300c85c6c0b03100c6003072424480706210781c02441c001442c5190405d101010043d168600d288801c5414515007800a0090b1804000b0350f015204800380000200300300d000c060a40200c040c2500e00b40340401c000008082e980e042100c0a40c1205c8201e01b40c913440030030994ac0c00c4411070059848100103010030881c40c80d414550190b180411414002031a0710541002045401075200e40c10344082072206001d8800c43c07280924841010031303555110300f07a032a641c1c4182c0b00c103200304000142d50000116a541c3c0e2510201400c80c078283d0403000ea40e45640c9600440c15110f0f164401008607852043e00800e00200f5004d40c0d01401075a0369140303988404940c40c110b440070f05a0b20104101504a5a40180d0001c4010b24110346000302805a03c0d0b07035840560041004500c022441603204607800a030503403260103111204000703900541099030f9a80c451000407240721038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389810701 1250 389809451 389809457
    0x317030c0304020f01112a0d030905090a0f1a130905061303020a1b0503120405180c160b01080c1c030c1406010b09010909020304050d05090402040515090406150f03020307 75
    0x300703044604071b080144180340860700c034044442c5507154040d980101c2103254110300031418011b6820210f904078014804407030342502c99519560314050b1780c80041454890504105041c91441c0d020032103080e11044488e001250044d8680c401c0c1482d010890701c001d80020000e80003c800a0f002c151802110710340c0070300a0042d901c0c241000e60b910002c948a0b078080080c4441011800d00c1281030401c0003054800a0b02011403500d400d10300020302c0d421081c00e0b20301030484050002554244400c041d81c0d0440110400004c40d45810301c1c090003418000d0045101a100340211000e0038138010030402c4401c5000e08000044030150b071002c40780c0d48009072040d111a25000380c040040310342000490300070300380580141c5e00c0d035170144001041d81c41e03d81e11207420f644c010f10a00c0081140400d00001c11a058102548d5a5400c000454043c0c040c80d400300b41e224030503051190400d9001c40041c48800340881e0700f00051034a51400450026180280b400024000b111080d10356020350f00031500882942 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389811951 1250 389810701 389810717
    0x2010603110102010b281715010501090e04060203130f3e121501060215063c0604060905190f0b0a0c020d050d03050f240a0e100317030c0304020f01 65
    0xd030503c500550704c0001504668050440885882403c0040500ad008246030544c4111325241d500104c03c0d001400242659138004042050000b2003503440c14501e500541d9803804042070f0400d00741d200001c2454810300c032032900d121a89190800746010400212041780b0707190126040900174a164005034540c52440780f1520808a400f400c91914001c18255004001d0b61081c0c0740b1210b104a009070141d070160244a080c0b520718205889505200000c000111034242040082a1041720035a0284c0c1e420007000200425881d60000001d02a180e00343d4180c0a05001e500622040d245148500c5014220302901800403410b224001c00c80b181a6242c0f130b6416191640010394000414103049511ba80701c10380d964885901070003200d6020000b80042120341c03034120300721580700c07400080d000b8010b080201030321340079622454027070003900c48544000c20074078203000c3d16011a0081c0c0400d0b207030b201c1c90984040700c460040044a00c10b00712040000d013191103550a100c0c41c00b00c0040418140b044807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389813201 1250 389811951 389811959
    0xf090310020304050a141507030b030c0a060f1404030c030201081320010e0a0e070e180109020703110604030203072409030e240f0a02031902010603110102010b28 71
    0x19001640c0118019406032603103800764a0040a41b0b421081507241c1500f122605400f60308500080315401380071414049081c16041c40003070b080c200c82e80c0f20300750b016081b0000850b00700c1c1e201c40c0d5a8200d26403078a8000c50886003c04100081c0145c0c03000900080500c00148010b5101d1054140c110b42c1c841307100708800c0a10780d1041c03e154294050703040e0130421039400184641e440410300301001d205450007440d0509015180410f190300034001001d10061200c4100b054aaa8a804145954070303089030b04075507140c803101806540861000c1d00000c2456465841520303001c5049801a0b5064000398a4016107640301d4907105144881d0b14a895a1910f50180240c240d0148444282c801ea4801d03030165118400c024480354400e04c01c154a80d8208111400e04c081c0381c3c00c40d100b44461a014646400a186c0101c0c55486000c0d250f031502040c0503d000504ca4054003c1405e90b440344403480359000c110401203003202e905804407076000a05d5260a0070300d5110440e0a940c02c2a032243c503207142503c2e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389814451 1250 389813201 389813233
    0x30c0c030c12030a05070e090103020f030f161406030717060109080105040c06120b130b06130b040501080a0506030604110a0b121e070f1b1203021e0a050f0903 70
    0x402e0b008802c101100104200a008291103020fa115080f400c141e0202d007021004030b42c2007401400024010141e0301d0030045555001c0050a0002c4018000c5038040300105d40c036080d100d2031900ca00c582c0c45050171039660b03903441c00380e0580c0d108140b95038908981c0e1420044510744004007400e818148000c20501081d0b001080c001c09110b01c3c01090110b00d45407414000400c20b600c06508500350310f242450034030f199910410300003005807400c0d1000c959500a0800180103100b00da06100c2d0303d0701401c200040514034038001e88200d403800d80300d2441e241d030384080020075140b0481d0140c0d80740e005031000800080d4004400014000050b200c61000303904c0e0303200301c1e11590104032001c83c820003082c00c10103a15106d808000c0e240e030301192504c41c80d003031041d0003411640c5800e020206001c4003801001e2240300262500a070740d80c0040a1a00704030180ca0041c000f58804c1c04006090f881000613900001009011100b03026056501e2900e0a2928001c0311016000300d420150b02d030141408004220380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389815701 1250 389814451 389814463
    0x3200706020a0f090f0506030a15031a0708040c05010f09150201200f1c150b03040519051c0e0402031f090b091306090203060411010f14030c0c030c 65
    0x88910401aa40c81580c1e1014049a101001e024200b04882205000c4110071845c0307074046800a482064981d140c0162000181001c0004104a0201c6040000500504600720300015101e207045000c1e5803501e100407182d9403401c8401078420344e11424200659441175452840c0590b09181a01e80542c8031a5254843ca25a09603200140e444901000002305810890000802608085454032405806900f06409610700c28200f0070190ba600301d02561240d0407403c444126005412032841c3c40d00035180c500d41003034800340e8851050001c0e00a100071001c100030002030b006801451070440c50401c24980c1c010b65000034007044440100356a1300c0d19640041d40c0540c5050184050380e520610070345012315000d81c403408030039041c10413400d6181c8481010640000500401310a1700b1200d09080707028200c900c0000f50988110342c204424018030700886900c541c03090780e03030802c000f1020b00121902c00700590b0410342c80340e0400102d02001301072001000701d000c4000030303241404070950a00d42015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389816951 1250 389815701 389815703
    0xf180109031d0108370c051201080a020a030b090312010b070201020105091204060f05090310060f050a0e060603040f020a12060b150706050c1e090405011a0a032007 72
    0x61000300300704508030402ca03029401101c0070720f806901460000c5c4200c200d07610501c18031410380c052140c8200c00e6941c03120b5101241d410048144048120460000d116900c0400e00c40c014400180c0042007810300454804245500200714000d00c1d0b0071611780f1040d20001030702014062104001c0420b0b11081860b1301c0e1f000344001ca40440e01c90f100e0740006400c0d540010700b136441c2c642025020031140a100030544040d1046460801c1c1510740b908001d443c0361040440e420b81c184200c0d8200d20190000f41c100c88142c840d6840c1a40700f660341c13002030080d81e00c4c490203500502c1207100d0002e000c03030074000d000e154800c1c02409800c62050040d00802d544444580282c00d01e80000701c0104e05001140c02442d041c00c030183d840c0c03c3c90200000b6480b005000e0008003c0c0103e4031031000c03a8041000f041030751402007640045800c20641142150216404190034a01603418580001400c214500304c89017a0400505641d00c2d04012580850007060100200d4544840440c01841e0003103048001d00045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389818201 1250 389816951 389816957
    0x141903020415050d15080d0809010f0f0207110301022508210702060f0c0a1101060e07030e070b070206070f0f080f09090f0907090e0a1a0103170c060f18010903 70
    0x100c60350f410300c006a401704e062141c52006a0041003020000014820b41100840d1800c01d604e03468200712140501a0542a100c0050078162030761100ca140b0340c01012110310492980311a8146142410700745c1c0209c1c000d041840d5034022280e001c4984c2d441d006007007030344100a92440c00b22600551221140c400b403481041c0c0c0c009070104404150100802c680203201003907102000e1a051f08850442c0c411040400c0c100210700040c011050800d40000700505070108502d1943d21304244010000d10160f2414105031151070000100c1070030704812111801d40141130395140085a80341e01f500364200590880307112403000f6003040416a104098080d180760400d820b42d035030103010200405040040c1a8900c940321690a06c01e0010001600c3c2049480d5030f0700224581c030140030f0b0076041c10740c001006008400d0f840810340d409550341c52000d041c4c0e0320558640700400742e02c00c1070b0311440c0640410b032a00d5602c8040820030f509840415254400303510900c2d43c820303104c501301150a4800611044000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389819451 1250 389818201 389818207
    0xd02030a061802190e04090c08060702150c04030314070b041b141011070b0f0d0c0f050403031b061d0706030e060406050c070c0605040503070614190302041505 70
    0x4840d490000000312240da4000941c01c2001c240c10305480240641501014050505c010707040710307210354101048a0f5000545610556039615115413240000c03035041d401802040100220b507008a600c09001c1c691192029082c42e08581e0151800a080c00c44460151028405000060090301300f0b60320591058200540c00480000c00c0c00310591950070090900c070300741c1403a01003510b40594041e503002c0545000280f0249400020341420b825401072144c03c1400074540c0c9011003060000c0100d20b114010402c54a02d01c0082100c200341940003c0001880400040000c64401c0001c1110660b24000580c210042031b40c403a411620716003c0780040c03424208080c0f01c2c020050101d10002c240d02e08041c00b84110486080342c072020000c1c8000e00340d9603688049078155055505a42c10a640711111120661321088054943d0300b01c1d100e03061003807041d11404034205100e0080e401c0c0041e8041e01060408100d00c0a400302806600d5101081590030700000036148034002160111031556214182d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389820701 1250 389819451 389819459
    0xf06030b0a060507030f0e060c010207031806080108191704030516151202030405030f0a02150903040b04030602030601230c06010509090a080a210b010f0f02030417030d02030a06 78
    0x901081e9400201409400d01c181004a50002c80860304d0060b00c0c5032942408201d540015800e0160102000c042c0d84085580001c158004062900c03d5080d405042444c940d11030007100c00c51424001c0101c0c0c3e13000f8a0409403060303102c40071000858400d0342c411880a0402c80108800d4000381d00a03521540484400101d46040140010107446803a5410406c100c0c1d1300d0000d0001c100e400781c2c9000f41e0340d0020005003405030910580b41c000c698900300a0361806a658000e590b8880034402d0b1300706020300001300740c492600004850490b00550011400c0c40c1c5152100002500f009048605200e4a0400f44070341000c06594914007948003041a5119440200a5860850305811240c0901140400e10400c5d26000540383c402c6503001c42c801c0d954100d07465003150071240344503007441c0300c40c464039910b102c00c5e00c2ca03000030614050a0766102604082d21000b15102e41300c0d421000c01682080009200c0c0088400c1280d5001445000f2680392000320081203040f42d200b1600c440302c071543d07640144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389821951 1250 389820701 389820709
    0x503071107060f1d0301090c050a081506060903010b09010e1e1b1303060f1409010902181018050901050603070e13140a03020d030f1808030a060f06030b 67
    0x1492059080c4000e051180c02c0c8107001c0c10305074500c91100140011001c1e5a0078580850800c000304a40c090000d02c90b00c0054908030f08502094015103104108d012404502e600c070000380001c2042c2500c403142e40c0e9850350020320442d54000c600b420307055500d8808041c85622400319080c02404c40307403010344039031402030100d600000240701850000d50608050010306d5800303c0d1583c60748440100d98035664801006411109031003680020318141c01d0098102c0441da00764407503044c540380301303907020156940d40141c0c0c0d003200c0d49210020b520038680d0450991820806604035403041011401d13462503512148280e011a8010b07440719102a265420894064007c1c01025005081a002080080d007002082002d490703006101c1c95000011310003007400d006400d07452880309241c00003500c0a10343c03e410025124242c403070350200860b040810381c40d41d1820500c903510744101c10a2500080094695612a091340050101d40e5001d44030140410070f109000b0b091070003042c0a4800040b4214400140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389823201 1250 389821951 389821967
    0x911040507020706020a17130b0c07050a030b15061b0313051f2109030c12050f04090b04090b090610060201020f090d0f120201020d0605040902032515050307 69
    0x941c11500400010072036180c000a1071300585a200031000c501918442c101c520502589040f03105a604982c0001505480e0390000c00d03440100d0000d5804507526042800030500d801e1000902d0340c612000061000501c02422011480c00205035038644503110200207183c0001841034561a040000d460095070340204112004100079201001070307040e814481e640415107544001c0602c00c44d0200b141c0d49114184004110140c0583c0030030a61380700d814001c1c13003a03080501c1150540c400541140342c03e8050400ea8081c18042c41c0f9841c50300d811b00d040307880a000c50180700360300300d9100c2c072400c0006a8a00c400622a003602c0004100c60702d0300181440002c07034154040d5040d0391040084079004840301b821516030b180c3c1918005440d12180c42c2510284940d09005051024128000340059034190020015144943d10610a040c0c4400c10801103903500200294140c3c41070040740340074500507401195040b01c0180505404e543e4207003200d01c0c10a0003c1280024000000700800c843d0003000b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389824451 1250 389823201 389823211
    0x90506041107030c03020c0d120f0c0503091921020108070305040c030b04020105090310020324130504031206060f032a050306060c0f010506030d050304050d030b120109110405 77
    0x2403140401041e260301c0700744200c49015007088018860001818000c018041203507a02030041c100c00768550404109080380c0c00c1c0300400082c030921842c2403041c8685040001503402a0156190422040170421400110300071210b02d8007a4400000d01481c4104d01017000624010710b130381e4401038620005107034800080103442494034003414400491406000c2c0c00c11b80f0390068001c4c0741511540010f07a0070b170060540da2a03140c480c040f1008050038494024602071041440058500d070316101352603c2d05074504503440c1d0411080014100004603a400031038105002c0c0c10902c0c0496100c217011020b803580d90304031502251f01e0140e00c002a03071349449510001529507007003c04042c41d1a4141c12030100c50302c07040b030400070044040703502603031100d084403900c040100865280c1da4440701000d0107001c0450b0348920901401440f140e12500071021648600c1e40301002c2d0a0b0b0460020083d80100445580250841a40c031140341282e1000d00ca040b0701d450041c06001c810070343c04401c02042d2480101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389825701 1250 389824451 389824459
    0x605010b0a14130b0d0b0f33090307170714130b01030b0307031127011a1908042d02040f0209030a0f1401050f04060b030a050d0306090506 61
    0x8041184240d001400340d82000032070078080d50703414850b032440340d920243d50000480014000b83c1c1102c003200c2544002146503041d6003010f0204440d1040000c4680920100d4a0ba04074140350b884010039030f401c100c7e603c40c41302800d041c2444002400b1a00d40841a00071520130300c011011075130400c3e810400e140c001c11016141021581056002c03941500030205545039940d103803c42c00105030300030340012000317420240c103d40d0416546d04002d0540c0242600050290302604240071005804943c004900c04554000c20312603443d24241200c141885c0050640b440c805100d07070740c070b030841d05041200f8802c5507650b180d00c0c905040c140004072074880b01c00e404040c0880803e0544540e0030014010003a9011075002441450083c1ca1501911416100070342c903005820045080040780d40404c1000350003144180c0c01c1240034000a0300f241e41c1901c0494000c4101c0d0001000030b16150080230307022402405440c2105031654546281030640009100032a0b200c001c14072401c0340c0c5104495012000711 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389826951 1250 389825701 389825707
    0x10e0d0f0e100c03050306180a0911060f0301120507030206030403170a09020f040c090306050709060810270e010c0203030615091302030619030813060c0302060c210a090605010b 78
    0x158014000f0310021000a060100101c0054003135516500c0303841c0c000380c0d00c1c0ca0362000b81c036107403815000614591030211521404100d24010b81d04000c0251041d039456404d01c075180d64205059101316034130202c07003111188505d00c002310068480402030b501891090300d07640441d10079071b004910740510041c01e5148241c503184481d800b69a511300300112000060310000340810b100f010407140c211842c0c00250243d420b01c8140101c07568050307584800c498580e99803161302d0301d4500a40148098501c149800000c10340440f11110140e0240c942c41030030340180000d1042c1000540c0383c2034a401c01c1022000d80c002008004072030038101003210045080076220f41c58201c10f20002128180e585060038a000e80c0400001c0d8940c880c44855080300c003407000780380c1e82140e583c81e000300c1c2030340321404604000b1469000018440c0c0a00d0138400754aa26030080c00c0d50780c2ea040c480000d10b421004040c00d005208520301000480c96107800c90103142891004076202004c3c2c01c000090729410307404820105410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389828201 1250 389826951 389826979
    0x603060e0a15020c07170c01270312030e060a1b0c080d0c051c0b0a0905041a07120c0804060501060e2412070c05010e010204061b05010e0d0f0e 63
    0x7065800d401280000016103034904132081030310340b0407550055059a802281800950b0100040c01d50185170240c1e12400b6189101440001c1503003041c1c410900070901920034030015a031107120652040c854500080d10943c41c144081c6000001c0d9802d030913641d83c070020501e9101c014103030100d04402e1800c2501c08000c4542c1c40220a00c038400314806080d544071040c034002c520950803602171104282099101c0301201c0c1071a0010304403109581d1159452003000134045840b8040c0b98499904102c01070340c0700c4412100b09c080c40200030941c000301b001d0111003c0c910400c1c2e12850346601019511042c051609280800490700180c1000060000c0384040200d680e642c40c0c0714105010810051ba0140754010305899424002e0400e041070606440f410409250340c0309120360200d90145009115005e141006a805c038803480c05424009003103803086071228120119121859031041000082800030481d9140c01c0c00742100903a00012650341e00c9140c000c4d4007545a80050808543c94860035603c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389829451 1250 389828201 389828213
    0x303112118011104290406350a090c0305070803040302031006030507170307170712081b07050c091e07020c0901060309050102220609060912020405190c030603060e0a 73
    0x213140b041a544511086442000005148900c1c295003806071381c10361100e0f06c800004d808280018524103000610300d0700d4075941003e4210b042c25040c040c1e04403084c0c580b00c01c49240094811400d00361104020b490000000030710400c03c2c00d00801c0458069600c0360300310310406081c0501c41c40b2840d503150030301405101054011a42c4400c4a0340c1d0307030713002c8150820380c0b12080c1507000d0383c0c001a100321111f4180d0364403001039074006c0946038892040c90650054088095401200503911180c80c0c0114003180b9440c024a07070000c3c00054010021140036040041c005005540c0407114800c494014000414092240c1254140c1164050000d02030048400011402400d41441003000f099202d14005040c08020b504840c0b9450b40b803403002d080c081d02c0454621103500b06101c1da4000803441d60000901620500d82c00d4280d5000c0c0321111000395403602007001500001e00036016004031208164400c82c1c0c00d1240c03c2c90784240e5140451140c0c6181400011a46110342510b82901724420960000708 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389830701 1250 389829451 389829457
    0x602010f060e0115020f030c160608090c041e0e0a020114250c1d0601090605040608041416030b06100f120c02210c01062103031121180111 61
    0x400200c050031362510306400c910f80110756141e800d0301d001c00a103410140c60082140300380041d180000e0780559940f003408482c680401c80e4801000d4001180c449000d1405400c148418802040111808880d0511040c1203a003840c034100c0d03041d44044a00c800310b5800580c0039002044110005043c8880c0c094a050480c3c00d201081540c102400007120402218245040c054003484546100704925505010482034060780c00034003040184400060441c403e204440c01d0724040d9882c61502c1d107407551603442c1100c8040c45c2a016000d500c0a456801d00e10380ca0403130083d4050131000c0d03244e092000c244102072454580320403c11031b50307064000c4035503040500018061400000000d03410300e018012030805425003490b0035198603e41c0c900110150513070140203840700b03c000130842e030b582d50200d0328106081c83c500810804011405103001c43c0c06588074050007249400907a107884604088109048003080d51041c180328910140001d040320300c021100d203507100000130005c252030400c1415880c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389831951 1250 389830701 389830709
    0xc030605101202040317071a06030d050705010603060507090603110f0301060c060e07080a0b011521020f13080c1e040905011b23040f030605090102090d0503040602010f060e01 77
    0xc030982c90707420000c010ba0742c111401990402c001482c0240040703d007083d82d43c4607240503184a8440141183da840010703031058080c0304010010145034079041001c1d501500034403010b6410795a102c0001010840c640a0b20744500b1056071001d040c5c0c1d040090180407180c0c1e88812090380601804100303a0880c2001c1182d043d10700302c0c00c01c1c4010405d940b070a580589080d02945010b406441000140f03e200056072528941c800d0320504035030383e01ca80016000320b01c85d106030400607464100e01c898502007100031980c035030f000070005031070924003481d8118941d000e00155000c070080051700b00300904081c0a6041803910403507018084030300c1120340b0544020541c291500c2180c3e2005103108010095000480544d0810401d00701e0035a80f0781c015200c0c5071010b40c4030400b90085890450a00a560121740c1a540b01c041340d140120700395220680281401032110641d0341d4200a40b0106544002012041f81d01c181c0003181d88900b4824000c0c00d4581d21003225040324108030083c000e040810052a05603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389833201 1250 389831951 389831957
    0x506062d18030633220506120309060a110a0f080702040507020c01080402040b06070204111e0c03030f041e05070801060f26010b090c04151d12120a0809010c03060510 73
    0x1012100300010240d105c0028000710310301010b144055154a00d42045200c0e02c01111000d00140baa10241ca40781d10076451803e81c00102000f401050a01030a80301d440030011600702c40000c03450345d4600646010341d07402a2a000408a103100842c03410340a016400106c520280540c52a0400040d1607254080d10081c4503544403009803150361149415070b40100d4006000b886420805415110194001c050110b190f040a00402c21858100f030126800b01030342000452465598004d00144603034003030421200904442181420441e0030700282803114040c03000341092500e0500060f0031982140d01400302c0c0e542901040044002034408250280c0107a003505000e11035415840c1d004200072402540d000e454041482050300034240a0000d0707aa841c0b003042107951001c5400d8502c410710300000c3c040d140c0301942442040c148807a0720400d45010070708968600700704107030301440361300010200310000309083c04008041c0390034003d0602050403030808004003418800410420340c02501040c1c24 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389834451 1250 389833201 389833291
    0x60f010c12081f0f03020406080a080d0906020d020406080a0b09010f0501030e07092d0902060720060a0309031407050a17160605090606040506062d180306 68
    0x405290f02d1910701180364200098050603440e030303a8520216003580001c1e0700461600c100400c400900150f9004110b801c109281e0800c01d2000c0a4806410f24120480f031440d02481900700008a50010b400075046540340d08260340b500e00c405100b1a01802c05c0c03540b151541c038004024120000c03000c10240c403404e180100300003040c040e07403624165045d449101500d1400110440c500c00c00c8200c11250683c1c103072800880c0c0041040c0d01e056409495000c0d42c815410003120f0001000c4000c0f00307103440040c541c45d11044240500240d050f40240d50941b01003601d41024204065101070484000716222502c0c5040c195240c0310960340c1c10081400030003040344455842900d9030560f080c2c2e1484c0248280c000300c44441c619000740506410369504402c1c0c440c01c170200f450340c60b05001d568407406000d84000e0811408070300030030b282700c208204540000051014265608030090040000b809600c0c180c00524000d00d0601d40381103030080c00c100c2d5a040c400c00ea840c000307954080307204c81514040c1031a80c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389835701 1250 389834451 389834461
    0x90a09020105071b1a1315020a0209100512070311010302030601020f03031e0f1b0a050906030f01080c150306040507271e0b070602030a06080f06060f010c1208 70
    0x56180703e6418043d1450501e46296051390980314101c50644e141c9000c0000c202009901a0140d80103031040d04103404111402800201d4040f015417805090610441d26142e4258022428081d01620107400d0321110560a0102e030500402c400d10008842c0b0041c844546107844152005c20b081c1c04803410503030000301064103603100308081145014602c081c0c960b40c3c1801c0a1510002d500d0011000300c40000d940010102c3c44168591171060001040c003011014107401c940c00c580d8404641d00d002d200041c48003101a0b00c8443c0610b101d85044806021594108050ba41c0740c0020101c00c47d100d6004000c81105000391501660741100f4191008244d64854240541e640124091100080458103a00b003e140301700f1400c1c08122104148116136a0510394400c10b08a00a401919260807003004060b000a45d103a00565009404c0d07540013a803103884030311b180d062140510301d404079580550240502484cdc101d1a89205203002d0802001d021050b5803090b6031002560340501c240480b801c0020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389836951 1250 389835701 389835707
    0x60f260c07020a090510050409021f120914120304171606090f020108070807020318040e071e0e2502010e031303030801080307082a0319030f050105090a090201 70
    0x61440c40d8018040d18183c2c4d02ea412600040404442800305210790481c000b600e4100742c0716440c4055000780841d803c001c00148902c400c1c808440f1402c082090005220669403054468070011034824042e5070003031140c000342e43d031809440801c03c04800c201001844002000c03101c1c456160901207403010b884841e804c5901200b0004c040c5c001d0201d9060400032010071540c0352285c00749030301c00d0725000782c40d0300c5112040361494012211103016a00c104801ea6410a00301070f0b0400910000303101046070441d0365000c0342014076170351110381c60f54200d142d01e80c0246c24075103480c0d0280c1707074425041059140149003018860070074003107102104124580303142d0092003034000b1001c141940c0c003100d42d5003c0f100d5903101800d003a40300c290001008031001154a442c003001b12460603800010300ca0030102180d6942d070030342d80c99404003001310105024040e03000710188040c00c0d84c2894023000050782d007c0200b001c0d050320b0130304041c1e0811915110040c042981c42c0189650000e218280015025070309200503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389838201 1250 389836951 389836957
    0x905150a12060b1005030901050906090d230f040e0a0209131a120c030c120304062006040b0601140c0d140904060305010b01021903020a02090a24060f260c 68
    0x310750802c070050740d56105136030450001d50182c600d0174000c218540e180c0301100d469140548407140a50004480d500300641b05e07140e103c48078180710240609548846515035515801003891841d4000040380400080340603801041d44604818000d510313103080c1000040d00c0b0402c034140e4070b1446665042c11900309840360341c40f243c8804040c000d440078800702e13801c10b90750b9a011106c0300c5c481e10406500300021b0a050322291503d540c180011420681420000c1d150302d0741142c00804203c02d10454003001030010000c1030f0040d40122180522410b1000006141e00b96200d4402c501a40c204110140c030080043d58040142d143c1c03424010050081c01c0c440d95038816010540e60081c24071070084140981944003400042098003220801c00600c02c200c48813150303424010b0052b800c4414460090304001e00d44641c412641d013000910070000101d455080451590718441c10440000305004440c5c10405125031642030707003014030b881d030315a81e11001803003e01e200e107803c0c0011410200d034020400c001a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389839451 1250 389838201 389838221
    0x170c061804050901090b06040c09090e0a02060d0e0105071e030e1e0f010501120c0b030603190f12230c19050a110f01080c031f0b040905150a1206 64
    0x400e10190a183c041030b03002c0c011801054415001000114010340f801b03101c1c642922189072185032106140c440414020304103014021564082c02c025503006a9071074000b400302d0b40304000700182c0d034410350798a01d0031580010301310340620802004140d006440c2c400e13071000d440b500b03141c041440820100058105800e08048003008080800c158204441c0402c00b1040b03490200f00810203a031303859001c0300524582020241203c100f0070024440c00d4040c400440c0d00407005822220600300190200c5040440c0250a4480d40b288000c440100702d03c2c020101b01021440c540203032661640241007200b0710940420380a0090001582c24052405000910f0303082000303c000c01610344641806520b80340c2c030100031194030855031008415841e000400c90310201060b5902d40c0581e45140a0006903400982800d40181e4001c0c07061401c4c4800d02c8c000409000588212501e661034880584140c80c800717000300d2900650b0462110b003d468a02501c8216082440c520a00342c0b42c50401d180241800c0c61 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389840701 1250 389839451 389839459
    0x525050d0c030206100f06051305060301181a031c021f06050a06140a08070c0b04030f0e04022817090703150b090f0a0204090203010e040c170c0618 65
    0xc9468150464001c1c680a4000d40960720950391380148032242d082507000700c04001ca0424403d01103148160301400501002085c04c20f101503c0c2c40020315940c0003680140703040081d00b00f01d440d2042240c02400754407011585008541803151001030b80703074106030f1500c02124201546142144d442005101040e9224040807520120f01d06901009450b4500549008900200000a05034800ca100a410f00c088a490608002400703100f1075142c14090010410440c6000c2c21070041034030703802102d000714441d840c1d500c082c2d40358040150852584c201a20311603881400315414080e40560000e0304100d10b001c0113002201c407a04151030305150070303000e10350302440d1404010340b2450000d201c5080e03a02410940c4604003803c4000c0041c0c90300c03585902d800030905008a01748a000398070994205807070700c10250030507486905140880c0c000343d02c1154006002011320040c40f415a02d0343c0c01030280494284901c0c0020056180c1d151030b0154100c0c0620130018006111034415008036a0300b0700700030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389841951 1250 389840701 389840713
    0x2409010204090f0501060e0303041805060112020a0f020601170a060f140406090203070509071b030e030f100e010903020304121a0108060a05070203090109210c06050c070504020a052505 81
    0xc010360f00200001d0080d01c01052260075020b516140010a40e0b088464141c01100034040408140000d0b09016099038184080c3c05280c4a10b04040d0004c2c000f504041d0755800c20344140a00001d00e82031060b4040c0031441006081030414541c0407480016164000c0310101e105091894584014225020050319015400c81030004000e2560003040c00c140c002c8044890340c94591040100c1c440c0240c0710000858000d4031900e00c120f40d40500f4000542c0039003041d400d012201b4020904040d10740880c14800e402502e0190007400d140d100d080025118003000300b107a02010796002c1d549101c1c50194010460034258020104520198141141d11042100d280c16580d9403d965a80318400d4a50b0101c3c00c0c00e2200080d40c992002050301e20038081696401c10f2130b4a00020f910480c10002030410b140b4031100d030104081f540c0070383c011000382007690710242d60b01c91440b07145052210075004580318900411580500307a9004064650786019581d18000c0d1385400070fa034820a01300c14000034820b008072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389843201 1250 389841951 389841971
    0x501030f0605070e0d0318080f031209030a052208070608180d0807110f0f032d0702131508030c0d0201140a020309070b070507050a08240901020409 65
    0x244450380c030440d21403a0280002d40342c0a01c143c8103d8010810290001c03402d4410b4004a0301c00c0300951030703606101c1c4108002548074000c1d0703410710710b6114002080c1d40c4000340855036039441c01d4200354000d8000b00030707500f00b4920701e40c000c2091007401c070b000100d014035200030504440c07059400401800b034102121403099032070700044c10030102102c0800c0074481c00411040481c6001c1000c1e580008580d03681046035030f82042c29036103c140f840401d503151255940e81d0010040400c4038400c0b030301c07041004540b40d401d1000000842c0d007140c95004681c41c110340c503107600388103901d00390b800031581242e120480b00d1003191650010a034119400401c0080000006840d00010006111598860007552007580c01c401d0260309a6400910252000580741e0020749192880d6018681240d00e0500761074030990703a07201115158011440a40c0c0641020381c04000c02e107014078800005011040140500e0b8200700104000345c2c0f500f1141811243d04100014034a4800390304503000360000c180108004404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389844451 1250 389843201 389843213
    0x5060a150905041109030a0b0a0f06030507140102120306011209050a06060e130c120503130e061008010e18010b040204060c1a090a0f11060c160609050f12030706050103 74
    0x10a2086500031850714118130308007901d03542154400030024008210402e40390b65140c1448400800d1110040d5442c0c41e0785d4a124220f001c0c0d040154000c1d8001c00703850b800c3c00d5000c1403d90640c44480e05541c00078a4220304c601d14401602d5110509007004c84a44844030161805840c0c1008010f12500886032180c0800400341d11080c02da8030131071f034a580141d0320800c0f40340c50100c400d1005071214035140e6042000341c10140c2071121507071046040c0d038208010032107070207160007054015400d008038020130450070b400c2200e03424464100907d1b16130899450502e2001c01c1c1d880c00b0382040100c06049017215001d004c250444541845c1c060702c00c55803203940346802071007a400e00b44100c070054401c031b103201800740e0450103142c05614040d02400b000079450380d50034510340020b03004680303440c1845010926980c0d0784001c0e040030303a00c140140000c60384840034481e07490700c59000341382440591a02488562502203000303030000c40075156000519440c9014510f540a1864000c0c070740d81c00d100002c020824 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389845701 1250 389844451 389844467
    0xd08070510053d05040504030c050c0102030304030e060310081b0103110a0801180b0301060b0a021606080105041e060603140906190209060d0c02030a0e120303040605060a15 76
    0xd0460400032921100950541400d24a0801e00c24403e000350468400007003589404005402c1688040c0c210780d500c0c0030030151107086030f095000c10010104035080c04424005a50013110910103103240d842c16580c040d10410500d140c03540100f901000003080491b141c0e81c010050b00c1c103207003107030240c840c50380f0013211980c03280d584180080d09101d0000070004804003030b01d50061a64851020503170a0003880b4030520403006400310241d450b102c0c0d0088c1c0703860a00c10395000c2c0c220b40440a070394240303250700a840c0000282040c1c0702001001d000300a8242c2c40004e0505441040f40d020076400d030052145004c04155540b400c001a1504c0380002c3c60b0340d05503009a0407949a0300028403507030340351f007a800d85900003210f1420200d4154a4142c0c0e000c6100d60082090003401003d150030440c06030300c62000c5400640541025a200007402c41d60940c008001c0c540449044452511041107a00070355224000980000c100f240c039000810b01d65030301c003035802000d0840c0410f006402000c130382004000302 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389846951 1250 389845701 389845723
    0x21804080d0f0e0d0215070c0f060c08061819020a0c1b050103051807060e01050c0102130f0801090f060b030703080c010203160c050d0c030201060b13090605060a0804030e0d080705 79
    0x110400007401c1e40a40080358462412031801c1c001801c947d9903a0082c2c030003061109080382c1054060140000284051055109a20040e44ea641a6280100034002d5204108203000c00d035001704000c201c031f030503505040c4030b0300044c58520146c0c458540d80000d40380d0302c0681c0070092295882c5100c1c1c00304c1021804500d0215803090380d003071140e070305c50581d17440c0c40008200b80d043d15600b14600910906001c1e410110f42e864061500f141303443c84440015003240c02030400c00d0019441c1c1403080000c401003511280160044600030020100260390f00e070607006d682c400c01021961141d14008080d40c003070000707400558026072503640d20502010410300079842180d40101c0c090409184081540c4100d14070020281d00c00b00901103440c100380309071440340d0496000c808640d00c4240116041900710041c2100e80841e020303803844a41030000c2c8000f0b036502c41c0c00007401184248a54191203030310141c0940c1260b05400c06c5040c0748006000300700740c03030b0400600be00640d80008601c810000001a000c3d061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389848201 1250 389846951 389846953
    0xb13021903081c0203040c12081224120c09190c02030307081003020105070305030a0b04020c161508010b0d0204150806031e1c0c0606060305090607050304021804080d0f0e 75
    0x201000f1440301c1c00324002958060040205000c05000c80102110495501c6000b8488107040c0f6500c80447c10b980381c01100c40010b034800090f400c4a00300300c207000007000c1c6003084070401400008200566136030f50b01c00046a01c1007000401003403649183c404032000c4141d0042e410310590040c8207000e5030b01d602c1511220f0004000c0300004403140c00d04031080040c0c80c1d05035181c41c81d00a1581b400c03525a00003a041001e102c0d071340d401c2000b003992280700504c40c80b02c41c2000380201e110030300c1a9010650342a07001c0203d84104a0304050700660044605055030071914400b0340700e10800705a04c00074000c940182e81e002e9041e18018011381e40003a0390600c03d603400c40444805503100380104254001500100c8000d5011080c9902e400400400c0301c0d010800c4d42c9800c3c11403c0c02e544904040e2002580040007080d80c0d0f1052100c5014240040c66100056041c1a45907042ca58003040c200b403058203840041c2d4040102080c1040201d000310b43c110b004002c01480f100e070210480384020301c0040240340c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389849451 1250 389848201 389848237
    0x6090606050913050709140f1f02070605160f1e0812010801020c1002091801030b040308070525020103090b04050c0f0315011a0c0307031d0d0b1302190308 68
    0x15aa444c00b4440c42080315030f440d110410b107480d500080044d0404805984102039450a032840c0d10f503d00740c6c540014120302d1461401f030415802a0928100d81c1160041200c00c00040c8941d00b986605c170101aa0b00000b20071491541d402c0101d0380706545d120300c14600c1420200b00303041c044a0070241851050100b641c0100340d98901e0f1341ea08038418494004000e40044650440552a40d0702030021001c0113026000c054840050345040840c09801c2212415065404d11042c54ac1c808100b90707018180b41001440c18040400716040b1500009000d80d0320300c6074581174000c69100360440c070365255103c0348080403805c00e494025181e40c03001e510b40f40989011203c441d41403900181101203070a64442d040490f900f0031030311028180a502d418081c1c250108000005828200000c01e2824065510b40103013402c512030820712640c550030054424044054240c0c017140b000c81103160000c204101503040c0d07640601c01300360380b104400f20041241c1d0758440004184045c0d0b4004003c1034040b2449012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389850701 1250 389849451 389849479
    0x30118060e0601080a0902130c0203180d1e260702030f070513020c0102070f0b010e010806010303091707050a120b1015140903061014040e120d060906060509 69
    0x1420341c2126030600066161020440c542a20340c000003000d4005000c420019020640c158191450000c4410040e400001d0504084418040390145a9400c0391290701189580c2c49000c2c03800c11901d5200c40e80380d0552000d00401c030f00000c04545140c2c2d903aa45980204010031040c185070401c1000307034001d00449100c01d0100320042625001d5480043c54150080c40c0d1003031202c001c1d0030107202d68140399403c004050200700011010700303a0b140318102d171024543c141004085908010390011100342d00100050001942082010055404651011144050544085240c003c0603449079400107800031011403039800f80e18000181c01d000341c9821640781c44000c1d001c184e907680b078860000b100d1958044421400d210768240d0200845091a031800c0c4201c0200280c1000c0d000d941042c03034403255034400c12a480080030500c8001c3c204507801c119500ca401040c54680c5030b40620b041244200041e00b1031500c0b89a40880040c1400e80c408000040c0c490001910b9035000180182c030814260311070394 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389851951 1250 389850701 389850719
    0x10e0a0b010305010c1404212013090506040b0915070503010603060b0403050309060c0a060f1a01030b010c0b0c071b050405100308040506070c1806170a0201080103230303011806 78
    0x11b020396141e0034a02e1a041c6460300c0310340c40b0904401130b61543d102c83d9915102146000c01003a003a191210081080040d00c1c404100c00e0701300580c5400011802c03d0700041c00704070b000c500e065103ea0094444881a5101d400f41c0d41041e00b14400b20031052280b44c1401140c550210203141610040c0d00c1c2003068544405d81409035000b1807100801d5540104034030035403070416802905043d01d01800b2550002495559802540c241c0410f03200c60740d50b00e0a0541108102030600e030302c940000c0c00c1c10401c8170303403043c0020314520800710040c0284810001040c103e00c1000201c644681c0c0100d1070b00c4000040e066240407400c000d2003414412410600814880046410180c0450340d2202403e4031b000d01e00f6083c0071050300320a0301a00c40c3c409980300003480c0c40c81303e200c090000b004110002580c42c100740e000381c801500189003146a80c8a600b0010050740c00800050541c3d822850102c0da00b0030090941c3c0c0051032414484450b40404000021a200500c40d03418121080120500c040c5464a45da0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389853201 1250 389851951 389851967
    0x1204050f010b0306060d1e05030901090609051309020f180618100e07140406030b130506060a030e19050f0601081506040906091709010e030102030c1b010e0a0b010305010c 75
    0xf94550842004500c0c0b501d041c08400c001544903a1440500c0703240400342c428441644407096859400029042c0c81c1c5681c00300c000b074090724850800300500c506090200380b110503a00001e50159689102110556031101c4d06104042c00040c00d11071000403448400d07a18180039a4031501482140c160004541d1500903d00e101300e640c041c101c9074091816102c140c4004015201c0414880310b41c0140d500b1a800c0c0380244003528007910045001204c100602200100e43d44400c04914901414006141d452108070b40c00c140c001c3c5400b00e5030006e02402c2c03a0922100c0460100300c0909031504074100800840d0f200d04d078541c20801d88846aa943e121700d41c07078241e2000070700750481070b810000b00a8900740c0d1001c880e5502900b000034078140f0390303951030413000b0000c0e20aa11200011503410025030b8001c076003201c08141a4029400c60911680c80781c0076000e41302e148088400c80d0201c0c461181303400d44c001802804580211040c6000300d0400c3e00d4000820700040d50a5402c03c46000c103043c0c010100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389854451 1250 389853201 389853221
    0xf020c0613030c0201082208033328090c0f05030702060a050903090a14030c01020109050604062304080711030d142d0301080721060f020408031204050f01 68
    0x1c01c043d9000940c0112901e08006080744416031409000c00034521080b0314540315213200d05520f698900344460300030300b02c0150809101d1980d60180100c00c0c2c482111190003c1060103481c41ca80d80000184049a140101444003502c0000c04d0400101744503903070402c00580b0314a444100092500d00012209031204440c403102581c081004105625a10351210f0b0b845002c10050b40c2c10010004001038200c0c4042c0e2000700349070188642e450443c503060021100c014409d0008000c07180150382c415449450040020b42000c0d541c58020f40f0011656100c020302d00c0b516038110846103090702c0d00c20304d9604164400c0d640c0d8010320040300080e0800254001c81d13032400740c541c0340c0045203810314105241c1c0002d00f541480b02e0360140d0f81104424180d40c440c15218031302d10310360702d0b50304180d8418501480c1d603210562580001c5000004d000701c240c01d942c156174004201290102c0d0700b00043c000b078495648030004a100014007519059008959039008502ca5010348040510299180c1d090300d0122613 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389855701 1250 389854451 389854457
    0x50603191e02041805070f0e0408090f1908011d0c040506040f020c060f100b19020313080105040b0f1b1c0501060908121603180302040f020c061303 65
    0x10300340d000c201d041c030944403000d00320044080205041d0b4045002d41d04016508001011900c400808002041c0401005040072138070310b501e8580380400000c9190000380018040e070300005040d482e680c4480308884070b500c0020b4140d45455000310001101400b80d413141c480c8a520b015000216002207540041441c0340c2c030001440c1000014007000000c040241c81e06521650300c05024082054a0000e040c07000010b50203070800d8900010703080d15426004080c1644684105814440061000305a070484410342c2040090b44940700401e902d5885890700d06a1000091000040c2403481500002d10031441056040550b0b1200c0d001224450002d13120940103060070401010311a0540c000340c684000c10003115110301c00c03c40c4030300d41260020303084400003c070f110405112003a010801081000d640c01e513030b90702d43304801c900350040c00540d41006042044400d5050110308032400080c01558005100f0003035a0300001c0414003c3d801640480c40b5070080c2000105108d40076480b4902c0260162 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389856951 1250 389855701 389855743
    0x60702130509012702040e03090a031e060510060210060602070b070804030c0602012c0726100f0b03030702060a14040b040b030711160506210a0609050603 68
    0x800340068600101403424541d42c4050040c0d11189426407a4401108185020495071850060000381c90900d41510843d60003001840116201c034500b03034084980284101c2c0c15034034000981030b0501510344001e001181088140b10480c2008a10039040300c1d066001c480e13030b0034103003001c1e401541c10511075440540c0012204201181903c0000e0480912607031141c1d02d003546131381d2081603242d1f1070303005800141e55400d503040c40c512100d4040045081d924660160b82d0741680c40d2580c1e40d800d00d000d0400400000c0d01ca02442658180e000d00250080e0420341e14409a0303005500020200d410030008c17418145900a0640d007808400c4542c0700742c020b000d1a240c914186d900303a41400c034001c545003c00d40e04010014002a405000e00060a02d03041c84643c1c0c0d05018000502c0d00c403c101c8420800d070444950500201c801c0b50042c1e0480c0c4042e03404507200c0030803511400610b81c04004040d12070324081d081045041d42580440300380c400c604403c00103a2540c405241e6180e01c1040005880c035508 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389858201 1250 389856951 389856979
    0x108060a031202011e0c0f0504240c0f14070b131203090302060408010c0e04020a0f0c06020c0106180f0b09040f0804030c120c060509030316020a050a150e060702 71
    0x42000c0181040d143e000100e6052485100c02000150111000014a55561041c005a58004c0c1c5143c440129440d09508180c00d100041c10b600341611a002203403482144c1103d00c490090203076540a682102040031140d8260400f40402c02500103260718a004d94a40414460801c03000c4e651020403601c4400c00540c00c24003113640d00140c0b00f90a90510003c00c10000040e580c1800610107440e500c0f00120300080c440d031029001115020b901d41c0300b140144480e00040c1d03072203a0500405c0345180340105421805041c100020f110301ca45002c004e500341034001c111560000c1843c10303018001c08042280c04003120780b00e02203038030400c240c0d9800b0b400302021401280c902c1c0b18a5003540d028809251502d1f17a240d030b44912600d500e5110301161048113050b0014000244807600c001c1003503040c858501401100040d440340300d08aa0110003081070540c8805540321046500c2c0941005011a92100d0303c5211b0048a130750b005a00b031001440d07480c022400c50803c0026144801d601412102c800140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389859451 1250 389858201 389858213
    0x207021f0c0b150a060207180204051e040906020a020a03140c07030f140610290301060c06020d050903030921030f092505010e0d08030a0902030a050604050601140108060a03 76
    0x3e40420803280d40601071554076515500031800134211500104061454410641c442d03900e503241004445105010030003075500c948402a00b02184241405d07182c070420000180200701140b0302600300361001c11901c05080d000568005c0a50282e100c1411643c1004002c0d1030714490444481c1c0c031a0440b800800015011650400460f44543c00f0102c010a000110358a403100c201c4616101484090041001e080c103900209696141280b1140c50403942210f2041244011311a0380100802c000c2444144103907517040c5d49400d60365180030b020a0400910043d56900169641242800340c6045400c0040760312126103101030102e04130b9070a5030380380310034030004007401000207039580142801c041c070b800200d481c10b41405294403000806030741010001041841101500c5000d95204602e00d0701081496050700c7d0300c5519458041602805480464100f00103020028501e10640d410300c02007000105109040e1031a00d111074480303000d40001104c1d092415203079140c1044003080c09201243c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389860701 1250 389859451 389859473
    0x315090115030c021c0f080c030f180307140d14070b01090c030b0415061103090604090207030c0c0e060f010e210705030d030e010b010206010503100b0415090207021f0c 74
    0xb03e40103a4440d03104d00c000c1c600d40784e090041818009254050001c4046801c042d02c0ba400c0243d403494282185010400c00701d1509020b000300c51360043c0e0320710f05401c0e1003042044440440d4000e601211482e41c0615203503507400c000b1814400b00b03d6000c0c500c0d0020b2200820350703074299000380c08081d25034a0724802400a00c640c803a260f0401d92202c5a040150711140103030321006452280704982d00b4540035009103420207440d07283d40903400800c1440000e40d516021341e8140d5490010042e9a082e040c6021b4030702e01500a0010000c3c2031154000484030010702042d44161020b80d0243e0310600000c004440d5010035980aa9001300c082c100c501c0d2440400301035880030540302c012101d0316a200d50019245c00110320031f040019880f506424450720080c0101c40142d5000c1c0024011941807000203a00c500c02580d01c0d02c03101d0382d9840665010b503280c0c0c200d0304400e800954444c2525886503c204040c4d8042c4105a0240200c0c403052114034607c042d01c070141c0036003580c034000100da081c3e54142d0700003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389861951 1250 389860701 389860721
    0x150501020c1305250509040c05090a031b030b07080702010e030405010c230609030a090e06012c0d060e011401050619050915030108070807030203030f0a0201091403031509011503 78
    0x40c4c41c00c80d40000c2801c808034018000010340c59003030f1280001e00401065540c140710250401400340034464158a4940c0e0b608e007566030181c1d10a4030002410400c1c15807400c0e940c0040c004500410500c41804d800035001400780820351300038031401d010760301d86580d01d11540c411540001c4501d2100d80106510103003040d1000342c4400c5030070005036441c0d0303018580b82099030001c1c83c5030000210704008907040003242c0018056600034403030524110001238100120310700c411842004004804011a082040d19180f094009040d85040686400c1460040c0b1000001594661800c4280710300c59105035002c604031075004148a190403007107c00500c03401d9040c008da00c10311900344007412003540c50a400a02c23150180b6050360b101e41c0350001152910000d036205030600d0700204814800741e00c01008981054001010507581c3d200030300c40803801000c0d6008042c1c040100d0950204c000031020004501a408000014550306a00030030071145910a1007600f07442c5102c680441901c1c0d0090704407902107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389863201 1250 389861951 389861971
    0x501110309041407031409060a091a0c130b18190909150b06030903070305131508150f01021011070b0c03060103050a09080904150902040306150501020c1305 69
    0x144004202a10095005424520743d4441089011607041c0304111500e4100a0b0074451400c004840d05e40340e04001d0501503640b610341c0c40c00028025100090321865003d60380f101070600d89001c07444810b412042c42d113001c42c0c14040c0300094100e9080300b912144811004c00d8812501482c007002035040100c2e401101d071306800c1c80b000038107d500344107401055000701030f44906081d02d002d140d02187c800380461031040009205116400100006641c40350b541030030182c0c1d03540e0740340c8011a100044c81d4422101d0300800900c42c24456404199103014256810102b080035845004026000c500c0780d008070f0069008042406a94490381c00600742c1945026170280b0b1301c0301e02d441d9040d403010100c0da00514684008140030301540d05200b8a980110f44a1041211106070341d5000e6941c492840c525205d5030311945520a060108942ca40003841900b5086541d44d58034a000780c041d00300007a0066800318250400035865001146511450000400e0301013101c19005440300203141c003800301081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389864451 1250 389863201 389863207
    0x809060a060501081906080f070f0803031303030e010209040c0c0605070905030a0b041a1806070806090402090403030b040c0e03011d150907032f0103090503090f0409020301021210081605011103 85
    0x301c0b000078400b400d8004152806002204d040800ac9202200c0703035440702c0015403040042199030512085a0f98080d54507180115008e0114180030703000e402201655170f4020b1605452070806e98102c148244940e10460062007569035203001652511103e200c0c2e29016002a070320a00000c044001720303a4418400c1c1c6281c89210442081c00031215401c0b1740e68000341e100c0b0303844e081d8801d004002c00c641c080641d00d04002d8500d00700010070b248281c00340009003e44404000710302094000d40003800050400360040040814401001300800403000000d8001e501c0e0a00e201504981000840c41044440004101c00d01d0181c08040c0541070003091010140105003010000a41403020881d0507280c1103a41d003140444082800550032024001605051900300e17207100284011060b1483c0c410101d821803c5d0582800c0482c018211105c4000d5041d4070004040a80042011401c3d00824402a841c3c0d44a600c84c0146039991050040c07441c60104000c2003082258454031501040d04000025207007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389865701 1250 389864451 389864459
    0x6020d0f05160b040b101a0c1c03150b09030309010e120609030a0306140307050f01020114040812011208041a0c0a05010f0f150b0717030103030809060a060501081906 73
    0xa61400c0109040341c2e503580c0d46080c0001c3c0420f0b410080e40101032200c0e510035052400f41d507e125400b60000d4070400d0003003c9040c0c80d114005000d002e600e00602e403842c2c000e441903254003c005180c20444031208402031103021898002001c00d5640d00e110145c011482c0015907001034036400c0c001054a5417110042d1f884c201400e901b404441c0c0546094001540c4603400f0a102400b5641d20340c00c404050900c03910386a0b03560754002604801c481c800d80313074410200200d00c0108d0262540864219214440070701384010040c1000041c10355020510003c2d9090341c898548400e428980400a4050003050005112070740c01440c80210140a90041904c1c2442c280e11441c10001d25400954499550700e03516001e00304180261402c00440300720402c81490b10241118000031540990010900085058020043c0d1580301c00310351242e100201d0313180c0da560f00d80200207003021144211680103000100310b403590240649000e4503016101c4800595a0044000c1c0000c2d007071100011240e1203d000013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389866951 1250 389865701 389865727
    0xc0d0c0b16060b01080702210f0703020a050d09180e0a021f0305011401090306051801020403080d060603060308070618021314100e061e040f02030a0b0a06020d0f05 72
    0x100e08011101e07a00580c1e01c40d54103280c012103802403442ca05000c030800c1001402e0754081074001c00344074074004c0e4002150b015082d06885008141c08070011420001d144c0040c50780009035002101d00c07410440b0202d110002040703d05218901c0f421850303130750a901401099945800905402c0002d0040750881070044c1c00082180e841d00c10300045c000000748845200b958035000f414050204600c90741e40b080c2c50403000a0a4011034403024086554440101c1d10944002c68005814035410009640b52501c0c7d0038030708290751041d41001c184902c0c007280020350901900800c030481e60030881c07c0e17081142640304d410140414503e0040c0c200e502502c1400180d0f11065080d804050000b0000307258002010261044203001d0f0540507100e1490004200300d8140e00f000d245c1c0400c1c10f80303101d0307601e040141d545c0500c0c007014048654002c0c10800d40003105001e55001d14861100040706004030001c1e40d040c801c1018141c02084016044a0350464245000d8030311002c00d2040d0f0b1030082d182c41c0341c07c1c00103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389868201 1250 389866951 389866957
    0x30607270e2d070e120106080303180a0804030515010e040c09020a0c0b0a0c020d03140403030e10020a0e01090512151e13050c030f07150c12020604021e01020c0d0c0b 73
    0x84808076148040080282c03c05d503049401c0350303d50400030040603040460032a80c0b400002d009000100345490048a400000c0c0001400d4652002c40203490b19202d140054807800c00c0302c035050040303515800024401c02c1e08040f02d0700843d00040c21071100e07420840103002a620800300d410034811440000d00c0041c00b8080c00f607106903a2000001425154000020b00345040c03140041c1c00c25003000403a441c401c070f45900e07640c0c2140d13050500048400c280000c07234dc03c019a804c4158120780c400316a100a01d5000125818621426a5544011a03c0304100840a06030f22400c2990360720011281d1645035414001c01e030440111103003051041003118500d422200c0032140900b84070350610b58a810488100124410030100710050304d80b0885d144035295945d0618800c9042c011502144030210301e003c0e14038042c1898014220344100440c402010396200004d8508074083e40711415495507000c2c60b00d41141000c4c0c0140e020780202804d40007048404038404000351120003030180001440441d040003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389869451 1250 389868201 389868211
    0x120f110309070509010501210513050d030905061006020318060c0106080304140103020c120a12050f090f0735240105030705010c0204050a0b030607270e2d 68
    0x4002c40c0d070400c02400f100d950180d001e603051003400c504800ea48402c0101d5480c1e003c1d0020400103003544c884c1d2903900c1b1000007901c06003860003403034100448142e2540003000414010320484660f0f8456050318201c0320107034411400160018400f01c01c01016480411850901c0101403504101c5da00e0401c03400c454041e0b00c81c000c182d0001030108030601e9005802c64046100b400d046082004c04020b050711f4065400242480c01d04c0080c04140d03450284125404480b14013000300554600380c001c5400c004019620850288100324919100305ca0018808003610584d418a25001200030005042c80c803141b5402d000e00903031f922188003852030070400482c40d0041440321140918400000701031200741070300b006000340c0100c170b014031150b42c1214081c41855815140046c0c01e40e0748000110080c051008419410b0003020244685641d02c0400382d5400703180c0f000502c004420301090101300c040b081c418200b80f142d01c0800a4000310011441211000018146140c000705000c0c14040441007103072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389870701 1250 389869451 389869453
    0x4020f0901080115080c060708070507120f1505150d140307120f0c020d020d021f030c1710060807020a0501020a05070309150c14160b0d1506120f110309 67
    0x1010449055865040000820117480034003002120840810180d2140b0f03000501010701c0051038408020003007180000030b1035000c88445900b1101c0c80c12191000c96520140c0d040441c1d01146284141144640380c0140c02000c4040c46000f0b40ca814818a0040e005040d900400700e40280c1054440620082c10941d10500001d046440780c0c40000d001041c1e803072128030800c0414000003005807149803012203d1601110041c0346445544002100c1e064407400004031060000c0d0503454042c4c0541000b014210a074031111030184c4680800d18a03414200e0b82515a40401d09003040740d18007410b501a08010030744191380081900b503c80a0030780c0e000e40c9207000011000a0310009041c0c0c030060040c042c1440000c61860540d000c03c004000d00b000c2c0002170810401e0a2003850010f100300105500446091042815995035020207840c0344c0264802e152110300307040c1090010101e00030300301c0c161081d80c4c4131400c40900d820808002000f02c000c1d00b00c889076441080c0411041c0320b03000740d80318040d000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389871951 1250 389870701 389870711
    0x2307030510090c23040614070b0c0d0905010c1101060611100203040503120f060f090403050319020c0106080109060b0409051b01050d140916080a08070213050103080403060e060f0c0304020f09010801 87
    0x38100616400c47c0480c80015110f040c0100130000d14920409038000b224100407548650382000c000c0010107001c0b0000300300b5840c00c2005800181c115100044e4200214000c011082e556030050380c0e842600030004909404c0640150244010750f80503582190085003224100820014082100c80099601c4c5030001c103034500300401494104016800440260340d111030608050354041c03c1404054040c3d5018880c00040300c0b1855059810b8460b500b03440d000030300c2403070340d2580c080703009011100d020340b63b039420280b01c0c0403141483d01800c188a0790010080c0402e13281207101c501003400041009040020810180d40e4107104c81c000c0348400800425204094140494100c0c903040c640400c4038440307800780c00c00700020b0b00c0c041036600045402030641c2c2e640e00342030710005905540d101082c001e01490030001006000498015005032072203004100801d0485002c29662400d080352800c94650f5030000140314141241d010f9608944040d10b1607800c0354084001924000090308032080300d0f1f40d10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389873201 1250 389871951 389871959
    0x3408030103140a03120b03101d012306100309170c0c010305010e06010c0201050d060806061011120d0b0a180614030c10122307030510090c2304 63
    0x110000b1511140c0c840c0040c2259203030f0750b81c060a20840810f00b0089242e039000452101e890520200488130100300e41000820148134001100c14202d85020109600e0903404000400381400c0244c581c030500704600c5c640740d4441c0c08101d11010541b11480c00c054549a4000000d0040640b014010000e811340e070382c9651035501020728220342d241600381014285401040710440d06042550888028030b03040a203d000f50005840700d22621050340300f040d18100d00081d50040c08a11280940d00c1203c42844000e00b5081c00c607103550304820107d01c03540202282c26080104080186082c8018072008140c0124420000b580c1d0406544031440b034074203907050039000390b00c103118000180c001000359030040c05000c07000c0380d40d5844202000707000308001d0900101040c042c06c044860342c1980c08007841f410142d207000c07001040b48840e0795030001c2000c0010514890090094038802c45054103003052040c5044151800707444a840c0c00010b000d110030100c9600090060100320000881d11101d984602d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389874451 1250 389873201 389873213
    0x90a05030a0201060e0c0909070509061b0601031406040809091308120105040522060b030f060c09040c0e1003090311030703110705040501030210050705010b1008070909050c3408030103 81
    0x401012903820403020004107481d940c03202310180c1c0011131442c01a41318840d4030003042c02c80c400c044804500924005000c08001350026100d4140c034032540c0d41e400c52403078000b1032950b200e00640700285103203030900c07440701c3d242400e82140e81d22001c0e0801901c91303080280c41e642131a0784150400c204074181000184200e0074107016107900700c0020b041224004c0c00e41c440c810032074600c0f9840109855111111403005540070005026000800b000ba00c2c264100542800003a5110301070260090382804012a030f00c0d80240151410b00c0c60240905486040c00c1344114002e14100c00c0031000d00080100410100340c04001814079241b03c2e03142d000c1e80243c82c050b0b807440d00b5070940c000303403040e0308080c018030050b00c07104151076880d003290905640303405070307031a00f2405400d41098141d04610381c080a504032a5021007190b002e9034258031180c000c80c0d00da01580040d508200e43e12a0310080c200300d605000c040441800c80b10899a10b030100070041019030101c0b442000002c00c0d940d01c2000700040c818005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389875701 1250 389874451 389874479
    0x20d02010608120d051b0a08010303110d1b0314031519050303070209090307081611030105220303141e0907141201140403030f0b12070e090a05030a020106 68
    0x209110042084071030200c4210518130804125481c0d554039980450540c164280c148010403480390400e0381c0718084d0a0b001440070000f40300070b40004081307804510101c41c0202c0d55501c881010354900c441c80e590070091280c11050000218204010190b400442c00348c89009175014041991201001c08115030821034440d40000711120010a105c00404c01c0e5507000080701c1900f0350680d140302007561400416411341c0079803040541803034000510031590998800c006070803a441070342c44120110b212020b01d0300725001125412075000b22580c40341d135501c01c0c010403c65090b1003850040f0304542030f40030010702c1c00002d03512001d0b041218103c003000007000c0c140c0c00d9480000f080050a02d5454006405140d00d16920710a0162003a1000d0010310803080d000121500c180480c84400f605062400800901c1c41d91000c100103882d003000c22034603141902204c041591342c0030041c408142011420701c41c01101130a080c40e944920324165000078818005060905899000014214500303001c00c80102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389876951 1250 389875701 389875709
    0x6060403240f0b13020c0303130c030b16121a13091b05100f0c02040221100e22021017040b1608010503100e0118060f0c030e060f06150406020d020106 66
    0xe070046c040410058000002e0300d91061520500810000d040c0c200f110b00b030b00164002604200041d01009030402d031441d851004000745a8030340c0ba000045032503000c05c80300044114020103d0001425445103443e4609100743c80c0c65010005032003e4135903da809800e5105129174040311741407410805491701c40b192103840e10940c20034110f030b940c0d5007400909600000c0300092085034040b036030b0784104104042e1a110401e4402c100d070400d0802c000381c20405d00413031040164801d00c441c00034518103100c0c441d064030030584004590790b00096508200c28407040b1102001040512a80c2048508c82c0c401c2c042e028501400c1010114209116204d100f00b0074450392900740b114290040007203803400511520034001070440041d903020000d04450150075105400b43d6111003007c130420911001c0e81c042624100700e05020080d036150301d0f4080c0c054480c050454613040d000440002d00d18103424000c50f03403050008040d51083c40111900380825007180d000034006034000c9034407482041e0240718442c054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389878201 1250 389876951 389876989
    0x90f01091d06190e2a1c0b010207060c11030a050712122307170a0302090301061e05130f020a090501080702150c0904020c1b090a020306060403240f0b 66
    0x190500c2100c001e60071025002d108801e0082c20803a40000700542c0512190007517200c40c03540c0318801d820580c1d48154804841c07a10501c0c29148030429800080c00a04407182a00c6400000c3d00944484800c00c0f6404501a0103008045040001410600200000d01004d0519005295050400285505284072040c09100a40615542002803c1c007005403403005244030590b03480040c0741c0114003003414085005001c0d0082110001590107802504207030006400801929540d040422a0000072238015595020414801c0c03085081c00304580780160461030340441c89403c0031449100301d0788101d5108000030a0740701c05100660f0701a072001d80010841c4002c2c9204400030040d840031060140840461803000107004040d51140d0301070350340c24001e01c400d4510b2a4001100d103610b0b480b04484d501e104000741d81c0041c0740d0418070b1090300c1c020080a08100d051605603a9445e1685140d0109106080c001020304c805000c2c040c007440780c2c1c4a41d0031001107041c3d03071180b05000380c04040500400071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389879451 1250 389878201 389878249
    0x6080112030c0209070e090f2a0f0f040807030606031106091305100806010e01031406071202070c030b09011e110306190506030703020a0e0d0503090f01091d06 70
    0x881d51045481c42d88540407500003603030b80c448050940f050445202801c1d0480f0128040140c41703c0003074030491140c02c0110318400f00c0d40c010b11700240d600880a1380007004100501c17131901400e440802070040480319503440342c50661550039103490034076554002c032021500c5050034020084104030180c00400191042420f0441810010788007084e2068925a2603544400240c645640d0420260050401405441407961140d8007250783e80e07000d010585041e01d00010702041c6c90400502940b041c40280c2d200c4503846248040c0c003000e0342c441706080d074260328440b201001140b0410a140d00400e02a000000c800911f000144410301c03022411480480c60007441298500c401c40403290b000104503007019000d850b01651a000030041d800c41c54000c10040200712201e074140d40100620300103500c3d43e48a030b03c0580c040016441c40ca56005000760000c2c401c00c000d034105040310414105050400c1d004050700d0300800920070030b85c028090042c028400901803036042c020440c1003240507079042c0001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389880701 1250 389879451 389879453
    0x1e010b041a01080c0f071a06030f0703080f040f0b07120e060d09023c1504090e120d0b090a23040503360d030e041104030b0108060106080112 62
    0x11103441c107540d0460610800da40090030440102e0101d0b1075a400f080945916400282000000741382580c0c0703a03540000b0080e000ca05035203130004440301a040e1040080500909540c3c60f4052504451000c02d0340400911001c1200c240a4401101610002d40c64540300c60036800d0820b400e8482d559550180b2280b000c0000442d19480304031000d5007650340c00440e40c085144041025000b12401e11101d41036550b005468501c0740000a0300c0c0c2c460b8806103504a1381c10f440030003007821045202c41600c001c0810041103068583d402000f414424841950074030070700880c990b1159808108480c01e901e640d20b8a1580e18a00740d203090f60048840c01c020484540f1880354840c1441402c00c41e0004100c144001900b000000c00840340948042010119064204281c501820b4140200e06190344551018201507042c034030419130079682c066907600800e00b20041444001d001f554000b5056810400010000c6040407003068000d100c0c140c006e00aa41c9000030081180da010380003c0151a049442c6070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389881951 1250 389880701 389880731
    0x260907090c0e060f0c06010f05060304140a150e0f03090a03170f120a180c14060705060c0c06010b04080307170c160501031802031902121e010b04 64
    0x802651480300c0c0c001600c200c0000140c1d082c0c0003000d401603200c840059002c10b800c82800191138042070304800c4a6450342c0b1800e000200078420300440343c12070b005000040215103404025242c02c2c026005440d001c003c075854441302c203a42c0b1707490040041e490f401c90800c0c8030f5080207501c000015280c007a40c240303001b040006035a038510788005001c2008400000002c0d803189000c640c03100e15648883c9545020005a412030070404940c5012054a4a100c15102c4100310003114000c603400b88021040e6414211152414001e810703089801590030700021000a90810545001b05428688203031661440e080c0b0390b2802c035058101c034031000000c1c4020070000100009481c0d459500510850303030b1030b1000002030054099040d060740f8500c9581a8203d050890f99047d10aa034020307030301403200c07081c80c10072958a07660442000f501070381b03c1817109011144081c0d5051090348010310003907041c0b100030511890646202c2014003107c1502c0540c0300194400d00c5000000e080584050001001070803450b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389883201 1250 389881951 389881963
    0xd2001090302130507030b030313090f0b011b26180105040513020a050d0c12060e010506090d05150403180f0303170907030804080d090f0b04030210030f0c2609 70
    0xf401035203444e000800d10303080c040c0d04500789141c8081d0880388c4038105107101c1d03000c80c3c250f4416030200501e00601c0e14221a82c5006840070342d04180c4417044840c0007007600301c10340c624407134065401c8540416850342041443c01c051104072050085140c94103003c554444401040562040c14040100000c00a5440d5242e108041c008402001a102d01b01804281c9076441010000c03016540b614289101c0560024038020795201c40d030300200040ea0b250541e85442000a0040b15030000e4180540d11040c5005222524034610078001da4000c00c41840c1000b03070031071060f20220081544002c407140d11000922010004051404000c5a002e140d42c60140c08e8010700c0c090584d0720305515001410304081017040000960340556825601c0359501c14035507c48031031840008c0007641080b00019581100c7c508202a60380c494061440d040c030399403c00901017803440c7c9581c103142c1c81c1d44507038082054920a000c400c1480352907220241d5101800b0030700840c0749880c200c1c2c00403c61414000441d20010391 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389884451 1250 389883201 389883229
    0x2403020f0604120803041707060603030206240f360f161103070516080c060712030203060d0605090307030f030c080c03070309080d0621080f180d2001090302 69
    0x4d45517a9211401c0c00c2d6240004c220200d19000800900302c82041308691113101180d01039030a842154586d200c80d004400c8103d40005c0401100e5040385000340ba080182c82c4102100500c14414490035143d41102141145403401c03460008000310100c080440303000340d50000c1100c0a944a5281031100312101114070880c000c1006248503507000020350400c2158101078210301103403600c0d58020740b42c2401088a0103044114000c0c101806100d0410320141c5107806d0303100121740750701419580f04038001d400003041d41c1d034442c480c0014880460240e1180034001c04c0b0b640055945d60100d4100038104070f0690007104101840c03d4580c02c440caa106480503040440c4001039a42e0740c80f400002c802070103000c000948000c1c030002c1c400b40303090359580c04181151248001c08007d82c403c842c111802070046000a05200010000088032941410003440340f030401409000daa488060302141a000da01001142c15030281c00c69100f805001c201c523034400300001d2a1100455055a010840c49850150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389885701 1250 389884451 389884463
    0x80403062706020714030c1b0303040b030406111c0203010e0f0402090a0504031806020109050706050a0f080a090c090b0f040b0a060318061416020102090105070201050903012403020f060412 83
    0x180e4141082171045c0f0880700b02520b0302c216912510240b013001d44903034180c0d1002400384074811242405040100545045606582110342560303079584643d000b40c0ba01042c0781140c400c040254903c001c2003104800c0210810078001a1250f050480d4601c5000b0080c1c02400313158010f40070400180d0740d0881c9103500c144540408113041c0c88510f0151649a144103035034568039402100420606c3e4150f10450405005c0e00440c1c480540d42c01040c1c8481c03141124440000b01020b02c40c18043c4e02500300d15400c82c42051000403011020344600600c1c0440e5001307003001545440b000306891174210b038000d40740c503001c507820406444913100040440d0054440c00c014580c03212110820301005203140203103507400010900110004800800368020105d0340292250280045441c545105101341c418550341078507440d01d011803d40064410b90403020180b68190740b44c9200882d45044220616841244600d0603495a4210b20400082403040c0e580c69005010a0004204a0f10703582490484103070402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389886951 1250 389885701 389885707
    0x200114090d0312110c15040b060904030c0f03270b09010c151406010f090602190f0c080c040e0303061c0c090e0c0f04090b0c0d060f0308040306270602 66
    0x201d4103441c0702950f100b0b1154031902d4142c400813070800e00c00c020043c40e2503060550795600505521043e0030001920060440703592000003800307500703040c4000d5402500074145000c9a91155035008000826807000310b0020b00d010454015010304550011203200100e11021851030910303145800c940a0026030504110100e94840b00703014000c034042d1400142c031f42041c00103c0f070400000700f0081e41a0380341e0780012484110f040325148030f9400340041e20907540c042e1000009070940851090345070303141680c0002c00415068001043e140c0083d0043c2071007800b906000300154100000c0b90014010000c080d0410010424141e48000041001e5180010b8130340d101a050308017034040b80030b1600800304030b43c40c0240e8003c2e104000034902420f8081100d0800303101415030140400d03141081c0c001045805000d020804191448010b441104201c00b40014003517a91004150384030303c5a8003d0303c42c1c110000e41801840381500480110200b01c03018071301510000800c12111010309400a0310003903000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389888201 1250 389886951 389886953
    0x5070311070506100f0e01050607030e0603090109050609070f090513080408010f05060a03030c06050c090a0e0a0507020d02280f03050c061018051b0403200114090d 72
    0xa5408044611036000c006500d8650300d01d482c542d140400d480002d003140d02c16000041008041c0940d03025a8921110004d60346d2901c0705010aa0304502c10841c1408101d0f03e61540030740324003020790f04c1520300d4000403810880d00c2c20b0260900c3c2c00505008181e8110f00b40c180b00d18180c00041c0c8045490520001441b40d0311040700d224001e5400794010700034080040c00042c01c00b015081b40001c8864020300304000d03212030303040000c0c0050071f2000602040111000801181840d4031103644034000d50302d4240380a54110001d030f40b40802e5045200f22001082c14048010003511480b40d00880600040c666400001d4010b581c2d403100003004510880c1036443c01da50302060045810030181c0c000c3c4aa54141c2d07052401904540091030025014450f480c001880600081413180c2129040302e00d44100c1c180401800010740030081000c1c10b10542103440c00b09120a4100803c0258041c0041c00703046003000341c08000f600d05800d01581003000b515142c8800555031005c0307403034440045440aa0108103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389889451 1250 389888201 389888207
    0x92d010c02060c011e0b040b0f100c0210030c02010e060106021c0212030a0501090b040605220207140f211b0f16211a0c040b07080901090602061303030507 68
    0x202c3c0d002012070b50804203002103c940a00c4620318055010a0078000444a0020f01003180d80d111502980403011400142050500340807400070700120345050f03900e620090300422400d014817a8500700081c0d94003a64440783e0742c2841440d417200d1141d005400d1a52601c80025070311811210000d1546100081c68501c0c07a0007004120200b0070210480e0340c982c034108070041c008100903c649503400781080b400643c6450a03100382000d656004200d90700c012603181c0701c00c1c0c00c0b0500807800c0c40319a90801589021440364181c144046c040c090080c030284002004c60340c28000c1e200c2784030079049003200d004400c10002506031b902d200c4c080c0174032003074040c00340c8416450008c02c01c807400c0281c01401c004800c9010480e9584042da90442203003003c0c1e44208100020000000d1030241601407a4011003c07808000d003047c9410400d14a00035007000d2f00c500042003546d002a80441e5164070024040b0f20958010b0300040007000741d400582000d1510201400040b044400e0040c105543c0b01c0000e55a540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389890701 1250 389889451 389889457
    0x141b180f01020f0a0303090201120e10020c010f02070606051c030804020105091804030207080115140609190b0d050f04030206060d060e0d0c1a06010207170a0b0c092d010c0206 77
    0xf05010484058a4442c10040c0042078514416400207101e03d001e809200918003d44490701d00901c000c1184803074900400c0000d41105140781483d540703031500c0c141c03180345c640003030010103000da40c0000d50280307070504001020072000403a4681100b00d11304c52000c2500100825030003070302820000c0d652100301c400591040710310502c00503c0f00c0749030280f009041c0c1c00900c1c0d41c15551079000070816650403c0c40703024964154464254902107010f4920820f0610802401100b0409008410031072168441943c8c0a8a01d4015025100d004901c4000482d0039015140e0000141e85528401d400c06403030003501c4501c014102c5015442c40b005803001c2050742e6203e24164010b110541e8843c015400000345595280383d029501c44911505528108190f0410380340600c41c140c0051400310710308290039002da1142e41c025034040c00343e48905804030f0701090017180304400e1400050f0f0380b05049810041c1071040745888550311880303940303d5030001029289680c0844000d080181f0030b40d0891000807030600c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389891951 1250 389890701 389890723
    0x50115080a0c17070807030f0605031902060f03010608100509040b18100204080a0302101119020705150405130501030822080a0507031e03080403030f0f141b180f0102 73
    0x5000f0200512150b00100650041d174071590240060040d010b038680556003240142c50b0705030065000e40c0380214008a51405c5544094051070402203034060100841d0000d900100114080c003041290700003225050001030482100c0d01725090402d070711822030000d4000c110310035003100f020340100a0f50040000828440b085401555510b403203040036a00c550403514100e0140c0300f141140c80174018a800340c1d0301d4004500000600b00265000244038200350010180198041d030140440e1030345030854040a9801d268900c0d0b41d45920f004144500c250100404012a40ca40350047c1700080c08801260383c59203c00c44810322507c3c1105d00510400070700e2b403002205118860341d01040101c045400c904907401003408c500f00800040140d0442c0301251300050008110200107800280207034040039041c4444400066030075010390b800c00440c1e4985020403100e161410402c0300081c00f500007041d03106176100800341082e59840d6204a145900c442c5544601000014441103903c01c2100140300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 389893201 1250 389891951 389891987
    0x2030a02070b090c1203031b030403090e10030209010611070b09030309370e0604180f0501090506060a0b09040b030309090c090a1706070c170d050a050115080a0c 71
    0xe08101e82807a5680c43c03d0381c1c040c0e000b000c103d181707004a00030101c00e42e48910360b1005440c4003081340031603809040d03000070320480610024580102e1440f00320401c16220b1b88071010301d41300c0c3e58154010491f200b007050b8404800c20074610108180c2d90408100315003103400c1c0890940c0c40303442d21b000003811800b40d624102c1d0800508060151080c2d1910f40b98000c518010f000004842120701211034400785900a01070030351600c80200c0c19504180d8000e200e14280360115801c01c2d21702e540e40440e25070620130305a4040c0e440d5960340c0103000c1c0038041190815000ca6480c00c28a1920b48800c00501803004a0380c42140c0d40c48007014103450506c202d444281c0300815034103582c501f251064440e0b42101c40c03000d005440441010540710300600303800c00c100341381e0402030074990356408088170030104500f0121000c2c4e8812071000300a000070400b4240744581c902000c21986040041401200d205a01c000801c514044134200c100d40c000f610b1030340001c41904041220b082c4d26605a0301206003c180d5920 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 389894451 1250 389893201 389893223
    0xf010608100b0f010c0521040311042c0106030602030c09030d020d140c070503070b13060e0906090601030912050c1204150503101206090605130b010504090614040506010314010c050a0302030a0207 86
    0x2a08800d07c1c010000d0f24803c3c02800808409607081c002110301c8060040704c000400070402c100d00d52035442e02400c80142000100368642c07070f655924142d0f00f0036030b0709001c00d100100300d05030140f4060002c2c00c540c155030300c0102142415880300030110a94061920140600019841c140b02801c1c4821006414050200d98509a0342c0c1042002c0f83d00c141c5d81c40510450401020070300d9841210f159001c04001454040c00781c4840c0e040010f4031402070800c5d4141a959882d8000183c1300400302c41c400c0c07506445040c0c44014075031460381001c015440e99279408000300801d20501004002c0f15000c16400d00e441038882c1d035005140031180f103060b040720509905012103501004101d800407249184558014000c81d00c40007a0107010b510082c0e0000c00404c1000c0041c001030901d03900400c600e03801240d001c69403602d80b03039034215000340603281a90542c1182c401482480b032030502d28031000f00508c00030044403111039001080340c022a00c0341020140c0010100d000305000b6019034514a8201c0b5000031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 389895701 1250 389894451 389894503
    0xe0102011d0c030d0f0c02100c0606060513080f15100f0e011403030c07030305180613090b0d0f23031215150909040f050f010608100b0f010c05 63
    0x1603942c252030500b0344248954616082140e02c202c01c281c1c03011501303443d07014030006650b00700305000c4885c1c030a20042080443e8004c0203d42c03180a41c0d4010011034498542d605110340c003d10b408051604a01b01c1680004800c8016450020b8070207034645a05540c0a40d03030300c52484128002038079a09c50102500c0c081004160044410082d80c1250082005680304010320828141c503030080c0d100812990300180000c1010900400041442d074407030b0303d04010303810030b241c0c006846c036001518680181b0290f03810521040406115030040c1c40000c0b100f55120707516940da404400007080c400180009070b484070034a5078102140c0c858880100880540c2d496000248402e4203452049801d0440c044404c4842d50031428501c201c204000300074808a480d00c1c1c0c0b4541070040401000e08100c946025181e0a403020030400e01a80030603002171000400d0892a03e8415071524000903102544030345420241301d10342c0e407481e165010b00b0800f030030822a01d06060404c1030a101030ba002842d46881c24035a004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 389896951 1250 389895701 389895703
    0xc020402030c090306092a03150718080318310617010b18060d0303180602130f1a0301050d03030e0303070c1505010803090d060207150c1d060a0e0102011d 68
    0x3054040841f542c50f200c483c65166803813015540c054510350140c21019030b0151010000c102150b10101904289182c07030f5488030341c81e99902d06580b18000c41d40000c15031085240c4020700f02c884491080391030203100310590040b02a1044a0081404a440e07181119010007126400103801409154825082e039401100018040c00d48038121034800d1400380301e2424600a252a5180101000780590000f14926601580103101d84980f0000c140c1e41d89141d04002002070000344035292546007058000c0e4549406500c2c000425000f60709180300d12500702c02d0521582040d00c0c1107500494440c3c0417603010f410144c008106001254080d800004204074a8a80000e903034050580301c1c4002d020b90001c0d4100788001c40d10300f806000d600e0f81042000c035015242411500d06221700508006262003141da5515035070006203940c0504254840e11700d19034443c0c01c032403198080480c401c07a440e06150310a00150880c450040103400b4040e407401095000c0c0d100b5403240c04910300700c90f0405243c4415000207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 389898201 1250 389896951 389896963
    0x19290103020f030109110d020a0f06050c071401020a15091505071115040b07020f0304030501050109050a0c020604200a0905010918050d210236010c020402030c09030609 74
    0x141c0c01030340d02c0004404281014031a0348441a0070074951a80b00300d4a004103c14a1900300007640c0c4804118404107910700c41e01e44031001411540c445a0b907171280601d1407410003203650b11200a4801c403140f82955a41c000c1044020b15502c1148910a800d0320303129030000301004000500381c00710091101000ca201a0301441c080c0c811a00d4065049464031a4180c0ea440a1500183c00c1140600420000ba0102080b075401c0a01030050720000781050800600e1500154001d4034141cad1210010081c0c000c5034420a60800711010f002c0c4842245140080d44c3c920000c1e00003800a607001401200d10580b030000003010340c0000b010644010780d1074402401801082c041c08036a1844d00d0305610003c10440040c0e81c0d03440c1e120b4090180112810016a00300b0101c0c440003122810100e401260b00c0300c2c038030092004020504094030b12625040a26282001c070048415100780081c0121029a0300f00087c1124668116405a0b482d40c48000c6c0d8071460003040b0303400da0148145001d000c2516008110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389899451 1250 389898201 389898203
    0x20106050a09021315090b120103020906091e2809051006080d050d020f04030302010507140315090c13030c090b030d0e0f030c030d020f06010e0919290103 68
    0x200c140303060302d60306100124490036030541c6201e8039949080200710b0020f004284111118140850620340e076000105065010380c650240074400c403401403045103450f68146030018000e4803018617929003000304004020001c0c0e05440e80d8a080b01c0065840191000100c1a0700400320340083c0900440d00c403c400f030103040c07408031100e0017400c14100e03200c50a48540070071102508000c200d040c07000d61040d140e560002811120f81902001040301004040300184011403007940001868942003400034403c0004a0382451310800c20820310440300e200101c259110201141c8800090300d8014801d4968400e01d0b1125500300c03a0320b0b40000a018000041c40110f800b0206e09018405000003016103c1c3c0780502d0304004103045441c03500c00ba0400c1d0304003540a0402400300d403480c100d0200082c0c80e0455006512005030320443c120503080c5020301c11a130051407041c0c00a0003c0c10100801510f070304002518140641e21078202c203013400302c0c110210340e07003c001c1521345554002000c3c0021380e103002400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389900701 1250 389899451 389899459
    0x80f010e010207020616030315030f02030d0809210705011d06130f11010c06110306010f180506130314160503060405070311030c0303030a2f1c02040b0a02010605 71
    0x14080c0000018021581215401000c1610300b8403030b0030308150300398445101601019660802c60000c804841c2c0e084014501440d0154080c580c14810189440d902c8031002007080710101c28480410710000740008003000c0c854a025243c0c001c003134180036034010044098000e60800700f42295021140180200a412400030ba0b4810381ea290030342c820b034444180004103c00d00e0b074503031000810400310074083da02505150440403100a51a00001d440724242815400310000007449007940c0c11000a6030b41380e00600f025440490000607440701c1007000d200711805040002610710780a03c4580a0380051640001c84000711181d2401c0b4a5580e4420150100890000c40c0040303854940000c2c50703071103254003d0050101e6410350392440d1070840c60594081d054811007202e031440d1b5406102452084512000010314841c1380c444500d40010001901c0b02c00350084010195285619401c882e022010080341443ca400c0a6020000910541d0701c04c3e08448004681056020f0381034004030100c2c1e000302c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389901951 1250 389900701 389900711
    0x22124070924120903090602060601030e12070206090d0b04050c06040b0901030c120207030815040903080f040804090504151506050417030705060c0318031e03040204060807080f01 79
    0x44001c0c0c8204a0901441400c100d8542211000300000c0716141041150340c680b84150000c0705100c00280c0306031460031030108103032800c03d0005c694100074040e4000402d28061003100c030003041003600e5480c1c0d91014291500700042240541d1164011200c1004001e4160541c0040c4c42c2003030714622005660071110380c041e03103c00e401d076854540141c80541e88035002c024503080e44800150002c046080d40070701448550400309005040394805421010b000c2d40743c0301c003d03242030b00c161000f1080d004600c0784242e05c0d2101e840d010030361000d0b02c00d511400d00d41d110700d09903c941c10700701c4503800396034800c400c1d403404c10080004001d0100c2401c041a80887c009014200e982814244c0b5090f45000c2c14001807410701c03082000b442c24801e00d1220f890500140d0340342c00c155840e03060a21104642d15400110300109101611041c00703920500b0a6132032001c1c5042a40c41e000c2c460700b030945a143c542034013030080045019991154084001070004504461903e40e4400455444103808507402c1e070194030f01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389903201 1250 389901951 389901961
    0x106170303010e090c0a17071710110c0d08040602090d150c020a120f0c0503040603020406020d03021801030506040e0615040b090105090402220903050d1b0804022124 73
    0x240780171100500920409005040001404100c031440c00c4008280c4941c034030010301c1303100c10780c0710004c0c0c6001d180142c4401c81c40144410162915510009540709081062102509001c550b02d0b4ac1840b9900d4100d040d0703291418050041d020b82090b4641c40640000b00d1010131807000e00c6c40b015012860403e104008207080c0c1039032900440a00a40403d0780070301002141803140e40d60381d0340e10b0400c0c00c140c0412012078503503500c0c40d00103402c1325001c2940000c0510485030100030140100b04146400d500c2c0030381c40301d40b030780030902420519814191248049040740e40e86402000328045264100c0304a850720442403405e02c80c20300040b5000b01d00c0c00c1a1022070b805c2046045050f188054107030525504d855091040c041c89015060001d00e003003541500284210340603100f001d40c040c4da20315403260482410f400c01c40b10241c50046210720a0054095020381007030b00c5a601a404071816901c03e800c80143c03142c56119a1280c880c6805405040c007159400d0801c446003c0500d00d103000303220740c0d42c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389904451 1250 389903201 389903203
    0x41221060e100e16050912100c080c07051f0b1009091506051b0106080703030906080f16140408191101030504151a10030207050f011a010c050106170303010e09 70
    0x103449082242c0c0d44040213034240d90150000b0b02c01740c0ea01415141d803041055601504100301d50001130070003610703103e00855096109214903004541000c2e000c0c50f040e0302c1d540c0e0580e20105c03a44500396000320b00303032402103107100b983c0111001c00c005401c10b0b484401e0584024965001d50191304c4080d0b00e00614140d90081a074991026102c00382c036454546455603644030443c000401c00400302e90740326200410402010300c0140c0c001c6200b40c8039002c40504002018000c20310080100202114020401c50803a603e4101110141d0b514289405e400202d40802060b80c41142c00013a100e00c40d1003052214241c80029030f040481c09507054041d03220b8500011000d0302ca060310b018144442010705c40e0b00d0900035910061070084100f0190145002c08d00204080211b4810305201081d404101601884000c0c002d041449001304020049807890800f0103100b501c00b40c078820304202450741c4000401100b5440700000d0518486079001c0707000740d0240c035a40d03984240642d6003d59211f4002c141d040710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389905701 1250 389904451 389904479
    0x303031d011104091d011104091413032f0a1e11150904090b160e01050f0a020f0a051e0d050306090a020d050c090f09041221060e10 58
    0x1801080c5620f000d180c0511900604040f119441c54081d15a0221300900b40900c90f8054001f0701c034507029120345ca0b10000c0411142500ca640c0e030b403210550704000442c01d028440d4000746a25050161018480e5009240407400000100201224001c0b103211892000184110b0140c030502c44010309509007414020005040d020091128500d26440e411615007148404455021140100d05000c101d90024050300c000300700541c1c1020722842030010b01440215580750080290070503070005144200001c00504c43d845030110740030004100424054401d02c025580d01d81c0b0300e0b04880c41500e59041141d26640c2c80310540305c140b00301801103042003001050b1800100090344607981190b9404c4180103802000601c00601c6603402c1101d10040c24951007154003030f04400d00c0e4140c03502c00e12814001c40102d0403080b14420f00d03041d001c01000400200740c00702e070b120301c1f86070520b080303e40e8140408a003c40324100d541d000381408004101540302d8106184514052400c1480c0503544055583e0118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389906951 1250 389905701 389905721
    0x31a100b390106213f18120209070f0221090301150f06051605060a0906052a0c01201c02090d060b06040b0c0717030903060a05070507020a0303031d01 66
    0x1d10707070000004620041c41013012815421940c02070701a480e60541281340c2d05c02440800c007180e50350300d40c42058080d5a10220160070890700c802c0c0e298004d500000c200171002441d003404c10405a075410000d903c00d01106000100b01481003840d80c1004d00d1303541c2d50382c0103001030b01d02a6180002444d00503041d46014000c55420188031540719040003022140c42d8440302504c00d003418070100d540002141088001e00c101065440001c8000706c85c603108082d40c1d00901910501700c0c500031520500d800608082611103200c40c1c0c2c0c543d65104100289001d0240380f4065888000e00d0b401810150300001c00403c582d50180f1044150b51111082c001c0c02ca0144c0c0406c40c0d04440013a444000055070b0740d101c13501c43c4000500c1c813403d10f0740d18400500e13168043c0c0c00300042a040a50204071000400007001100c80881e4003540c01c0246039400310740c0d40c040c0206001501074407100451000c602880460708550f4001e003180880b5903c90030090040c0500b41100c1803100807003a0308498050041c0705050400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389908201 1250 389906951 389906963
    0xc1502011a0901061b051f2004050f0105070501141905060a0b09040507030b0918010e07050117130f0305040509060306010303230405040204031a100b39010621 70
    0x301c100011701c4000c8001c100422205c40c880d02e41440d5800007803a0700a003032458820004a264007100303040500c0214143d092000c3c0060070300091140c8d41c0d0324803c060b408102841c04580300c00385420081c3c050429816040104030204040c401042001c41507060b000702010340c103001503210403040c42480f1406100c0d51100f841d05104089251038560011a0020340d24070b030200e030b1155040c001501a400c140c0e50451031824000c003e0340d14200a0140d08126604140900055850500013800481d1059040c10390006100006042400d80c7e51201c4801034101c42d04005d41040341ca0082c01d203912a0050b140f040c001d80c1c1c0003424900d400036a9505996056840060800351010452907000e0480b60600c2c1002091202040549481c4080c00040d8004c401c082c07200c105134440e561008130058002803031544c00d0780041c07100d03a51000890f6a103800889003014164080e500320390100e9500c0700412421100380450941c5420150400e00c1601d101d80c1200c82c4400360244192204006120f005004e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389909451 1250 389908201 389908217
    0x9090303010e150117070e2b02010f0504090204030c0e09010e1b180a022805090f04020702040e010902030709021305040e070b0d0c09052b0c1502011a090106 69
    0x40740110700c0d00f1003140c00c010b041040c009a0052294050013408590a40018407890f00401c6640341c140609280200190b0540a42c02d0144482d0954203503010000780c1803110340d41458046030300c40d6040350001c3c00e01c480115107690b260314041225030184d1040c10f20820040000c90b00050041c8100040d441000009114165044400403003048103001c40f02c2c1d0100f041c820461f8002407103c400c0c1d102d02d5450000681d034401c50a08000704072008008a036064040e82007100403e6045011030303a81c00300403500e50115460310f00001d0064851142300079041810103050300c204060542003401740c20310840039203448544034403880080340643c11100e0012640b88c1410031080c10182d120800c9012090705031054035441d001d52880c01e611118203a5a81e5540d240e20b102550343c0080e02c20068803003203846055444045419261203440d56060014018101e4407110800c40d0081e050802440c021810100ca0030f8a01c0c0c01034001c21500074407400d58002ca1071125140d02d050703070901d4141c0ea65600d8082c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389910701 1250 389909451 389909461
    0x90423150114060307210204080d02010219110d0c11060a05072a030b0406090b0c0c070501090e01090b19091a04050405120a0c0c140141121509090303010e 68
    0x382c0c1e1000c6c0c080d07601d4256820400400d4001040c081403205070110380000d6511200b0340c0c89a41c524410b03075002000c014580c0d110303010020300403581a003241c103240b410852586440c24801034407600314000d5540080001803401d82c2a401c84080e1071f07d2401045440c1e451038484200200b40341d0980c0780c116240c3ca4840c400e10000d8045601a500a0f00600c000030380c04c401d6980b0503500c59020740e60b0b00c0c002c04001c24540504c0604208000c040c10080c030b0000302c640c0ca04000600c0d40f10040c02080f0a03540c8400c0351001d41d0321042c0d20700305040c90400c0d02e102c440b1364a580d04c03030040041010818030320601090031900382c203140c06018000c0e98810020004000013201003012074110390850b07010000d01104900c041181c001d81e03440581b4241840c1c1007d03051540000d80210410018501110303003007641c0745010040b0900c10b00c6910b18a0a0070100003051400c040c1c9644580078070401c105020b04184064280e40b02c40204d0b5022081e5801c2c5000d481d1404001e960f070009100e0040308400b071000140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389911951 1250 389910701 389910737
    0x150305070504170f0303010603020915040b0d050604090c0b0309010f050c0906162018070207030b070504170102090a0609080c01030f1b080f0c0702090423150114060307 74
    0x1082034030a42040c4c809914080701480c0c1554001e9001c01c00083d00455a64507a28003600c0c2e10402e140002019890240f030840400c015000710040f0350105940c42d000200543c54980041450030391248840e1340164581035562113607042030b14514070941c41c0c02d02e5016038180c540301d1540110f08080c000c4c0d00b8410a0810030101e6440004d2445e002000c1220080c0080c2600c4c0e11403000c800454241c005481c1402d047c4064061030600c024071003082d20040c0036919402080030029650045120161030b503c00d0015181c910550707100c0700c0a010f01c120000c60055040d40071b0103d2040817900088102c4e03443c0000c5812307548074024141150490384400c41158025405110480c8a440d00032a00c54900c440d28001031440340c1050012403102d0301005050000c6503029a03010221680c4a420250720360085901c0a5000b00020800c0f07003804000c00c00c08400c403824845041c1d40304c04441c2070403500d031040b5041d00070030f00c1052018155141162524030303068040e2442000342d41d50309a20302d02008151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389913201 1250 389911951 389911979
    0x70807020c030c091008160312080103020d061a0d05071e03030801060806130c08090c0a140405090a0204051611030f0d021e16020a05031204171c09150305070504 71
    0x42422105c54642c00038031580b003440325400480403010000119450743c103005001c0c5031403107003c0040099580040c00144c0d10903415050030390f00308900040e5000011001c020f103018400100341c1c01842c100381d56042000008540090b2468108440480c003000b48034045041d910340401030103d0b03c501e00500c1a00d200380c1c1c031540e008000030041c200d900b0b0000c403004101c4140d400301c900001d88030401c00050110402881c00341d10819190310034414604040c50509a40408030325124a0f1a000400c40100d810000c211540d038000b0000c01c010306100d19003001c000601400200450450342e544103841e0404403d4030440040360020503e80a0701e50b182000075031007840d0400d400100240e010007001140000350180c19003003004000590103500420568038659408603100768440440248210500780aa4003184ca200c40c6050b10b00c42c1c400c030328506041c1801c06042d040400d410402841c0d80d80681c80e0000c40d070100024041484106a0407070076110308450b0500801c0041000300f200341514443c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389914451 1250 389913201 389913211
    0xa0f050307020a0f060f0524040c030f020408070f0605030c040e270102040906080a020307050f0111011118010e010206041b030503030114041803120b1c0308070807020c030c09 77
    0x5a0300030204541d109400c1d03100c1342d0f4082e20300c10f5980e08002c4010b0294402e2a8002d00c0c14400104411600d1a2a907105a00140b58038007032600c4e090034024141c083d4101e4440350300c200809649564840207225501c580610900b504407800110000e08540a1011680251020202e0b189003d080804000040102800113403650302a00d000c00018401c4801c0f440704100f10307a00140e074442ca013101d41d1003643c48640001503642c219000410040e07500142c0102162019684641858071240050f152002540f5103006075508160319551104080401800d0640080200010358a1000c1c011525184500d0526000d40e02c03440104002c110400120028000c140e0907a05401e61207130341c0c00b41103070000e03481b0181c04d0a06080c50401882c1c540a0580c84080f080c02614030700a16403801419003485507602c0c1111a40c91440552546030440006c2170b2a004000e1b807001540b40340740060214000700c40d1400000d40043c003240ba1184046600e8500c0322005005202c145412000c00c4440c044c0540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389915701 1250 389914451 389914453
    0xa0b09100c080313020108091914010b1009030b010609030803070806040e01060f05090109020304081b0c0402030403020c0f100c0602032203020a1b06080115090317090301110a0f05030702 82
    0x110780c800102a44010343c40f82d074038a03403100350b50a480e10000d400c6a0000d00000559002079010840380199600c540c0d1201c2e420030303040301100f4410301c0000d005000c420030791500300d08400c01221460b90030002c1d800440340701b0010f46c44a60381c1c0742021038500c0120700009004020410102d00918445e80415030824401800065140c0341740c03102d00d00311100ca5100d8114100c003c00100014904000c40500410148205625614080c4c2e15810700d8031686000711500301e1528a8070b148120104442d84201c0c8000d00300310364a0a05081c040d680e006080003246c41815410010055400c1400198610039100e8840420380101565010040e400c002c00ca200742d515804182e80b410304500040b1200300d40240c0180c05020f10904140c00c1d282160620245000b2540b1020012181c1c000b0b00181150041e05010801c1c011061086415880729800a40b00c1422100f1030f821f030041000040c810011304070001c2060304140070f8030180c540110039880e00400c0e018200f11001a004500441d40000144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389916951 1250 389915701 389915717
    0x91217090f0913020102100c0e0d050709060e09010e160506070807060603030903051c0c0206031f230409080d050402060c06040b04140f0d031104051e0a050a0b0910 72
    0x12906468040354540e209900302e0f040710b01135507014080c0e007d40116014003840f0a50803500060600c05e80b040390140920703582c624000920034240700f188050500c6140500a280c0d070340a00b201e18000a9a40381010352a01c44510203a40c0001171006a000e01c820031903045c035143c0410400c0c0f0341c00151042d02c0788541005180c00081c421f1150302c2c0958441c0d21441000b50441c28418a04a1491003801c4070040005400d14170580190400b1070159040301c4840d42c940c2d4490580c010500103240c00c01e10780c0035200300490040c0c91301d80340b9901c00c0c91400d1501c2528040c80104015036842c1031024042e02d904028400071011382d500015402070016010b0340c503000090f02c0d45407800404072415510b04c2c2850b403c0c0401c002c84d107a0040c5100d24040300800742c0c0d00c2c0488025031a90b80c40c40e540e905040e0fa0300d464442c21a00c05d0152001032000405645509507042c000b100541401400648504c80880c2c001c285841c060742c04000b980d5225080e241001903800a02000358094042142440044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389918201 1250 389916951 389916979
    0x210c02010e0703150506061804090f0206270402071104020901140a09030b36070909030203040503060f0912070303020904020a03021308010c020a151503030f09121709 73
    0x70070180b0019440740c04d844500914864581044883c050031302e9104078030403c0000b01600080380c095903103250403240011b01c0b02280ca803005901d20111002904140b0104080d15203032000424050150001094000b420110500300812486400710041c11016030751450480c60030b107a07001d80450724040c10402c001c0c0300c3c003440300744003500071000542c003340d0308100500030805550304d642c0c0c0141c18503500300c81407402c04405901c503003c1401368060341006100648019501000403500a104c0e41c0030400c16036115040c003e490b6400350144a000f0300c514408500507107515180306100c0e100403009401c959034910072401d100c1d0300200080d4100741d000d00404a107603540b4030040a284117280c030016135a4003044050318820545502034543c90f45860034201c01e4503008140c0c181503503030152010b1694070000e440c02009094225411401103100c0c0000b10800d9000148500ba00003035844600c1842e81e919241c0c0c541034285403004080343c80524404451441c49006820782500040901c2d140c0c2c800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389919451 1250 389918201 389918203
    0xa18050411030a0e01020414240309010221060d02090a02040306140a0b0a0b030c07020301060306050f100e060a050d0519080a09060311040e130506071806210c02010e 73
    0x2100d038001c0e9002800001d0012a48007445403010400304140250705040c0390080950304a0490805140210011640c0074021208a80349005407035851030b01d5626400c03c0d05125000b0b4010b12a80caa40b6503070107184a1000c40c004200e640304540007014036001408550070b000e941030000c0e00040700c1c15000d00c0003000007080340c005c40144a04226902e0307000d00d0458000ca06030b40e00d41c08100d0050209000c140086241c51046030380c41005107140950700c0a0500c00b00740103001e40d0340b0107000d552414017402100381090405900030420014a41302c0d054884485201c2400d040d0354459100741c01c610100042e06003040d5030002240144141d840d80c1c82503840103e41c2254010084609000020741d241d0400e400452140181c50140382c10008140d440c8204101b03845517004140d04800d07032400180480700000005003520381c1c0102a07601c0c074104810054444444603400002c82c0141440c04111540f007003800c0c580c0030112013040394410307140500c03000081000c0100300b000c40d500c614005101c1c0174 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389920701 1250 389919451 389919461
    0x22180e1609090209010519090203071b080403020f1f080a0f0c020a030206160c060b0321040306051501120e0106080a05060907120503180105250b1501050a180504 71
    0x38101102042c800503900c10815003c1d4160011441903c01c2c0c484441c0d4458410f654100703544400d40700598036243c1075800e0f00e29001c19400c401c0e103440d4400003001084050009841160b1094035503c5090b001d1400300a0340c01040c02605034009401520f8041c0d0300d1181c540300b0f80000310002c00003000300b5022440d409030343e5458907410142e4418005041055810031459134007510180f801c02548200200040c010b01461802030001030704e4410ba0219507809000140b03d1a190318040940b00c07000c5500c0070416002032000362081403514000a007803280d08140030004420582d2060401c141d840d01c10001482035110120702996a41c2000c1804a020040f51031014040c10080544d854150000d5242603160780003240341a20034451800014030001c140c520400803034040d80380441050b40100c1b200e009a40b44500a4101c004003d40c0104200d000a00400d00684526040f990340054410045681262580c0001c800b0010000b4a80c8a100745400750b00810060302c0d1020381c0c8200080540e8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389921951 1250 389920701 389920709
    0xc100e10051f06030b0f0a05030d200105161107030201051b10050901140618060105071505010f23010e04110d090b16081003032a060222180e16 63
    0x5e9035a11414490302d03084000c41c1403c1000c880300c01e482070800012940700c4014031240420700c600682040030a50704040004006400390000b00814502005954200c50481c510080812604c40c2c0341c0c14103074000f1401105981e0181c442ca40b40418111440306020001c80070b500460144409404014071f0703078001e80c1d02618045001103401d40e08600b8141282c48054159403103000c0d090350b081c4450752038000d616800a424240385859401509000107030f000200822405145000000702e41d02040100b0441503d19100140c3c2c1802002c12030b100803010f40141c85808915a001640031510306908013989081100f0300b518240090b02c7e295105455500b030084443c29540310030406d103008840312446107501c0a182500c03103800d002a00c2c8000340c40500016040000003040c44492074603030f5144641041d558640c044601c180c1d414194000d402100802403007070101881c15441e9208400d0820940340c0706e10900c0b000701c042e010308900900c0240441d0b92180500011841401120784402c8010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389923201 1250 389921951 389921957
    0x607240204050418020f090910050709261e01020c010504060615140a0e0d14060a0b04020a090504200f04060210020a0203030403080601120606050c100e10051f06 71
    0x10724203010801058405840b03803140b00c20281c40d515405a901c1502c0c0c800710a400303850044e565101c241026091491005440704402d0500b42401941c036030040050044411000d000540e01643c0b0f06e2020001840115106603980464146160304810424101069480d0740006103004c000c2c4100d035094410880d42525021360b909810040b4134101050001c6c12091407500e0782d45c0e080701d21001540f40c00703090303005c0c01046a501180061074640903c0d000b074461304000c60084070120007965039038401003101d1005245081c09030100b03450400c0d009403802003500361144000c2e02d0401043c00001c0010041c001200310b120060704040328100c03002800c4552502c86101d90351820443c0117481e24100c01d85105045204000281c11a40d000c025240c000340e043c80c0001b243d886080040f920709545103001c10301c0f40d140c010005003842d00f0000801981d4107035000c0e543c5002d5035080d0301c1c003110190010300240e03030000d0150f8032105032240c1c4501e0340501c0c60f00e41c82a4410710100a000e00d080c483e00b0174008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389924451 1250 389923201 389923207
    0xc16031101062d27050a090b01032306060f0108190510030c05010c0309050d050717030c01150f0b0d020c0312010e0609150103091e050c0a0611070506072402 69
    0x10b4043d90b441000707044010008020500c1303130309803075903a800c4c2c2e02ca40707196aa9441010450306802900700310f08480d00030318a85040c0d40c40e41003000002000709240f5403000e2000d2007201c10b014011425911038140204500b40440103440151541100240040303110741d0355550b254080c2055103d00e034011007820720340350b40150451505545040c00c40c0c00c0503042c03040d84040341001942c0010705105070f4100f80d0b00c2a000051072b2410500d0320040c0d40200c00100140014004011400006400031416a4000303002d00d0118020811003100203004d00088042c04c001c0601c01582c08100a000d0500c00603801071606018403003660441c1c010141e860140a400c0004201e500310010002d5007000c4100c0d01060745040c00c0c0004442d001c7d8540b0340a05158480307006600b84011103002949002000764a03e04038a1186031094403048040500da118044030500414600c3c840e88295103000d20401c014040a81410200003160300503401c210394109a0403140c1c50000e6049903004a0059044009a2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389925701 1250 389924451 389924519
    0xf03050a080f0112120c02030d03020c1b100f17040503180306060f010807050d0f05061f0813020a0b0d05090d0e0612071112070b0c1603110106 63
    0x194042c0ca407200075502030006010b100d01000b4001c0e042580510b658401c10754820083d11100b0b0401800703545400b60300c1000071180d8140e00180114020542070303c60700c412000c143c00650160002442d04049070311a4888080d014045c1d040501115042c00840440322a9144480840460b411100d6801c0403500c180070415400180c0c071056003c03400b801032880e082c00850802d0020304802e504101c8c00308046039a550013070048480032204104240100841140d1602c00f401003650b055000c0c400e202d54618500c01c43c5041030220300d48c83c0c1c1c1c0d20080d5444050340c40b824a403880c0802e9034400c20750340c40001d03030040c0d9000400d00421941e50204042c074100038500d003481c904403000e2080c40307410b070b4a5040d1603a1312001c441c000d4403141c140c2c64940e2211401214110120403100402e031140290049105444001821200d0701c2426106ca0581d60301c4d52044c150f010b0401c0110786400c6007070305100081d000360915002c04c000c1c2000003485699402c00561219095030010b0344004480311000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389926951 1250 389925701 389925707
    0x6041413050106020c010c0c05030a06090b09030a230d05040302010b0f0a08031b010617060906010609120b06040f05011d010e0103080912010603061b080a0b2b0f03050a 74
    0x1080c0c100805040040b907241003401394907540ca901c8141d0420130b020740c2c2141000080d100391005883c000e0101d8201d05091324200e4001c00c040001035420810308400102e440704004101c034100394890356010f0030321414051100c4c180302e50b5150510380c0642401681164a414441e2600c02c500940c00401c2a00b40001030100b5105010348003402002c0b000011b008540002044a400300110002c4400103e00c00185e980188640e422002401e0b442c0c64034000d12140c001030345c41c0103001e024181d81da180d036590f005a800040c54842c280c01e284401c144100484c50348a480c6078400000341000c02c14241101920040701c200b41c00406c6004596000441008012a511070250001c1c1d40111420b5045807103052240c003500040310310559003507036042d841a401303401c883c00442d84040c0500103407140980f42080c01c01041c2e44003001590950024000c10001d0007122039022002d4105801c0c1d8040b07143c101c2c0c6c4251182d21286501d2030064456001801f1308102080c0c090007030787d54944440301a030b001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389928057 1106 389926951 389926969
    0x9061315030602120901020301051008040303021218010e1204090c11121b19110105130b09040e030a0e0907111504061116150605060414 60
    0x104200d0b00b5005010320181a000d0480243d40c0e600304c1034200c3c00309100b500da01c400f03144400040f40e8082d40c4640e810038000e1038090729000a004030030a00c0002600c1101c00000050800007a00c6000e1060070020040c500242a4500200b000000f0078080e074014421141c0e43c030310300f0100090142400080d040200010769006d400e059070080c5690b004081c050448007143c4880c06854180415040620392402d14200c0c070306212a181c000b18009031111450501000b00020340f00b401e004c4400c80000c00044020f55a1882c26005100594118086201082c0d1050013200d02c49500300f035480c0000402070f41c0c0364205503100c0d4401c0780c02026491008d40940621592100d0300c0101144061069001e6841030012000b418080b42d00d5100c5e0350520a202c440c54010940020000e41369100c0b005d4485001198080d11070300001c1d02130f8000d510403040c510a0615001c001c2c1002c00c96 = true := by decide +kernel

theorem cover : BRFrame.Cov 389748201 389928057 := by
  have h0 := BRFrame.cov_init 389748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 389748201 ≤ n) (h2 : n < 389928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
