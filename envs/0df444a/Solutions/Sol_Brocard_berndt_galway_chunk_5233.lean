-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:15.941801+00:00
-- url     : https://prove2.me/submissions/17b8cd2b-594f-4eb0-aa52-07005e7e69a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941007194 ≤ n < 941187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941008444 1250 941007194 941007217
    0x120203120f1204080a1209020f1909050f01051c050a080f0403050316061b170415050a050105030d02031309050402030102091e030606150a0c061107061a04020906 71
    0x3116810075407200c1440c020040c02c070820900140901090255000241c500c40016507920304030480b40450704d10554003040c0c2c0c000e402c84000124a0840e28040d0b80c10481001407101d40b0783d40d142d4030400d1100391070080c2c5060101401440040c8610304203404012103220b0313071709048000d65001d50707a46070b81c0b0040303800c000d841510086014190790701c00c8421103000710b0304507048070b4a84501540100c0801850841125514a0544801451604d103a0104402c3e46243c89140c1c50205014015110301e400800441d0200f00305c4908070440c05841c412a4061942d10700e0000d07541d070411017414030300001c0c0718400080d580140043c4d840c01d40300c1a00da8060382c0c1110b10106440d11644040380c0a405441c524590141c400c3e4180326000b901c480134440860f00860071512252034680a201e00c00c0b0808001c481c812030308000d0500742138042c02c00902083d218400000e100032140440fa641c0ba003103070704122441901c500080490a001518013150044212021440c04007507000044a51003500c0f036100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941009694 1250 941008444 941008447
    0x190c200907030b061c06090501140a060e2706010f0206150d110d0308191b05071b080d0201051f030f050a060c03021210060e040213030f08070c12020312 67
    0xb84e1541029203c002c84038003e80708212103400c010201416040c0a40c60b460352410f000002d41480520045e10030305006419480c101c1d0800d441110103010101c1081d412082c4000c03004943d41c03000703040003880240700d00014103504004000514105002c14108110348c068000c1c07191200d5030103e011a00241121503444110080c0f030050720000540c084e0070f80c0084203084400500d43c01405103403007045039219482446c01d2030003c143c00c0f220111480c2500c3d1980146100b42240135000920049000b8a580c2e9050500d121043c041500e0a40140138035400c03444001c41043c3d02409219040251020b070401303245400b02441c0e841c80701c02d200107458804000e0f101001d21009016680c1517581141c070074000f550103d00e019000e54400d5500051002c0b407000011441442c10f8528001c2e40c0c550b544040180764901e0421020f90010411015404000f07840000016090800c10b0009403041d086a525101c09003400325201500d540000c0410407101c0d210801a540850001d40d0418000a40d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941010944 1250 941009694 941009711
    0x1407030c1704030906140f0a030c1b06061403031809071707050730050c16081501050d0317270106150c0f110105190c20090703 56
    0x80300e1401881d45100d07500280da00c01e0100f0700da441071100c0300750341a03515400300700c1e11000c4030044107128010780c0c040175070010f100350307005103212350409051a0701d94a02440604840461000300d001c1c41682241e41e0f41d611142007110300c4c9090812041c0102c01c4001d942060701115040380700003440030001e80301e11144400200c3d640c1c007a400c02c60002400429031140c0d441c000c003018140e6482035034180d440304000b215042b400840c102070000a51417002c05142071944c501c1701980d031a0401f81000303840b80600000f50845c49a5000c07034a0007460144000c02d800f442a124051800070103070006030140310000300c50f17000311707800400e00500703040c0f212445521580c3d1803989101d03501040041c0340d10b2101155010204040c1500020281c60008141c1d49000402c50030546002d44503d02c010002a002d49085020030114000c12091050604006140c554074428420000006101100c08510320401c11700c240800500350306040812034201c0090502c1c130000088405200814000c20582c8a0144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941012194 1250 941010944 941010947
    0xc03071104110c210c0c0d08090d030e09010b0c060711100e0610081609020d02090918070f050120010608030309010903120902060a05031b07080405030c041407030c 72
    0x140800d102107102d440c0d200c80704031000586845040b1583c040c4880f403007004101c145840011605c10702d84120003803003194600800d0201c070f4055142c0a469010080c480e8040d251507013104a01c4882c880e540301c06181d040d0404022607148185c1084440400900019428101c0081d246070404550f007003034401c01d0700c0070600302d181c13001c0240c4000010381400b1901e0390310710000590350301070604c41041a011a8650702c2c251b070ba518a2002450044c95031102c03c2040c903400b5401804003803038903140546812461004a04599416207141e840070301c2c140840300140c1000c0c0a2000507115400c002c40025240c600028440086094a255a551896800d0501c00d0b001d601210040c840001030fa502d070728158280318000c084481003980483c02c0080101b0000b23040e0b01c500240c89134000d00850400c040914112101e400043c01c0c0f01d413000205005400101e030b104060080248201e1009075150300308028581444c5440804901942c03d14030b18022005070110380326440607151170b001030384550743c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941013444 1250 941012194 941012201
    0x708070203150403030b03341a09030709090c05041e0c0f1709060c13090213090c05130902030901090204110316080c04060e0a030204020a02061b0c03071104 69
    0x9601d80308424150310504400001c1e03a102d42c0c020b0300e04109418124062507100c1d0017000c1d5240c00c0314000090340d68003008034003903a69081c0f880400d0040441e20f660306480001641e02440340c4000c1c02141000c0382d40b808220794006040e007540d0901542816a491b04000c03442c500417548200d0f00c0d10008400c22100e40700c80c03064821001c1007405008142c5c140503114010301c07083c0500048107041504208000030300141d0042035844001d2000d030b9603105450201c0d0f0089668075259500401d400070b581505400030f00451403070300310f19120381e616001c142c008503645980c11905200c014007a12a1640c07608640401322040204090fa5070f07548c3d020000d0041c40700c000c00942c01880c00034110f00f6244980b0155200300e05c000003401000800b04800c3e80c0040f02103e100700300c0a800c110901c2032501c10b1040c400046070260419030b0031604c90780082d0681e0801c9488400507030002c41044080169840f0284025012100f4180fa00700d800030601d0b182d10030000050a281c0002d41c0081d4135481d940d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941014694 1250 941013444 941013457
    0x11070206071a01051219170307030b0103050c161103031308060a0f05060d112209060506091b0703090e0405031206060c0a111302030f070e0415031119060203040806090d0e01050708 79
    0x5285598900d042710010f0024046a076880c3e000074501400a040c00d440c1c402102c2c1c504075803404240c8440c0c0d80c0d50310160140c00281b1705540602040c440c01d5030113661400c100c3c001d80304e464060461494032081200464240c480d03004052800e04c024011940c507080d9400c0381480d000040003101c4120440411b1080c3d807401c483c450000e01d0708803854044416035220016840c4280e40c107010170740303030131041003443d000a90b981c4103480c20b00094032503819445030041008a10034101a450035903103031007030515207108403001da546804c0081d500e80c1140c5905800b5600802c00c0380e0785801d059031317180010303030701d9840600007803829800703412561203650344c0800b418420012b031000395904c0c5424040c4100d06a0150b5074030740841c8241e10002e05034501809254a51024240214090391850322031202010501e41c4c03280d005000c0c0c0041825040d02e0a80c80f030064a00740d00216522480c10151500d0408020000f000c150000380c82002120f03404526040080000d05c0d04544403001410030090620405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941015944 1250 941014694 941014733
    0x804020103110415020708010e060c031f0e190c050a0c030e151b0304050f04090201050d0e0c010f020307080714071707030c050603100911070206071a01051219 70
    0x108000460300403d003803000c20b586135982a0744110395124101e07070a84011302a00e4085402000000e119414898050340c1d11003080d111000c0c0c85558420403000c00d035429001459054040020409a0300f0641d10041145038442c07000c1200107031003070000386075000788c02402003004954070810b02414840c140c01024008000c00c01c101c0d0705c01c40c00480707015030f000602d01400d0001e441e48125018102009070380850740003509254071101d140081000401e40404124148041442001d042181a108102007281000c1c001c0c5000096600050b0004c01031602c4170f42154010400c003070004544c10103548440f584603460312800b414111490f424541c0343d8021407a00c410840d8200d5409000052440c11280110003105404e6101c5061005c01d00c0115800b404003041e0140800882d0340944c000d49205242c000c041e4200282c41d40060701d1644506c42c10790700c0c1d102d90444041000790f07010071240104030840b440704480010300030041d190304540541c882c491492203000000c1c4036040f4010382448070320b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941017194 1250 941015944 941015947
    0x11090904030315050316050307230d030c0b04030909050c0c3c0102281706130626062208070606060315050604120206090f040504080316080402090601080402010311 72
    0xc0621a2030707987c45280d20038440d821000410040f8200711019451a40504a03003c0007180240959505a00c50880402090014010110303110314480303030086109503152406a842c5c0710120702940e0000d88903081e0500c00b005124203002317001600c440700d0900080c0c2620990500b0140b410002c41040b162110300d04008540c94140c0f41c10b43c014030034001c03d818a400c070b0a84840e0074080c0b00c200c86905d0030110365298120000032590b84881a030204005140303030b034000e01e075a03450021394065078010b2040355000d13500500e07071900c032103440c171882c2400d04010002072402081082c1c008a107400d80e00c1001d401500300034144040d1b0340c1103404803030f0010320501800d0342d6050002e004206240801d0101d1400b00e2002c81c052800004480031502c0d03c940104106034540c0030001e4550116804d01c1d032045020401d1141c0b41c83d40d002d054802c60240007150384902c0c1941498040d4250003000c42d0820486004000060741c40e174030087c0d04130400303103044400c55a5610040c0c0040140381030041c2ca0690 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941018444 1250 941017194 941017213
    0x20c0309041503081c0c020a0b044701091103270303042009040c170106080706030c180b0a080705091206091501080c22020f040603110909040303150503 67
    0x3a1020340c4085d24100400c005000f0320104c100d844240745031004107007089807004640810324680840989880c140560704125404802c00441e80d04054100034805001c800050094810981080d0041c050044207116564071b10344202d2480c0320050030360f0702603112003c101d0048480c044030000213000080440b0703a2402c05081181c1c1030082c40c403402c0303d900b00c0344111842c18184408528020f6500c0340b001958a418035100b04c01d558904c8040380103d650310301000420756810024800200710300d480c0094406955180103011168040e1741d0340450700d02c0b1104020b00c00d14041101e604150314070b40a0490385554204803854071458a020342d2051080100000b4604007003005401a0074a9049800d101c070810080c81002c1c0d02441035680c250045005d681c218201407032020403049141081d89102400a080d04040b600040300c00e41d05d260022400340001c076014403841698010301c0000e04d0030981103c002804050005000508164840001c0e08224501a0003103014100040c20b6504810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941019694 1250 941018444 941018467
    0xa090e0723040e010e0c0f040b0901030f060c0504270204050603100819020a0e090f07030804060306090b100c02120a060911040504030c080c031b0604050d03020c030904150308 77
    0x100c800d00c2182c403851510860001e1040c051290ba2400c4603480041c0c46a442d0310020889030314058802250440d4407091590100e4ac0c5440300f19020f14424010200548140e007080000c8030400346083c01071220401050100a6001c029000801c00c140c285441c400340b000304080103030166038080c07900990040f061050780c0f185a0400c9040e40d104e50111094645c004e0054241c40c0550316000e0f40041c0018020311030240d4906440350310a60300c90488075804220700e50ba9140c002c090740309481d10a000308040c8003196060089074014140c181041c40307100c0e40840020680300e0450016010310594110900454031804164004050500244c0b0b00c140c11606043c0060302d2480d40444542c1c203111100d41e603030b03e0075104031805503402d0340d507a85488000c1e42e01c0400b550300c00b0b915007889202c280300b036424080ca464050342c18a4041e0000d0282c0d4101450040d2406201a440d0400c0c1130052100340c0402d4030000560740e9110b01110042500c4081100128003a2507030b400141c03042c00700044100428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941020944 1250 941019694 941019749
    0xf06150b070b06151b0c2e0c1205030601020a050d031406040e0316110907090302011803051c030204080304030c030b09010b0a05220905071d060a090e07 67
    0x9501881e400b05860703035540104034200c0941c0418401c010303002e0254040c00e044494a0440b40410907040322007158101e00050340781c04e110f0420108020101e40682c0307070901780032690140740c00e04d03091840e0254215a56020211178443c00c1c0c40c1000740101c00102e85a100300001d42d00c0035044020b035401d44000c014020081c0c11007500060313084c05810040b85003810113100781041066581c000c0c50520507200260f1140c00d0003508203840200c2e0405610500399140e01606024004035203808130160718510014159080d00d400d05c042c920904c0d6020000304070081003c42c0d510075580c1c0011401050035006034024001e0b60040d80c41c41c84003180220070803c2c10032540d81602c6c040c8030780e00240d6449006107802d842d030440807070b5000390340b00030304000700c1c20490305e0603414281c5600907003240240c0701d12110890f0030911301910240d0060300d0410480e15101c820034408500c1030701c911450318040c800300341c010700076100e001c00d01070340c880c081c0700d030904140300c068060400d00e0300000d0580401003030b00022 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941022194 1250 941020944 941020957
    0x702030406020f0712030c08070b1e01092310030c091a06040b0f0304021507030201060303110d0c02060a2a110109120209060f0d0803090d0c050a0f06150b 68
    0xd4800c3c1041c10303890342d4000030070f5801c807402403034002d58100843d03500b1210b030400a0002c4072510024000f000c0020b5201c1c28241c400d0f2540042107c07488541e41c1400c50450040e8400344009144c0708400c0109100080088103401c81d4080821143d25094917100e110100342e8806040d09840e040003103a0841240c000c810310440302001c01901480c50410003000340b00b03501c60b090094004200c8114180ca40704007544e4410300081002c40c9403a0101c0c40541c0e65805180e007140140d541d0078083c800c05800568615402d1040d50090040d0494034802922403400e10384060f1041001045841140d8815810219440140b0f030355440c82c10305e000304803030041101c80c208907044842480048455481040c51008a8924036140035581240b5000d01c0f880b403001070142904000b869400ca0490340f94070900050b409c3c440c2560300ea0700d160000555080640300c0040c1d5003007090507003d00020580c005160b04030560400d40982c80c0014600e441c0e0001c00041c0e40c503521583e030fa950001001071118000d44413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941023444 1250 941022194 941022197
    0x2106030105060a060909050726060102060109060b0a050915041e0608071715041e060b03040b010b0f1e070201110c0616060b090a091b05010c15090b0702030406 70
    0x103640b910003c10802100c02c0c000e0f040041d0748081c0800c00c2c42c01d0f03a0001a0044160f0810003007201c4025079022466945043c02c0480b15240c000388201d65030304025040c01840510801c001542c28814082c8482c45154850000c2002c0483d0804996a4030318104142480c000b9210742d4550f542e04049541a4000b04612180420b0a00002e0401d001d03041e0548154602d5441008003018042c880c0c3d104a805080340d0f240300d030100b60060343c949440c0b04140085079090091490781510342030800a80300790b5080f500842c0e00a1090200181d1700c05090340c191074880b451552500314482081289010359441c0102c1100701050540c81651008009d00c1c00038000e980705003005542405c80d5554028000c4c3c07094012504005c5601d0a11203511140000c80c440c5601048003e00751002031003680b4143d81c42010701c1e40e13402941c404c100e001d146640c852101c0b0118030443d145088000390000051100c0a4029014501c00d0709141030580e01072040541e1002e400b45080c00d10f000001c0d5a82c0041c040c520 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941024694 1250 941023444 941023451
    0x70b01061707020d350114030c090f1305120307110a0f1403040807080c040b0312031317070501050f091914160902091f120b0621060301 60
    0x103507041d440c240ca103100d40c00c180c005003025000300b9800c840d810600c44406503809114100c0c8400842c0c3c050040c41c03110101e019240350343d41001008840407140041c12442a400110100021340341c00c1c0039680d0060041d01040156510110210f58112144900914500800591080083c8030502a50180b07265680e03140c1d018a46001090b5100344c01350014110301015022507002030f828010340119210480c00350303428180e8800540d89008a40c0d002901c072904085440120f506161050101c0c421044000701400a14040d0100480c400a08900040d0018040c11406c1c440d02d450b071303812440346031904903540782074509140307000740707425a60020b40015071030110785204000110000b03841c28402980e12501c6040d0340e10544441d1480300402c807801004009040f0380c1c420202680241194000513035290340d2002040302511600400310743c12061441000203035a4454000c1082410f09600001c1a034001c4000805c43c6c020f4150102143e5011403174148200c001c035903c5c5005aa003a0000d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941025944 1250 941024694 941024717
    0x8120606040b1812010c030509160609150302040e090114010807050604053703050f03120c16120e0306060609010c020105252102060108120c12070b0106 67
    0x840309104a201d0722080580a1003042c80f50011490030304200c110050500303000700c034250403031429a481e0f028410013080d03417681000300c800c600b44090b02e81e4064480b000402941000f0020780b101c5601d0161400c3c5d01c6030880e45044c514043ea040380d026214940c1c042410f8603000c4a5103002c0c112203c514004158581c0000800c060f001600e1800c2c0c030f20007841241410b0500050114072140700c9907032200c46003d4070000424038140b0701c1c1c3d0007110388290300e014601070075403c05516002c3c00c00c200c203c180c0e004000c00802c904501000542104a41d800c441e5100d8408030320f040d9664698401900701001c00344030058003a040032885a00d00c00603015107030640e079030108001301070003070082490110300440d4041005601c588014101d100401c01c10051801082c4c2c140e13840c0102d200741c11120000c0c000c0750031901e00001211140180e00510042c90151b040001c03858455854050001c070360080810a900c01c00414008103181e03003861420591501e101d03040c43c034103000080c0300c0c0d80301291910610 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941027194 1250 941025944 941025949
    0x71101020d0c0b0601030f0b1003140f0601020a030e04200a03060b0708030403180308030c1b0606030705040c050c03130609050108151306270e0d140307110307081206 73
    0x244200c03908414020310b1031352841c006501400400301e400c01c0c200d0340c56801022039510340c041c0b6122101d0b80d0b50000b50760f4103002544002c84901901004151404c0340400c2101d0f80c7c006010b04c87d244d410701d0f001d81a921840e011a0140c250b01c101c0842c02c0c40c00d080310007a8050144041d12207894195005d10039181d54060250a034802d00d500a041d002c001c00018010038010800103040444081003003a20681e40d0b11103158a82056600f840c0103880000d81400e8220202e08000d07440d042400540a541480c0340020b0755020380d17102e02c0f4041d40e01c0f0301085407400d000c0c000780d9503040030f03402c1666540c1c1100f040c102c0001c941801804085900c0000109555100c2c0003200d21840c4610361286075451880104402c2c141400c047e00c40d6281c6880011600420179005509600c0a03803040b02c803d4541251000281c840d030400c10813059008410801605034000301c4100c6090800d80800d5a0381c841329030483c1d40c040c041d0003038101f9103c0025040b003041000001825002442441d12406031101c008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941028444 1250 941027194 941027207
    0x50904020723070f0f0b0a09051003050403080c03071b0320070302040e030a0906030f110d0e010f0509151503060f0901180c061b0c0810110703051209070b071101020d 73
    0x1805e40c3c0c81c60740700040c0504100d0303400601c102d91190500903140d642da0000190640240284000081d440f030b011b2208054004504581125000c11424114500302800411940004003010303505032101c010481898080d04824441040c000001a00b00318090700d0903944400502c0101d000f64036065103554030203004410b0300d05240c610303500c508041c2c0c60a5002c801a20860b0441034489544000510010600000030301400d4000c10000c03404600d900318a500f104c80c070000c46420a41060100840150082504115900c0d205043c500079103440b140107108441c4c40c400141c01d440341c40103222061040102c801e1181007410001d01158001d003159001c46285100300521111402209000d49409040229124005c0601d0f42c02c0c0c0808039280c1180100f0260721041d0141c0100301200d14040490203200040c8454001452030147e0a6600601a10a101090322500c03e400c020811001d0140411401048440802078551085050400540e03e801000a01509c507411411070103502604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941029694 1250 941028444 941028449
    0x7081f0504050d050708130906170f121b03220f150809190c14010905090103061104230f12060f0603070503030d0c080f100303050904020723070f 64
    0x2c000c3c1011224443e01590741d90004041218407040c01e1080482642c100c440802c001d040a0102040051500c50300c101340085240304140d40340c00500d039005010b080043d40442e29001985000c0d90342c0780a4111302404c036009500740c5080e000014681c520011074000511601005d0b9501075400303580c41c10340114442c035a00c03540c1100c000004001560030301031103032554406620b1041d03850800c0101d003111602c441c4040110b410003005402030088030300404000710048000e00b4031204241c1000d000030b4000b901440700500098076600c00c200c2e41070404050350000e148410240b00030801915a03402caa2040040d05401840f94203040019440c2080c2c61485118902001c3c3c401500d60300302c00b01c464400142182d8140c8103002d00090381703480030401403101890018000940414100008121500140c00d2100300178442d828081c00616107803805080f26030605151744d80303000b41408200a03018950028002e0800b240d03511281f4400e5210341c401d170324807280940d42d41c2a1210a1307400e500c0240e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941030944 1250 941029694 941029703
    0x1509030e180402090c0705151f060210091e061e0605060d0e0c03030c011b0c021c050115090906060501020f0a0b060604080a1b0605041419050307081f0504 68
    0x8400b007000360030030240c442e8003c078400b201e10389080b0301611640d01d09085e582401d11001c54480c10800450013691074203c1141c0c135070f40c20070714081ca881d4009545420244869400540c1c1ea80014100414010580c0303c0a4501e00400300341c00840c1030400040030016500041864810f981d80e28441c6240b0440c8244e0b0750081c0190300741220504020010441d9080c440d00c2072050190b00f4055640c20409060241c034064000b159001d100178030701784440e100c060842c0500500c1e5941c0d0340140d9640710000707042031410401c030342541d2550909a003d4a004100e139600341c03480303400103c0c2642064109150442c05402c0a109460340c450049035100041c47c44081550080c01003d00003030024141950454070040580c1c1c10142c95405550a220120b48101e5100005100740a1107100403104c0d00003e00c0d040c20418102440c101390440ca0004c2a28014401c0320540c3ca546110455448102c019200250440d0503030342c0c90714102da50b01c810a20b040c2c2d078038a007a051080c6000700240a858801c0d07601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941032194 1250 941030944 941030989
    0x803120103060911060f0901031a030a0b070e09100501020d09031e02042004030212070b0d050a09200a09050c0405010531050916081506071509030e 65
    0x71a150741008244481d4100c880d40010903140b030496480f01d000d0301c0c803c44c822052583d500141c6d0009021541500d45132080006030740b4104100d650046980b1100f1030700021803038484e41d502602242d0f4a80c04040e6a40e010352002c06002503501c8448541050719000e808461a905000d0307010b44095403188402410081226032202c0780d103051032601440c6610141010685405202c0a084040c92000c904960800c0c00b040c10019890b041122542c1a01000050712110341070180181c49481400ea030110465111004a406903103e50310682401c1d030030219041d40c0ba0f02c501050a08030366070b640c56502c40c201a51001c02d8040492007003038000c2440542e01c5203028076200041d2200e802c40040c01500e8a003020501e400f40084030640000e5441c0356a4442e200c908010410078000c0e0003400c400048583c0303650541c00da82c1c2016032203400c4a40f04002004110780d00d07000480e58411000c00500803a000d1019110400d52500010b14030f600c203444a0007802580300500802074a00500740308039945 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941033444 1250 941032194 941032199
    0x302070603291201020409060311150301080a02011b1a0a0b01110304030f0c03080c03120a0b01050d0e03090d030306091a030d030c050f041202040c080112083007020708031201 77
    0x1014442d03030640c0c3e40c9420016050541c0c0740c511404494080e401555000d050809480480c1360251022030031845600c07031281154140550035035580c0007084005d040c0302c1c51081da0a400c543c1c481148413042d500001c424846860201201401c0c0015601c49081c50700b40001601c1e80e42c05008005500c001040c01503040034515100c05215408500068070035500e40c10006c004200300c4801090011002c5004660302c1e4009104c000d00400c0c01825a98054030703006465070390b86c3e4000300304c401c0c0d407850745804203d41c004086441e0031031207031203120796000c4000307000d41040540541140080310402c40c0304101e100f41c0d034800e90b0310201e0820801b59041c2c00200c3d003861264080e9000d51103403c5d8515150f42440f503450f0340c00089500c56003101c801c140c90180868114540760142101a101a2411020952400c000e000403409010030080102c10003044600b440b0040100900c1100003056600031a81400005211100f1081c1c9020006009540c1c01007615800007080310789e550b035684e61003d078503031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941034694 1250 941033444 941033449
    0x12030c0e012a200402090d080d06080d031a030a080307051e0a030f1508031605030c07090b1507031403090a050a03030b1e130c1209030207060329 64
    0x7084250a241903595045811428a942c1c00c035442c0341d20f105465243c03020100d80c42451030f030791102403c00d2081d40100007180b000d4840703640c0c01d20303403d81c4242e000f0344410004071000c1c042c01e125080030700d9611860500100055060b0000b15200c00300d031840c44004619401450746a1b1800c00300544264020004600c80c0c0740f0a0000345024044010307110b40c040e2002c10410510b6009440150000351140c5000e8031812007846140446800a0000c8442d2450050f80c0c507161701030300c050300074143c800301c2201c014050b052040310000600442030380d11060b190300400005081405002d80140062191714445450030300032030301102c0d0545c07110b034018040d000903468070340c0c002043e40c3c0ca18000c440c02440061020064669141d101e17071404124020080700f8401c203501c88131800700014101c001c0c01d02d00c3d51a07604903c4900d804451000c40c004d0322100041e40c1c180d00742092041c0203883d1080d07e01c1459070208100c0f0580b45195000e1010319490b440301c04000c490203d18203084080c2d00035850040c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941035944 1250 941034694 941034707
    0x30c090705071406010e01030b0a09030e040b011701030f060506030d091e1706061c151808030a0203040b2d0612010f0603020a0e070203121504051312030c0e01 70
    0x50384140490300704031400200f290b05004003070741301c104805084001401004840313814168040300a840400030050f0b10b442c018203c0b22003549003801150344441c044002c0c0d212358484c1c8003a0341e0100c242c42031035942c3d25042d006000604400d84200345090045850342c640030800340750700c0c3c0740d65881402003410418850583c0d04500303410a6103002c07110f8001140c0c0e400d1078048400c1c150f00b2000d4501442e012040c40a482604901c04031400c4041b401e8200181d41d032100089104002800000c1c9404100101e2500444040f0083d2180c036020017004000456500210b100714804c10f028101a21109004603508441c0d800c01204c1030359a40174402d0702200c001c1c4243d80804c0c014400381295994941590848501c903030410026520b0360070a100b0743c1020203d4600030104100d04540343c2c500400000d48a0080ca840c54140c0210b50001c1400701c0c542c19141c0d8032403140140200070348d0614540802c2911040607045901620810140080364003070b20074243d0a84503a1501107040380d0100045508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941037194 1250 941035944 941035957
    0x60c020a290904180303020702031b0a180905010e0f010b0604050f0f041e14010b12190605090109020d0e0d02061b0403050d11060c0f04030212030d0c0914030c090705 73
    0x81c1d96210741045164141e84003001c0c04e0b001c1c0d10010399800389401407604001e264103034642c125007045500c41003511820049422510420840d14002c180704844001604590b940035190303609101814581000104121501d903400364001c120220b07103030040c0203060046100c1c5d07079444400110959101d08201ca072010000c240104001290743c200346e20410010075803202000702560f03922044043c2180c8908a0f405400303084a01824103406408200c10510020405940180302d40007400c5100317140d41142000d41700c001e1000400e907854221882c0203412400b214101d860404070290901d50000c20b1510150307202d58082c0005595070144d10f0851024107142c00c8018504000010200d0b43c01c2c011028045040d6030742940d07009060044034903100c0c019081c2c2c5110001000b034241c010940d20100c2d01180d0703054580720300701080a0346260940c02801640d200c07040c200751001110507482208a029507141c3c40000131004a140f09040d542d02c0c1020265070800c0b1400c0108400030f0044015002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941038444 1250 941037194 941037199
    0x115050411071406090c01211104090609020d0b0402210612072303071508070c1a0105040c0c0222090c06020f0d08061008100f060c020a2909 62
    0x90400240d0303d1020f491080e501070211a0402814080039076820720203840b1114091030b0124440181000118800450400150070389580d0200030424032081d1058600900441408002403070b6103250160181d4080d0030804409880c020110115142c18825a00e00d066000d00074040d1880c0b10300c040d900b411000d400b4980c00614840162080507041050102600c644810f0040c407207040740c40784007000200c64401c0d100760070000082c0000c03080010410300e1121207150460250301c80041c156004076071004081c00199127100c0c00400482d04915250407114161000c02803001c0000c0704640c550b9103481d0095001c1c080158000d180c1310340d210700d41c0300401007580005d80320703e940c0d0b541c070a084041d0b802280503070401201d4800c040000c1c402c0450b83e002030b013401807075450980d0010740c00d0000f00450800b8404060085448288101030480103000501036062685440b01c2000e850182c07624022407213901115004500c8003407204091200c29000e2114901146902062603080c3d04a1400983c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941039694 1250 941038444 941038447
    0x90f01031b080a110102120d09120927090b0106111002030c090d05030c06011d10030c0e271011090904030f020312010f030605130b130318260115050411 67
    0x10452543c1e500902005410040c005101861450481280c0c517070301c88804103001030341100700250741c00000c0681c00303c0b4500033070501070302d49103910000910010402604040821001088140d08041c50300084c82c40031045590260001200c10140d200803501d44c000e20764140700701d0784c040c20303e1b50030085494030440690b424010039519191426070240d0084a058000340201c0c03010700b403081c070741c2c0b034102d0310117032030b62204a085450b182e0300300309a4401d0b10603800074180050800d0340612020b101b1726405d10600c0704c00000100040740c0e00d400544449030503a1074485c2c80003880316010101c90341100041c1c85c1303001c0c40d607840d02c05a502080c85c4100400f507000401c5190944c525425000d03000e03001c602c00f84090203040d400c1c01802c40314000d0500e01c0108003901c00c140070515400b00542c0c01a00c1540c3c40c001101c142c5400c0f10000d00b0481e8100c100d080810000c1558075610f12a43c5000c6500c1001ca00c5a501240c00303542a00d00c00c00694260301d21b041d0050000f030620380c1004a000340801201c0c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941040944 1250 941039694 941039713
    0x30c0b090309090a0221040602090d03030b01020f060f07081e10060906030207031403060a120b1f060816030204050306090715020c06180a0302090f01031b080a110102 73
    0x5042620884001200340c00008141c0b240c0e00d841c1d6003064005013503800840c1004510b541c40e07071241000740546221805000001410007038190100e6403854405401d44120b01c041c0e140c0940501544002140940244090f1080e801400a140740c400c81084030f00d408140c44880c003c1c1c690b00d101607d40c030218011095528000702c0c07100301460240c1400d0590a07511403901d140240002459004030b0101801008180d0220b6800240e01420a20304034030360f55030351140d400040e0064603e5121b440c1506c3c180c1c0a04080c001c440f045a4452440c0c880a2003801900150f500140b08039801500302140000011031409840100c40c11800d81c43c03420f00518041d200ca002a04c2c10b401112400c0c0103500462080c40883c404240c03d0f40328914500081030107641ca500044c0550042d40541501c50814178100119995a50440d00c0255000b50405101d41000c2c203030503207200c000340000d5513038444014120707291040b6034038000b00b00e610070070140114640c50b56074840e0303001803011054114418010340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941042194 1250 941040944 941040953
    0x20f041404062c070609050405240a09090602031b03010302010c03030b030c0d0b0601030f0b03030901110a2a0503070302010e0d05010908031f14011b03020703150204081903020c0d030c 81
    0x10004807400b0341c3c0c0144001854500001d107100d880787c220b503014a0402092040a04c9010701d10800d9040380001c0007071516101c00820703d501540c0d40000c00e9a13040282d903405103c600d0f8000c6001c0d42d1400f020035541c1208880b40300052000703120007400520020b202c0004248290b10065805100600b968003400c2184000740d8100b07040c0509940e5440ca501c2070006a6815205504c0c054020f020203000c401c3d091000291030b4083c0415003414860154034a00c031a0100b40000707000c160707120501402e100003840c000c84580707003003e0382c540d4401074113200031801c2c0c46c00144020440f94142e441c0d03a00d40c10781c602800b0002c400c924084071503640f81c01424000072007200145100b03203400503114450313054500b0405101e803260b40c480d00d004c0319841035030b01e13031641d000c180c2c60406103078040001007002551804a141015541c0054142c1102c0c0a4104c088506500100110703290502102d40c40012048003188641d00f445d4000c1c050703407140d08203d02600745a00c003042c03010701a0420784002c09040d2a07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941043444 1250 941042194 941042261
    0x1a010e0d061b0305090c040b1f0201020c0313050a06090e01090b0d0b15210a03032a17010504051302130e031902160305060403080c0d0c0c020f04140406 67
    0x954004a1340710b00400c216914200081201c000c0100c500344400400800456200c51000c8804941c0c003180c1551135440307034001d404444040c11107004580d0f4803400302c0c4008050a6a60107510b2065202800003d06c0600c0b8032070079410f850050701c0e02402a413a00302e0610007400c6600c482500580c20b4007414000c129486150385c41011403100d0006070066100c10041c2020f612102804600200d04c0706182e4900000390f0359001503458140010040060740171204800e203001007030034045904800921005a001030288200340d100e99040c84180d0b299010030058030400c07180c401c0300c06034a818030f00141c644544620000f00303006000103000c1107a421064159840343e540e4520514400c4203003820250304001d50307500c1510701c40190b003c0c507080d0703030300c141d00c80d0f0000c0c1010b001c12100202107441c0c0e10524045403000c0003625420081d9000b0380001420040180c1d6060384154000000341499080c03d00841b410b0141910a4110075030725591781b00018a000c8403404880c1500d9034510026590740d44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941044694 1250 941043444 941043491
    0xb0a12120816080f0604092108010b03070206041b180902031009021513050616030905041e0f061a03010e010b0f0301210602040b0d1a010e0d06 63
    0x8610048100100019141050280009104031820740407040720952000c20281c004c8080f40607600307241c0b07502c400a4040c040c0d40101401305000e075030311070a1203031a03010100c4282c0c6660302c8240e03050703907103001c0d030011070200700c2e072050141c0c100000050000c2c141350000205d04900182107070300252071b20841410510703444190810b13181c0e5425014250303c0d082100490140309050107120030125540480c66800280c0ca03040c40d503600c0400d0400c405011140450003606000d0995519180c0c40c210020085074001c405070081950210007140f181028015000c403880d50000c2c5600e04c400000030b500007003203202c800d8102d0503510745020030382d51001d680c0504104c11303040700d40e40c483d414904841001213069100c2c0c008a402045245454890301003503c0c11900403110044902003541c0c140c03200341c1c803140802007030140300040220b0740010b81c60140c200b45940d00000c103c442212a40c04000802c45403110b404510400c0c101142c0c0d2410008100500c0d2081c10003090350680908840b21107640030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941045944 1250 941044694 941044703
    0x11030309070305010e0a02300d120f110a1d04090c060216030224070b1f0605130312120908072d021201020708031e06150d0b0a12 57
    0x65400c0080c002c0074045e070900351500102902c2880c0c42503000074105041280c5005800c0c0090a815039282401010035141c88000c40940d00d465000c080000c00744503036144a280030902c0e10280e001c03081a1803103403401e461003104007140f03466041c0030140d0b2481405140a03001070f048094075040f90311103006185100340b05100540030a42030800117802c00c47c140c0ca051401450a1908101681d6440b40c128400030003060105031002a00c20b55075194460b280340908409040305c04d218180e00f03c680c1c5100e4500312902c1101d003460721510212141d21452121183d803c02c1c941051000c5070000100d04503180701400c10f815900b0328940f406090760000d10040c1c86094000c944c05003400180d00144403192090501d0166501840040610000a03240068000e00e00400f441030000c00c25811100943d801504050b100d00e82040380c0050111071b142d004108240c0c020115942e820100000f90701c1805160790740303080c028124a94401030544440c1a03600c104450000240c5208074560044018000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941047194 1250 941045944 941045953
    0x3070815270426070204090206070203030307090509070c050307020915030a030c0c0b0316361517220c0b1803070b120a060b0c0303010e09060103030c0f020111030309 73
    0x5042038202c003000b48601c02c1c0103012400c0c050f800c207541c0c0707401c8450301c680c12180060142c400b07001068440c019690003d4252000000340101ca076000318207032048030421100700c03507680da41740000c50303031a00500d20090107980144440c10051409050559100c2c0142c00c0441552807041c001915220195906070080791441080c04180003c2181c03002c0500b4201101c14a103042c900c115000c0c0c4004103035001c04002c107854080f03400f02085802420b8251900542000e01c902c0c0000340050004248038100083c0c4100701d0303e4221318080d00c0190a00300007212140305a40c0e504d00340c00903442c003100800008502403260100095001c4001c140078150f40050746440c0d075090900400040310090100b4441da200b40e04c00c0102002e00c1c0110b502200700d010760854039403201410344020302030030341204903525004038400d01c10100c000041c5048809441250b10180c80e03c4100300d4075070f6000c1c04080c3c00268004443c801280d103030f00307288800c14410b140c5111b4208640e0403044c1103400942c0c2c44440c6130007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941048444 1250 941047194 941047201
    0xd0e0f1c030525080313030207170114150919060905161d1e010905040e030c1605030601090e0a02030106030c14031c0c0302100906090c0b0307081527 66
    0x3c124100c0f0f4100c0f120765601c0a1144816150307010203000003015441e00200141d0510308252003030100c031000300088d100c0d101c0700b101100c100c14040d003103055989500600a00c0000d8980405400999025101800c0159a07403241c3c2e000c41c0207242404001049552103100000f0480750901c07401d442800340f200003503008908284004c01840160101c4965054142120f00c016961100f403071080c0241911007404400c0e0340d00c0107032104401540650b600078a4030404181e04403001c0001d010078160802614100d03207481210b4001031082d0b002d01034055118100511100040c1d920150301d412500f0702b1240a0400e1381d00090a480c01a0400c0b41c142d0458641040545558400c41429100440c090607010504490b208041880282c244040000203000c0b03206141c000d100140114419a038184400040d900f80711018026502d0b0480341c400c0d008400140304003d18041d00e01410095441c0c1c1c900c0d890f1011600d040428030400c980d07010340000000c440b181c009525402e9402401201e45084c1d29 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941049694 1250 941048444 941048467
    0x30806040c020a230a0b090105100b070f021912120e120a0f030c050d0f080705091c0215041212050405010c120207031401020306120d0e0f1c0305 64
    0x14925007001081d035100c40b900070000340142840c8401520b41c140b03060f000d103026208281c60680c00101c0603001c50800420312a24030b9040d0400c51190001c0e40803555a00d5950059512903c42d030711001c1c4c001c5081d0044000140380058810340b10703d501c2089404e0180d181d40d007100c41d05400420845140e6501103002c44401e400c03503007061095000303c0f20358200c1c0e001c90724180c0d140e503000c00300280401008a001010103015461081146030400211070f620800000c01800100c0034405610120354460001400785100d5021501010005041c90303000e04545c8181440e030801984040364002d180388580c1070390101040180004001e2010880035119490401e4000c503051406004108070080209000301e98200d90340c4014142d01c01c860a4880c1c0710f0b01030480c1081c0d40c541005155a81e1b286e9031249100054000e540181002c51b0400600c3c5034a4800341d68038166044540081081003403c03540e9032500e0140120a40f4014005400142e134141c800c03184804950411070100e81c011031240d1090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941050944 1250 941049694 941049701
    0x30d020309100b0406050604091d060c030a06080304030f1b081c03060f08060609070212040603061707080d0c020103020415032c03040e040501090507060504090c140a110f0a03080604 80
    0x2501134504002d0507042c40302003003480c8910b02031050002c3e16120150050006101003082c800c4001d0300340c94040c100319140c58010b600c10b5a40b0180c040c01c1010100b00c1190200c00ca07012a40e0020001540720819070b06d890940c80358503aa094085680040002c03400c800340a01c030199032104005080009459001500301c1d0140c0e040340319401c04100080c80750110000315103030041000c507030065040e038401800324500072409121860384100800c00160f882d8041d00010142c40705d85e20880307200e81c2400032080d902c0d00540701c2ca880b540e001c940100c480705d0154140080300d90043c9009440c15031a2850050905810050500000d41d18101038001460358940141040c0443c0c00f84d05601c9041101146d403406640646c4203e0804000403c0030032100750311181c2d00301c1c0d010041d1540c25540e088060103035001441046401401c22406140140c800c0329041000491401004e007005410a802c507030b0042050340202103440b40c002d400c1080d50041014a110910a60b01c50304146800820301054 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941052194 1250 941050944 941050961
    0x70c152403080f0f0d020f07120e0307030605070c0503041503050106020a1a1302041b030515031207060e0f06060f0607031704052404140a030818030d02030910 70
    0x3840c403520510000d820342040350005082e040e030742615a8480d103a078007407a204100c40c0080c07081c400110300d0000350a10018140d514095020038803243d80b802002e480c26a40b00b0702140d03241d045081c2c140000340c201e5000d20742090062500107203030450703641c800349941c2c003982040c0c1c9021070407d400d6600d0750741405950701409061002c0d00c1e020a241e900c1281c2d074400120024200d041020008004403d41082200b0303150f0010800e02103001000d03e800c1d80704511010040010f03042900080b4100d02d501e9144000c010050700501903440700c0d1b01d141d259604080421120182c5480e0326007810300e403c010021207030161101401c0700e410285e08000c6070036000a04d5600401080c8129808280c119410028990390441071200e0b5031b94519160341400b0710400500f5030510034541083d41c80c1800f42d14188aa0711500980d24114090181d55a40e280400c40040c005644500007480c105e046008640355440c00b8400c032030a00201e1581042170740c000f1180395181782d01c052004601c60300780e0b0041d4581c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941053444 1250 941052194 941052251
    0x1203040b070c030c030503060f06071415010f03082811061303080a0506010c0501020a020312010803040806060d03021606050c10140705130504060f0512190b070c15 72
    0x4a42d4a0740e001c3e202c080c040101800344003000c00001c45c2c42d1100c1c00c0074141e9040090100c0da640d03145140c4a40c26180b143d80181880c03003101040d054800e000f1810070b0594441c14190700250349035541c0c2c84400c2c0d000c3c40505101d40f0041240c5520303007000044800400340c0907100d82d90003a040f062054034002e40100508912402c41c8090b0002c00d1b04044519041120a000031a00c0e960b0940161900304141c080140b4a610004241140e194003101030503074900950100340c100d9903500da2141e920f00443c062202c40b078000e100071520f80e1400207043c04070a486401a41d200402c14104181c100e616544800c02091001901c0052080f06000d15000c81c000c440c020425a000c0498210351114001c05003024002d0001c5c1c00ca4032400c1e1380650000500c002401401116281d043d003c00410183c803513140103000944102c41c070004041410f140e0800e185c0300c03040580c44243c42c1c8003036900000d0032000500c4407158000c0c011804c0000c0c00702c000b0541c0754000c1012620380380420000040d4416204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941054694 1250 941053444 941053457
    0xa0807050319080606030a0c020c0a03050706030f02040503033f0f060306160e011215031707050a020d2d140f030f030901020f1305040f050c0d1d1203040b07 69
    0x202c51703981c842525005030300144005044900504142e18110200c00c200d0341c0303c414040008100b00340000d40009980790b550b0140288071560305a0300907406180a40c1d03038150818880303401507004428910741842c198209885107540b0003066540c0140001c00c0c0d040902c0c1d0031008010740d0303500c2c810800c2d4100c01c058000300300030300e04850881012f0500000000400035010360600c0941c4c8247c10b0a510943c20b400104490301081d01e4880b1020500c1c48116022207102184030034250152003610261178120700074142502c0c0990805c414000e003000d040f641c0700b4882617070240320000200840030200001e0819415080d59040c4900381c80b5140442105550004001040e14007001c401e035005c0010142009841e03031201001180603003c2d00f41c6130460b412002c2142c000c420a40b01100e4101c0e2026641040140c2d4000c01d10300a5030000c4428008070a010030666039154407552003110301400c000403416408d00c8180000d410540b41c0145d48455450100501040c403540c603c485400c6002810240d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941055944 1250 941054694 941054701
    0xb03011d28050c21150f070f090b09030703080309030702090a02090102031c0603050f03030f0a0b0d020f010908010222090b01140304060603080703030e0f0604230a080705031908 78
    0x29a5800c0180b041d90300030035001e8082e030b9046101d0150b44c0000c40c0782406580f0140c02c8010300c1c0e49071060454a88032944550004601020b014030145140440b5680e1400314041c00d06e01076a1042e80b1140010390948106500000810391100142d07008002510107103582d0300c01c030f00401c00001c80107400d285005104000038040380c3e07000011500802c007401d01c0604008a40300111000700030b02da20281450094082d0462013060110007140300710b003060010b5030076403500f902401c1140c04000f0420b13004505100b02e080540b620740da504280000514014440c543c5484d11721342641c2000d0001c2188002c101401c1c10320500111100010342106081001461800c3c00003c0c501030306190109a41c00000020505004560f00007402279504008016901d08c1c00f440e00500402c81d800055103540600c0c10f94100c014008a0b2842c01141c0010000c050608240003100c8440402140c0d18490303c1a40301540000d400c5802900c1c140c0d02510165031901144101d65042217001d07160041000409400c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941057194 1250 941055944 941055953
    0x1202011d030a12060302100306080d0807091428061407051209060706090503090a09140c0a030b1306080c01180b180d0c0512070506030103060b03011d28 67
    0x5840b0040494a04181596055011000102040c1c1c00c080e42010200b00243c04031501a0041d800700c1d12000122400640d8009040746c8040c03081c1c076014005014020300b0049220241c60300155881c0c000c0002c6002c19003c00f000d80c550010307151841c001c000380b41d4100943c68104032002d8a9480318103551745411420b541c1c8039181c44544107160014075000c1100f003103903242e28080d98544c0794404401c0200d02d1003424210f64070b4010103040da211700c1c0200c1c00842c0383c10850054120b8a49100c03130760041c3c1c2c0c44280307521078a6000b9100c0b103420950745d1a0600e040e55a0100460f280c6a00e03403800040c1e041c103104041d810105081e0880303041c000800c00908200b200c02580c01d0131034113000a41903c0d0180103030101e19400002201c15880302e1103a402c00103000d454100c02d4211001122040b622441407002e841d00c0700b10701c0c4503c81e4400010b200400c003203205d58012104170f84000380000360411058100b5060b04040031090319090344a440c2140d41000b4080840d10745803034200494406002d1980d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941058444 1250 941057194 941057197
    0x10f09110421050607082a030a0926071b06080412030204090519060801050105030c090603071212021006051003020a02010f1b0306050f0109060f090e041202011d03 72
    0x140030201c98070503062102d1403210000b0610082c0d408001e03182d0b2030620100c01000c0038015106e07250414500da41c400c061280c1407181e5000c00040344143d41c19a43e414060000070b2410180a481550003030302a84c100c0b0000045070b2142c504421121916955542070500d4403c54219040404840009052001e1500014240d5000d40d100505407002d03001000110041e000c5c95000100d81d509090a102640080c1d05d00b03503140c0c0004020400c1442e584040e0b83c0d081c3c44003840391a4054002c55070742c8445043c0003500c00c0c0c1c8000c0103030403141d10303070342d01c20300018002c0000a05940c1400c404016440c0c25505002c050001c0c01c1d4000c00780811801c000000314540000d06a0f039051550015031092601d0007904410010103507190100b00c100c0e0314031422050300e40b0015210001900d4210003040c1c9213001076491100d0b50069540c030380d1950421b2800d940750341d60008482c086c0410254000b894540c00f81c1402d120718459008804070340725406020307007515100000a0581d00d090301d400d40710501b0000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941059694 1250 941058444 941058449
    0xa0209040b040507031b03030f170703020f07050a08070b0708040c090c1701060905100c0b0105040b120607051e070b150f1e091b090405042405010f091104 68
    0x520302199490b6490028a89407856000030075244000088900c82d442000d54001102c1c040d0300e48441b25460500102c07803540c11015054030030700f0103201081c001c91180d40a465010b0a014030f06240509a460f60342c60700c211180c0441c0c903c03c0008440081182c511803154020404c0c4c100540f9034102655000c503110818064150500d5403030380d501c03c406202c0c280715420288441194185543c440c2801841500580a0715000300c2d03c0340c0034048070728812a07071070a000e45c000504094a908010030000a4610a07500c19404424054407a810a0082c45141d005080a0310344e2940c40001800e191480912100c0300300c2d80840c180860030101d41c1c88a851640082c804440c0c1011045150004140840c07420a07990440300541d04584c903040300c401e01c0500c6c820100c8051115035a041c40b611800070944c52407115504040c005500c0d142056000f03a03400034481c5001000c10003949441e188080d403102000035a441e1250010007040310b5080301c40000d0302081c0014042201040810740d2240315a1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941060944 1250 941059694 941059703
    0x1513141f0806040216030c050601170a080c010b03030f180427020301061a04030b060306040c060503070219060f05010911090d05030d0608150123010c140d0c060e0a020904 75
    0x14000502c82d60b03c60f81118800c401c0106a884240d046060003051030b100d128007100e01d07216100021034010742c1290154041408140200329a034003966481041f90401c8500112645d205e030742100060741c2c1800602802443c00c102c4030b0710b501700400203190b00d81254040500540c600041c42c0322121b80d40480000c0c1e00001c001c4150300350341a01c0420300503d0310358007101100482c1525200d411415100070800c0780c0c0907284a85007074840004040d21103109941c01009000010f8040007810b0065002e0750380a041030042c2e842c0188000104450900d00ca601104d40c0c542c0c40ca5035038130076089803103100d001d819101810400755062200301d60252261040b0548510300d40f488442c200300e420000c46050202e5004140505030f920b05059a03500390102c0c0d051400100f0000100d143c200030040710625542100328030f211220a06d0064908100702c40054803941041c00070505004410070400440d01182d0b40d40c510700d81102d06000c01240c0c007640700494140c1050350b010016903510020f981d00543c11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941062194 1250 941060944 941060957
    0x7030323131b06020a02040e01141810020301061e08010501050d020f04050612010623030103060c1211180603090a171902062e060e1513141f 62
    0x16800c0071602c484402c0182c03408106600804280140d0114104069074425a001d0250030b92442c40d0501f80c800280280075122400c0c40091004070101c81c106003840d14a1301078481140012011000780d13402604001c02194100c01c1d5401c4030b0300c480442c2c18400c2564600349407194141300008259108580100c2303441ca40104d10141454490000c440050000800c226984c1c2002d07921045121070900c56040842d100840d4500e101c02c0461114040300000006649103a003956142c3c0300070301c000c09284e420880c20124030702c0c44040342c0c0b04400b01d900200c2107058440102c070050100542c07120030744502519040c400c0c4410904001410720704a42d00c01d24001551481c0300725202c0502400c5014014507108001070342c50035802103606405034181c1c0d02140c200d408846a824044a141640c2030004c104136481000b4140c0302c1d400c515244400103000302c40d6a0f10840d00500f054010540d0b80c6807078900d199081000307941d09680c42e110100c0c1620082580740d501d400c9900782000b03c400d01c1c01403101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941063444 1250 941062194 941062231
    0xf060913212c0f0609041d010c091503090c120606031202010c121128020705010c020d020d02011206030602030f10080601030611040e090d020115140609030703061107030323 76
    0x407451300355480c403900a0300400500204100201c060401c03c4140c0580b5440d0984202c6094451001d04041d01c0b03023000000030100c44207904038024038070840d0580e101d811200000c500204c2d0440f05016440c002c110100b0454110300700781d00a01515060305055a01d405600c03c240e40d0029801000d103603a081000401c4e207080105c0d000207100b503c0f1681c0300d42d000300f11203421a81034009145000c0d40c0e2a400c98000d15101c000545010070650800781d4010342640c00b03080140390522404200a106240c80590800511b49003815a01a0f070800c40e031180e004010490186680c0040b5580059450070581e005860070658a0310380c5c5041c00041c102c80c0d21004500c4070002d0950803240100540c0c03c040c1c9407890711500d090b0f00c4e0303020380701080c1c019420282800071110010205009494410428148441c1c041013004141d40c41540303581c0c1c142c01002400404602c0c10302c00e000501021882c11507480c0784c90300d4001c04403143c8070700082812104201040305090003030102544103d040c031300005c0c00e20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941064694 1250 941063444 941063449
    0x1b031009060e01020705030a1103090d1401060305064017190503040302150103051902011206031a090d1b03230d0f02030f060913212c0f 60
    0x118142d5907000060900402100000801c4881e409075150400000312040507500c9200741c03031225a02c00d4500e00c504000c2003d90040d0b00c00518944d000064480d501e940350f03800c04104079414818030000d4228200c0c045280c4401c04400d52004510303000d08030310405150394500140b44054200ca04a503401712005602c0c1046510386624005a8809440e00c0440200242d000300d80450060007010030901640a104900c14180d980c828064568100c01042c801038900390020141c0c10042645480d2001d450503100780006540103094822149656207103080e003480d40030788035035070a90040300c41041403544020b00d00c10b224205400c56540034000e0030100c031084001509900708600581c0c4604100f20114018003040124034401d00c218141c05400074200d00044458100b41201c2d8000281a441c100c3c0301268000100040740201c143c483e158194800c60f18411072400d80144012540c8480d0049840f806981e07030055202d10148448204035203004141640901482e1400c0c0449242e5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941065944 1250 941064694 941064701
    0x3040506040b0402151204150203040507050405060103060e0a06080d180909030903050322060f020a02091e090102040303032a0f120e010f0c0903030f210c0e031b03100906 75
    0x244004c1084d9a140c00340ca1b24001000c0b10b0546e422580000002c2540890042d0350007981d00c41c03138008001d08904ea26000900c4060500100070f64101651104041480075000807000c1c054180407000091003410028002c0c50901150030300d500384641c07030750028440c1c0d90074030012094840d071000200e00d070041031505030749828039908010f245000103c1c4604091800c440c1e003040e115541611a200c1c90b95610044c0d40c241181c48003040140c101005406c0507050000e22290408007948000b04010584100d10003452010740e042102030350002000c10038564180580b405812020f0405074403800505490051801044a100203201403003450041c0c250007040d50381d031186580301c0280b0082a4031100c29009000b52030540f496580340040707490700544107008040c182c3c0d9046e11080205245c107401501c0e050005c03103070184035411a214080340c080450146540300e160341d071982c80468501504250410b00f0044804003040441207403041c10746e0b400034000781000d101100014070307440347c2d04100700503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941067194 1250 941065944 941065969
    0x1c0c0c1e1e0302060703030e06010608011518090c021c090b09041a0603070f081003080405120319030c08060d110d06020705070e040b0a0b010c031413031407080303040506040b0402 79
    0x2200800c5c00e40130705816070419422840c060080c0e445507078031100140c3c2c500b0300a000304e41611840680c0c1c80c20341405090480042020b442d40703014403956900300f01007a1380841c00f1120060f00a0804025509000705150b00c0c3d441d2103090561446060140c9054980106141d66120b80e46444000d11a052505015400302c00c1c081d0505a4a00c0d15180145c030b000a010a0280061500f0001910340d03002900d9500a80c2d6214001900d003d282204002015005101100190000300302501c80c0100c1e04100c2100c84030b1640740031030780661001300030f400c0e040010400d6000343d440800050000f0600d40744c46804460850300c0d54a11002806c00100074019004020124407400802141a841410b98184601d200c0e1510445d680d0302d883d00b6800b40c9649890880c00b0401c0006d40c140000d014503006c0c2d165407160182c1d030b1b0407c07105540c081860070240d07100b03803031500000c801c205000d101808094090043c2900862135400e091340c8542d0345200060015046420305000308045607908803050b80c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941068444 1250 941067194 941067199
    0x12051e04030c230c03010506060403060510150314150a06120e0601030c0305120a2102070501050a0605030708030901050f09120312090714030c121c0c0c1e1e0302 71
    0x2c3e10594000d81c1c8071242075442c0c0204191042c100d455402d03280c14010175100b10406001142442c1c0741d561150080d00028002c00b0b80da400d07405011030032440710b0301103240245455030302061540c0c9408a0301d0320080041d01412a40074201c105010580b10301c1a040b044a60a107007100c0744c08100d103c0382d00100100d01305000940603c038000014000c1c4030201d0030569005209036203042d6030304a5041042d2084092050100301c036003540c0054240b62849007109041c2072a0058074040940d07585e9030845404540c20318005503a00070034003050908001200240902900552502e40400000f070f10f07a0151080c07007060a030001030410100e8946904810b04003006c80122600c60102400541c078109088807a1030340c030711505500050b5414041005c8103214805006088002c44010a1007a02414000040182d22503071803004a424090003c0c107035400025543c0860381d400a103800104d505195010381c5602c4944540c180e0015082c081e02c80c11200005420348010410404c0015810840da20296 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941069694 1250 941068444 941068463
    0x1212021609050a0c05030108120702030a0c060c12111209040f061517070909050403090503160608010b0f16030221090f03120324060f0a12051e04030c 66
    0x12441d003950400d80c002c488200d4203002c00c0040d034030202d601c0d01007482403104d02c0d880724200808141135400148406030014003501d004003c2900e070400744030540d91215002031042040f80051214000806195241a2400c4055500303400405556484035011079894800c00096542d03596585900020002890010a01900d41d4130401b0101c1410031490400104d030003950307828161602c000c507880c0300340183e80b80d00801c10704005944008140007030084040c0b100914002c58103645c100b01c034841c8070b204811010381d0581041c41c0141000c0701a03100041d442c8003404844040304481d0309580350700d4050b184005030340245043c12807621000c070880d001c201c8405160801849004402855102c10035a50303000b0b007d91034018103540e913003152000d00640d001030001c41e22030000c1c00b01c0802407041c00900e541e0812010000030b21250310054020242040002c0c40003900c43d00400040d20b90174400b08108a1032510b2701d6040d40040c80116041220088440006d0405000f406402140d039007101502 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941070944 1250 941069694 941069699
    0x50a0606120603150b060c07030b150909070e100f2606060307030602030c040b0c030702030c011e03050a06180b01020f2b050403120519050412120216 66
    0x100814440c01500001092060030884109103409104220781d405030300c103075880004080b131100500001038665884402003013201d200703080402a01024601606822845082042c1108407e0020391030850045400e03100304144054041405802c44e5408448000a0366a40c1d00301242c054031900418544e60a07480c0100c1d0b0300d0020130145c1c141140a8400d0303400303440a00801a5218400c4806a91540c0000020301c005801d68001c0d541161000042c5400d19031542d441a00c03581210041d45003552000c603008095183c1080301c0c2704222820309111150240b140080704030b4828a008120074103441d40080382c20094107034407038001026100100020161510407003400791040905403401032059041001c900f107000300d000041000041c181d03400c034501c8600c2192040040000e4007090000c00d1000101007605501a000c109049954441c5d4421440d1a4614024000c20820040100038801841600b0541c0005482d8981108072440c40c0ca0034a44120700c0d2110f4070002c440d0108860500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941072194 1250 941070944 941070961
    0x3051c03050a0e07150216060305090c0603090318040b22050606030910090318030510140112110402070c1d0703111b07180f0509010c090515090d1110080609240405 72
    0xa00a076100000c1e80c4d100ce59500400205020558006605801c10000e0703036018011007194900440c0040c101040100c9074100048560125807011800103a00c0141c4020382801445166403140d421031300c2a007903003003149805641c2e200341149001d0040c0e440c40c00c0030506006005000c0d03540702e0446c031907100e10307224600b45480e142e041c0c0d00c80d40850700303240ba07000c002e100d1783d1308250513607611103050f540b01c4105440d6240c0003400c2e5076000d030f00268200200c802084041c81c424001c3c00e00034181c1030070044a86010045100000c10840800d0710301944101d0b214680c00c111134184080390301c902e92414000301c507541800c41a5114088003100b07040614050303a940e81120341c0700b41501c281007200741e0714003140c0360a940e234004003200007036841d140a0200307141100d07840d00c0320130740140160309020301280032460b0800e89010a81e00350427a411041071515182c10880c003e01400d00d404034017410020045040881c0c0a880500c005134400c28266040b01d011154003d543c60061044c005420102031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941073444 1250 941072194 941072201
    0x15040221030a0504091404030e0607080c03030a15060801060c11040e010518010c0912170408071811070b012108070c330f0903051c03050a0e071502160603 68
    0x900480e20f0505000c2c2c6c8022600c0000d252040e03400d41c0f600f182d18441707101000300f980d0010000310b404d22010b01c103500c6007600030000346125544800b80010050603c0d00c40030420340c56a40800b080290940052220ba84c0c042074250520394450119485507103c2030000780980038018510f1640d610345003c0190402850030b105038100d03d010020004151500c0341181c0d00005406520603c486510511001410303050912803441d1034080c0130744c1856100c3e032000e07040c10556801900c4030107000c0d40441d900300e00c9100341400078282c6102a86420a1946c07041c803400c034144510100f15030050541c00c90426801c600c138103800c0d071142240d070342d030380180c60300d204c903c000c5028504140c22080c01310441128031070110b01c4a01c000e80c1d841151940c0c00e810480c2c550001802d01010030420190000008a040100a020342070f2070007558029a19a00000c4c04c403000240b966409508100311000c0e07800010403450155080a42011276000400c8030030383c038007811403114882d266074442000032210707810350 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941074694 1250 941073444 941073449
    0x609101215061403070c05060c09042a121e02190f05070816120804061b1d1513080609010c1e110616080915040221030a0504 55
    0x44100141c00e0044071070412010301d07005000c003041c0d155000010340312045000c2c5512031124034117003a4002e00342d82c9503410004140c40d800c07224000420300312000c0c41d050143e43c03030100460306001c00000c080030301881180015070700407040c840e24208030862021180c00081c032000403082440c030101144403e04c2c00030360122104c11400002c8080c1d0946040c440e09240111000550382c9a08100540e1078070406540034843c280905030000f026080043d0024030885440000707500c4001d4036117000e007401b5040d5200e0840400240c18403c00312080c160700315002004290034004004d00580400000c966030816800d4400b0b04103030041447e241064280400c1429070b008402510700382d41750b0302c1c083c901765039070b40b1044004100c2d0401000300100e070302d41418034410043d00e0003e5032000d00c03520036410010305907001014040c6124058400c0e94002100e075800142860041011803200742c507078007603c4801b40c0004d104005d5200c4c2c80f160903042208121107115514140c0b641c40e8041480902154001e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941075944 1250 941074694 941074727
    0x4080d030b0f10050d020705072c070912150509030a0923040f0b040f02090a060e1011070f14090c070b0406050901240f050910050f060910 61
    0x52526001800c041c055081e400394050491a8585000c10058540c1d1700030040303414040c0c0d8240304903070102d50100038203030081c043d00c100403540700a200b00305044a9983c904624465244000740030485034000043c40c100d41d01141c540d81c0c0c280b1b46180064044a00202c210350840c14103041c0701c145100800103040c03202c201e0710f0b01c0383d01e00d03650110b188040311982c00c243c175420a42241d91640b07081070380259010302000b070400905850040c002030200e8042001d554581c65010a010107103080c5182c4a401030601402c0451211220100003051a2500f402c02002c0050134209122502402c108000145c0740e010028410192a10314942200c130707441c400103100f2240d6001140b19070340203108650711a034029441801d50b644a880b8a03000e410041c1c0150344540d40d8060080c2c030402d138103c12642d0007881880e40801545410f00702000441c3e503030083e038030454845042c001c4440e15107191400b2030f07409030399a00c072451003c80059001d014941409402a9400500c003c1080e4046200704080303a05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941077194 1250 941075944 941075951
    0x6030c080f0f0703031d09040b09010f02040825081c080109020406411903050709033806151e1e13030b0901020a0e01050703020106090204080d03 64
    0xc2000342d40d10388515000c94603810035501440403078400c124120103005240c484d401462030040200b00e01c160111000d40d8000d801c01c0600c80346803000c1c0100b01100700aa4019414141008400e50b101d030b401c3c0484035901815401144001085288c25800502e0204162030036001d0900c200307034044a8200300728001134031000012450004510070b5034191840c0350317a0078030303e20481288010700244060b41c110403245d4084000364480d100c0d500712280311103019026500d0302c40d40ca0134480f0144407410000f042c18144000c00401c15440083c10f4106c941080820034130483c4000c1d80c034080754852180300c61802c914500c8001181c80b54a88074083c0d4010f40e02801022100707c4a56110b0003481100035042120084841001c22003102410801d6608178440200d84c02c15501030700160b00982c1d0ba08035442e4845e4080041c04907140f01e20b5804080e40300203525050070746200a2001c2905031409040c840d000c200c01d004c2c0742c400d5221001814400c01c0840d40d80f5140c04080d42ea811403032440100103800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941078444 1250 941077194 941077213
    0x51c1a280608390307030209191202060a030209040903030209011b3507030309020a1208250506150f0402041401051c0212040308090a050d0302160606030c08 69
    0x42103004510a10103243e180c1e5000200042210741da5001074401500840d0421003c25803603080c5000350300a81094800503a00e15a0400384201c410390303100c04040055007000c081156820104800c260a0b504507482ca95817002031006034024051140c0590b04240303000300c41c0041640550081000003000d803510009041c0307288400e050b070550014000c1c906017031010040c843e085e021401d101362641c60854640d10980051204d040e540000f0020780001c2c5c3c660074080154205038040b1805060324988a0640d4203160304c50740c3d6030384070f10b1040d500307125043c0c8104035100910026040700785601005454490a002030300c229076031200a05507201d09020500703c0d5261405100f25021034000d1107440000140080054459800016030400c48241010820307900541074401043e42e07080102e0b0400d414107041c20002c240d894000c10500b1190311050280c40410400101702685400c60714000d41e0300c3c0100d044c80705011800d04002030006080c40004010400d03048500d409030340382c071000c9440014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941079694 1250 941078444 941078447
    0xc030512270321060301060302030a0b010303180308180a090f0e0609030a090302040b01021507030c02060a0b090406090602090307060509040c0f080103030c030c140616051c1a2806 79
    0x10034410141c0305031411200c100c0c4000061443c0c580c1c8408004c00008025940340c020a0070040703804412102401007400610406030000301d0030742082d110b140e0000515065503540805842940f8240d02c0c80024070180b401d0603542c0d0f5a0700c40280080742424003580703140c0d4500401a00500104508601881001a080190002c00e880f1008401d84c0c82c41440c40c03964003484014500140c045046004119200c3d524551510045009403480d50700001c004041e110700906109001e4425500b06013050103003005a170390310a03c2d40d00260007a00004c4c0f0140340d460182d0003031050040d0182c1501503000009481504007005c0c00014000792014007a030f0b48504030854141d04801405030100300703030700700500c080f038403410645220034800c5c14980261b6440d40c4418a20900004011015900940c10031030245c00f24103840c28600182d00380b00e800c02c10f0308640c4068032003282103440c121507984d030480414030b0000210a03034000c03009007518910091210400a19070704601d007604041e0a01c20000038850b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941080944 1250 941079694 941079697
    0x140d2901020106140f060c0a0f0309030302060624090415090209180402211504060605130507052502060c061012151a0306330307060c0305122703 64
    0x10100107111705a124814010000720743c00a04041c1e1281c450030100c040002c0104c42241c8545009440780f5030441d196160091500800501c180c2c05a8000c00034006a010020004640c04803006401902d417481c60f000302d0300400039080d4005454480c40301c0040c800302c0c01d07801000a00303810b55080c66000c1c170181540fa040d940c2520000c0d002056a20a0840070806410b6061401d52640551f141c520100505130f42082d01a10180c8510790781d208104840e18140c442910000c010160034131142c6410400641240207a0203100d10f0004600c40003c80d81040100710501c18ad07001742902d0b1506845501c41c1d90341e640c211210300404030101000308100380b601c99115940d0364485503003000301e15110400400352a615206c04556503140e80c025456175001e01400303214503a1412040d02c0f80495000c464803458517581000c8503000c8028002010f903c0210b80030301a43c9080c03d19107508441843d00303d80ca0f02c1108400401e080c000014002585002218800103e0700341d08903d24101801c030b21a6143d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941082194 1250 941080944 941080979
    0x7060e0d080a0624050913091a010501030e0a0b150a0308090a081b27090d1e170702030418060f0f1503150f0603090203011b140d2901020106 62
    0x10050241300b400b0801d4854002403205141c0a00103105c030702c8001403a1015994107040440341822a035510340b41050150701c441d40182002d190901001804424440c1c8414410501400680346d90000481c602e11100c0c0f41030040740b0251000c078590b5030b2410101707101c4d000503104900c608002440050748850000e140c00d00e514583c4100c01d900c1040c041041107841c0f911007da0010812400190782c1c1d01d244201c11881110703420040d00300d82c5001eaa000b044000600b0003000010304c80c00c000c40310140e020030455150241048071803240e8481341006da1640c02690300c8245012504044020140d01c6500490102c61203941018070091b115481d0140055442c0134682c5d0141503011400160703807094101d03902d58104080c14200203500d5840c00c03003212400c1d810200c0400d459007521002c41c1400d200b4081c0303442034000c822000c0004400d00030482e000c901c2c01c8640410020418007039211260307101d11104c50a581808040c84400010004041003080b1240c0c090f5103013000004200c081e50030b09868 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941083444 1250 941082194 941082239
    0xe1e0f0a0501170a1503080d0b09012702073c110f040b060a021b0f06030103030c0501020c01090c0603050a05090319140304030302041503110f07060e0d080a06 70
    0x3045440183c0b0401d0030000074800c00109890b00707116000e00d42c640030350001071400b6017400c030b5560640c50014001d8403440c8050038003a002900040103420100d89600b440310302c0c7c8a0340c0504a03900041820701a001d072420260104940b60003101200001c106100b0480103001c40c10301030300c461030072400d01100003a0405410504a0307000d05001d4a0602041404d50400070400641039030000c0105000341c010b1600d07000541d0180603807804400100031b40c05468101220a10407501d07140300801c0940c04184002400e00140c3c2c00318a080203001e4055600252a5038001c00241b40e1901701f507a8824024480e80011918003030124407006258090984514040e2004500e00152401e80c00b43d03100e103030004141003086403c0502d1510141e18000c40c040ca009a80141c2c5a5043c48a1026003001c0320b9062010316281007210f2885035105c0c02941c5207110300000c1e40340c45018a06100c0d000c0c100715210b40d121409410449a8090307040005c0500a507a00d0100b040b06a40f80c0803100c183d16140e02d0a0708 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941084694 1250 941083444 941083457
    0xc070312020a120b1908100609061802090a0b1216080403020604080313060e01022104050d050d0e01020307080f070c03090b0d1b0302070605070c0305090f010e1e0f0a0501 75
    0x40a250f00380d000014001c4001d4032001e100da000e60030400b03020240f41c00154660300012014440e407a81c80c0900e8000c0d00b2240340c2080098174000000010607088010a02c40e25004100326000d541c0d4845124028080c0d0346103255960000c4d00c2c0c03c040c0b0001101d00803200340242c4d4801d62240d2150316864410b0b585500140865103960319045482d030001020455850028154100094000e01480c2e00350740a510001d030316a00303808210215910200030034802e8040640811021510000380c080e44820a070030170719520b2403c40300c1d40000d070115101542441d070000040c058442d500c8070140c1c0c0318200380303d441145ca4071005011a52610320304d0000c0c00160f10000180415074103c0000c000f045500200003c07450a40700748200400841441c040200e076021a0394424004203004032a80308e10280380119230642d095401800724001c00d90380b01d01840603480545401e034095951002c0c01c0358000c0c192842c3c2101c0d80d8111030b1108140b07146501550092010405504181d0051425520140c4400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941085944 1250 941084694 941084717
    0x260601060305091e0c03160e090f0706030209010201020f03150414100306020306030f06040c06020f07050a0b09040e01060b07050708030901050a080406060308130305011d0d030c12050c070312020a 86
    0x804040402103a214158080c3c2a15240507a030b04201c1c84034111f00c038039111141203141551080c501c560080290b00c894009800796500c00d840813803210142d80d024100107898a071250300403402405003003c0701441c035200006200c00800b600ea200b1107900e0007110140301c0601d003591401090481a550b59a148151200a0002540c1c0d5000f440d401100502120310b910710f0828414079010090700c00356280403024505122055040c08052079503120300c1c0007000c80a1900010541d81c401502c901c00300c0305c0c8040b0f0350007000c0c0d40719003010035117400d121b00a0020949680e40700c2c5560744403120031100d0b441080d00001c1c03241008400d032140900140c69580c1050303d1010191016a030091013251500c2e43c804010000621010242040c140310f507091907215401c42c5002401c6892150002500c1d00340003c5595080d60000760558030b401451402184000b4240c41c1507960011140b07132880305900300402c004203042018040c0c00024083d0b80c0d82c100150000030b0300c4041b1700c0b13002400070010300c004480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941087194 1250 941085944 941085973
    0x50a1e020a03090f0c050111010204050307050d061b0e2e0c230a06061223011d01020d0605090f04020d170a020706113426060106030509 60
    0x5011440708508010a940040d07039540c1c081000440400c861a0b55041000e020700d503403090040349241c2e40d05000314038140c10400001d036140358910500380305102c0f4401810400601c0e42140b84a0360b1a44c81000b2509181a0049e005007109120700e07000b5200d910207091040d0304803541000c0703660a400c11002d01d640802088a900d010f00f07100340d5001420f90140040c00031142c440c40180d96221018048148192400c10140c4526a1044403582d080c8100440400d140c000c9802003c40c6500300c0780104000180d2590140031156108038010b0000340b40043c165406400030708105a0840040018544039020020020401c0c1c074202c043d00d4025000030010b0a1842c240c09a05024007510f081252281c50f070b4500e250b01c180308043c010b0f08100c4081042d20f400030b41c8117031502820809800044400e41d000c05950314a142424104038100d0b000119211298052102400030804410620b00161550203043d90721110280d500d07114110000039124828484d40b07000d6100fa070064031000220f041d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941088444 1250 941087194 941087197
    0x320304181107200108060f0108180c100503060a09060e010b0d060e070e1002010515010305100308040305250605070b150a0f06021c0503131e0312050a1e02 68
    0x2501c1076100030032031140402c141d43c1e40300010a840c4206036440d0039441c80010b00e500e1014100c140245c814a11000d81683c0104540c0d901185480d03c589030302900c041d546180c00c3c01d1240081d00700e183c04001040c4c2f0760b4004001c42c814034050320028105566407c451044441e2441002200041e2400600c41c04940b0002000441c1481d40081000b41d09c450408601c480252103c101080107800d01008505048100d654010001d000070081441c00c40e4184400c07800c81c2c01500d04065a44c000608429180d41e030a00186410210190701c4544a260a540d0740a41401210000c0d02d00c203a01080c4036021040c07903054402d180d482c1803c015159844175840f20000d00441240c21308104c1c0400181c0f2503c8180006017414100c400400c4d02d0413102030f040091000c0c2004c00b2110400c601d1802d550020100c0303400520b200c2e80284440600e09101c00003001784143c202004041c071b1002014581c0c2f10624000300614035004100340d407151014401145c48008254548141812403110441c80a60 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941089694 1250 941088444 941088461
    0xe060f072f0931021f02100b030a05030403030c032a081c090809011124060117070503040605180a0b07031518180b0a020d0932030418 59
    0x3c1c0e502d42e045036075180c5604064401207010b001c5100c00c840c60300542c034010501e03036803a4001c80300d034031900c0050090094441a003803608501c142d45903180c60030380391420000600150b40002c01d0703940b65512840d0041281c40801015000204003041e03410030150540007200ca20300814403080c070500920380c0c51140790b0f00035800303500315141c1101a0007a02169030044c01c0f051403140300301030780d103410190003d0001e09001200f00c0c0e485c0d01c004035180503602004c184045803915045900c81554940300100c80a50848a0006101e1442410300807100d40000155005500c071300c0c0140f286580e031071b8074000e580c40c441450341000c0c1d2107100c030400070486d0011415040f41311403034040b074800d04102402282c560700354000c0710301d165100c1401c0b02700f000354800c0c400344a2800c001c100b19804a034075200a4002d0162100000c1d550009185200846641c48400707030b10350100d40128408200b8007441100101580a51240740c0c1038100800d17591f40c044215000e8518580020350b0740c0e40010312200c010102d51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941090944 1250 941089694 941089711
    0x1508060a030203011802030d0203090901030620040306020702130e0c1009120f230a060c0306091802090603010507050d15030c18110f03070f0e060f072f09 68
    0x81011000d601d081c02045182ca80d17540306100e0404c010b205251a0081d8020b0150031900140403103459540c8083c04c80f41103a820880100c0c49001c4c3c901500b1244100184285821a000400004100243d0081c0c011b06008448040c03030700c0f01d41c08a0030b003a642a989270869907004202261014501006161002002d601c1c080f40201c0d182c9158040803050402c007038a01c040702c0150302c010001134489402c0c9003045811140b03004a82c40740c48a940e00b4550f14014900d0352541980c8064a209a010200806940b0f80500c002c401c840ca00703e00103980164203a009560540000e0720500301409000e0180702e5681d64245086001b01c0803c00800602500c4040c031561064008017180752101c0352806054111b800c501040e0410030381404032260040589409001032050010101d031600a907588041d40e420f10340d1816400d11021280340f003d1148050380a4070105100140040d400b002e0405184610464807a81360003141c1d6004a400300c101030a84030103603405510301c43c1001100726800c004031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941092194 1250 941090944 941090959
    0x3030e0415171204081f14060d08091e120610050d060207080f0c07060905090703051801060e0118061811120106030b1f1e0c0203070b031807150806 65
    0xc4005042c803c0d445548010001e41c0140c07402030070501e5400141b0054862400100160958984034040c8654010b0485114954401c2044180001203044608004000707105001245040043c0c103288401c503195a4000d424500040110301400100c50b40545411250030380b80320320308403c000e18036100c038400b100d00307580a104500024131510007070200041c48080b07054884480444951915032580e00c40410000780d10010021038480d0554680c200ea00d92501064603038941c6e00000510b802038009034441e610300440000e41030070040055050320b400700140400c0781c400381f81c0b12080d52141e00614551041038844c00300070b51170961202580a94030b140560400c0b51850510b0070000099000f20042034885500c102c80d482e02d4526140404104914482c1d240c81d0000c009000141042e010103c194642240d416158000e40d126101c070386c0c0c010b00310b07132040c1d881d2070000905800943e008412403243c400d05603091030300424000162001032280c40f03103c3c6495407045400310405001315401c1f035903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941093444 1250 941092194 941092213
    0x601081b090603040f11010801120f0c08063301052d0c010501031203091101080601140f0c0c011103121b070302061b030601090501081e1003030e041517 67
    0x40b81c102551055000d03480c050648017203030402403040181a00000c0c10007281600502c00d4121100c02e60808540143c494000855103180c00e184004460b0407029444c8214000c1145000c0c0580c00920348604020611000c020207104104011510320f4110740406d00c28008a02458410a2100800d010360b19020358103646183c4418503982c440e41030302c241c6075107c60050040c8412f10f5400803d15020385420040401a51a55201d000c0f075018281d040154010200d070144c2c0c4110124030052215010444d0344407419851020158080c68948450f8005c40402040960248a80149118001c0c020b145401e5080a00c1840070f0300c014240c805180501c1030559140f0341c081c015145281c8130b40c0040c5000e040c5402803803012020045c850f03442110400400200c0d9034070080c1a001c4610078204402d20f9107600e22801000c00c0d0544040341d180c030782d04003000814020780001300100c901a48070220400440c01c2800309540c0c1581da130350195510420204005405c10890902c1c020701c0c40241e900595 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941094694 1250 941093444 941093449
    0x150b0405011211032d0615030711031b0c15070b07180f030201170105030c040f09300504060509090c070b0f100830120f01030b09060601081b09 63
    0x800a4412104a00b041040c0020390b148000041500f031017044070307120091405100280e00c40c010400d081010003404804142035500880410101d01c8a690682c4c0d15840700200484001d19000e458802c0c2d40704a130000050380c00c01424038510064001d1501d482e0040341e40b03034141d4014002e4591300c100402900d210344110758441c0c1c441c0142180380701e6511058550b0000620220051962400c0c00b98040e0040006540000c6c01c080102000d89001c03d81c02884650341c3d008091100c405804e14103182d0a0464640c1c0c12081041074000e48640c5081c442811001201c41d400340d4000c51010800400400c102441d00c0c1300e60a40c8610404041840c200c0f05a48244108a080e43d40000000c001818072880307106001004000d17104090003031186c8103003e101400000b410340c0320701b0342c10000c0b606c4414500c40c1460032510303800301d5540070705103a05120b07110210600302444103448810b00080805e04c0050301044050040105940315841034450b0700e403130b1301009512013606147c0e80b07080080f00340e242c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941095944 1250 941094694 941094697
    0x103020a1701030302061918060506130e030d0509030720060d0f061701090b0613020403020d0f38060112060602030c100504051011040308030a0f150b0405011211 71
    0x2513100354017408050034480708501e885403002507940c262a0800c540901c551640c0d00390282032580088000c661070b140c0c10081080c40e0801032002c40b0850519009807818400000140015074095000f00402c3d520001815100e02070360b00b00401c5c0302d1218030703000c0d20021900f503c508015801001c4501e402c503600e00010403503c842c010040065102c0c0030410070f0515a20154420b40ca42000a10a44e9030b59a51165030324070040565105503894010412254250342c165005168040d009803003007980b6090406200102080444007800031300c1007240c100810b400355030411071108034000413110f0a43d031050030350070005010504215080e4180a625002030050310018100c5402a5940344803d01c40f081c182a40c81e1060070a02d81080c0a000000303000140c016003101c42807000003031610707024140402901c125400544002c4003c41804400780781980011100212900c040045050a00e260301c14001984107005803844148420401c035400b03a00603109000a411000840316034100120700103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941097194 1250 941095944 941095949
    0x30409022203330e06040311030a2007080f070f0501030209091305160f05090a06210501110706060e0f09070b18150a11060123030f070905060a1202030a020103020a1701 74
    0x13203038083c001380030902d80c1007440e21840d2480076000e54034040c40c40700081c00c002d104c10140c0c01a080d42c041100344900f13052100201802c80c80082d1070b04824072416899550106000d0250324030245400080c6541c024800c036028017002400d000001d54502c01e1600d0b0141000000ba02e290081c60150341c45006014000f2000d0311501d00c0c16a1070900f00014440080307001003d40410380d241c0702040c451010700550103040c0040c440810404d80d10030349809805071403a105103190050021602c5c1c410442150002c100369075039025240e40c80c4d62000001c81c5894016550000e06030041c00003803042c18102c100038801d0b1107001150720304002c0d030740300030400c0b024840d081407a200101040621341503078407840000c10302164800901c910b5061040e070b101034803d155800001c1c1501c10141080d01d84050102d001c1080000d000d4450803982e411030100a000210340c518032038007100c04080342c41c482e68807501101c950050000c00d42461640d00540c02503000340700020a201d80041d00d041004400300140d400b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941098444 1250 941097194 941097221
    0x611010e0d030e0c0d1b0504090503191206080105180c1509040605120609010b030d08150409300302040303090b160f03170714030a0f02090303040902220333 69
    0x2a0105c41012801c2006c007203402c200c2c0f0541c10042c0200c00718000000340e130a800e4240c0603203090841c7e4000c1c00e8a0203201d12012441482c100900051031007019030105202e820100985000c8a05222090351038034a1010b090364840d04500c0c1082600384c4802c080c00c000c4030040c00c009041919003000800c440449e141a911951010080201c620001c0c09907028550054008026a5044400140031181c1c0180fa031030480d2400318522002d80d0f56600002c05c4103402049844038444840b0907012129668100c11200515807101154518440d00c02c580c102d03a09692403800d034506001ca181803680c06280c00801180003c015040072501d04a09400d2203442510303002502c00030a00004c80c210070040c03640051100d0401c400015410342c808a0b81c0c458845d003400104809035000e540c00030b000b4044141e13018030000c0b8001ca40b42c115a802040349014203000910071002c40310040003090218000108400b0380b0420021484c1c41c1300c0c0210f0034001009000002c1c004840724104100c881d41100d440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941099694 1250 941098444 941098463
    0x1200303060301060605072f0d0b040b06060a050d0b0a24170f0c130f1203081005060a050705010f020a09030b060a080303220c0f0611010e0d030e0c0d 66
    0x70189024881c04004100f6400d0241c1842056251680e0000ca44a81c82040941c40808d0b035051400503050000c40010080c010481c51180f4105200d44207801c480445240c54404080b41c00750bd0440c040e0340c818580c0c0d50f01c8600d050550f02d402405480080e14003074024280130408a40d81e00889a40c001c11107514007180019281041e000703025030708100c00e29000d04545020321405410b4024007035809010a032555030713201104a408004c2d40f00c190b2000c1500c0a40c03200101e66500903861580d400c42c0250303208501505c603005a08981170303882c0309140e030090040040c0c40030b140c09000a006000d018100018245040409110581e4031103000b100009050401c14405c0000c0710481e160004001c2d030301e6149a50800380c1c125500c1c031018080c880751b03140c1001401c070440c0d210070340004500e6001410310141c658814100043c07800c18020784000c04c482081519545405208200f908041e02000b0080c42c050103105900038115251b440b440c5000c2c40c6c609000a40303800013410103285c410b050300d9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 941100944 1250 941099694 941099701
    0x6020c010b010909090c050d02120610060f020c030a230102120a060806162106090e0d142208190c050301020702061e161a0c0a0c03080601200303 64
    0x4085080380d030419001c01745001c101c03102140c0125011401c2d41d4081d00c0f10141d1489600000300381d50001d41001015110703d004100010030010b41c958210340440c0c556101c80d00c0c034000280c1e03c519070340311003c1e0541c1c04070b803542022481103c44450a115a0700d43d45007644d030301840180c01c0e40e002d400c044420f449504203100340c070909489060000c01c04100a070045e4107004608a50b640031a800d0001000001c8000003103100020280b03041c000c103907040401c80c4980d120f8180016009841c01d0000c680903a4940340c402c98003070004d01c0d00320301070481610b1500064034265000040c00194100c0080e400080100343c800342005424030720245040900035032501c43c9064071400c0321a03040306009034014890310300140c4070842075410208142401c1003222812070007851003405082c0d201035074040d4240b402414440348090a03001c0d04a003014958141d41d48114000740c40c45600c442070001501c8a0f80d680c0481c0c425000c0700d420050525048500c50711034003690650109407412140707980c0000090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 941102194 1250 941100944 941100947
    0x270112030801060c1115091201051e010305060c130509010608090106140307032907120e0703020d060b040e1015050307081c0c08040e0a2a0e01020a06020c010b01 71
    0x740d00400701864283c1e6010201d6480748071303002c808442d660140da02c24000c005501280d5055070000c0310050960102c0502041046019100c203071505034009452840c3c0c0e20b080d0802040032130680390804001c0005455994505100d9405a0020f041c2d103072010001240d5540e403004843d0080400c0c0c1d8400000303007001081d07031b401c4034440c1e403200c0310082c800421003505c2c0c3c40c0410726030116900400001c0c00c04c0070749118540d480e0080300d089a5520f1000c030400c412160803803544074008848000c208103000303221090960b28000c070300019500c11901580c0100040f016040100c22441c040c1c004a52000b80f60340840c981101c503805107201c15140e04601303661340420f007400b1004101c128000d0101034509420251102103070060440d0700010200b800142d02e00400c18000619444902e16545991340c007891880e0b1542500c500884600300519680300e1004c0081010000e0381100703603d000300085000698404503405681c505501030710403104040f0754644042d00102d00c007800041a0040901e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 941103444 1250 941102194 941102207
    0xa2a180b01080603010c1d0102033702190213090b09010218030a080a180f0f031e031d0f031209010e060c070e0c190f08070311030627011203 62
    0x40d50080e03242c000006030705a400514110344092090751f9404018800d40100e0030f5200704c1c0344041c040482d036503c580c411140b4100b07004c40341c01d20110003010805010000c98403182c000ca00c0d0b050545010a803035016113000d8000000c44001c9080c000b5110401d03540300c076180035046500c0041c5950100d0400fa0441691205080e180310480161018a20075514840383c1d01800c2908010800c0e24403d1488805207181a98094800601400303841560b41c0382d510440e03082c5000407036240050310011003294149040100c451039042d240c4100c294a410081c641030554070600341d601009512010306031380c4050050480c0e0b2003680c00300030b40e1075030b90130f00240c40d00c0d4003003590314090481000500d0100802107116010703a031007803031005091344134149505403034011305410507002c200c2c00b138801101640114040e41c0703181640d00c07106000e544618050713040303074000d0040c05281d44040000440914103000066903003041d60042403090424038489501380e4909800c0f1101c242040104031052680112 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 941104694 1250 941103444 941103451
    0x40806040302070306060906051e0a170322050f0103090204110a0c140309031902011e05031509060a1802160812150d0f030c0b0709170a2a180b0108 65
    0x3808903270b00d04400304582d400f1072000003603030800322500340b0043e03910522503500820030100308000c10920f178100c482e200c0d4859011003090010006000d00451082c2c1c660301c0440c0c000401d01c1c04040000d4006502a00030f25004a030300c01e40c0e43c1980348559400300c01802c0490650782d1340802c04005840c0032040d0901c40104100386070700034000000075030381c0014024194aa0b0410071100c2c0c041170b03c0180d9020308030000f854245100074000990b9254044055481041186543e00b0704072081c1c400d01800e01c80585000f41c02458500060115188041240e0704103006103800601c2c040300d0360361100c1d165030f60800c11194030900007030981a40758140c0c40039402a070b060004100c046c940000180010000d00c800a060110b007100d01014036000303501c41c400031a00890031120742d140a0740e00611558881c002c540407090040c40c6002180c1000400c2031100e41e220191020044000740c580906400700d4109503c203044198010920080d2600e03e00303c502588440807507030b010900b001405c1e010004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 941105944 1250 941104694 941104709
    0x9050709090b0601140d021209060a0e0c040e0c0303070f02130b011d01050d0c03050106030c1817070801090303021e13052b05061e0c190504080604030207030606 71
    0xc1015000700314440c0e0450f8203c0c4003403c0581424291441c1ca03200c5001d62040340c25079601c0440d440c0c5100480886091148021400396051a901c90107254112038895911322030540c0700364a48049410300d40d004040c0495418119410300e00c032000041e1075030307206110460710100000d1841d0214209503100104c0440600c2040c4080070f80203000814580e0f5980103a00d500b00c0d1000c103201d43e03900480c00c0301d070b0310909044144520441c0140c00740c080d10f828864040040c1ca0007041400140c820500d820141e0040482113001500d02544000f14070f486207007154060148a200040c01c1c00f0900c141c0e041c0740d110303440241e1a801d840c0c03507030b044404c01c5696500554204002c11101000040442000c2c2d0343c08968680102c000c40c40c1c0c1c000120b200045009030001e600380030b01d050004c001358042c8503084045155821407440c5010300e85600007a01c40c5807040c5824880d10740003200398100c0e842400f025150075401c00d50b071240a2450302030180d0341540940c01109003881030040d00d018000290404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 941107194 1250 941105944 941105951
    0x40819061b0f030f02040b031510020d0c02040b03010605210c090114221a15071e050a080d0e0606040e030423090c0c010509210c15070309050709 64
    0x10420003070030b051850344082d001c055a0b100c4607a10031201c1d5060300c001d848142d1200c1d07107a1070701e660404d840007440301d0701034800d10110302d00703201c01d506c002071242c0c4041040d99010f45106081d428040640601031286925540362040822541c03243e06050300c01d0b950100c1d00500c4902c0c40ea21036404c042141c0c40e40ca0160b101c000041c009041c02c1c800c00020134100b59118050781c844100d0f49140c0640b182580d4401605200420b003c040b0304c122070011a4030216409405c002c41160008080e100c0c40000034003002c0010083c802c074046100481c00400e00074000d4900d4141a6070300c880d51a4000c480c00c0c0c80705640d03480824001541003081030381c480c1d020380d001c005510060302c01680d2800b4900c03460280b10303c8981000002d541c010807031049690040e0600d030f03690070000d0822046c2d4010000d43d440c42e6182031b0010300c00e65000500001c542840c50050b61402e030b0382c500c10003441d5000000c1d150f2588600001078808601c06241c051280650360742c00039510300e1901e041c07810301e072242e07020040090a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 941108444 1250 941107194 941107241
    0x110d060603060f05060a0905030607050405010305060306040b1803040806040b011e0b03152b03170f040f020d0b100501110106150804020d0f08120a0c1e0504081906 72
    0x14a40400f4040d1601140e08640301d00c02d8450445260f41c42e600080e805000705818888141d80007030107803095480c242c906100741d03910642455581d000456006d445110000c002c2001010600c3c1841c1044010308140c0c4e00c0c2940b545401032511009860444501f03820f003004210782c0103080030902c04480e40804100c40d8620302074030905140000707042e1142030500d69034a40b050380d82e4001025402e4500125001c00080c80c682940001001c3e80c0c07050380419000c0f41e40d048010b100010041c810321800d5280310064480f07444240180100c03039400c80e00031034108207040c04101519000f80c4260a4070314155582c0b820f21000400d501c551407801004c5a042507018081909031040807040030100746818261941c55000141ca4a008414094030307c81c2c00c0e001043c28020200020018001380c043c01020315180d00003200c0450f65010140d00001e00c824043c001c040448903005a4400d1141c90b1883c00c00b83c0b24140c0c6403c0c1891865003d461250340081c61080001d61702604018000d64000143c4030117 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 941109694 1250 941108444 941108459
    0x10903050304140a020d02060d2d1d150703020d2a0c0213050c090604060519090608041b090f0227090103080309120f0a1e09121401110d06060306 64
    0x8403186e600a01c07401c008901002e0042a40d4006841c2d4909407060009203842c00d941503590010706c85082c14000d082c036652144d00e00000320340000003261b901c020700340035068454014440d030025010720704268003041020740032030300d50043d04009840c00101a09004600c1825100041b110108500340024055a600980d84080c148c100705855410040b400795a200544c08203440740340c0f03100754440c001207404210194420064403101d0f075445108402c118420100307403819041813143c5400115454001000540001c100ca080000322006070001262034021510940700040c00140c44c0b5a404561250307441041010498001c2d45a85c009840c081840c001c40d1900381c05000280215100001140800504000c29030303160700d5040c103c42c1c6510382c2c041c0f142d04c0c6074002080c42000502e0160030312403035800c0b2450125505055100c482d41585015034400820042007000c2c2d5400081c400110100f9074280110102c0c0544c81c9031311039039018a500c0c00000c64000d5013200c810145003901c00c0c001034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 941110944 1250 941109694 941109709
    0x1270606090e10030f150506010c0c090b0d05012301090b0f010f05090910060f020f070909030201090b012c07080406050903280311030f0402061b010903050304140a02 73
    0x114640300c080002643d561041c50441c0515074001800c00c6407075007500041c0108171003611400f01c3c06100a101c152140300045964000840300a040901802c000f0007000c21070394032490012130044e040710380040403070311751270300311104507410f00072000d0500001d41034012a00115030240403003030360030001c64108502143c820805100110b0502c44100200d40900c2d004400ba01c01c0f9410040c4060800c2c80c2052843c4290b81b554400c9101080012600c5080140003050001c01c0003032001c000c289640c5010400009030012400603000e5560355040c460201e140241c000c1e028046041c171101c2c810842c03005100200b009440b00380c101d403178048148400e2030ba21440c01c6030003d40142010179030b500d17420b1480707086116141440c151650607056078819101508400b840340e500e5614208042040d098503600b041c401240d00f070210035035000000d00140b40c0240a8456402c2e076284403c24803031006642c03802c4446224003580425004001c0000700308000c03644841c0880300304041c01a80b901a404554503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 941112194 1250 941110944 941110949
    0x1606050d0b060c1b061209030d0b0d0203061f090e0610060f050d1a091006030c02011a13021317010f0b0102061302041e0203061e13020319050127060609 67
    0x20380544105240a40d1384440586c1d440703146a4006c4c914030700304968260740d650712100d004c209080c100f10034030603903241c11044195804c1d00034020380280d95601210264040c281c890284078856110340c0403401c10080e2085001e01c0d10355900a02043c1840300d0201c01d41d909a501c038000f0058a80f44036040c69911100f80d581410700c070103000c20307429255040d20800c41c0e0798080340c503044a0b0031001c01c920170301c0d005192400c44045440812240e00b03016412401ea908801d00b4240b0011845000107090400014020040d216004014108840c0c0b00c44141d1101a0ba80315004442618581d440115000e00c07404000783c0494000304081841c2d040041e4603020000c2040d9440040d020ba04825526030360007180a01c0ca0303058407040c0d60301845100c20b0094000380e4416025000b114000c020090301d2107600c2000c8200248030800c0880298286406544000c2c03122061403403540e40286200e0550088078080d01c2d400070000300284c0045500c1e0090700301461200d50aa06202e004c00041d5044200d4005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 941113444 1250 941112194 941112223
    0x10c0c060b0d2a0504090f03030b090606040b0d02070606060f121b050c010f1b090510080c0d06150e0907080121030c020607060b120102040e1303021606050d0b060c 72
    0x1107601c80c0307a00f000d0005000e52105030402d00300b05c1034100b00310289a03143d100c03a10a480410000003000288042c07100210780007900180104000e0050310b011401a045685081c1c0f001351410030b9a0780c480095800b503500205c00314001c910754007003007030700305011100c1001020410402c0c2e1310340100c3c610f041d403e04c1001d50705210000900e01e4115070300790805251062064000c0c000034020f5910418040d0004417039400003001c400003c90340b03282c08441101a040207588440040d184c01c45042c0103540400c440000142d6259000188000300c071100075100340041d150400848258002d005405400500040403c86604014022981040340c800d140511400700c801443c0754510b0306440c201c660020183d8081004140c0700c08008258000826441e03054491214810402c09100d09074000e5004440302c1890410025080a228000940c41c0500034411100341c01d1000003800b81880694001d900045e00004000e0031003016030040350341e501c0042e2182c92030414520500303625403900c402c0e10107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 941114694 1250 941113444 941113493
    0xb0f0918090607110a0f050c1201021c020a090e04050105060405070215011a070506010b0316020d050f0715180203010e0a0b010510180b0409180206180a08010c0c060b0d 74
    0x85000c101041411405c0d6841074481d202c40ca03071420025600c48804500c0d40c400c031100307011624181e4060095466004003100306080c600c001c0034001000e034010554000c10460b0311000025200b0070780744400c0c000c6024000001d2182001c10071301080d81c00c0180001c0541d4851080110030f0746035601d00710304403041501294103038031309500710980c988241031014100f4440c440c004141e101401e00190701926000b03c00006184da5184141d032204c565041d044003041c4144624098026282c006046262248820110000007802c1c0f110841c0c040840005100c624109040110305091113407007641840300300200b881d1055580c520405050500499002c1c0b0316503401c50158a002d07009800200d1140b8280d07404068542d03480d05215040b038850000000e0600c0340b2a0a01c0702038081d28281e09401610781031170500e01222400d4020320619200b6040440c00c0780c00a0714640a115007500e00c6c00316039a1f1188152541070100c1a66119100765200b5240c0001c510002140c602c45010f207954000500b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 941115944 1250 941114694 941114717
    0x7080a0f11010204170c0411040e06040204030b1f080303090d05181c0b0a1b0c0f1713050402040608060d0f0203030f040305152206060b0f0918090607 66
    0x46039001c1c848211075449600103e0085031400440c0d1918824040800448007580b21000812061320703418030003180c0d80c59041206100034018a81407640c8034002030f2000d0719155696560400f045000c8400c914070005000700c00c0c00b8401e090044200400040c8010740c114200440d00980b1880103880d0001841000180d004501c003060501600c01c520040500b41180c1456040d018107082d42541240c020181030002005209540304010b100c4410701c2214002030207900040c0c84034000070b4004c2c0e65040c10a03e031000000c40e20081c2ca003160321074452107921010b00c0c5500e180f1050403500402c0c4190700500040c00510b51000c01c450341300104556503c0e02c0f130700714102425518602d29010350503000020b8000c8a08000703400a00860b80700d48200d80c00e04c03c0c200c402158200c400d55000081d00466044807240031410009520103078026540040e042c1e41d078805006c026840382c40b01800e1414003050304150b602e030140040c190882c00d200c0382c504626002e04115121040203141d00c2c2400709c0792428 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 941117194 1250 941115944 941115947
    0x3010618062c04020f04150305010f0308210a020d1d0307080f04030605040305090a0602010e0616200f06091b06070f020d0b0603011503150b0d0222050a0207080a0f 72
    0x100070b442c2014004544e02c4500f03513440c44466005000d48190103025108000c05d00d0312a21a0504858100411903941c905643d03443c5c19941c0b10a02030036400c034a05101c02c20b48418407807460302925030000010303910b42005203018140c03200002840b410540040d51070b101e0300c2d804011260300d0b590102c2ea19656140e0203040890700d01640d08003401c01c915180800040540100c000c08511100b00c0740d00030280e1351580103e00342d0750018142c40c041d8000300c0204030a801e0207a5000d08498160521558020000182050042c0d9000b8030114683c07103c5000340c2d020005000e0381d80c00c060944058031070149040d0400306a1044441146e01507280040c00308144000a080703e45165130041071628598418100760541807400c1e03919602c294030f04140b401d880c2c00582180e4089035480401c005c0402c40d0308800500800401e0422600020501601d000507920360b143c42c004a40710b44400d8400507422500041103d0000380314600c41441041108003150040094400301c018600d82408900c0031682c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 941118444 1250 941117194 941117267
    0x1020c030f030601120204050d120e10020c0406060e09070e0303040f120c0603020309191416080f12040b0d060b0c070302040b1c032703080301061806 66
    0x40900a010100c0e540101030030150095000d4242645c4038140700c1c0641c00010304078401c62241a5002c900c0c040a0000210f980c01414408501c90038485508520380000c40c000c0451a40c170900160480308504c240f0b80790078441d0801070440c030b00e02050100e260101241040002508820a0011000d030707020003940c003042110007030941c50321211891580d4541256100b59018170490716103000791070206085100b0300c03da80c8120a180001d107580414448142459500e0030000c0d41c8003a100541821900750402c902900502c01808100074036141c08202c0d1700b40340c0381441c0c1c2c03140c80d0401036804240014500c15901030714540c032549962a14a103072000005c0c00f00d070340007581074100071a281703207001d8000c6182d8048a009480500c280803224017080b4400310001c0031030b24501008040200800e225441c94941d400401051134818020743c480c404842d502984100d0360707080300000502c02c1d940e20185034030900710368940402da403606141c8003a00340000c0d01104003080d90030b030234100084041e6a6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 941119694 1250 941118444 941118457
    0x108010b07140d030b030118020307060507020a0e01120507172a090103051f02040e16090b18011407050a08090301020d1a10050301030c1a07150507231603020102 71
    0x12200da84081e820064050002d05407003d103e5460320a01d030300c1000800d08d50b10314440c5c0c0180940042d900b8240d040d0f80c6034000c1c800a0340c11565540000c6500380038005600d000e000b84809542c401c10305840d00503e8040d19420400300c0361000082035070802c400042c0b00540000382241800c01c00c411900a00c215003a03c0703429036100c10100000010b004010904600102c00740c001140c005001c1c0c0b070701006a2007644102c0c104090900001841c980807504864407a101c2d5251624000b66104240812500724416041903102c000d081001d1035a000164802a1500d10200e00d00b4416a9251184c44503000304018121800000755140956002c0d8100c4603605440001000a01003440702040f012402e21000c0d4050006040c2d0240c1c07250049090f01d0499501450340f110b994100240c10441d0303156541d044100e40c800303000040000300ca04c5904000c080b20f43d040020a0301c0c0400006180b4a0035070b041c05604001003e003030081411450803241d81e09800c91106141024620742203009101c1c21 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 941120944 1250 941119694 941119733
    0x50306010e0301230c0a05030109020a0201090512030a05010f1805060f10030f0b0901180b0303131707061107140a1e1806150e212a0108010b07 63
    0x242c044408841080c4c03010f0811000341000b03400030350381c030010401207200b900380c4e0380003084050004004403141a0001d00754000e00b0300c0049036000450b52460318203002c2000000d0800c40100c104200b4103040c0c402e04d4010070240d0f10700681c05141c1044030704104030041902102ca80c859002a1094940c0c3c4047d401424000d08014060f50f5120401001001620050007926040100000051600031025816103448100b050344900c48004c41c03000815003152001e401d0f010601403a40c0d03410303e600701d010017042d41c680142c6c0811940d00002c3e0504507203410580030700c6036114511603c1d000025982d01910341606070450700401610004001006690000c0c1c0942c00782c15a40c00c0e40521041d007001103649070141e1290b00340251010380141c0da000d02889083d801404c1c82c440945110741c00c9028804405880c81c0a4180880004003080125164124855200300140b1041d00c0b0110314042c5040301c1d1a009856403546034000a002045c10303c29110030000101c0c0f41014044130944204005094 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 941122194 1250 941120944 941120951
    0x60e070b04120606050f01081f0902030c070605060d0c05210604060e0f1f050604090f0b01060e040207020f010311161b050105130533041e0609030201050306010e0301 73
    0x210a040425524402c104456480c00e28900007410300707100c040e070100150b0507111440310f540c0b0149040c440c030083d004043c5030710484181c0010002d845100030341c0607105400340703507a0b50810f40c107000d41030300c001510b80c80c0900800e10f003034400300f403095490405a40d8100d03100308001c00c4401019440d80070b1f61411441c903000c0c80b030900c810001964440b10700c41e6a00c02c103954401100c112010b4860400680303ea000500f42c16520342d407584141c0c84658094070043c000104a54103454480c1030880c06a003c6907000c048000501580e80c000301a105d40c42d004a4042d8944400b690110b0320a1030b000d1242414182c460501d90350303007000d001c20384044498110a280024116040c0540340343c0c83c0003030380c0c603000c403030b402000c9a1075100e101240c1450308100808502d051500060060400780004040d4506000c400309001001403c40d044032404401c1ca00951964189292000d20019100952040d664402020001150400a80001c407502424401e4072542d0f95001680c01c4651382c501c140c3d05518 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 941123444 1250 941122194 941122199
    0xe030102040302090f06150a120216051f0f090f020d1a04060506090c03040803060904080405060a200c03060a05190203040317152404080613060c05040e04060e070b04 73
    0xb052031600c10801228030b011501c0120690241c1f07440b60120b40707000a1512010544201040c0e0010800310140c02002d040300591516003604080d40311180b64035419000c400c00340c2d0205c0302d001c3c070070b0094144e540401c0303004100e6444404091038400d0080c050410a20420288051844550811400000f00d08076900e46071402c4030041100700d4045125a405e0004200440081e000f074034401c41d44684072615644502c003c001c1c100c50001c00440d91802d0820000c12a078403160003401c2d200106481c1d01017240d00041c52890b501850708031554059100b0b401270701e8035a03000102030b60445401c1d400000c40d601e030703542c0045d251013811800c1c214850000041c0001c140d848210480034400307000b0f9100064a905050801c0c210f2844040c0707078050300a000b50b401044500100f4881c01d1400d0203a5842d05549401c2d40342070000c2250409129030702e004800d0144620b43c0034030881d00009180c121300e024100324141032900c001800c0030740015914042500c160340108654000380c81c808101c147c031543e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 941124694 1250 941123444 941123461
    0x190203010b04030b0f13080336010e2d03070501060e0a0c032a0c020a14120106320a0b03010501140c0a0b0c22171b010e03010204030209 60
    0x14018401103801c2c9030b50340b0000345d10202d294901c50080300c840c240d15002c2c1c1c02503260071142d0340000d802080300b5101012001c036900d10524105a030004a190125400301444420340d0841d4401d241c4d110380303900816000c4000c2e03100120441c8159030648488180c500b050280541756008000c0010310640c40c0c002c1c0403401a001c85a22482a140580b041c4104050514210705950a50304048000c1e4140c250044080340c04122050002841d071a011010340201e4000a91002043d4441240c2d501c50505404a5007010302011043c1d0920390000c1c08568902102c0e20410031aa0060280766400411042000c0d014259010402c070001440b2048540e00c0340d5500000b58000e1040d68040341d514080d40e0513503030010061341d4080700413601400d840800f0761038180716202c0082060817260010015061040500300b070800b8404100c0003001d8440e42003d120010199446e0200b50907a4801c01c080d802d03822032040003e052139400c0c81d125000b40f16000c04207000e409150030096004810908101908 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 941125944 1250 941124694 941124697
    0xc0a17040f08010219050c10140a0506120a0303150e0708091b090f07051b07140604151404170c0f060c1207050a020405040b060301200a08190203010b 66
    0x210038041c03111041660b01d0712460b080b4460501e400c01c41072001d1030501700303950142e405410801400c000741d4101c07038a030f58040300840c0d038414444491a00e010060104218580c894544d00000540c1c3c0107910f11801ca03081507440d080c11700004c0030141c03a106004010441030b00207000624108000d01101c0c103151502030229501101c403900b5920a010300c5102c28280c0c0e1051141400010b4421a0386854a51403200740ea0001061501801400c118540c00003005550901a001d601e601511a01d0f040c841110103080c0304842d1544110300074842407041500c030644948a11400b410f018449102c0312100c20703400e010740c0d884110700d0f80c5a030528402103400419007141c840822074040091381d0240003000070714003a81050040380c0d400708000880940c0356000030104e41e4000c1040f207035000321170b900040c20f540003100c003100c1041035902808158242402110312000c62204100300c00d400e44514003c4601940750050204031082020074000140070313007050070f16008804c0541d42c0f582c4411021446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 941127194 1250 941125944 941125949
    0x304020909060601201c0c050c0402070209150f12010b0316060206070f02010f050403031d07060219060219090314011512080c01060e10090605060304080c0a1704 71
    0x441220300090500324001c14194814a4140c644182000340d03080c054244c0d0036110042d00241c410041d00708106882d20b45251032003401665170140c503d40616099080c02d100d40c2030395000d240180300480060ba07a8544041d4005414504409600c800c0400504030000761200f480d0484002006d1050528040d0840d180340c603403e81c211050074448200b602c103002c10b58404c0790016042980403456848c811601c1000f550042d1002160013045100c0c0c0d41c007100c40680301280030076600e21891616005898401e00e000340c0310303005043d0040c684080a51500700303030f0090105075008442c070031040244960548804480e00607000c002d400c603058000d0180c0320103010580b24040c1840320308000d828140a012060300c00014801260743c80c1165901480d44c07000c00447d81d2200500405070742610900c518001800381c0c0c2001983e904042140c071400c0c21180d00a06440b40c203001c400e10035903c46008403074100b64818005541c820810f94150309060795040c006020418004541030508441b401500a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 941128444 1250 941127194 941127199
    0x30102091e010f1b06050606040f06050a08280b1201050406090302010b030a170a050c030a090302120a030c020616050d0305040308150d0308041e051f021309230a02030402 75
    0x41c050312160003030340c0c4584036922080413250381490032400680c0b181c02c555009403019215030700300754541c20440e24021080e000600060f5003c1a4984801d6000f000190031005540700781480d10280b0340727038141d6480000c136410441901c0d000d66851070740b160345601580302c4800000b0802400c00e032030700340050422000d040e0300560070f010350520301c1c3c580400c00e03814840c0c2c00112141424003403600e14020f90800001d45040c44005e00086000c10000c0c0010b01180d1516540c01e250b15040d84100840070141b15007210f0a58000d0b0f80c1600041d80000102c508160102d85050b203801c0c4000c000000710111035802012030207607e01c04040181c1603081640118869140c042260742c451b196444154080002541d0245004900030003090040002c250068003441c49001504403002c81c80d03552100400c0c0868207a0310440c0c0240e61450381d03040111402c50303491400e40c98900b102c001114100c00c18019411302d107941c0c41c20981000768042d00004003200e001c0c18404945071054035100203402c122026030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 941129694 1250 941128444 941128457
    0x70b07031107030f0c020a03060902010f03060819080d0c0206040311060f130201030603052d010b09270a060e0d030e0d050706090503040806040c0e10090902030102091e01 75
    0x4020034064020074161800340464141090003d403422146002d88011242c18801544400c10240e11007501c8500030314040ca00101e4519001d01c0010f0000250b8649101050b10f0310005110589001c034200c0c07640d00048540c024016000d00f40004d5030b128078001001d030549841c60f65400d072030700840e60a2090740640c40d1190a40300640400d0388860f0112000d04188848200261415a5040c14424124010716000078025103da40e102d00c0c1001c510750011604112640b510b048402e80d00c5080c42d0502101d0081c0040302d000000310300042c40c007802207400c900707003035038040898408582d400708180f14a10848001040d03a0801da0b000300754405048002d801414807900003a4024010840d6000c5540b0042000301440340003103035142c01c41c94084400c682c50701c00220101c1c108101034400307408028050710550070140f0f456410016640c0c41002200c0036401040700d000f441d602c3c2e450499210078030100e00d0201910000b0300a1107014042544040820b0444440da84412065420310b0303000c0e00d900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 941130944 1250 941129694 941129701
    0x1e1008042a0902030907081e33040302011a01020f0a12110d1d06030603070515070506010306050907061e08070e032a0f06030615250236100b04030305070b 68
    0x162003080922034146056000d25480e40101410f05940550506124281c408240c0ba41d607809c51651000d440030f0300140c0d15038600c01580c00300203e60389002e01c400d0000b4000d2020b800f07405502e518a07180c000c0e100300c0c00c40d40314104407809820281c07122144182074444040950001408005002d01030310000084107601070307402c0c180401124041d0b40001c0052030102c1c641010410300c00540701e2503182e0000d0070702000001440030000c0501030741c40303910302056a00d000034001e403500c84540c2c0715030100191040c2015145513541c400756554404c914181d11241e035084415a801c006980c8400e4051245045880d144500042c0400d40c0d40d0000c3c60189141041a0400031040c9890f010f01d0b0b4080c0007040803e1542ca800e0481501c42302c08000070070708004803c1105d5a60803100d4150300340000904204400310303d887c0d50308404000d00020a1010080e0200d00700030b9410003021070400c41850100070511511003030f07181ca002030007148202580c5039100d14004041c2e41011a08032816a01d18011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 941132194 1250 941130944 941130973
    0x61401090e0a3018150815011e050d0e010606050d1a0d0308040b010b0a1d1c03050d18080a0e01030603140f06100b091507021e1008042a090203090708 66
    0x4080010385240c6d02d1103c59200d01c034140444804541d006070500451f1050740c2140228426912250405626000e442c5c0c0711540d0b19000b9502d4129030600d19900d03007041403140341d4100341540e2031041075880001c1c0d801c9211802c1500c02084c10700752a4403421841d4140d08169212213094442d030320801c3c84107016642e800224115018140003000400c207984464080c0103030ba03803a8035400c944010000c12020314220300416003c8100709050700025000102100c220400d8000e031a41c41c00c0c0300d42100c045013072503118142c060242c102070004000d80c4500b1460030303a100e80c225402035608884203e074200451a5a1a81c803554102c14030601c2c043c403c0001c06055007162450104e9002400c0f1794502004401084080c1c007042076030005200703043c400400540c407141c03115914041807a0201d10404580d600300704450b441e1403601c0041000781307020807000400600c0202e00b803245403c01c148080f050208107110f00c08442d0040300c012407020080041c84000000c400c2c0864440d46c2c2541d80c00e0026085 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 941133444 1250 941132194 941132219
    0x501031202070e06270c04080d0c051005040222022d0306060a02120d020414040b011d030717030301060306080f120a0306030f061401090e0a3018 64
    0x1030985a42014000680c503041010549580c070b20b5a507540326140305c0d60720748800901425135a00030302c554013040c24091503804200036000001903040500540c0e04640e501561640d1401105006070f40b10400b19045480382091010602c10a110a003610942c42008000a402c03c0803032101c503100030a08589007c204840308100c07040017144c017500e1a41c0c2d0200b44040d40d40500c00311021441214046501500c440c409002100840c4002680d141d15200c514905c0d00c60001100e4444c1d880d2505901c490380e08564000e03800043c00c10380b0440301c03000c03000090030802140e1083d5805c000c401da6000c40b0403408001941078464a4501308415a118400c060761210760b2041c4000c1030b880040010f40c004081400341c00c00c01664500450702c13039183e0782c031411181400382046440070b49411610619004103000e40b8050190b07110208200000da0144550b0380480d844064204080304008101901000c0003107940d8628019000c0c24103803160a00031700a00d101c9202d0980595081070106200a1615 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 941134694 1250 941133444 941133449
    0xe0a0903031a03030904180b010305070e070e09180f0304060801050306070c020607080921101b05070b0a06050a03050f06011a09010e130501140406090b0625050a06050103120207 78
    0x1070045080003982d1702448003c003200c06840405540c11024500040c113418100c0307010f10f1280e00905a07151500481c1d40480d240905950300340400307510b40201783c0e01c4401100368003a2042c2150300c4441e181180c1d140c100787e000740c0c08001ca400000380109000d6040150a8101e500903005c480e5190344500c4100c034041c5100900035440341040001c0808035130104003400e41c46a0050840f07414407114001810b01c0e90115007540d606400071100d1081e21210ba02c00d2109580442c0036910412441590081c43ca120b4514020040c01c150004100c4140d09684440042d0801405000080d5140e0601c03030396407801842101000c2c85402c0021030001c0c1908814000300b6030403e4003a0410709801c0c010745110000918180d005040c200c001e0000d0903450141c540240401d070030314000241c0344418002514201d40014010608154407010192601c0048542c0f0301d00c40410402508011a08d802900315444801b410500c5508410000c2c08881d5000c0c9040300d124030414a01c9110004041e611040c091 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 941135944 1250 941134694 941134699
    0x902030c0306071b17120402030d020607080105010f211416212018180a022505010b01030501120b0402312403050d0c0c0e0a0903031a 59
    0x404240d554a03856640d480e80e14800d052000703040051000840086d0400400318240c08404014441036082c24002518503200302c0c0702822540c44c02c2c0314060f100400c184289130401c410700002c0c0400a200e6030102141501002c00101c4101524007084050260360b00132200340703400311012681f101003000a06105d11480c0d1500d820024101d8403400c0c2800d102c2031030310400c0d5103131051900828100e091900040075045c10781e588600c510307010002c240201c414128010030344026040441024000d9090b8003ea0003800035a480701400000e40c10082e1240061801c4c29504e281442000f42c10f420900400a080c1ea0400050780c2e030700740140d8100f61141c1d0180030041d0300c4d00800c0140c2822a04e41c081940c6002c0149040800700030550011146105880b0140e40d03a9065481104a100100c01a101d83c40d540070b0042070031601d13403a407201403906c1d02c1e10900140e42d004100300a02d03481c2c5600141080100c0c2102803030a001a0030240c41c2e102012400030707181928440540003413034048019100003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 941137194 1250 941135944 941135957
    0x2011409210408120f0706092006120f0703091703040b0c0f09040e031e09130c05042304060902191b0b04080f0a05040312030216030c170d0902030c030607 68
    0x141c4c8541c000759480072007200b00c14102005503a012807034501071600000d2003075050720000340c509441d00881d024034102a6118a1080001c41c3c07030310100300001350b00710030170051007d500d4079140c0081e0010f150301000280505c0d854442d04022510301c0018511990241e81041819900c3d282500031a124030300588801003c2809400c4e81408e117984100c4a5402c11011207140a140c1849460361002140e03803c4000f003c002800ca0030340c109000704000c2072a41c0300091180e003010700380c0a0018040d60292f50300d801042803600c00c030b02840c00e203150341e4080082c1c02001041d85440400d8040d61001d0b05000035080c1d4030b0400c0c4103251040d0303c6d03203c1144903d2004c18107840269a8422107020140090342c811006012231481d810a210090180071800e8031842d07612842d61804000015003a1051018140b052020b02c4403248940303400d401255243c0740c00a413000c414035207a240680d0000c0702649891340450800c1c0414200d600140e0568001c404827032641115408040e5611000c07907044002821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 941138444 1250 941137194 941137213
    0x21501060804210215100929090a020d020f0a02010510081e01022106090a0e030a121d010b0a05091006050307020316060605131b0f02011409210408 65
    0x9040c00300c408565031481a1781c0d05201100103d141d00105503080311a442595208000410f0305208190fa28046c0006513070007084500c6445845c40311500b0a0b074003a809920010b610468240e04558000d881302004540307a5141103071005654011409044c0550718250101d00d403a06105c8060742110310700d400034000c031007e0440385003409080740102d0b80c1d159002e02c170711107900300c0040040345000c4050004401034500740c001c12415580191218200b6840c0250041c1000e40100031261040c440c0c0c2090481d4102150001c2c008007400180c403142c0403140e802d070240d500f206410982d46020708039030361002c1c0340d100c00c2002103000040e101ea80034848410720400441d405840a164003da440c0152030500020440000d500d140240d406c0300c034284e0b5000c040c491481c11858055000203407603020003044000d41c1c95000da20502d0101d40c000e122900305a00b5205100350007010b810b84520301c1402c001d007000350070b840d0355410001010240000c00d0340c0504103074003000e098404480051004107076500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 941139694 1250 941138444 941138483
    0x504150c0c020306090307031707050f030c0702131515050d0b03030c0607050d0f09030c0b0a0b0a08061b0a09030b060d080301081e1902041812021501060804 69
    0x342064840040c480000100d00c0075075002d1042c40e12031880c05000e11b0f940d0040e49030040803605000d4480c100c106c0f400044c40310507507104082d44c0a000c00070321440c0d62510fa8036500c00d102d00409400960000031004400b84d05503040d084003012441030343c805041c0603141d0701c3e95420300210780f10b9000000c500740f11703510615419400082d50303818007505a074508903e0105090078694101c42000225500049000d1310450601c02c003603021200110030011101c0580c1c00402d0114807104c0504488202c1002c5610364802e40d00101413503000030807030700e0000d6840c01c64030340340c0b5802c86020422411080c51b41031842558022030b02ca0310455510802c00c5c07402c50b5035003082142c000d01800e41101005d000c460004114078000c0d800381c6510303002059064101c202c040e21148241c00d03441c405810500f40c100c11200b4400080006503030448010508031550340b8005212400084090070b51003480c41084a859000302d070300a2203024402003582c050f80ca800069130004400d440041a00b500d15000346c1c41c0a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 941140944 1250 941139694 941139701
    0x11010b06090d1a0705030403140a050d0f060f1701060b030103051203070e03030417191101030f0902040510061205060a0614070b070918110313030207090207150b04050415 75
    0x40f8810200c0114102100402c0342544904590304008100000f080c401455048005c1041d655000c0040620b0700407a120000c1450144a40108000e0384903411242008482e40003080a06580d070718103006155242d4008090907802c060060483d4a04030022402221180449042c0d0740c100c2c00406e2203d000b00249101640010404410018140c3d6800d1050703a040c030003030000300714007100a024035241d40c8549040114032465041c0500d81d200e4901c00080361a0300320074002c40242030004001070080c42c0343e03000e00303082c4034020f6006260004008000031050003070000c0d2184d0707a41d41c000e5404101580c504684045d5103150388107511450070040d140c400c02e0711041814101e00340e2401d014095940001c900c205585031380109250100620250122004410300c100500c038003844141c818501c40704203031001429008041d44898940b00505000300101d400811028408650b00c04103800c1c201c2082d00c0d0b001e0010702140c00c040c078400e4145441d002d45400b441c0c1045039034858040e10103044008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 941142194 1250 941140944 941140969
    0x1e0f1202011404090b01111516090e01080303010806060114070f0c05060a080105030c0607020f06030606040b0c0c0f100818011805160e010b030c0c03090406031211010b0609 76
    0x1000115012166a000c1c0c800182c001000d00c2d02c80400d5400f180700025007403c5902ca5215410341c400060640c2e10314200086a421404403070701e049c0301c1c04255508443c1d050082e00b080740c115290754000101d601e4000010b5040710b07078540035240341ba00d1b240b004403108500c01d0700d080c01c005011302000340071501440d1a038012034400c0282080702c40c0e079940400c400b03400402086010522a07001088941400e100d10000910f040360fa03146450000c0d07001400000d00c03004400d00422010001809a841d19400c44020342212240c0381d80384c0d000000181d40d150841c22186005e400138218100c00d03410400103941059100303483d145d1039642c803626880580003c103c020012992164114102044c0059101102e1405036024120340041c03000344104800c1c555109161b03580c0e0041c010031a41000e00700b0359400480b1145000e0b906c1c1c065042c20b91443c0a16811998020b20301000042088903461520540182030f8540311407403e0392200312401c84400c450740c681c03c00000c11100003140f41c0300c4a00b00d034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 941143444 1250 941142194 941142197
    0x80a0506010e12061501030b030304061115011e0504060e070503100b03070e0924060d06030c0b0703030c1d01030f0e010609090b090706020c100e10091e0f120201 71
    0x25803000c4a80020008007101c1d1460800d5000001444a8104545c030100106002801c040c02109807140102c1c0ea00c1c0b04034410700d0f0030490130480384034200105001c0001010b480200d02c42c0c46507120720710081d85001d1320802c0c3d1020800a180028070f4109409030008951240421000320341d1740700340c00e50f800e41c00213094000841408001040b039030f40010203540210100c0d51280c5031006413000780040c0703180c0a80307a00402130071802070fa0171300d4048a251100701c000aa404d1601c94510180e10707000780c0600c4d00002c1001071205400b02e1981d07603641c09002846d00969050000e210690380a44489000c0c0d00040c0780c1c0741a444802c5900d5000341c00c0349100c949103510001d0784640003180d2030b007101c281da0042d0b10f100d030312054240180000313002c91a81004a0340090000f0b51320740314000c2e64810007080d2607030141c1d80218607241c40c1d5010703259540801002505041c0b0a050058005000704c1c428001c0803401a0000c0c291014965040c00080a640d21200c0620700c0c58145030001c4804284c00074101d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 941144694 1250 941143444 941143457
    0x412050f060c0301050a121e021f050d1b020a2402040b07020102010b0105120a05151c03020105090a0305070204020706021c060302091b0706110f0f190807080a050601 73
    0x20140da410044188103000d1654035540340d5040008202c0c0e41c1030b180d0f000e84d0182078040d96144c0841c0b50708824600303a0055194418150810344007150400c44d280843c00803510122101340c2913139800c50010015804040350802161002f80080700c0f000c060300c0b08220040c0e006001d054000748588070724403040d0880c9107102c040b03862010f020009a0f4403903004800211004512a0308550302401400741c4004242011814081c11121044010b00c1c01014030091580701c4000c2098910264225100108040c0c41c02129003100e0a8203420f501c12403500701c1c0190f1900b4001804030002003003283c43c80c1d905548113490300e40d807502000082d410014054805541c2007012a44410940ca4405c00a0500f80e101184c101d14500401c43c1080000f04540d141e01110004400850300b550200c80c2c3c0c0c590310190009141c4000000c1d8125405005210118004000f036401400c0c0c2c040006880010090342c4000c00400b40243e04503001030090382c0c1807000c240c0980c0400c54018a40d042941d00490614203c3c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 941145944 1250 941144694 941144713
    0xb19030f02010804021c0c030203070e0c03190f0c050306090109050c09062512081e0105010c0c0509070309060513020105190c05030d020715050c091201060e0901020c071a041205 78
    0x40c1b0504111520072198490b082101f0011414144054030080a162a08210030700c0d01a04a1109110050a0603a05003000f840c00c1030180c4907900200082d503a83c2002c01c100002a580505180e000b5521075101d0418103000007071410f11070203035902c10354081010a092a0920041c854280c01407116500344200c2800c040598143c8803089040c00f50082920400061081c0000391030f0301d40140c40b5200e40511050304e161981100700006046510a18102d041c00e00710381032803140e1a10342e402196008001800340f145080d0b050700105002c50261a0030080380d103814000056099032100000e010550030300200000c40b500d0151400d01107100d0400303000310760032965940e00b180d000781e00b04d20b15294003080c40c0c0c00f403103c1d900c09102c885440303010811440c00d01201c1c100d818000c00703a00600c20681c0d07280d00c91142c0c2080d0000001480414150241814041010344c042c1d04000c046c01035900c95136100007402c4a0501e0103441d0b0008050100c8c1c80d090401328403140180b8030380002d585900c51441d40c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 941147194 1250 941145944 941145979
    0x2070606091b080702240406290a05012f03070803160905010e01020a060f1103090a021f0509060a0c05060a05390a02010b030304090b19030f0201080402 67
    0x100031071070b00700300400c1c00b5003144940003410340c240142241c1c0443d440704243c940b08454000d000c0d5201142607010340829a12840d169024010b02e141d0460806612034110048159490f8803201600d03045691940309616003004458054103003440f007120101300a1051000f032980c803520b002103040081902c0c0b52031103070b854410300c56200b610104c0f99030300b0807040e84100c1176010341070340058482440d01660501c00c0c800000e6842c0b000b00400b401582d50b0396207500001a80750300111030a060b180d4096242d01c1e098034003079291598203000380d001d00c1c84d40e100003091a001c042c500742103550384d480306070414188200303000e00398124400c1d200034004a100c40360080760b420001603224045480e00410b0301d1600d14070180b0360304070403040011041c0c0c5212a600c01907094110303038502c003814146a181c56400746003080f409042010039494040c080040c011405036078540010000b0407090751485440b0804d04c000c082081018807000d46070f0441d221034200198030845005801070300040052a144d08031905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 941148444 1250 941147194 941147201
    0x20a05030c031e0a08040210020c0d081309050123031504080304050106080705010507020402130e0907140f0a050103090f23010608011404031b05122701020309040207060609 76
    0xc601810740e0000c6203c0111000540e0414102c1c100d220322181800e6004401401c11700e80500004e00c900320503541e0800c4c4502c20040030301c400000030b2140c400704984d402c0501c02c5e40d00116141810b2120204041121092405030038121445811325440c0300350421405141c840e003080c1d185074103005003600c000c1120030303025085005074060000301e0b9a070306144c6055421504694840d81c51030b04902030800950ba000001d5a5800d601a940541e80b4041c3c6d0300404501d2110b03800c081036403030184091103040680004c020040d12208600440d02e01c603031108008114900c4520180e110f02c10180030f01c02c0794030a0700a0036015120781c4101008104903a201c84094001302d1341c42c411000d4208900c18007803824003420300208003c5000308203000408954543c4583c3c02840903091000030746800a100b0145840c80d100b032908a4140c0704000000c00c650744460703004211864452005000e4551158000d800c05000c42c441600118a4800c041c010702000e50444c030b00540381c440c3d07a12030010b441d10b0740c1d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 941149694 1250 941148444 941148457
    0x619050c1218040e160501030e101802190f121e1b1a090906061b0703021203090901030311070504020d0e060c0f0a08060d0f1a01061716020a0503 64
    0x8a440e102c00d03015803d010880b0086100511a5401036650600c6a00e4410044082e01d0003860040781d030f401451140d52500c1b00141c41d00d00702c10302e040c2424241d007110b1055091220f1003111000710000507a0034011465030030b80251060003518040401002903100c00c060f58243c4250103c140b00700c2034281c0340303a10811400301614803118409000d24101a0081070b100070b40703040100305588074600030a456060140c4c040c000e0041c01224041186680e0b1307103058a00ca22031900075010039100298140c1e4440c201d5120407030251440c0208a40c0204010007940c12280d000b900170003142c0e00e1602c08582c0c4001501079500e42c0c4c0036174000850740f9221030008081c00c10350300070003090818241090b11b2510390010001c54090005020885000b0b01590031501c224000c0d24201d442e507180c44000686004001100402c10b00008048208211802030840e14441e0303c042c20b115140c2c0c4e640010380f07680e074802d400d07070003010205000908000400c888140b8488280d1048030320908181e5161840c603402031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 941150944 1250 941149694 941149717
    0x40b060625050d080117030301030f2a030c05010c0b040221030c150a0501030c030f031713021002031903091b06170106020a2f090c0909060619050c12 66
    0x1482601c81294100307404600400c40750300c0d40e00307900486c002026100d0006001c000c041da4021000001806848030419040d02030b40b094484400c803644001c3e1401403641d110403100d059010100240c15030085042484641d08080003180e1691070350708122030380d0079009525001e540c03000080c85000301e007000070b4210080f4010041040c10b18617110319080940040c003c03025182440010700029100c101700608a80d4400245c0d0981126071406481090650251211001c9400c04114902881505490003203000b07440c4600d143ca25100704a03201d10803180356003038a1281015030000203110b40d2241d55000d00801196003080019004030090400d140d0006001411603a9642c0362000000821801050940010f1484210715603416890b180e0700d081c1c071101c0f8207026a8514010150740c0004075480c0c4c0041c03081c42541f030304003000601a01b0100d40140501d00a600042290801c030045130040011401c0c250b581003880081110254400c403010700c4540140c0c1d0030240c05400b81c00c0a403104101a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 941152194 1250 941150944 941150953
    0x60e0a21030e03060915070210110909100605160c0801051806250518040e1c05120609071404080a11012102030c131203080f040b06062505 61
    0x507070a0007480210b1400205120303400240500c80c803040300007160442018041d14240c110341e10045d050303041000741c440c0c4181203401c0941582030551030710000d120300802100c034886207442d01150301c444c4804c0f0307006590216008104402c00300000412950f030080c41190205c0180e07031200840c034299401a283c3c503101c01c1d00d8030070b595050641806180d51103181d2602d020f507080c182c200300410350318011400c072090140020355610a1000000c516400d400090024080070a0304c08010f43c4e181740050040108020b55056804803510400403074482003445007d8091980341c040030008200b4028040d20107110184241b10f0b00d480300800034000a240540141c5181a00713414001a03980c98451018104812461030382c15000b19103071110003080c01003a0044c0c580d075170300d1400100d0f031294611410614440300b0000494210301e0b010f1aa24034130030356580f00e040c0c0303840e2440c40d083e003400d0b50003c2060365801b000a03c0360030301402800c44034401510385814241e0145d84c01c00700040e41542038586810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 941153444 1250 941152194 941152259
    0x5100b0c010e191103030f07080d110c0a051e07090f0b0901030b040302011406010c030c17130807060314040f0c1a180f010c020d0213022206021501060e0a 68
    0x54040c00c1304100c18007039000e0f62500e1041c049401040c0b1505900030702d41c03400400c07030700803020143e840b03240d0700b2100000417039842003000c502543c1c582c61003608817141c2c41540c9510414903035184c1d0f41c01590350050000c22110f4117005000004e4075200d2040d61845680c0d2590b11240c0e6659800340c2e000314021810519280ac0c503040080c25182030980d001c41801040c4e0034410b1070b0b40d001c0500c642154161400d180385000da0311f8800b01000220090605222000c691000711040c8068107808071940c41d42110001941c4e240f05605450030710060000401c00320002401042c0b03131403c0000001c0c0310742010b40f816500c0b9540a01c456417840c0d034a07500c03000040381c0011400720200d0b030341c410f80c602110200d91400500e40001c0c00100d402e40028045c062169104c411500d8580e04c8044400380901c00b55203e8004441e184820510f00da01e94a80c2451114006490b03800800d00d2812140003000b00c8015a007012030035510300d10190301c0141c100400c0c80d000154141c0381c0340118151031105044060100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 941154694 1250 941153444 941153453
    0x3051b0319050705040612090201020a05010f0b0406051f051602221508070510030e251a030601050703022a040e030301231215010f060305100b0c010e19 67
    0x142c00034035400500008010900000c0e0b002070181c020f81903180710105246040b0f00c0100c1c14611883c200134050340c00d0100c0d42e071502016130807101d0000403c4d182008442e03a100b0400c4400220070707010720599811110801d810368400e80040a10440d41c040400000b41c0d285d0211b222002110b131160441059040c103ca450503260040041070301b000414102c4807402c0c18000c42c0c44031050b01c50b8520032060310700c0160100f030003038002c030110031004c0040c1c418401548200440c4c400060004004500c03522102084e400384c68043c062a00001840240c02e41c2d58440045d80e9035480114184c0541c42943d41c3c080d038840c00d5108004c95140404070848102d070929040c13009650403040c02413020b810920050004d050f0505035800011390b030324101541548180d0100c3c071610f106008404540c083d810305200d003d840f004d01e0307a040b160780d440c504142c29540e000807012510309441c00c3c0e42040240b4410000c060300180540b4840004800005030f00a1402d001840c108540c6d00d80c0c00c040001841d08420300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 941155944 1250 941154694 941154701
    0x13240306141302033004030b010e0609100e0c0c010e1006090209010e06131d010618030210121b031e11040b031b0c0c120c1003051b0319 60
    0x42c0b040e03500100c01d5015540007030345640c1140300c895484c40da90540c4e2904c50200c0080c000790f003180f011445a940c3d80b00d00781889600c000340a0710004160010108100c0d09062281071300c10900304000405032414003200d080300300303009030000c400f10b4428084440c80b401e00384110b441e1940940c000701010045a8042e809841040d409440301c0e034410300c8102d045036085138070740d29084000c0321110741d15010202a03000d24816604031012440580c00c544e00700c01e00c41d50100381613804984404d070f01020440d00780c03810052203000c025040600090000e0003180945007541d8052480100403c6000401e4011480e0300e030f809a0240000c1d0702d81050402e00301030309a02014a802800041c4221000c14030041500e200d2445091440d0200000286070407040030164404000038001e400d603070b90140d010387c030381e5011040e08042c8982e5501e01040320081e000038884a07500300c0948003c041040b582c4055000301401001140345100708000c0713606d40303d0914011442a00c2c413500099000041c0038406044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 941157194 1250 941155944 941155951
    0x403150e0f160303030f060801090807060b09060a050f040e1006030c0b0a0e060a0c060203070c060b040501050901050f030c0301060b1e1810021920030303061324030614 74
    0x7182c02109a42010740c80140084040c1c0e6014100490000c100f18030510060010358007250075546061f1014040051030340050464601030321060252580305400c0014104041e20300307941c001d022040803c40c500f030440403800b0140008100203400d101d8110380500f03150307201301c020090325600c180510810228080308000382c40344100b85801d00310b0701c0d2809020381c40e031501420f01c50355021840360300782c5108440b4400955402242551682400600940088000c031401c686950030301c40c005255061504c02e190485e00003e1000d0310592070102030110300188030106a4060151485d40029034509010318002007030800c03011540e6007407000341c201a2407418006190381c24000c0156945e038001c0341250806001b030895003011680ba0b807000581c50301e254402d20000201c014503040d01401455240c1e0741642d080b06061668582d41c21082503140e100850fa0785610807100c40551003075502030744c0f01e0f50038465002940c2d404144444a04650700700d56a00c01c031032060702c540400741444000c1003e90380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 941158444 1250 941157194 941157223
    0x102041706090c0424080705040b01053f090c04051608150a1d0108070902040e1302030a080313120e06191b06061403030a08040b06060403150e 63
    0x52410021680750711440c0000c030403480b4a0f2101c0c1c05e50304a160f550200340c0c60301421002c600f5841d0f0344003000c2d61907541902c16144a140707850229001940034908507048800803080351902c84261540155825800c6914108005920164030300c104a0700d03c000c5015510200003061103100070310400080da400285140e01103030754007610300b4409400c225007540110784404403032600000390003c50f041ba15658440c2e03001400100d2214103911110008a040e11200c0040d1085541c17110561800d070f101d2407080c0e4000070f0048000560700c80030340e402e602c031140c40102a50300140c42034850a07495003040d945d103250207124154a03000c00c208003400a07081c03082c50070300314441c505040010b4a0b6010301d261011090103d80310000360244106114211542440818102c10710f550500707000505490085404114100386401c0349440e0002c1a00c5182e00c0c2940e489015944994800e490224068601303038110074280400f00c0020f00d210010600c0085102c0700080201c4c074448054a0001b031211000da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 941159694 1250 941158444 941158453
    0x4020915030307060203061507210201020a051e040806040b0118060308090108090a062409022a0304090204030b160305221a0405030c060a02031e13020d0501020417 72
    0x11000d440102c203841d0015042500140c9030350790903020851072804100b1248601b24009903800411500032820f0040300804205c2140741030210000341d08078812848007101080303080c005940d204070f000310000401041d80f8035603424243e440c901c9524210040c0c2c0c0440c1e8030a0071200500240c40c2c880c41421200101c036400380003075845c1d03445400d0644100d41c989030421901000140c03039000100000c6484035403101007007000c0c040300b8154046007000440c1824142078101d40018024042e80280c0b5401480300e6800030700711021201c0769022031000c1400b00424002444000340241291024200850252400310340c1441e020055416003109005030f203043c10300e407206100341030203142c00d41c440a550000c2e94030006404d5007014070840d40c40103811819405924100400c019020002e4131180f540402140e42940315042030030f090340411034200910040801c411404101c0c00452260480700f85064071040d1340700c58000c503807042022201075900d43c0d000201000070301206101d01404614650251 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 941160944 1250 941159694 941159731
    0x2030906070b0627070e0612010e0702070e010b0d06050303030907050f0f0a150905031f0c1b03030605090108160b1315321e09040c030203040209 64
    0x60441d0080d18409407142c01c01c0300001c0c41d540c4070346082001d03849048141010115840c4a810704004c01100c440d000070349040740d0030201d03080c0602542d050007440c013428003040e800c14940e684840401420607007184a60100011014a045445c0b406060210b18040d5a044040c150006070b4605500c0035020303a000b081040320901c4081004810b580e800c58400701354504c03007800150141e040c0f5800c981d01841080002850100e2610380040848858132403482c2035680b40d00701602c8d40d568205207100082081c1c01d06000c00034981c0403a80c44813041c10084426950070f903003c00380307107a174000440100c1d66880003880b26290800c0307120700601c070600042444514140301d4480c2c108503031080040400300401c1c41c0c0b001850f150090006012580c4c0142e4270b2380d10b4402d005000b000b1000c5488010b050600190b448182003040030881454404c010303d01e03001d00081b210800041c0d464250040280a115022441d034543c0a07100e07266905540140e00c9003000d0041000c5600c0150500c20080c3c4080985d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 941162194 1250 941160944 941160949
    0x14010f0504240e0406060e040e01060503030f2203050c031203130816170d1503030c03050a020a0b01080d0314040c031502040315050406050609040209012105010504030f020d020309 79
    0x1d4041203021420ba02e05030701c074804015180d41660400056100d81840c201140907075109440c181141000c07242407003140c2021301d01e6401c841c4503000b0710342c03d42c104102c802c100d155620300a2284c24908001907142d54038001941d581d01d0031035082204c40743c21465500b2124030b8100038450700300103d91440b51450900c1d5800082c0e80303410384001004070b08c0105440000d032021840d085a0203420045140326068020101000f580c000103803032140c0c51070900b220a03154000c2c0f40c4081900d505848000703100301c3c10745003070352141c00c0544001d085114506c1944000781d100c08060b4024030342c100040c855010282c1c2c028040d10b160480e00c1125407401800c10000c600301440680407a03030041d40c1000c41d40d01000c0b60b04068400c50700041c00e20303072078812960524022580410b1145014400401868072480f0800000c09403c1c1e43c0658051204001403010304000d91018180e10061600740304c021150f07076a96401d484c000c0305d058020442103815001e1151301400752242144007172018520309000c4000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 941163444 1250 941162194 941162219
    0xd080708070329011112041e050315060f1f09080a020f10020f030703090f0806042004021b03040504060515030a0b01033903020903191b14010f0504 65
    0x14401201c007040500f66402611090008202e020136034250400700c812011250780b091086020107441146040164072a81d0582e50a44200801400540c0380c4d030031300300084e10409040036501046401c02c80c0007540d034102c00407a140300401a10b003024601050301038202902d0354020301450308484000c500503a220507902d601c0c1c0504950001240c2407440e0101d10700309040988003510702c000180b8000381a0860a910f0403248640088001680c03105000340d16608242d50003007034a01c44481e02d100f001001030031100c01c6078004d0700c01800c0818000350ba0b440040ba102d80f241442d00b0006080c030040c00e007030182c0e502802c01981d88460b551103031440003006100050150041c02d0380d4104042040c5c1c4a6045580500c4030341a2680d404031051038020200c800f0192549080c04400d0041c44219002e4000d03222202c400a000d400400b4080721840b0b80d003946948200c41407040b617190a0507100300e4011420103068084c107220b047d6003403035001400701c90440001c2c0b001d104082c0802c01440c41302d1b0a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 941164694 1250 941163444 941163491
    0x60506130b0f0408061f090c0c14010e1605030f150a02030a06030209010608100e01050616080906040b0403140c0a090b130203090c1f0c02061b0d0807080703 69
    0x19441c2c0d180300d2031a0300300403070050740c11441560081d503003400b06408040c41140175280100702952049a901d001c0b0304225860313a01a8030124401c0003034039001c61138001d42c176800c01c400c110012504c4a54030405ca410315520f4403280300c4030542448148660b0404005410181c00300e18001e091049024010081b180002003c1c0400d6640020010b00c0c0014103400100007107034060311414817540c48103800390a0f10021181c9010300410f040c0c2c005071417821080350390304850000e043c003464070100c03290020400c050341409441551042100d10301a0711000001c0000302480c09145845504501e41404104d480c440d1a4003140d002c05000070090391280c4030241290941e2000154210702880400d40361030364011404000e602c00701c100001500e01184081c86450700b120248030000c00c001c0c080f4091020391515000046984e4110401414a0002040e42d4404407211081c041c1e444141a4500030316820000c0000e4005401e20143c1500003049540004107170405001c42502c040d040d803040090710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 941165944 1250 941164694 941164709
    0xe1915031e0f08040306020702011e090b0a0e0a06020c0a080714040f0f0c02061501080c12130f0507030317090d0302090103020904020c0609120c070e0a18050c0406050613 75
    0x41c41c000040052108580a1481e400030303415488070758074101a4000e401800059000c03541c0c06040d010325811543c04c50300048584e803222114142802c85036159500025000380c02c0c800501d000c82c1440d41da01c12410010002a07004181c0c24008009020724201d10381d124003203a070310665041c0a0381d81d80405a0314074403010754000031000e110980c180c019000c10940c07080310303a02c0d01c4111880c56a012440c5032040201140c1c42c07001e0382170303031004440c80c000c12521090154014001d402c00320351182c0882d9000080600102205001070301c4468031751050200031205640f10050400c10940c1000c0c000041c50701c03025000d605460417802ca00d8485144040003000c041d40055040081da002c0d905462102c04094030854035118001e5074541d444030192818070140c81016950300003488110100c50030b015403c409449400c2c5040200100d62901406007502c00c0d450307400b12107200701c00c8072000745500e000d00300524152441c1404e210403a1500c0d00f019014650400000e2000d29903030040d001190100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 941167194 1250 941165944 941165993
    0x1d0115050d060b0d2027100809010507020a0b0f090a02100518010e131e0e010209090a0b01021e03071208070f0201060807030b0a020705030307020601090c1815090e191503 75
    0x411690b05031b2440c0308689a03005900348550701006612812161203440c05100030005600c4094090340d5030504164010094200500001d12407501c0c28421900a020107040350703504082c950010340c50802000c130140014201090007050130180041031100d600c0300382840c138a0340a81001041e40c0340300100c40010040c1e01c403141c2070501600c040c42040954036400c000c004406101c02c20794040e62001e6010382c0725003058404155a01030510079440804016001048460118003410280a503d500606054001807100d500820200440d40c9400501c59030b6070f0006290040c17002d802c8800840c6c52008681c0f4110060001407000101c003420350707803c4065220640d40b201c4500005c3e01c11544020030501002c0140300f00c4a0300020078906039541c00d542881010302210045610910721000300035000035040007040010082c003200610523a081c64491120380d25008212100c640603142000e072040b83c4900282c0c4000c2a114021104510050140301c55185489018000c00700d8401882c04586 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 941168444 1250 941167194 941167237
    0xd142508040218091c0e2706090a02090405180105090c0102031e0403051c1403060303090609040e060f060f091005220510030201091d0115050d060b0d20 67
    0x2c006621020484200d0103550001040e4024408407600b020036020b05001f2040b03542a62245040303024080c1c02c410075200541c3c480c0108511140003a01c021040c0d0342c00c03c21051503407154002c440c8551251080c0c0180036850170715840c2120740041070050380e03801140000c50143c2e404030480392502082c100002c0d455030440204061840365910040043c410405007100d8150044801e0401481545070000c0a001da1440c50119100c02c40310303d45d03d60020004090280360290142401c284003600000b00d0208106480380750400980f1344850a420080810034107184c16150038034100c00c03d442d11502c6003020340c000302c8401e000e80501072054007041c2c4d040d8050340400055420b0081b006c1024022400d08800c1440425154003043e1f000904807800468011001c50404110640400481d01c0c107a01e854100000581c55003001030411804004919100300da0740034400140002d40c241c19030f16a60030b2030b1502100c02a400ca00d907461511040001441903203015a10500303880401c0c03070050103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 941169694 1250 941168444 941168461
    0x30f0411040e0a140f030a0c03120f020d1a030309030a020f12060a05070311070809040c050408070308210906040803070210020d020d061a0405060d142508040218 71
    0x1100b10340889248110500b51050005041030840302125000c1030380c2d01c103c440c022032900d910601074080041b854445404001070300c26103c61782c5280d030130781e4002103002c00c0d521044283c0e8444840074040320380722545404520f180740c02e111030995046005614000041c1c022035183c244103803010f8403070f4400e020642120788402d800500415880c1e01aa4a245091a0020300600d402e55507200001e28040c0013090040400040350746942e04802c0040c2001414820000030b09881640c000c1000018031000072108c40801c40f0350041e6100c0e00120f43c40b04225800c00f040a61195807020842c1103040c14418864000b00d40c4681241c1c2000000d680c03551020026880e0250150292132410700c0014506184440c55003c0c000d074018008080c800e50f9940c001007501e404480102c8201c01d04100b00400c99864280018882d03507076031010126030455010740305040040304542c800868010300765030004421001e00900c01c04a11420400e90605050700421480a680d200c201c00303c00030300e0302007103480e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 941170944 1250 941169694 941169701
    0x30318060304150908040e2d1302100c0510091208180601060306051002010c02060a02130b030907290307110a06050108030c15131205040e0c130902030f041104 70
    0x301a14806014040d00741c540a401c5610074400c0307c945a810302e01150b04802e41040c28040e02c541203290042803100c51741c400c1103407134018254594050400c0c0381040140c0703456194180042242e120006035021908100b400d0070b1201c246070340441d24150654000648100c0d203001000380c1881c1940b0140d59250600ea02c508000c0441900c62080d03100002d10550b254120009484003582d480000500307043c81a42690800c492481c0075170001c900107824104103902078020108076240305407503140d41e420160354507070041e00d02080c586c00c120010301008100b44000d240c1e0701405640d106400d46d4800d913503d054040030b0100c00c104440200c2488030f0920400c01d480c0e25503007040c0c040095517500c4000c1d0780e5903488508040707124081c3c441e803101112b42e0b14503601d101c2c0f50004001e840501c03907640c035462100b40382d040715800c0c443c040c007011034482d86c0e010440c0c4c8282c8049511540d2103c0c1221000119012a03011044c00d500401c01c000c1c01d8041203940ca6000340c0e12540180c02d8060100014000c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 941172194 1250 941170944 941170973
    0xb1e03070e0c07060e060421090e1905180307020f040e030a0207090f180f170d0501030309090c0f0c050f0a0609020f031c1404090903030b010905030318060304 70
    0x1050309800d0204a252100080c03010f41d10600b01000820428061309481d1401110040e28102590505d141415032484040340c08031b103e41b03000c1100341c0d12207014620103070064425004854243d10050b118445034400e65401046c004490702d440c0c0c001600b1580d90740328007000203004050030400c0e501540c580d500501da00c282c1d10b20a4903107a0086c0b640080d0b80e440d13240720704c004481c2031191101424405110780c0c070311542320719000d650307039407a903100c202141640680440300c480c0c40d038107142c6034031340c03244003070302c0640711014010445500d0340c03d00520400c081d810000500b0b00c0d1207044000ca80d04085400207406031802d000114600701d051950402d00d51036158012406103141e00f004014666204070352841c421501c03041030852002c281a50340302c0444a030b0a0109610b90b82d034103014020040540032030540c4843c01c3c0b80c291601c03a444192035007070300e00310082500c4035401285582c1054000014240030740041d070419980c9603480d401014030320305039806000e00001141c10320441c488040003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 941173444 1250 941172194 941172209
    0x6030206070629130e030d090c08150c0a0e030a0b07020a1506080a1b080d120f0c020d1103041a070b070c080f0a11100501090b03010b1e0307 62
    0x21079038030a060000141440c0702280c07203807810211221824001000719240c0005000e001444c2005034040000300600520910352020710040c0501e02242e1014090744c20380c1e40c41981d08079450b03450060704600c0d00d80c8448030800c0d10b2003054100070100c10a081650440741481c42c1c4840f41000030700c0441d00341000d02c02c2c05405003003a00204414207800183c0500c950344100103440f5100340034080f40c4201c41c0070340a20724551b0814502c240c081910a845030310204103c1611404c410307910301c100d518143e40100c0341d9000c955207200032081001a446070007002d2100346c0090284c6040705000075200c0e80c4200e110401d2290811404102107410010b550103803071400600d580b81c0034042d585034800c1e00b20322000c6030b40031941c03c009a103081c81842a0000c1c9540700031180d0038030320b0aa0102480d40c02c03034008202040709403052070800304010002030030040c010501c00201541025007803030944c0c0454a10600a0303042668820494851110000c80c40000c00c001c8900503032000002400c0c4400355100b1030303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 941174694 1250 941173444 941173447
    0x301050a02180d110d14010f0c14130302090c130e0103140a051504020d02090a0b010f020a03020c12151006030c3204080109060501030b07090b0a0e0406030206 70
    0x250310149640141100b6258941065000b20071800b0007181c00e00ca104018034001e90070341540034504020541c40707203181c07040e481c00c0724607400840c11b9030031030b00d111400c0c048007a10754000c050865001a05d0f03824072941c05104030b160607070240d04806809103510009000d44035040010f181c904030a815200003d9000071031224080c2c0d15400ea00d40750000f804241c1e20310b60348284801007040001000c5800c603078048007030310701e40c039041d21050076440d00148141d070005075400c9074070300581d1188495882101a08800207805070490001403000c800c400070300055600407c80140403940000d052646808111007603501d10628903100741c14880300303101c08105060b2800900803060480c010506c03d035210b9070750401c42e109034180300710303200409100004000c40c080f00314800d004135142d00c1002e42ea07180c004403518041d602c480580c215901400141d0761107030b0350301c01842080f101c40c5045030006042d14010307600d21f0602e2140a024890300900b1014044141050310380d076103640d0440001581c0041516 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 941175944 1250 941174694 941174701
    0x41b080c250c0801091e05210307081b0414210d03050c030f0103020f040621021f0203030f07021c03050405011803121104090f02040e0903070f060504020f030105 71
    0x1c90740c5445801c00c5030b090510403800b0a003c8014450308000d01e42002c80076030a0856241c40b503403648200d100030b40c0c1a02540c07040e105440c4401041300f40701082c10908030769a140422004007000f4020b0100d0001f241c20300c4d100382c104c0b86082d09440030b5405102d14001a81140c0e4001a2292500305080080480182910180c1c41005c580d103104080c90b910180016642d00c2201d50407481b0440700c4d000e5060b044801800076080010300c08803052780180001903c00e44a960241c52008918050700508100c05014006c40c100340a81100c3c1c811950048118142c44220294403800014004030340344002c071002841c958070130001c034058041e0280e4529580e02070720034001e001d4070084a00350f03415820304102d000d0f40b20740310500501c126050358036443c20000c0d0b5200d00d000380081011401000a00307000102d0300300c9242c0301c6c010202101800050ba100c0c58140703d41050364004100180c184c01c28419500403418222001e00d015030301860014850707a441c8001a040c0e0325403501c0c250150310304400c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 941177194 1250 941175944 941175997
    0x140903030103121e0804030320090a0611060106030216060509030d1b02120d0e07080309040b0d1a0c160b0105030c0d2f0619080105041b080c 62
    0x10350680c1e009646020465940d040251582c40b002c0400d034002203d2111480540c038814503000f50820721138030b008941140c42400c0c0c6100181100308454031010001000d484626001451200425990030242d54039000400c00a4a540052103503130103042d00020f203100300141100c03092021680c080010001400e011403145ea694006100d0080051720740741d01c011001c1d201c0203a42c2d00c2042c01c0e90003890710707081c14850012583c001340c1c08030b0400da03250103c02c0d044031810302080e005094854011511090140c08000c19241107000040c01054640401030220380c0c0300c003030001c04007400644464a5100d880b10828544113181c05024039035103850b001d20411540d25900743c101c407400c034104c46811000c1c0c020001e0040d80403000a003050300d22103020490404075521a460501c1051003c10190358810100d54a0740c00f6450600404512003c00048241c001d40c5540c0509016034017000745a03880514072450103942e540907130900030a0000100c90902e544100c0d002e000304050482194410140c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 941178444 1250 941177194 941177197
    0x21e03010e0a020306030a020409060605030f252412020d0203090c0a05010f030b21030304120305221131020a3c0807080a110d0b04140903 61
    0x9480c90400c80e035400b0400280b01070003641d015003001000380500407a10f030700b0000203181d400b004440e15900c0360f400199030fa800344020b42031300002c2006083d080c10b842c3c514000303001161950b2a80040700b01c5080c007021100310342c0280c00d0b00848003e1404501034440644104481580703200a480c00041c1050300b14100c0e801031401941c1c40310442c6c01c040000c408106801c00207000d407600040040e90800c00203442604144122403018048166004880030001e011101398110b10410743d0000040c802040900e1950161040c1245130801081c05d207880034200f02d840c00800c12904944841d404014000c000c8500e0b0420040203214006500149500d980003400400004601a000500d4040003400d140200ea1800b40350380d13601c01c0181c035070310a200c0c0c10072000d4464048400c10f2124101d41980300b500124041d80f00e0381c50300d03280c81c0341400d0010220314009024180c02803e0094912180c51100180c036200030f05007202141102e039100214004140c407031015085104403c0c240419040c0120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 941179694 1250 941178444 941178449
    0x3030f18012405010f0201090210140904020409020703110c090103060c021501080f070f0e0115020a120309110d0b0f15060412332304380604090501021e0301 69
    0x80707417107120104000c2c09a00b2180f180030081e4208021442045940c0e10401f182d80701ca18080c100369041000d40030103e0103d030801e030425110140c2c00140c1c5820b1541154101003181c600500504a540e50040403440c540341c1803100810460312a5038114940d8001d1240b0304c6120481c8254110300e42e9640040d9a07141000c00e4055584c1c01004000300704840c07003040410954050700300da000164605460401c40c0ea51b136880060450003108004400260642c4101d03001d0f141035507010a21041c070b414018203242042520a20607030700c92032040c00081804001c02d5110030314035108c0000741ea541000591300e1809100c6a43e00110005000c03941e0240b28054881d480e010780c4180001c001c140010b51911240000c0039100e0150810340301180e40500e03001401c020300360180040c03640441d0740c25044652000c0c2c404841c14010070707940100d29048030340540c150144440d448904100c540d070090140f5580640034901442c2c44014241c1404425012a08410400744082d001247c00407401e030204d800c02e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941180944 1250 941179694 941179697
    0x201051333050c03090609040908030403050405100c0f030e03160e09010b101e0306030c080c031c0f081321080105240a110d031a0303030f1801240501 66
    0x100245041e648650165180c0d02041401140f50008100c10449550402c071410703944561105100340001d022500034600841c8291600d60b2620b0400c0e040000b42c4484040c1d0004010120040c08089442400204c0d0101c1d01400c02111104d15440800e0406042031070032404900510130006110444140451140da4001c0081003e04a05410441c0b8111820700c0c03134000508030001c00240b03440582452246501500300018500e0341c995070042e620410354055115500420380344000d40c1010f00048060041034141c0107592001014045c0045080da00b460b0200012000010b0701711440383c880441458202141c40c00341c002c03c800c40402c0c1085403240100040d521000044ca41c24458110041054103245420314000c0342c644c1c142c00c640140c00103000b0440e0040d0b5802040c0b0040c0070000b500049a80c002c9110114600300410207011340040a010350b0080040007540c1e119000859004135594002d054642101c85055024040003080d4103109900a4500301300d60050212200c00ca0750203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941182194 1250 941180944 941181029
    0x50c03250905060f132904180335040c030c0b0c0a030e0402160c08070e0130151b02030a02070501050c0f12121303050702010513 57
    0x156000034064950076a0f6644d000440c9040d298a185008030300350504d80d4017000f0001c0c100f0f9901030000704038203140e203e001c5000080fa00c88003050504e070241c00c04a990000c0c1200c20b00318240d4005055030482c45032041c80f41064500b500c50501d40b0081c25081c950200e087c410a400d080c10115491100380c48100d0307900318000000640130814106a07110b403803140c0d001e80402011528142ca00c035610f00040781d8015400c002c02928805010000c110b118018012091710a007841c045915091164005801c0104401c004001c42a0b0701c80301900d240381c0d40620030481d9108002c00a5901540c081c00500318000395841001246403076000890341c0b02003600c611a2510b4400c403d81c0c5a21070000d5400040e04500b034113110b0f55000b08001c01c41100940308440e144401001513034105010001104408200007504d16a801e110102060704910041c007060f003148004e5901130814400d0440090503c9008036810107040d00d82034118000b000b0706084540150025072081d601090524541c80080c0b80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941183444 1250 941182194 941182199
    0x2040906060c0308160306030209040f17090f0f010c0f08030f15090a2d050f0108011e23040f03080703180f02030a2f01020105061c050c0325 62
    0x1284086030380c143e41545400b0403548415049103803c80d54542040306140c1c880301c0000060711014803040c032450107000726a8414055207018048100420002010b40c40c0c14401c11034281e131402000110914102c94000c0c03103410001c0166607000c086e02010300806a020034403414070070242c0007144115003428100300f0035511540c2110151440316a0303260452103400000300f030711059034898602c1900d52110182880001601d04103c070702401441403c2c00d071240c0501114210b141c41c8240907101100092091818215880c0c4d0504e002e007103203107501c649414040c0e82070040015022003503111081c002d412454181080340f000c440c49134080f0005a45800050745851103032052491140100d441850400115110307485841034030302d0241d17414011400a20001503450920090a15680020309010641c100d030413254032256120303903410769041c041080740a580b048103e030400c1c18000c0c0307003140c1c0e00c801d414814a4a407200591607090320808180c90120007510510022440381008070868554 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941184694 1250 941183444 941183447
    0xc0e2d0103080409020d0603060c090608010b0909160918020901021510090207020616060510060c08030a020c150406020912070f053313060e0109050f0f0d060204090606 74
    0x42444081c280000901c000e101e040425001486403601c41c80c1b000c65416243e4440c0021181c59a8100e0085074800c0740030401560030008540c010b1821002c00760800d05090041940720100626246446081e04000344101f80601345510190490b0034a40d0f042c074803c5141c040c0250b10a0000c103015119800320107210103003080d02640301c0c03507041201c1030001d8940000c000181d040008200c0e40250706200b41810038102035500d000b040c0c0200b10100b10790401c11200b0365442c100750030250400a00d030245001080256007140c0e08401104001a51f54041140103810041d0070b0030780110f005500c0c404d000500c1a59000342c9195801100d0043c00b8000d0701480c10780d135481d42d1044081201c048901000b145c42e14180b00c2003001032650818003011800d0072482d030b00000640706044000c0002c6511911310126041c2e2030040c00722030820b595842c03101000038210f415944105071240f04001002c14640d100e5444084001001500e4140c64941628100b00a50047d0003000c0f81d003450a000020080e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941185944 1250 941184694 941184781
    0x613111503360d0318081303032303040f1a0a14070e0a0b0a0e060a09031b06082a0a0309050c0609010c11040b060c060a0b100905010503040c0e 63
    0x25100d0b10010700401e00014410303006410b004000c9031854000d080c1020204002000030462555214403102003582503140140454842510110b15044c06914142039500184100e03500280c00c8240040bc1061500d04000c4220b40b003489020903480e80e40511010306603c1d00001140090007080c42c0b82981d4011045442e6050709003020752090740380404200704d9092400504030040a881d11f42081c080b010302144040e80031300f400200160f00c11400b04207110b403c0146510481e80f03202d040000340d00e4a80c00900428001c1c0400013049803940c808604081d582160605141225a0303c686582c01d151001e0300a0810003425140d1380990b90b100c05282ca071810883e04103843c141c58003104803c094440d00c504401a55105400554400020076030350781d0400a041048000b000800c003a140c00c14401c2c00f42c0c0d80502060740964008680700140c01c0d040180d2506544007817070010340f03070380e558141800201030302d500c40e00c2901d10b100c06201c0700007100541d100f0403280054001c8180040601d44000300d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941187050 1106 941185944 941186041
    0x90a0b03070311070c0b0d09051b0a05040c080f0c0d0609020403140604020a050f0d06051303110d0915031b050c0705030613111503 58
    0x52a038103006007503040f40400400c1c4d0a254081d5108001980380380950090705a0109130407900140e01d910581c8150740210444040801c83c0402034a2904003903d1940120f50920001c1400e0030036014500f08541903648041065613880390b00c0503003000240c074014003a4810000c2e00b02082d010b0058501404c0e02030303c01030340d403803440c64103210983c10007110381c181c2e411090400c800760f1388440c90001107400c00c0d916480c02c800c0200005814059011005100628040a1210b04280b0095030030015210741c9580c40612840c02209031b480d4035484492002981030300c41800101b6a480750130f88403000350b05010032402441c2d140382c03900c00301c481100300020350040fa14040304581007000c200180f000b60040c00c0c1078249071096110103409800043e00090b021410188644c41346801072602152003130041e5100d003011050421065000c6001c40c40058580c1801e109940c0f46080d86c120 = true := by decide +kernel

theorem cover : BRFrame.Cov 941007194 941187050 := by
  have h0 := BRFrame.cov_init 941007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941007194 ≤ n) (h2 : n < 941187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
