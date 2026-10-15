-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:43:47.313651+00:00
-- url     : https://prove2.me/submissions/17c89957-0124-4c7c-9242-1e0d89811bf4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916187050 ≤ n < 916366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916188300 1250 916187050 916187057
    0x9010c05030903030a170f1501050c100f0c080c16020d0302010f110c010c1404090b190b190207050102030702010c1a070f02160503030a030506031014070e09040209010e07 75
    0x141542e0302c0c1000074114208481d2105640500406c1d1280c03c0150018802000441303050f042c400940d41d09500507000a1081c41d24668a0010f602418540b448401040300e1843c81e1030510003c00100c0c0c1e010424400d50340e69890300070748450701c0b201c3c41030048803400703942d44070207a0980d001442c040c800ea1070308500c02c0c000803500d0a000103d5400700e40074080070403100b5500088402c4258020f111b8140070504605121500508171132911219004078040c0d441c049131341e9605800c1aa0751030442800681e9086580c0013a25100d4265001a41255118502e24081500c110045a0001c54030409070fa0f010f034001d50503c0398071f40044400130307120541070340c0f000e0b900d040303c0001701e00342c4188510540303041d29800728241071081d000346413840260014803501140c10050156603004070440d4010b02035071901003104c0c0c60700030001e414090080482800d0520f444048464280c000d4502403088090381c84100741044440700340202c03050704032002580110848014080d0f010014600d0390031185514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916189550 1250 916188300 916188307
    0x26070e0a081b0103290a0305070803190f1d04060801020f0a020f060903070f1103030c0607120605180403050408060a060e07170a05040303020c030c060f09120d020a020c13020d050c030c09010c0503 86
    0x80b2158201024ac1e002144150000079001034801c0070304d2012a20b008240c42c1180d07030212440070003080440a0a5010074101c3c100c0c3c040b64031555030303411000c09440c1c1032008664400d003105003a81c4513440a2004005406203014240040502241180c420346c00080a14076000251392400710300d40902c40102c50b49880740c200064151002c00142100e030781910020308803802e024101a0003e203101035023003001801c01c40c061000d521051403042440c0307805034400c0311584940c641035a2500568014960b41d112f28000c0111003002a0000d83c102d0720b6104800502d40c840c084121010091f010400307a4580000001c80c8140800307612455010303019140050400d500090b81e00d085030710803084454660712203028413105061405d4601c0e0040c411900600b6407846003447c80e0014060a040411107a6000c51101e20941c000d00a40f071024000400103074034110507034030240080d0468441c0c4e074a05454a000079001030b08210840b40100404d95103d800c010190004440e00f0341b560000320340900061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916190800 1250 916189550 916189553
    0x30709090612031805030703140f0628020a0509220c090801140411090a180b09010f0509070510030908121626070e0a081b0103290a03 59
    0x9110300009425541d0442c11500c805041c010030400b19241040b100e12956041003255039030008a190403603a01058180428442d0704000341008072510081101e40110f8081048004206100c00a65800d540203010317442d210060280481c01214050000f0a030208848a514504070800101048902203040e102d0391700703104401700f40c0e0344104500d40400c240d0082448164820701a029010b4024140301009150513114220310074503140c0c0e000e0040a11501090311403030700703402c0a0315024650b0310b000b13a46600d501d80242e1840b421034802c19907510b070a07402c442c003812038002e80b4014000d86004011542c1031004001180c000d01c1054000e0684d1410360303d00155402001d401a10301440d0440d1032881d2150480000d82c6482511070104080e0552151443c85803040a0084004051907008507a03141e05050300d10100306d0300815480004140d002441c3d81001035800d2020440c004403000d00794803d001034044e10000d096800000341c0c1403040015006400e1001c0c245d0490040403404241d86d20b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916192050 1250 916190800 916190819
    0xb0c03060f090a02280f0302030c040521030c06042a0b0f0d0f020703031b0503011e0b0d062412020c1c020a0201030b0105030903090d080d020c070e0a0204150302030709 74
    0x1030702c4480c0074050881c0002c95105ea00002225a000c0e0242400c0d0702d50714103d40000064030850241d01c2c0b02d183c900840c030750010000303004000041c5d07504040329602d81ea84455245d55010480341111341c0c2c1d480c0c200b644030454441c0c142030300410348442c0c902c0307400741020303107010350b5400844401c41070381b4080c00a00440e001c02d00515910b0900100c006943c5c4d8154200202a00c06007502101c0c1c00c0b2071001d041148039071000440741151780e404500e111083c1031031003a00811015502c2204035410200310b0100003009a417200080700c043c6d10800b407022a48101c909540e180ca510f01c20080b855a0f0685100c004481e0003c0c94071011100030340d6040d4100042d103040d10303c0410809001a40700c0f000850071540c00d03200d07120110909003005411403030301e10b01c419664450602100e00400801003034a080051072800c0d44c444006544043d910340620503070742c1c1d6944845203d0005e00d03185400c0401e407000018822607055400e030035203e41150f60214400da002c2e40c0068003020401030500d00c0012040324 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916193300 1250 916192050 916192087
    0xa0c0c0f4b05030d020d020a15140a0b040b0301060803160507080303010e0a05060d0f03030b040b040f090c12020f0907090e04150e010e281505040b0c03060f090a02 72
    0xc0141580701142d0414040c1031a041c19a45103105660000d842e100303803150006a12041142c2c130455811140341c41113081d20141011080c2070404d00c502600b40841d28100e0b40040914402c00c0d5400c014852444080600380e542610070303004183c108000000b42154100101d9108030f02640844d0010380e6560925891580240c0c0300400c44160340c0b0610009417400d0140c1c80d00114100e4800782c101030705465811f51211207440040501d030f590340d004001c64449800c40c501e5040000d204102c41c8220a000502416864504913942c15191802154110380080c1c404141c0307802a20400030040d490081c0018104050524000c3c0140d240c80040d8030662060a41d00c11b61183c000409403402c3c0311120016940718040414041e414001c540341c402e0000282141c96100e140c90070102202c0200b041d41e20001c85410140c03403e440b401809110001c141c1010b0700403031191a80781c10130760311002a40100e0009603660313070340300030146006a1207262100c00c8507000f0144030340042c41d2011078504481c0521 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916194550 1250 916193300 916193429
    0x3082d030708071805010933020106080d08041703100308030405101406090403080a0605130209030706140a0c03030e1902010210090305190c05030a0c0c0f 68
    0x1002d14082080e0280e12003460800038409590542d10103060000203010320700d0314010f1450b450341c2004580600c110300e4902420100c03402c50850742031201500e000f40600050300071074500384500764502c544188140006446203400c01141c110600785404007180641c0040c0c014080a41e5516010010a6000000f14061f038031810080c50b11401c0548180c060b1042c0c002140c8040d000c2c07100300401d5031540039005502035454a402107155841c1100310008080503040242c001081c81002109602d03646c0c014601804103c0489918903075890080340c1c40011480302102c200814450a103010703029465409025119040100308074800a03941482e25038a96810044d0815034582c0c0030965070140f01082d00c00c1898001445881c40f25117014160f0301c640071138009100081e88160404511820142c03610b030741d004003941d5a425400d18010315040725002e081d0750f03007aa92100083c0151400d824081151402908080e0280c0180c00440c411180b055180c0142036610965142c0d8a40000544c503805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916195800 1250 916194550 916194557
    0x11010903122604030e0405070207080a081c020306030703120e1302071109090a0f050f06010b0406030509010213140a03060615081608060d0c0801050c0a120603082d0307 74
    0x2801c1c1d00c60480c10705414031030342c841198040c04046903200c8412906903005a0300443c241c0c440c000101d00e1702800303034007003d0300340941d0390b01071704102c0d04000800c405801261940340b03074030010200c40200c0c44107840740c3d54198048201080054623002445544103042c0c2050265402e035440440c200d04001c0303203088a810750000d014800c01c00c42c10220101038009482c9544076103840f03007483d0355541111001a292184105a18080000c20013414040c4081d0381c06480855a5804902d099600180a0280030908100000701644014070a8500120240019800407840d001000115410300c4003000d0308003680ca41d0110100c0c019008481c0101641815968071030710341e01c002004414054885800310301c4481c00b8030041030b4041c1355190402d0003101d0079500d802640c03070540b4480c01594082004c5508100820005008030b501801c1028181d85900c01a07030310f4051003508a8130745000c020328040c41032010b0a0001d0303ca10156a03841d07180540d0030305526501d120003101c0d410840c0d450001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916197050 1250 916195800 916195817
    0xe1219030b060f0d3c021b030a020607140304060203070c0212101404051e0a0b0106020109120f08150303070203010510090605030a0507050f010504170a030810050108041101090312 79
    0xd501240c4985482d0762815048400c40da41d0348102c1c0854000c06000ea41c0c84070440c0e4042e409a0b41d5176038111100c44a03007201915060520441c116200d410000e0200054001e41c40000c454a00442c441034204000d004010b00d5a996556010003e4101800107000c0003400c035082801a1110074614960304d21000042900c1740e00049580d094816035031881d04981a04c2040c040080c20029518122080780c855210011100325602c61421400e607102404801c101c000001b40c494066120f074012600601840c00310069105e01524400c2d0294445000155040300183d50206074030b11603124207400a01b44d03071422000d600042c2c00e48a091b01c07a01c1070811014410000000b07248101401072074180c0140c00c0e0170a40303841c2c061300c0b081c15209090189290501c2d14010341c0c801d000b21000303030600d10700803007080300012030380385d41c5103003c401c110f001c245582c020900f104140c03a80e2a0448405a44503160390303641d96918504070f132588107801e050112004011000401094060307000f004250740310900e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916198300 1250 916197050 916197067
    0x3030501140f03070b2119180209060108071803051605030a0503040e0c040f090f050a050105101b12180b03070503010311130e0a060e1219030b060f 65
    0x34544040345861140344202d00c242001d440100d0200b08035661074041c507440e0000c0034024880c0c00c82e0411543c49144e045820807400741803105000718560000707101001200d54001c04140140d18840010394810b1718200040e12562081d0001e690101880c9044000003440f5400e007015050660400c880c030f5040442681c0002d0040880c0b10003c01e4100c00601e071010740b40d151903849100c2c5014010040c84e881c00000c407603a9110003113178000c10500d20701c10111580c601d02c4000500c0a4060010054185404244c80c0201402402c0c141d55005001601c82a4071401c01e40c2d1440d01040c036441c400e490b9034504404101d82c20440302000d038098480303032440c503840c241c0101841025003012100e0842070080c4603889034002d050707905507680590342ca501031540380e000030103420b0b4211088a003542070010b104801c3c8004900000301a100e420144a10002ca00f400d503103c00c004580c03100c00000a10030301485031004800901c07032421078180024a158110081031156008501603203210304001460407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916199550 1250 916198300 916198319
    0x70f0605190b0a152d0906020c0910060516060504121107030302150402010e120309040605060909060d030c05060f2e093308240c13050d03030501 64
    0x20800602201c0f2511081e0808140e031391380503004102c000c2040304400400070a0081c1e60a95000001d603040d1072008425200d50080241c0e0f5039006a1006003d070107480413071402c1c0b40c42c031140518401090440c83d90b041640446240e00270140054003402c2c52100d14001c180d90b0b00c141801180590007040080b0101a0701500411810b0b4000c0503a61000c581007020035070202e020ba1555080300d0b0440b045449500040f254001c4103400030f0f85c4402518081c007101c943c000014275681c1026a070a10043d6601e9081080303902414030065002550350700043c55501d00940300c0031682d8030a0410100b10703019916028a4600129025503021810b101441003100d65412a000540f0b5054602402c0854140070415071440912800c01000e403501d508814143c8060200b11840103074503068810304817418000c07403014401d40704514650044410019080c0141100d16010710080300d16515652034040ca2455030754094600342c094485000c5010407207984a40d1405041800380d80c001c0740e654142078000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916200800 1250 916199550 916199561
    0xa0c240c0c031113020a030b01030c02241b1207020c0a150c020321090f0109060504060e0a05042c071503050405031b03070303200d02070f060519 64
    0x842885005459140000c103a01d003401c09403940700c400c042005894002051064040f14200308030f090010038840d014907855405100d005101740d03070500541c02101026078651181107007400c00300180a805940f06e10114902941103212040c0501c0f000f1030030003901065420100d0324290801d5050b0500414540c104080121400101c6502c52054685104414404e00001c9000305006641c005501950780500582051522040d541c0240c0000304049511660101c00c50743c0c8078003001014409503500c80d841003c03d454641d12a14505403c18000b41d402c8079003116030076030005802c01c001c14903484074041c0c0000400d40403120800c1101c4800992580368800e011050250721204c0c042048a6007220450708100060030002050303100c90601500794031440c404c0030071b100012100015030f010004011305289003e60340801140880c00c00008001200745000103d5460611603180e002006500901c09217110381d021001c403440541e01e642c141d034811101d285000c0c08000310041414101c3c05807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916202050 1250 916200800 916200869
    0x102130602100501141c02030715021002040305070b0c0705100c1e020901060e04090c060504080601081c0e0607121d0108091e190b1608060a0b03090a0c 67
    0xd204960600310b0320b00341d18007061080d40c40f5140e1b03501c104800c0741042d40035a00c5c20381c001d425603480320f803102010140340120340250001442643d44a0001c07203101c1c401d60341684d6000340900b03a43c80c544a006804c50300101111502c0380103c074000607007941c600040e0002d0303100c01d841d00c025500c0c2c00d082181d17824803001414004581742624400c01640c9140040781075035000e0403d01c2180303e036140454000c080c501c00080100b1500311010510703507004400383c0120b03403507842100c0301070380c031920540e03200c80305102c0081d24021506022030055001d0a103000b00c001e005000ea034200a240c0d11804d0b4410310249240020030300b07007144103a06002c049240080c2200c20709050040c0d00b0250940d6a9906e10340040581810010041d40c1d4040001c1c4108100000c100c0411007111109040070140e8171070a903003d00403483d6201007151040d00030030350f0500c030f10320081603100c4840c541100042e0a51009011071650b0041361508000500e8a51402c8080c0c20048c0c842c3c02c0308804e0500b540c0924484003003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916203300 1250 916202050 916202083
    0xf050a0e07091808031305250b0d111206040b01020c01020c0904050a05031206011704080a08150d050304090b0f0a15030f0f0c0e1c170c0102130602 65
    0x6003100311040010300002190341025000540d14007044540d01051202c00008006900c00030078850450119620f4602c01d5021300160740d0761040104108144000140900300091000f41c1c1c01c02c03002040002400e070000e005040410010b0024000c20595448111090110b41c00d12060180c2e900b03161240e40e0400d902800280901c1c402040041c0d035500362995264481d001c400001010044180815542180d2000171280c0380e21024449401121040316002d001444048580280038011002c6500a0750042c0000307240c1050a442206d0300103008100f000c0b24107030341040010700d84031813034900d0900340504041d40d02e80d03040000b814181d8044140c40c0c0d00c260032a02800f20301380c0c4d07016413020489010701c429102d21b0042220542c0a01410b1809244c03007440c10440001402250f004404070009660718649000940c204000442d6440040c4901c1d050141c9100070014074103540420302103042010650410341c400f00d9407401d81c0c2c4081c000c0f840c08403440e0030401646404100d200300c807030617001c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916204550 1250 916203300 916203311
    0x405150417032503270c03140a060e03070b010e13120203090a1e051201090c170606150f070606030b090a030f1b020f1311041805061e1203030702010f050a 68
    0x41c450002d540034103a101d08241250703001740d0100001e03e807121700103590100582c03001802c0c1c001c0710754407404d0020040d511141000c225244aa41c040100c0d0f10840c1e10556100c1300341d013030941e0f1855085004014280c841b4100c104440466011100c0b926607062550045a541c540307a800d01c04181d6443d4810601181068180001d0301d000c50f5442e020f641090700d1034400c420310845098090b02c2070110103000c6900c04400810355a240c0d0080040c075440c1001115042d450b10400d1251100821b0154090f8510a1100d910071140d21030050801070300441010480c0c0b501d0b500c542c03490041c15a150000c9074230080c01c480c10150446906102c241c018105190035000041b1902c7c01e603507011074002d100b2030f03000c10800016aa401c1c20300b450410742c134400b001003601c000074400d51548540243c0091000c01160903071701c20340d1409817a22980001d4034104000200004070884100c07044603007a400040840c086c44180010400345218003519400403841d00c25403a0b20008031100500790701e0b407890411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916205800 1250 916204550 916204571
    0xc04090e010b0f090c2503140307120e160e0411100210090c0e16030501140d0b0901330f08031b07080f03180103050405150417032503 59
    0x19032030b840700e04400341c4c0c0c01e1943e40d44007020480700c1d11131010f07101084030251034202550304082d5103c0d20001d12071303241c40400041c020449445400101c0703040d400140c3c520500806043c07160040041c9034a11000c80b110070646c0020f00380403190603088203100488075002c2100340660000d0349580460281c5035240070313941c0000001e4481460ba15002c6545464003090800c2244d50341c0298020007014065101605201130204140d915011500780021300307210000c05c81d01010214000600002080301001c04c0030750742d4121a8140060021545540c0c0d29074008000c0d2401d111802d6004089a0802120b40021000f00043c03d540c1c1040048141d50b4400b4040c8110000860b03c800c1c40c8040d401c0b9942c90412000d514080164000000c507014190966440000000107813888070451141c050110754440011401c4402c116400b03040c40d4010085400d03150040f81125800c1030180b5185603d41092081c0f00b03166510954107a5060780810540384140d260ba040040c103449210704d81071111a402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916207050 1250 916205800 916205809
    0x1290a03020d2414070906020102310b0301030f050106060f050d0207050705030f070f080d0e27040b041e03120b011701060e0306090706020a03051b060c04090e010b 72
    0x345200100044950800f580e600d201c403400c2c41c1056070211000b4001d00020740e05840c0c50b007030241c0c0c0f01400f251101a000c1407032030042c020754a03403038070880b1a10004028041c00403651883c03a4001c2030030b080a0900480d9400428000314042c0d4000c5540d00340d0040e481c9000c3d803c58071158084010032800010246000368080300300c41c80e94420794005629840c25044c550b003000c041d9404a903241c441c2811001303603c00042901421500200103030707211140d03a020307a40e8540c2020722050000408003c3d18401c90f00c1c2612901c01440103058080b01c080c40c1105803200ca448007650180c0d016405102004100a003501310004100f03540004040809650354010300102e00c0b18403c5542142c407589101d0159105240b0645600f0100b0326117111965078000141c000089060034602900411000600c614400102d00046503401e03401850f0304400b64030116201e81004c0e541c0905545120394800005004028890050b103040da55150741e6407624082004449c041103040d400c60b41000101d42c0f05656 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916208300 1250 916207050 916207069
    0x70b070b0118021204031808010911060a17090a11040b0108061c02061b12030f012601140601030c110a02061b2b1d0112060801290a0302 60
    0x1c1d803a558408a0341c68071284042e02130f0b82e02e41403000f0302e80300402c0181644981c41c00f60443c0899100450341d521000031034280c0304003800190092400981c041d4541c01d141000b400030700000c1c40c000c1591000c1802009202030183c0e0507070801e03801495040d090242c46202d110b5055000c5804100d100c001600107400200018520343c807400c032980c155641c41088000311030324107900030500d59072a6009030714000403044861418189209149045400000000440340112550030301540a0307803030b202d14603004903518104a90041491404c03030303c102009015040001d108030007890801d2508000050803140788105002c2044520a0007480518011444c0a103054040d51902c0d45c40003030b150802c2007103040c2e440e030b03110a11455000980c0c502e2808008002d561180010701051082d24504441d01d83e80b800c0c81e652828a402007600256024081000742c559004001062160340d90108600310382c1054400442c4030f61800030b00203d119043c0c54610880c0048804112081c00c0d50085214040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916209550 1250 916208300 916208309
    0x5091807091d130206130b030103170a05070605040f080703021b0306010605070f0828030b04111b15010914010b04030b0106050f04030b010b1803010501030209070f170106080108070b070b01 83
    0x340d0700c00c0e070f00f429503e46034101c45480000c9004000c00d155100e1082c10254402d2005a582104100b040b06410380c800d81141c0003800c281d99a1814000c2c2516040010308000e0011513008214400100c00210008050b0a07101e000313402500f400c0c0e03032401c980b8a000500311280b910076000480148803890f004019503d00035009016000301d002c1c0d0b40b501401c10310075204e2411100e0b20458040010421982501e041072200340e4043c0461031082e0180000e07200340740d0f04903549031414440c4650250012200c0c141e850042021242c41030403466410345035501c00e81000b80c500f610350781000040c0b0302e5120a68010b190b2243da0078941844c68039219200f58040c01100c04001002a0ba00c230706811050a87d0080d5820450380c0b1104e507500e2940303050343e07405000310b034290f040040e10380d02991070103128841c12242c0207008a1701c103580e02d9a0499035007a0180e80d45c1c0a10480c40c0042c95800e4000d40300501a09450302c80c041c5ea03504140324645043c00c107902200c1c000c082001760b032000500088500d81140e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916210800 1250 916209550 916209571
    0xe010b09011a0c071e090221040206071a06040b03160312090812090103050a1b0311070f1a090d0f05090607080706050a06050604030c05060a05091807091d 68
    0x1041c1e898100040d02c264040621640b04d8008081101e001502800300070110001c440c0f04015a03402c06001603009007240c2c55070342e0703001d010581170600c0034543c01c0b94400c3c4010f0400e4904412503641e011034892400c607420b070b10380d080b10401c0424242442100d401d01001c400810030701052a82d10b031005242070000410b0b04c0707090003101d45038038001c18000024080d1a003c0d2036003010490b510768015045640c1e094002070803c000710314069600d11900c41c000303183e9840342008143c446000d8001c0c10404540020300b120070080f2801103001241c2d0b801200f4828800c0d140c01800395252840d00c96800307030103500c56402c0f0b00804814503400041465051400b400c013151038400400000d5101e001d0213101400c0131000090702003c0001682c0100c1c0310f40c59480c42000030644902c2806074502546c04001e00401c18100240041d20304030700500348038151460818945040320021401010030030320321019200395072050140781900000b1500c00380032052030341800c0e0110004145148203010b8001c4804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916212050 1250 916210800 916210829
    0xf06090603210918010806040b0601030209010c1101020309130f0e060f01150912050d0f0516061a0316061b03141308010203090304060905030304030809092212030e010b0901 76
    0xc0e2601e4421203041c0b0134807018400c103076a581c42c619403205021507044804052000000f91030b58080e10907100024070680d129600c2624980d540d14080d140850703487e06506c0b0034064404190b03503500d00d9120f450140d04010800003030305d452401c1581e080b08900c02c4e50303402c18820014921003241d0030f0350443e000309030140d81030070328840305481c0d00c0607540011030108100d00381d4400f48800060040d141d0002030780c07443c6803511f00000460f91070140d02c030070a80300555160007030085401504002004150501c0d10300c8001c556000081c43d040c0c540e200303d220100380710310821030b043e04510880a80280500c2c203160401c1c0b1994002c0001d00840c4181542c1e450205e00c80041120b01d101c1d11005e810030400855507070404001300703039807500030b0712494001954060000c40e032424040305440441b60702c610218101103400c410001c003c80001c28042c20309680c2c501d00c0031800760b2035069005450282e94480007140b28510001c041d01c200786e4000c0344d168104031402031561504480030f4110740300540515032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916213300 1250 916212050 916212067
    0x61810051e100e0c0702010e100f030b01110f01150f120f05160602060115020f060c07151a18060d0602090a03021e0a081203070f03090b0f0609060321 66
    0x3102c4540707810110101c1024010440012204001404118000d80b283c4002955941c1040b0214240d0340d4080c00150074015107034013072030098120884002050405050703c01048044a24205c26029081c0786a911a0000751000202a03c640d02800206000001d501d0a049080410721405440106512141a1454180a82400079018818804104010250f030f1218000d54800080c0100181044802683c4048600006907007010036002d1019100e5540c500c50b81200c50f810100b0180c0700d0341c0141065511069040c4521008090040790781559550700318144450113080702c0d8100c1081c45584140461340c0e485400024500e40d02c1540982c0d05c2120b180032811410f240e5100030341181d4111542c040305044114444924131064400d803620b1661a48219074a0035001000c40c120707101080400d5059110b1201107000b000d840c1408140b515080c0c1d070b68010103a0480f25501c00100000c1807242c2c52503c0750a10390040401c900070002215040e11034808050701d2622440742c408000760304c15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916214550 1250 916213300 916213321
    0xa0615020d180b030901050a0f02090f0f12100c080a0b1c0303270203240708060a1a07060b030f1002031e01030b15040507050a0f11061810051e 63
    0x503080f110350309600c904202c02024042c0005441c0030980509120868414104a01c280c840942000341074410b800c01403c01e000601218450503500f01080386200315a20804008804211501820000701000400401000088043d00da02d19072800d200e6242071940e0394100b00031090044540c070800502c0a460182c0080c0b04101040e6645181f503035410003101d09052034041124000d80c1542d000e154640c803985030014204041d0502e170f10190010072000c038422038020347d000c41d004d000d840304151180140d070402140c1c8580d51010900005588040100034050300401c1c14040d00142034070650030304015120309205d9141211250302100040c42500300082107e02c00e80c00d40d00c5c40f002d41d61681071861514030101c0d4249807081c401d650070b1403103007080e00c41e0700e01c03038001566043d08005d194241115115034000f441001c2105880c000c04103103405100d105c0c0034101c140071841c004090350901505010300328425440f00d034542001c10070782c0b07107464501031ba1030000c0c10381d86d20951756401c1c441d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916215800 1250 916214550 916214597
    0x807090312031a0901030206040b03040f0c09060302210303070f02010f02030a0c2003160f05011d011a1c0c1806090e0a051e0a08070b0a0615020d 64
    0x504541c0e00100c0d80c0c054290142d001401101500d420b012030a9104410310980d89030070b200081d00240c08000800c07114107014095a0484e10a04500b5001203039500c40625038126034000c00d0b5841c3d6610b6080046240c001500c0740002c07540c5c19400e00901340500b80c1510703404000c00b0641401049400c2d042454070130f40c0013144040501c44119201c0c10503000b0140181200c40200012400100b2884e0b100c24030700d07880b1440502c01e03400845ca41045180c024142d05110300040301e02c9580b08800d50006002806180044080c1407204100803100384582c07425111203e884c0c08031602401c01d102120707101d00c0018126255418400c0c5920035a42c43d01038124180b42e40094600110b000300b001501d09942c1100d000c0b05c828000c00e109002c903079541c40782c0710b0384c40c0c1c40014102c1e4010010901d031000f80074040301d88003c145041d03ca055031640c403000c0b00340d8000d42c01114002400b00402c420100d940c425800601039508000d2800a00f001010b07558408400c0308400707014010114070159009603c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916217050 1250 916215800 916215803
    0x2070e090a081305190803091e0303120f1003020d020f061e090102010b0a122a060203071203060b030106181205010e010c05131415070317070f050a08070903 69
    0x56552460495000d0101d010f540c000c485c0f08610480c407044d9190300e5103080c0d4050700c0106002c0d43c5404038007000c00c0043c0c0a0304000c20071100ba8032401828556050000d03116003000d112801065113002100c4d0b0b01d040c0c00c020100524101901024009a103502c00115109507042e18000c03220b0201c180059401d02546d05801c840300c0c031121040e844c510080004c0e02c5152f4007a002486101e13201000c0011015079406a83e00404c10251041d0100e034548002d00004200301402413400d42d514070700000c202ca26030b080a0090f03840000c08108200e070904000500090600c1c041201500341050700d1450b02c4113104005c00c02c1120303540741a101d4400c684410060000005407041410300e45042406040902d441101a520b0004020030706401141121a4903481c4013880c0e00741408d0051480c040d0309480c1072145c00040700f00aa0010515040c01041d041c0d002e912601d141c1c0d030440040791191240108001c0404c101030700804081e42c0c000d03050715107803c0142880e41e9a42d840300d0b0100c0f20019182d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916218300 1250 916217050 916217063
    0x10b040203071d0105121612050c070c090509030301060c140105101503110318010204080d0e100314040b060f090103080a172a0f03100e070e0102070e090a 68
    0x744840980c1007120180d83c1c40442001c4210040c103080107580500680d00352120b9078084000040021040e4524070404100d01e0801c0d007051000c0c15089011114229071022303d24070000f6011040c44000804040184440601030245203000c000150b01c901061141c01c0a200822003090100101e24440c41704182100e4000c05c00c0e4504001007094584c1c09200315044c06003100c42c49800d80307100b405104410404803011a00d151546400821009030020514415560910022a90300f030301b4044040d04808a50361002c0d100114000c2003062002e40362184203051130b0400d0300074203000b69240154804d40050000250f545d03444c020541c001d0200003c5940948944000320812800c5400b0b0704045007d0364410303100d02d0495010410044050b64800711202c070780c444e0101d038011107030a07001c03001254865590034007081c0a05079510350000d9680005241104100342b116450f2510ba482e4800741e203140c690080e08814002039220701684c000c00403400c0e180000900c01030410401040850760101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916219550 1250 916218300 916218307
    0xf0f070812040b04201809150a090302150433051f0611100203070201020423091e0f0a0605060f030f1e0a0c0e0a03030f030605060415030e010b0402 65
    0x380202c50f00604030f9084820305400682d0814021200d05000d26146020b400f4101400c500d2503005401540105107245a100e44050b8480340c035a00c070b1026016440c01c08020442790100d1030040d0400b10300c201f103a240009008101300c04540da0b07906110201100e0641090043c04650707600b040001103000c281d000c182481d06111004451a4100b401910801c0d40555815140c41c0100d40c0d007060700d903900c0764680c001a04010704c1c3c002070f03000b0341e000685400014600b9039112840424070204a64910702004d11181314042c80c1407069055910031180100300488200307040c2c0002070301c0800340c000c00c150300b000000036080d48820f42c080c401820008140545a90b0580d01c03d807459401100e10b9000210000041241075660301d0565a9800031201d50202c44e41d5107007101c00040210f116500e003000540a0312803022307101c00710b07e074014500a68524820501516010b410740b08564003450050f40100410800082c501c035201c0007051543c80e002c03819450903883c450152021050490f4080e2000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916220800 1250 916219550 916219553
    0x303021005010806090c2806050d1406011202090a1e0f080601060e01080714030f150a03030e150d06122307061115010303020d02010b03030f0f07081204 67
    0x164518503035450318000d100503030726841580d0f1135203410f035903a40c0030b42e0019505446615214030407424202d9082e0b44011001000c482d850020b100c5036002c1004a0030002e0185a0503550f4000c607031b200c1103c0c0080c8400c41c141040001e0540c0c400d217002d01070080c0c0c04243d00c40d03603503918400c0d50018420010071848040b80c003424560f904041e41f15403000c0d440500c000164585012035041d048985507101c1c549201480001076400200080140d0200726840c07a500f200304040718061360040c0300303264006041d8039164004906110010200c240704000803081007001075404070024042e00700503900150720b01c4030030340442d20324042e040401c1651383c204040403400c001c01403203c1500b41e001e00b140380201c06e00256070203034986800c0500c0145420200c002e00c0210b0048100a031031007a807500b00c686011500045880c68034081e041100140c008510b0a41c51a509008007064200210041c51a240c1d070f5a003050b07250b1160200c1c00c01119000300e15401400010320640740d00010000320050b80f481d00f03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916222050 1250 916220800 916220803
    0xc0d0504090f09020307061107030c14040b040905060a0c0918020a090f18020a050c0d0f080c090a170322051c0816080c10060311030f031606020f0301030302 69
    0x81c02407400403860500c0b01440da80c0b850003022150f90f005000340070090b0402e201100d4031716031041c100d00d00c4c2c460203c0010018040440d210018014101c56200c540641c60402040c0d41341002d00e648a64200301491022803008a075490b048480440300040c504a2143c050f07070400003030b5109285011006000c0e80e4880d4080d0001e044d500025a5040701031502c138000c0c3c510004860103601101c101400451480740c603580c0c0207040e818154145241030040f80583c0e1464000384500e44000580c802604443c00c50b0000c01c8650801c0321511840c0c100400c402c0420f46500b10b42c03180341c0ca080000b000c010794490082c4100c420f0744201940491816803001aa040500c41c54400c9a003e0044601174618200c00c0011242c489540318003007a1401c0c0864550650020103280144c664440c1000305011500c0e0130499044c061004980109940e0b24504140320300c000740e41881402500321075009a0124008001c0703031a188000c0c41200505051400d2000c001d01821074055180840040040b051580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916223300 1250 916222050 916222057
    0xc0607030b0a08162c18030d0c05091212071e050d1e0216031b1e030203010f1401030b1b07060605040509011406130e01020304060b10030c090b030c0c0d05 68
    0x10000040d0425005008201c007604400881701002844203101181028044002007441e024040d02124240030081c10300200320b9060341954004a000010101520b082802c0220514007041d40070700928003a0040580b82e030f124040000302048a188001e4210782851402c10b00030940000444581c0c045084010380a40d000c0c80c40080360b001d040400700e81151000501c254a000d40070344041410740740d07980711072400508801c488107501c40d910010800700b40311580c40215100c0401e40d426154914010b143c21584444030701e002c0181030113504e000744410f00d16154112503000c08000b200d07503120402d0201413807041c018642ca050000480000b8003000341c20642c255030b400c1710100469101c400d9400d00701d6050400c2410b800300443d001030440d00c1c01c0c881c0c03e035000e00b111101080703183d1071a10080c03c9078402c6030110340a83d030355551602c03c3d050981c2d44030910300f4a800c04200c0701841e900701400e4210b4503c03e408400d01c001001803040e14810055034010308007002150f400404100c0050f0a941 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916224550 1250 916223300 916223309
    0x9091a090a02030f0706211409010f060501030207081e0f030a0902090601050715050601031119080c0304052e1401030314120c0304060204031a010302040b060c0607030b0a0816 77
    0x81102070301302406101280403070454142d81c841920702c0303941340f55582030414900c0c91101000d039601107120400c03120700c483d01e103d042104000141307954040c4140782240d01075040107041610503c55100042c800e01c088070882c401517100b9421000c40013102c1e41042c400c1080b15243c1080200602c80581e0383c2c0e1700a403400501c2154424034554a50004645c0790007042800f80c03000e2046105990386454981c09160040d2040c500454601c4a44040f0b807015804001c44103488002d102c0e250b50001d03440804240c0000f0032a47d0681ba40c10725031250ba6075450380c1d074100440403207886410044200f9000130361141c4981008103008a03e240062803070740321024801540071900c2404409001c9540c00f046071500300384418501c07095100c100710280310f60801001240c8907542000040081402c160300d61404d906800e140c0400e540c1507205000603035001d0b500c0540560010f001e240b01001c40491040d5020710710340340000302e03000c0303020000340d030301d01c07581c1c000046405094500d10701c800450440800f0786 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916225800 1250 916224550 916224553
    0x4140a1206020c0c060903150403090f12060f060510080a140f1504051e1009090804061805130f11030a0c1103030106021f0e100902100e030709091a090a0203 69
    0x18204d24107005251080c030040c1c07641904101f1903040341c203040f0b80c16980c02900915000d4100c0ea100c0d05803015140c0c294200c3c01134011210610010448075005128015070041c00078032605242c240030a021948255900d0305021031000041c40c1040a540314900524001f101c0098908040b8409041c80c4420389032500845c1d0407a98500b840d0500d130081900903018549410190310104a8031800094080c0c05c62541c40004000080d4500b403e00448100358016400d81e5075039880e101b40030709030896503038820700d401511080030800da40e150b07036a070741c1144d60303510010548444c00c41100b00200045000703031404190120900070f0035000c03076001078201c145030340720390300e0020341c014980c0c0c0d59000034030841d0010b901c403a140c80e007074007421040707403401c8040502d000c9012002000b8250402e24221002200e040c0d03035840000c00c2d840c01425103a0040b00038140402c00301001e40100391105414068000b0315a240d60204081104402c925148252815104949418890201515403248001c264401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916227050 1250 916225800 916225813
    0xc122a0e0702070608011a1623060714030c09040606030b010207090905070b0901110601080105040c0504090c090e10020c06010306060b030c090103090212150a060f0b04140a1206020c 80
    0x1240d00010f800410796280d41c40e0020180c0c640150412120004001881411414840d441078001001d02d4008a035204500b115042000031007492400301119848203100d9011a00f030000264200c00b2a8141816a0340700d590b407a640e0096040c04c620441c070056421900c1c007003000440c03907459404090003034800d83c25030b2242d07070b9280e00b000d054907882000078141c0c2e0854807040000341b07014001017484000606040c085640c00c144010700303000c003da001c00f8059440340200300c01c00c0102d114003006883e0484040209000300d4803181214042c1303008018040daa03071903c803086801c0422001d80c01e0440340009550381c50036901d03110303243c200c2880100c032154100640840c1b81404102031328410085482c500741008907040c01100038242080b03059070007007405420355031201400d020141e03042000107892056400e05c5040401140d403194041c90f0403000610051014410380e01c00c4404440c4102c030304024102100000401001c1181d019400e1005070510720400c0003010b4015181e0103856030b094843e0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916228300 1250 916227050 916227061
    0x41b081501050c1509120c070801050711030d0b011404060e1002030c060a020304020103141e0606130506030405010608030a0915020304140d110907020f190c122a0e 72
    0x2c1d00d00803140c250b54103400c5074050303040300d00708580711942c08a5210100c516404d5802d2850074030358050a80e907070344c07504000e0040c800100e0034000c058100050b840c0c4407101265000440344c4a00800107551151a155507001295a101d516004a0101011007981c4d549a45600c00f40450b058030228038047c0b000c2c00c84881d80c4500100036600750343c6030f60003d018107503030307246081009506c0103000700c0c18540c0c0c49054041e41030503030440f00d1142502c01041e080c4000301410203004110024201c074810881000311510b6032112041c0d0b5001c64800303440440e203945071440c0c51405000c0c1604003000d0303484041000d9031f05a82c4400c0d48011122401c01000420703c8170300f000ca880f4401c07401411000e0207400004203603400d0600c1040c2c94103000c0c540d103035140303004000001c101e0b41040d83c1c800010307800074500040f0500107000e0f0542c24130358640c00065001c3c4594031610f0368003581c801d059203051a02c48400910520416059005640980154403150031002045034103d06c0c0c01000c8152411000096 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916229550 1250 916228300 916228307
    0x409051e070302310e071214090c0a0503030f180d06090c0902130e070309050a0c05191a0a020313030c1a030603120a05040308161a010e070e041b081501 67
    0x200301d65080101d10704d201d09040d2060600c9802500910070040c59048040e40482e0600c00c6560900950351548040d08040b01c9884c43c003618068600d124540d1524204929600081200c03116030030100360b1078075003050b40c201800244d428481150485804001c06080000c3c603484048520b1140b1944d10440340c9400c5040708902603202c2134030038442d0604050000d03d00e1144030300c0d03000080749004500e40c2166551746d410140f07000b9040f41c82e611508818800392820004851001485241c210710092401e5038a108136a41d00c00400d0300d26100144054075103100784111203000c2c1c05010300054140c1c0d68604582804450700c14400881040c44140304040c3d511801c4034002c400c024003c0204d11498800003c569005500d100103110040100000143c40940541401918243c40c0c3c3c1c7c03081d00c0750402c4070941d210030002c0d60b444803d000051041c8181e80701d441c1e80003007140c680304480b030207000c0104000303000d807a10300485a18500c1d911601305a10510b900e200740707600e0042c0440c0394824030054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916230800 1250 916229550 916229617
    0xa020124030b060a0504020a030f0b03030a05070f0c0302090709051503070e0f0316060815040c020a0602030604090816050706030e122d0c06070e060409051e070302 72
    0x11508540140040022410035107000e6080303c00200110106607031800000c040703a11401030000440c1d00c8020040c00d0300c20910070b1810f20003044d40036610f4101c4002d0010310364425114000c086d0300000300500c052100425083c8080e40e40980781303580a080000014081c015144502481050080b10750322041510ba802c3d41d00070840751300c622040d04d000b6020410a090808091500751203440c1134107100c8000110100001c080030340710070000f030418100c005889001015030500843c00e1004174828668000303410b20b049500040e00507203985621001602400d070404001c0c00150740410030b55009480c021003100f80900c10011580403507910182582640c10030690f01c2c030307203410224140c0303a4207c2e40401464000c0f280c0b07400d803400c415045219440e03505101003030314004601085c41450710100300861500580365080124240b40480300180740c5200b1400703182c000740d41398008200b440c1a040040c0c0c00d41420904c8403401858a100700a00030f400800c1d41c0080b0f182000f0300d01902c1c21101549 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916232050 1250 916230800 916230851
    0x30b0106030b0f130b03030d0903080a091101080406090b161e0f1803121e03020906030604090609061e2a030b19080d080603030309070512030706020f0a0201 69
    0x43c42e0340000564100712051000021900c90240c480300382088550303060004113865007800000103800140d0b41001049014010107828689207091462004101801c06510040c0000d291100c0b880c1d6403850418054a03a1910041091007141d00707000780d00b400040c21540341c00d101c0e40c4055191100343e00e030b411091154142e82d80070420200261020a1203211101c02403070161000c0b0b034240381d891f6100b06008060080700320001d4618410b5005941d1030303564202c22405145400c0d800d08141400280d600e10018011a1149950704500c0d402c000c0650001c0c00310903003000042000600d120002e5500814507080c5542c03151400e0843c90002c00303008810318080e00c281d43e5515400ca0741000a50040404e104019070000911115440000248004c00082c5c0b541802500d001c1070f004901510321a006000340340310307170803d004000408070009064400c0301c00807200103140010040146003144144000501000d0000420f4035240480800410f584050742e4020031010030711160748068280180203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916233300 1250 916232050 916232059
    0x40f061104031a161d040b0604080304080c010f020f06060d2306070905030a031202030c1b1b090f06042f0c0d080105090f040203010204090212061915050c01061d01030b0106030b 78
    0x5010107601b0a03034040d031000b91029110603c0c080d00c40410900c3c680090f48510038a6000e180c1e4207450796404135440c1100c8210380002c09408105000c42031715484024825030103000410080c90034440c4041c0d1082c05000c41d802c07400a0b000740c030054a51a000b040b220480402c2000c2d1000841d03003800101c542107036030980c0e01c903400014141f0b200400307540060030407921000b0502202203075082e150781c60602c00c81d054000f09400c0d90903041c100780040c0c040760b80d1071040551204120100079400d1842d40d01100072103000608090035503044401c0003400810a030703c540c0c1111100044100c0600030080b44a066084507401109a14200c9080d002401b4079908030358540041440064a0320060fa0898801000981060344403c0c4500803608204030104400b4134840174001c460410b424024103959039428500d0205007800608100c60021101c3d03041080000034501518034000e61140010701148401030030f2188181d10100f100310008e01058072600640000015118081d110384e8055080140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916234550 1250 916233300 916233347
    0x30a09060509030f061f05040204050d141e07030b0901021810050c0105070306031a0403050313230a0507060306080c0108070201090f080a17040f061104031a16 70
    0x1103480d900b06000c010380501c140c12210041050074403505104030140400703240380701c079030603021110b0303800c0c681c81103001d988108024030540d101c0b60071000c051904080d076103940365130010b9035514000280141640d911040c4560300c6440e00c02291079406c0b2400380710b5881c2d80340c4503096214200d100d44000d0002020001034034004a0515040c140041c0c03800f42010307402c101003a5001800e440b4202c641000180e038491007801001748001c02c41e8000205022a420213180680d0003034841d10000c1c08500c200d11918400800300b020031381d4541d0380c10f660300c640b134081480b03280f04c12030741c40c041128102c569000e18032022809070300c244184170072114a400200440d40c0140c1c01500c0c9040040c3c401d2085541b901c079542c011401c5551504000ba00c101190b581d5000035101c002c004026410035010070728801c5c1e09010118500380350120302540c00050008c1d070080c8003140184d952041e94402021310781c082c8440c8400c40e110555281c070808480c14001403484441034121a070001d99a40c401c070307441c20301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916235800 1250 916234550 916234559
    0x40c17060114120112060615091707080a0503031006080c0405010c0c2111040b0112020901031803020607030b010c02010206150a0b0d05150603061302030915011401080603030a09 78
    0x418150708002100c1c100d00b440c3c055010040310806409800a5452503550092503040190902c5000b0080407081101c04c440c00400c5001044c00d041c80c4070b01d9400c820060300800c4158400d000201c000c00b003040407a1000d03e4180741c001d032241c01c211102c090300065400c000179035900407580944103014451145140501703000040d56003480784c00c3c09545910380c403140416180420780040140004246002d588905c1c01c2c0341584150070a00103050165050240035031041c0d82140b00b15041260010700940c6031005040120010310142c41c0720410064200f200d2820b054001c96503c1c080c200e107503002d200700c2c81e0280c015100c001c1403840c02030042c0d000c10005070384414000762103885500028800a01d0a607140940c0c035141c1c2001122000443daa0002e00006803000c1100005a002c26102d00d4110314003100040d0406040c0319140800301d030004001a41d0030014840c502c500034032140c29001c2561140354144400a21600080c003280d80200800d01901c0c1c0001964080307081980e691603000d091 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916237050 1250 916235800 916235807
    0x1c0b0f0c0712020c09011e12051203040326010506160311100e06010e041a1302060310060e19150c050102041e0603091101200703050c040c170601 64
    0x400552000c1014001580014003059a40240c0c02d0070303030300400b00340342d101042080d42507040e0321540340f0b21400c4044103003106820800c0303012900d92940d0011000090b040c01c40c00e2403a0a0b0958204d000000100020503030000c00c520304020351200343e1206003c4202c1180c0d0001020302540398030031800d2007544420746000e07c0c0c2c41130140c440d20340081d1070001580d000f80340103584161245602d441e0f00f0003018044041040d14010030440040710841e00b400c0e00c0d0500c0700258900c0e040d1302c1c1c18650380000c0340e00c0b400004464500e680948070355034130301c0e0400c8a0700700305205d400380d00000340400d12040c41c5881c2c01c02c068815240341e500f180c1d0b206071a1007030303494540c030186065400f030080300c07113503500411000c1c03025100070642e009801607080306030b4040301e0301e802c0143c12007003d1629104400021441c0e517992604540000e007403000c031040c0d41107652100200f05402031100c500c01c08101000b0841c0110b403400c000f5400303580034031000c8516038043d0381007003800281c6000c10b0b00700c10006603150320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916238300 1250 916237050 916237081
    0x31205010f0512011e0c02240c0a1809060302011d0f041d01021210060207030804090522060c0f0c0f1509020a090605010207060903052e0e07051c0b 65
    0x710310b800000c0c0903134071294100d0410101e212205c40a60783c0c1120a04e610707010300c4440c80f11507450107100615100107205e42007006010f0040d4903150000305000b5044d50049280700b400c04d003101003c8404d50760302d1315541d000d024a400300324005040b10f2828107401c50740c88411840d0140c003d284c61803140428041c40020150841104032442e0f03150441c45180c203080c801071099891060b100b101070310f405101980d6101e2540d00400441d0b03c5682d0801c00b1410081c2030303900303640e9000c9012480744c903a4020600e2440f026200c58a01210403881c038402c222195202d40c414202079210b090b031840140e00256011801da5401500420482c086180040c0500c0920a00c140101c0000218082503070040750302006e06400c4050203a5407180180415a0100041c10080045290446030b42d42103680315616516866218410000c80502c44803600d4207041300401d500c10018403c00410400745011550340200c2e00c55240180007900c0100604c4e13074810071300311031640c01071300d80c10460b128022020314010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916239550 1250 916238300 916238329
    0x1505010e122a0a140306040602160b130312020405060702091308030f070215060f09060d02120d11011b14070203030a0e011707080c0c070e070804031205010f05 70
    0x501c0c9840c031000e2001c142e00b08020265107902c2690192014103016600140b600003026020300051100c043d540c2c0056020b41c040e03440352000d41c03524018825101c2d2200340c00c40040c005448141004070080c0c24050303040784d8a00a565421000d5032440350034089200340e01485130051803c000900c09403c103440d80c10b401040f165289800c401d00ca498240351904140c9140700940b039a0002d204032070f54104516040c069912007204403030300386440022540f020341c68030107005201e120300040c641d0b81c800300305400045d0090401d1303600301d43d100032803502c5229607a01c1c440400d0351040c0300102d10a05201300b16a580124003816150801c1e5882038442c50f40200b8180c540b00c1c07003002080010b03181800903141a5140384c490412a2000700700241c110662419001c504000074820041e03050341c0400c3d01508100781d201e54550b5120300c0084a401c126054100d0050601640c0900c07203101d501c104a030388554040e9841c10350406d0500100410ba450a01c241103d400c0301101c00c1c8040d1030081817111149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916240800 1250 916239550 916239553
    0xb011e03021e030a14010801140114210102031f150503130c081f0504110105160803040b0609090601080325050a050a0303110406090936061505010e12 66
    0x111264103150b002980304442c40d01e40a92644d801c425900d681540050161100c90b0085c45000fa800590305110304051043e403890030505005104943c440100034002c003000d40000b1220302e0101c034541d9020b9482620704030100f000b026900b568101003038404809070b40340c46001140503130011404444a03003029208425001190b08690006802102100020020b81010f4595903c0b20b0b061403102000312125445514205800c1100060601d42072039039003402400d1150300c9180340700412018036110b03800282080c500100340000d201a2408a511909045a401034a131b0b40c0c100c52a40c480c9803c0c031858005910901490f181800c1400300b4401d19005103c1c40000c3e91015140e462805900c0403040d41e035508483e80e040203140d070501818502d44040d171400e07481c0900d41080100415070520510044550315400d201581c0007042a0440d80c02e00b0040b80d02e4602c8852140584068890b4412600c2501d8001ca4602031402418200d0407580c0585508181c0e00c0d01138203104c815610680d050300c0b035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916242050 1250 916240800 916240837
    0xa1806020a090f09050106080c03190c1b0b010305010e150f04081306030209030c040b01050403081b0312070215150616060501120615050901061409060a03020d0b011e0302 75
    0x1c0c4061501d500f004280c5440089000c0d40340010240c0720b80c070041d281d103944120800801040403107101c080031600982080000f030700b1807010400c64020380b000c070f00d82c06002090406441400f2800300c940c1e0590307006074000c11040b105070061170f5641454070038030f81c0204404400503030707000c0c40f4200196005008543c1c00b45000840040100100c0e46c41d040040400e50100b100d0001d410200f289402400096500700894141540060a14016031000900d074480010b603185610014010114000014504894a42c007020112071180c160440e000d0005104107109501d1540c3c0318054140505010609607a200d440c110030701c44181e0001c1c6c0401140d000c81c03521407000071854400d0a008004001400403202d8161420b901030750500c00b0171012100600710148815a03d5810550450707220b803d1074071074050000702c2542d1902400061590004010030803c95480d050f0b0010b00d602d1188038020030014032000010744141850303442c03803070f81e01289003502c040c854003a500030038410390381d440c1d840704 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916243300 1250 916242050 916242059
    0x314070905130b1c050c010c200102030c0304031124070f1415090d050c1009140a0f0618170a0c1e060e060708071d090403030905060a1806020a09 64
    0x1a80c614a019103213200c500300d040542400000c1c0103032100900c091030030b201152001d40329082c6040c0307064440400010b110440e18090b0f03008000b12900003242c201a40d4855079a8101b4003104080d4200044c021200050407030b03400203009504c41400b61091020b24141162a113600740480c21030b0b002260b20224a10b00c09141030010400b07801d180410301d81101d03151501040c10760070040b41410407414804244004030310b0040c0426028190722400500041c860118200282d070003030340e84104011802403684c2001803204169003a00082c2c060b84060082c24808003101d24081c00204001e07003028504858200014800002000d43c80715600d402cac0c0d0522260749540c91606000d55484204600c0030b1040010007c00d40103c015100208021f08441d15044a0140c8260f20007000042081072006400d070590900b031005020f01440a0900e0b035041c40c0910300a001441301d02d0068455205000c001102d200045c0103104002005408044042105584040c040d422040700032044c000c0f566400b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916244550 1250 916243300 916243309
    0xe06040902040213051318170f0c07060f0f020d120605030d111204230a09020316170112020118031e12080c0304020613090204090b010314070905130b 66
    0x2040800380d020100540707800b081190020f8805a4480d03124102600a5032045644081c7c0141541012860405c3d09070510030300041e110754a82d43d0700116000c1601e045844002443da0b05591094a4a01c42c00c0c41c2c0300c0c42510181d41105442c001640244002c0200034400d000c4e039125681801004144181c9500003c1e00304810380c203441000503030400d141800f545003005103884444100c1e40f0503140c2030070100090b00c903060315075a09034203c01c10f4010307055503101c81e43c011004140d101e00071912414210740040031004051491800a01410280720185103082403e80c103c034a15584001c032080b00340d00540d11148001c1d15042900c6204d80e0010106d6200e281202c0b10300c0e00d030444440036001a28010685a04009500d8100840e490402c0744844140301140c1d0000d4044130040e032201c11030000d00e51905000e400c050469800414000340304c0d0040d403c4006c4440e403d8030207000b4007952058007648401c003141c9000c0040c480032000c20440c10428088000e07040d0481c000304100c94201e004c80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916245800 1250 916244550 916244557
    0x311030f070909151a090702030702030d030e0c0301151403150f01032001021009050a061b1101110322050106030305070606090e06063307030809160e060409020402 72
    0x4030041d1201c0e28641007081413500c00741030240c4003408210a194002c10300c42d40014200046008150705004580c081d4001c04c00d841c5202c3e8000c044a0003600c0012005024207000361101d4017a10681c0381284103440c06008641d443c0e0351050350050903a10704610f4001c41d00f00d20080d56018002c2c441e8000e1983c0310140d06c644603080e028060107055246150900c9102440410074451480390420400c05aa0204540300c001e054100041807074107a604105082c11a0b02c0c8004024500d400c004c1302c42c10707030801a0920b1625843e03c3e00d600016101d0380d49400d8644003105548441e00400005020227000d0f03186424648440e2070104005809540e8036003160115081030300400c2d004200c0c0360800849000ba035000e080d00920074002102840c0340f0a6603402e0241c0361030311401c4ea902c81d040c000e29221a0307407030000c10b4414003000d15a0310303810a49032a80c00307044154001105980003d0174071200044808e48245064090250945010305101c6046409003800f07a01a492741a000013603550b03030019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916247050 1250 916245800 916245809
    0x90b03061b0f071127060613170d11072d1809021c0510090503190c1419061a0907031e0b0609092e06020f060c040311030f07 55
    0x4c444403220b800040100a01081c60316180c0c0c81440e0030b82c1c11482e04101250703034101d80c0548055803540c40400302008180f5003504101e0500d043d44800840b000000540302d0705089180d241c4103510001f40442c945c65292500402c500c00c074000302100b031a5115002c10790580b090b031300048031110380c90b50801c010710260084820101919040032400f58a00681040300c40540c202c0e100b014855280c4d501503e804005040d00c40040d41e0709200d106101f403e004498020000c500000121040700d0070192400c100c1d40c0c03042d40d00b0303141200c01200040c0d0000c0c1c1002c1d29480b004604269861344c0e500c2101900b0020280c000203180d80c0005032103910fa0038102d078050407403038074082084e0898045035401244c01d6154403840a042032100c4a15483c0e40c81150030300001901d41040541c0c40000880c41e400c0b400c4055070b01440d02642c4c03001c088070050514003d551440d8292500212203000300c039502c041c15100301060b1442003204000289201c1501090060301800b650025164101c3c101e04040c4560f20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916248300 1250 916247050 916247063
    0x90406060c050f0304060e060706060f0902040905093c0604030807021507050a0c0503090a031406070804050d031a131b050301360e0c010306090b03061b0f07 69
    0x1050100b00081c000003401e41220710042d4201440c1c03c2005045640b51580320f400f4003000168003003448000c2d080a03000c1d101031201c0c1a806130f620742c140e00007940b00c1d10078003038120710381004184840301c041484035104000c0c00c00003204042180002c1b4000c4000c00003940784540d81902e40601c01800c0c8a4a84540d00a843c0c14000d031401a03006802d1a4131070900108101c3c3c65010003a6507900181550340701c0c0220f00d404569441c191800f0fa00d140700c0da42c50aa40042c2e20361001041050300783c0c0d03001410440e1403d5401075120346a0a452962054500030415004010514011440790307100610840b44590720780d112000c0c0c0d101084219140c102c1004601d80c41d03c0d62410110110300700c1500707104440c5031603441c641c5410100d01e240680d2a19603400c484010b5428001c03491904004411010302d03440802c00340303151550042c0e03100a184038640c0405c0c102200000c84c640988501ca216040c0640540303055940c0c241e100640b01804268104005810f10801103000d01071005804424070a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916249550 1250 916248300 916248317
    0x8090f12011802130b090705030a1508060402012a15060312030e010510080304030209150a08070e0115120f0219022410090b010c02120d0305360309040606 68
    0x600400c000c00c600c45a10107405c08010101c10740b100140305a02c404280341203a100d03210990414060480d800d18007a19604000f80403403042e40104065000d40d1003602c0b105111007183c0241c8400e038580381266105155030310344003400b2810811034090216a40b95000407115201d0340d4908880c0b825107442d0300002d07036400302c00d006d41e102441959003004a26071803601051030700004540d01d10544c00300a018800680104100101e4030f41a440d800c440104101d600546555010780c1e80c0055204000450148100004800786e41c400d04800ca07140d0381d0740b01c0d03603000410380c140000b904195204c2d0300016030030402c84049034004d9013031081500b520f0340a4461021049030440000c0d2208a2845480300040240841c01681001020899442c140d021a20305e04440058407403c0c000070300a0340001d00841c6c020b10500010030400703c02c030307460b4034104802d0b21405101208001001c403621002d043d038114401041007400c41c1001120450001c8915056002c40400d0548905600c0031000c1442107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916250800 1250 916249550 916249553
    0x5030a03060b03060d0623041214030709091e051905060603011410090807091407032904020f160c14030309040903110f0d0f0c08090f120118 62
    0x18010100200500142e0301d0450800743c002030b004010440d80140020756a56101d504031070307a418030070400c858004040b00c00d850b203401d02400d4070200010300c400051001c00441000f02e604002e5034000e14142d640c55417501d0030050a03600410088010603110b260b042001d0010b04024040c0c1d611407070740031400e200e0300d6009224110503518041c100c0751050905000611481620142c0480034040440381200c0c2e80160034400d685801c0c0c5038001031603e000c2c4e0302c0080b81408180c0c0011020a040009800c400e60f90301008500302d801001c61000c2805a80c889440070342801030102a41100040c0014a0818220340790040390f80b10440340c108846c1c0d4021010180242c9000c44001858480e1600350b40d03401480c0007989902c20004002c0c490f0f9503e03a403080a0603c1081c0b1119002d0684007110b911800d00305403680d1741c2c800300410f08001000402c20b9050345200300e01400303819600c012078074200004c01d001c00210006061b0700b079030000c21150401081410134000c20b0300c078551042079200c078464035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916252050 1250 916250800 916250807
    0x219080106050f1c06020f0d09061e18202d0102120403060c140a02070f080d12020d1112191416031b020601050a0602060403080c0901091205030a 64
    0x1403405104c0d15110f00014a075407280f919800030b003540410010707034a01e00c18120491500800c60f462a070340d45050414020031005a00c0342140400500c03400c4501d1103140c01d040280d42d1241c454070241c044c2c050610703001840c21803802c0019405c2c0d106108803541020041020425a1841403044510306100714540071080820100c00b94802e01c0501140903000050b1411480303a0b220042c095a03171003038000c0740345120360341042c5d0103601140c10175900c8a610310020342d19841d9002c3c024401300d8069000036121000a100400014251070b08c10b13400f40060750303080003908440c0d480605641c603a4200cbe03030500c03004030042541c81003078400c103109400d140003074040e601101040045160f14240351102c1c2450742c017280640c8a161480300d01c944100c0c400c0f08801411281c50401c40f8042c0038005149035a80200d0744e80d041c0c0300181c0c2c50380c4c43d0503076607c0308998a420540d00600492540400715070350600e2580200441541130403e100e000b03640d43c0400406407010311080e2131701d40003c5402d0600c80c1e030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916253300 1250 916252050 916252069
    0xf0625150209030601030807060603171210080d08090a050a0302070e09060727030b0a0209040b19031b0f06030b0102010c0905090c1e1602090903070f0b04021908010605 74
    0xe6040460400c1c0703202000c40c0e07540c030044c00007403c580070100d4030204000140d000000a181d00c401850098045400c40c0c101c150000c0b000d074034a10f10100d001988070f4484101e03400890b5a03020080ca1040a40c403000c6d14001409459603040c0e0140100c0301001c500100001d00e5558403a5006260a501c0c29003a11140d54014040d04400d4000400f4469810b6004200c158040f120f41d002c3c0d9050740c2c0380d40706d00310711011a60004110300c000300204082040c26034050003060100f0f0341c05002c03032880c000070030001c5048a00902c404080007501400890701c2c070702101200807905141c0890751074a500440008007507a43c8107000107074440c40404602d50342809800f0592140f0705061800c02d04120000d20781810040c02289504000710b0350101c3d44100910403140300c299032a40d26600d600040c03420030a0501c0d400141d01400342d01000c640c04400000444210682084140800708050340d1140351004c0040c0041e603000100088615100285144900040c81c144000185151822050110020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916254550 1250 916253300 916253333
    0x130302061b0f0109020604060518150c0709151e0e04080403020f0105310b070b04020306010e0f15060729100b090d02040e1203070314070e0f0625 64
    0x90420a6a00040c6c456400750340c02c0d0380190074400d440e90f03192060014640e603280b0040b079000702681103200d48450400000c4c401c00c0c0c2a4000e0380d24841e10303611810180c0300121444184400d0312034007001181860701006151264018884600e290b13540507000e1064402c0e1010ba032440e10004040045182810074007000580c2802d1840c10b111280c812001c610031035130b442a42c1d2460401c3d5144122000c0300740000034000d03a02100391121b40381d09080c050042e08070741c220302910400e400031584000785403149118080c01240c030001a1b0310f075401100600311034000305810100a00c0104000f80000603450040070040007003080c1c0344a2000d42d242200300207031601032094203031003050000f209107030200e44d5064400d40304075000100078800700d0700404100d0115202e50058070b0071710f002070044000a5015003680d0368107021b86103035807400b0028150213481c01d90101d00e450051050506042d01c00c0781e03075078100400080c00c1a40c0c501011250800c099840c180340944070400e50104907040a8080540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916255800 1250 916254550 916254553
    0x801080606220e0705031501170a1509020102160b090312030903120907151707031109040c0908010e0d110f0a08070c08011439130302061b0f 62
    0x464252000703a122148249440b00d545a01c2c0c9540805000c0000380c009040180448618400c2a8014007855000307010742c511002c2c20741d6610a54901c001807003e03d0300d4124004801c21018031700707028002d00013140128154000d0350301034001100d0001001c4004c00d456000d40784e030303005a0000c0504007881c5c0c03406d8a01c0b0400a01c24043d401c0c0b40002503e0a550285003124810340b40ca680395803920f80c1c01d51180d0101c140c454072044220340d00c000d00f102c08200c2e00c1b00e49a000c3d1680c200650648035403003924401c3c0d0780140b0801c0e60514058000700304440b103a0800240203911442c0712070a4a4031507030256a01d074001e24a06220b981e011804644d03c40c44c960240c000d00a0805006481e00718019003c1c1c5140e034081100010311400d1078000d8020181e01d07000304480d008180907240c0400c0e04451854501c11b0000584c405240c000c02006602c0304221100f288075001201155081d400200550401125000e80400182c813218010f00d000b0b0b00030341314440314400010041b07281031154241e08030203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916257050 1250 916255800 916255819
    0xc020105150d02030f0303070e09010e01053012180402090d0b0612071508060405090c040c050d090605040611160b042d0203060709081b060f0a0801080606 68
    0x72803480c0c840c010440100d9080440c290365000203880c2c40642d80c0da510260100105100007036070001000708482405603000140b688e40c1e222040c403a124240301e0700d40c010100300d0070001402c00303403024641c241c030104142c140c0c552100c0480602c1e02d0024010041110303c001403200c00c40c4020104c0704107960f405c4030158607004446001c14114101060002e000980c0c81010610903603d81d030307030800407002c200100c0304000d542ea01e50340803003a8480e10303400c040754020021980c0c50410f401040e203d040190014000e001005e0709100007800e144590400f001030034070488a07000114024500d10a02401c40413503107003098100303c0d04a0f08110120b03d039511082102120b5460380c0a43e1138007554008000310340f5656182441c1c01180d80c11402c1b02d40c48042c0074044001404d0b41403c8615450080d0200c0f0300c40d99502c2005c0d01c0d40d0382507000310100d50340181403006c980b806400294640003c090b105c98203240030142498010341100d100d01e0003003581c0300c0050002d280104a503503406541122036404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916258300 1250 916257050 916257061
    0x30060506090105160203030f0c060a061403030306091510033c051f03121206080c360a0b0d03050f070c0b340203060612011e09060c020105 61
    0xa44e00ca0b81031542c00e10080d040801d400d644d000d0003074030180c0c400000b1807a40c030b030f05e441100c648422044442e0001d861402e500400d24540c242c0302c44070388000c05402180ba6440702010050700030002000c00710324507403030800001543c0f2550b8010481e68150303203003c205030194484625221400d99501003800303001c42c081c000880f003c48022404800300c42400903180d240ca40e42034410340820343c61200001070300200081044460600c120980e03a03140c0d101000e40c600400079205803440c07480341e106194481403051809107007507040da11002c055175070351090008001c1d0171080010086030042c40c00881050400c66060f940d409a010791072411541c65034400d01a9030b001d020780c01000c0a6410041000c03a048080042070b01a10018142920b40d2035100c2003200c0301141c600c440c42d40c600501a030707110741c1e840c40d11250010144510364014040c0c04c441ea640024440c1441406078020440c0d0340711754070454203124145554001000c40b100c042892010740c10008243c6010303a83d0541103a00d02000c109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916259550 1250 916258300 916258307
    0xb030d09030311030904150302031b0a180b0409050604021314160507050105010e071413032d05211309110d0204090504050c01021207060903300605060901 68
    0x100341c1c0d5160034090560111031003c145940540c1d0070040d005880d0a1003550181d0804d11880c084a04c00c07004c480c4c011403e0101c01c46071413403009405030401c00814051243c0e20900e2940803000c4016480010b80720b01c00c41c0003a050300e1011a06079a246c01000501040d41451000c522644440c500280845c241e58032040018000040ca131120a4180911004120b4412803c4440d0190000c00a12095031a80396035040444140c40c030f000851030041c00c00500ca043c0344140c0340410844c0140c10b1a0901e991500111a4800840814014000780d01c0451800e040e034003204d00140030314001c0084110108080b0480209a107c0441200702031000203070842401c0707024030949842041c00701d4146a1000600082d00030a803480300007900100300814081120384c032540c4200e02070310895092209480042e41c643c0f5002000d01e4007441c0400200c0007080c61074102403222442031078101c1800310603860003482660048402440d00403000c3e50303d481d0120354011f60020b04002c5a1252400b1040c41c0041c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916260800 1250 916259550 916259567
    0x703080403031d06180d2d050c060a0207050c0f0306150a18150504020a0504031707021c0b090c03030a120204081c03050a110723010c0c03030b030d 65
    0x18105034640769198510f05800d00691030405100c001ca5085007840154122040b8170f041c0034508034820000701e049110303c5010307104001c58a01c04601d0b07031804040100d1552400550300c10050107400c00c4103400d11481004214480c0241d5070b00107807100d5031880c0941c10040120044c03480344281401d09240c42c3e80200c2d440b85c2045403a0b540c03062800e400c0020400111041d440440c0c1c256031500300303116500058000262038950b840500018984500421089001c0c8043c0040010300500050000445940c1103010790044c485525040c9049503002500c00b240c000400c04061a511741e061041050f441c1d00d19030080c50140141030020040b5012a41d2805a000c41c5000c0004410142040028681c125400307043c10100341d50071842d0301c2681441c410040c0c2c5030000000e14000004c0d00b080403e100300c0c02c9841121518034500142170f10389000c0c015101d00d076000c0f904880741d0169040721091040e007001000c40e403680f085041c1e10f4140602100c81c4c1500090207600700c008201500c0d036020300c50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916262050 1250 916260800 916260803
    0x10e060f09070c0203010c0201061a040605030c0c0309040633050f09120601120c060914060d020d06090b150403080a081f03051c0c0f060f020f070b0609010b07030804 73
    0x801c0700341e40301da40840d01900e01000c06034042d460001c1c090201070341074000d041920402c0490200051071168a58060b1003144203460001c0c40500c00f051688a00c0c4000300510410001168141590080002c0440302d560340001038810740000d4140e03154007031852425904e0010883c100c0c0c2442030050141c150301c105449551070400010365011076654401225207800810742c02ca400e03668603540d0710040c60540c060180c440300c0510300c0000c3c12a11071039000307050354111000000b14140c08801c0c082150070400d0b80303800c0d8540074096100002894442c0600031300c4111400b01e801096102484061032006400044a160401050004c02d9103001190801445868024282d0390340c84a001c1c0400552030038018000b040350400001d1100009901024041141452000480e04031040e80c046100c40310051400135030580301c02c0494150350042e40d29030304424003d071920042c0e802910ba150b000d003d0468580083c4000d2060318103121080502601f41110b4041c9070500a880c0a0290f0100920 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916263300 1250 916262050 916262059
    0x5010e031b0a0b03040b0106020c091323061017010b0108041b05220621060c12150e0c03040b0103060209060405090f06040506030304063905060f010e060f 68
    0x2000541e403151105200240f94070b8103000d48905180c54440202c03030082c07141c140148503105030140c0910b80810344030b00801e83e4100081a0142c240d40e49090f0400c481c6144407210b5038100910f10b00b4206124030b42c401d401a045405040f41458101c01c0c1010f1204c002c0d1400ea1b15000903084583d0f0400b91054210303801a1015090348840c098224240ba401d8100580080448204041c9110350a4684400e40c00b40903041c40016180e04001400b500803d0400014100d05200e00000c10059405425504410301d4078820003402c0390070f06c2c2c0a40f510511050140d500302d003010811800070448035a001100c12070028a107040644403c0902c441c18080502030035400100160715549040480f0014038001c1c00401c01403a201006058a40d01180e1044c062810300300050300b81d00d004000c03034060b14580c2c0c80300195007800600981040504055520300440c0010802103e0f00029041880c3d0030b01c204c000f08654508011001c00114040e4003440054100900b4410265a141181e0120110994 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916264550 1250 916263300 916263343
    0x906081e040c0506120708150105030604090614090706020f0f0303011719080306040b01080421271e06020703080306010516060f0e12030609040f1704060905010e03 72
    0x3002c4040510640c0001d501c0003000490f5004803050950081c41600540c4070f4904607a42c011031fa0044042842c038641c000b610400000d140e07031900c2e41c400740006024000c0002e90110741c0e641c01d003044009652041003544100d004100040c0d04200c4c9040000b4010058041ca09480640940d0f80c00107000d2816100400d820f541590a030070400c6030046104c2c41c40d8400e40d00e4450610040a81c8141d80b00c80c001e074249100c050f51940546840d502980d03104a892070784401119040f001d551460015004004211150103e5000c102210400c40e83e50800b101c0811031804c05408401c212106120015001c851010000c0382e4011440340222900054116a030b6518040101e403070348140815409003880c0450768100340b00007640441e18640301004c08009510a02c0840c039030791428441d20b501030240401c0001c40904140e00929041407082c482e10715005201d03543c810758119089220b07a903a8202203020400d0507440085040100390a0038034010641032400482c0e100e1840406540c40d441805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916265800 1250 916264550 916264553
    0x10608160320060f03360d0509060706050a14010f1a0d06122f0d080c0705130207031d0612180f1c0509090f040807020904050d0906081e04 61
    0x12811a9100c08541413102e55074a00140c2c041d4a003208881c004d0515080c5100c04000c1c0401410008a032a10890045c94620b100030011252540003085c003540118061040c4000104140501800b40c400014086080b0404900842c1aa80164000c0c603400046030f45c20030044a403240910540a035403600f0030b50f41d040411050000c0e0400394441450b0130181d083d041d061000303d02d040b88094500354041014100944101440d0080d86a24181e2142c0c000c80314a00083c40c16000303000c280d0980e002d07103060f0781d682d400159420ba80743c0f1030340640d20f0300001c60004050340000102c3c07100e90074541003c07001400d0000b280050080340b2140d28000000000b05910030084c0c841c2a09407100c1a044a900c40c0c0560f001030380703600000305012810a1041841e1990a015000756071000b1f40181c0031004070f60710080c68a03850400500140c0e40141c003004843c0141c1c48070080030f4810780c0140001d10401c8400c807001480f2486650149041104280a00c02040300320400307400c024160070420314058445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916267050 1250 916265800 916265809
    0x6090b0d0f0b070201180f0506160207090f06050414160903120c02030a0203070b120108030405060a0c0305070c030f03080a090b06010c03050c06010e0601140702010c201002010608160320 82
    0xe0301035000100d4480146c0c2c06c20003507508401e006a41c801c405648a640f180c400d61500582184240805070f046410248004803480e400b0012040f428200420615601e1006c01c4c1180d08003241020804440c6c1e0401400c03189441c070200c0040c0301482e103c0304082c91a22000b80543c0d150b000c240030030641d86c0780030040d5a0100100b44210380c0040c1070390340550703490a0010655100500e040032202c101400001c2e101004415941210000340c4124903107201110701701c1c0c5401795214100c0500c0030500c00000030420341203004000c0c0d4890354131070746105554100500700120044c405101c80341030221b200c0000344099a019048202030074000b80c0010035143c1035030b11740605600d22604d48180ea000041c10300ba000d404d540140b0080c0c03120280340a0b03120042005d4441c803140070340400c4000d1000000603490404010354420540c80c0a01c190b42140001100c08400000040040c2c1d1140c3c014881c1000070300c41c41c8891020820300c621164070f146e5500143c24851201c482c80c141000242010a454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916268300 1250 916267050 916267061
    0x20a0203060f090a021e030106120515070221040f12020109050f0303120f0406050705030108070315021b10180f060b01030e0708070f06030527120d06090b0d0f0b070201 74
    0x34001c04106200641161000c6c2901004484511940c01c2140016082206c403d0646695400030060149034605008046c0400c1c00078002900714402e0034485042005d082502000e003054000016a40c1d5107004070140350700704a504210308107041c0050020050303800039901c1d0103c8005507800002245694002800d500841075060100e82e1070808218003010b120907101d103e14031442c010841c5880301c100484803800240214401e43d4040e000500c0881ca0a80380c465000520680142c03411414040485040d80c40c051582404d504c40024811422140e000d880681000c1030b50704000400315032507181000c80c4900010b80201d43d1103110810591103500b000f0040701e00741c4200d40016a0f5402c4d0345a84451074495031801d44500900403c013940300e405158000c2d2558041c1c1c00001120582c04807584860300d600d1041d9128194100502b4021407028000010031700c400010740034544001c0e0f4060b1041480128412741c020208900055250100c910100340c002c5000e9403c0c1d50303141c405070300500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916269550 1250 916268300 916268303
    0x1e0a0b03031306030f050108010b1302090312070f0c080c030309040b0d06180b0c07030e091801051f0902040506190e090a0905010f06050a05100302120a050105030d020a0203060f090a 80
    0x1810b0b1040440e6194141d040412180b682c040c00304184ea90f2217040e81e00300c03070111440750b92245500c102101124800d40280004400080941d03441614010302045182c0c002c0d40120390003401e40b10000184103240d40c2140003091460007a0010002c0c01001035200c0c81002d41d028400d0340d4540d800002910f501400581c0150b2080c0c007000b06c44142c492100100d418158114ad000c0000000210942e05000540d00300c254551607030303040c58510700c0030461041d0000340501130720652090f20607000e4409001e034602405c0b07860b50903c103007045a0203116903002d00ea0043e1010320f004100c10040b03034690700c1c02c84100710701801a1100783c6006400455007180074049c000da212641a040c094284016408500c0b800d10502c001c0040c805000000402d603441440f4440e44800000344c100054106410001800412440e0051070003a4001c0c1000382680c054034910358030b50b511310040c00241801c10482d5208042c03070004054540c030a9001076074a070b01c014021450072164001152100c90304010b84040d15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916270800 1250 916269550 916269577
    0xf130e010b190e1f09090f02030607081b090d110a080d020601050a051806010522080a030e060708091e03010905060f0a061a03040812010e0f1e0a0b0303 67
    0x1880d84607241c00e02d80085014420400ca0b1040c04a600c0010140301140f50318008481003080501d060315640007080b03d00304c00e03144c5140ca016200016502030212a201e008035450b09281420150381c070030b0701800ea0460344084401c0410400303006a0710100d000c1034007039200088161003030f0150003003001c8201c0790b80441c00d10320928000321006900403a401d030607100f040c1e90f210f44007640e42e0b00b004004044102200f54002400d0b0100348194440d8004094032031941c031400550198001440386050001ea21280302c5030001e003d000c08041d400f024a0307505120449240741071440e540c40320b001d00e120315856144100d1a82c070704069044402c920550b00c454005000700103143c4a400c005131908801c4440d040802403240025244000d00d201e140241ca1062a00e50310b08801b2800c2444607610150041c0c460700700134807c00244c0300852010074003170101400c10002c3c906188142084054001d840c03407110034015002c00322408601960f070342e44108403400204200072207d01282c1148510b28064440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916272050 1250 916270800 916270819
    0x20a0b040c03080d05162115050627031c0804021801153207020d020a0b0c0c030622170c01060602070504051003080c070b21060f130e010b 61
    0x20110358016803040f142c011b4203c0c2c003101500070032030b9812032010700e10480d05031800c035088080807076920440329801c100c0929407050345c54400103140e940040708801802d112415601d001c612501c3d4030302c21062816001402c0c421b000c07082c5840e6200c440d224550130040d04100103020b555442c000d044c201d049a01030355a0a5841c1c000e4032040440d5003c0c00001b103107403084419038070301c190a0b100c5c071201030b02c01e02e00c0c11119001d19070003040c0d03001c0304081e44d02001402a030b80141e92026002c800070708025014940d5012900415418590303554a040d2081c0c00030820424040c0d5038014010008000400c00d24542c43e191428400208515496002505c0c5c0405d00070350892055112740c054814a408407064103645200b00002d584e0100c0c2c4410790420031802c100002100800030707149800c3c1c0702003500c4030103848010310102a00b0510b00c2000300c0450f01e40d14083c00015611031070f0480f0303080e6900c1040342074400116540e0182c540d4000c0000345d442e100140011001c0d44001000303000100f91040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916273300 1250 916272050 916272067
    0xa0c0807240c080603070521280b10080c0f18090615090103150507050f07030504140d050a0210020f01060b04050102010c08150f01090509040f060506060406020a0b040c0308 76
    0x200303000340b01240454040c40c0461031900d80003c400040f07500083c04491010009004d03100310665981d0400c10a200d07030b00ea41e80701039204d03a00305644d01d60306200c9001031006500700710460b89030240104041d9083d12206001c001c10100340984400400c1d60b14001464203500458a8000290a04000c0c400a4018041d1503600820204d0040380030f0750681c4c40e210300304001c104020400384401852090703400766004034050303d074201603400026801c0c03076414501508001d416a51085004030b001841c000340510084e00305089030418003c0550b0020700400c03141c0e035000d54070050420042d101b804d55110380451288200050503620011000a02210b43e545640c210160014007d803409075003020201e40a642c4909002c40c0b0805400580c1c818101c868410302a544480b007451904201c4440b4011401c0e8545a14980c0118030560900b602c10a290402004541000c0c00c458400d8400700020007105500058140409420014148540d141c40c41c11115281c00b6602c010500940443c4189 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916274550 1250 916273300 916273373
    0x12060b0604230f031203040b060303090d0b01181407030906020f18280312031d06090d02160512030c070312030e0d080705070606050a27020a0c0807 65
    0x40d1640803c0d40c0107202071420070308041e201c1403500c0303042613040d5041c400078011820610281d074010b10007400707880c40c141000010805100b0210019140380381c4a400401c807a2101902d4040c110500480030010054404400b000e0403a002d0078110405840d6800c4509024682d41110301c08400b1400d843d9450b6008a081410038030711a408500c19802d590200761031301c0c8640001844031b40300241440400e07083d59101c030704072113104400c030003010743d80d0000d101655240c211820000301c144c401040a86882c0003503c1c80c3c00c00e2400c5440843d00010220380b85800d40c02c00c441e05981040716402e14100300d42e07002c180b941c014003811a90601c6030400c00410b20000c0003050124a140d0f81d410b100d4104044125643d55070295440c10000701c00800040b017641c400e8000e03286130380c810100030034550f64410015908001e40d404c1101d140014111482c1e0100800e640c048030450001e0055007001d02d070040107800030414140c06007204200092400030055200484800600e214040313026181001440c1c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916275800 1250 916274550 916274609
    0x2006040914061e060d0906020a090314070b0901030c0309080a0c0c080c09180c15040f14031c0c05070605040f060806031e0f0a0503030a1512060b0604 66
    0x81c0141d00300d040c0441d0322030924207904100c1901c24030050000c00300c0300003072100c43c0d40a00300503003440740d80d030703400f000026054001001c01900a0355154615803d600b8500080d044615404515a20401c010010000110306907540c1800900f0700090721000e000d01a401b41c6402540201842c1d4000b071030900d0702d0341010b40000b041e8010121002d0b040d484800440e907503481d1424a907130025a10780024801e60620900d1410055140c0641e441c0f8034041c0049240000513500740d0048810219003406074050600704000242b5002d14040700e00c120b44000301e074441d01d1a2040a8500c40300e07416450105005038072035188141d101e000c88030140d503100401803040d08240a44074201c1410300d00040c07951700c66401d0500800d8014040d00c280500d0403c0003890301017511401c0000e00500034400c5154005010b404103960149014542c3d0740341500c015821a0200c20b540458400350380800d00a041e0103888200016500460009020003901300080c490301450380b206081c1c1070203031408507440e4024400c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916277050 1250 916275800 916275821
    0x30303150503070b0a020c03030f0712120c02150702010612330e1603150f061d06090f07050a081b0a05090405070f170a0603021207170a0f20060409 65
    0x31f94540c00d007210105a22881844400c43c080c0605108100204c0d0890080c1100701481c0d060280264403642c6410f426100d5182003c8050b0300841d200741248541ca10001c1d62140051008215607402c02041102e03480d1464009000e0741c0c4510302e00c810b101d614564810701c101c0030001d00317406410700b1900c980260100805502d03141c000c255240c51032141c100c072150241c0c0e50002003500d6058600e5a0800206030300170340308000d01e8895900040f840c01d0300324400350901c000e800b102558900242401051900548070105070311075102041070003035002054952400340b40c5480c0300103803540d4072160b1213112200980461184000b9001d00c8984c2c200000707007403da10980d41400309560340c1c4e406580e00100b107107146001c40c24141100503c0086241d60642c060300c0002c00291680c0c0b03e4000c5503418a03c8002d00ca0658400721007444110041000c03441b0b0003501c40010804c3e1441c43e581e40c0b198100d0018004d081518440e0031700d01000310703003010f038250341d8018101035103940d503c40e1914040c1c1420082c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916278300 1250 916277050 916277053
    0x304140709090804090e070506190e030c01020303010e0a02121501030c08070e01120e01090606050310020c15040221010507180f0e19020301080114010b13030303150503070b0a02 78
    0x1100340490144410550b08225464140740c85c1602c154080c019050352181c0707a00507144041810354070710010300310007842c9078403142200b542460b016050041158031103200c2c0c0d11011079001e5580c0d0010440e815281460f60141072903c581556a000e402100c1c1d419000444003000c0101d14441d01c4480343c0191000d0742e062006c41d00c080001d80395010706948285c009919222042029409082003124103d0720401c0001d0604005810a08560200004880860301c6010030131442c90204801c1541c1d9821706411403800c0805401940d6812554402c1508901713810005400d650341d41e655a03101c400428a01c0540b201950380841c0200b100b201c50380c000c54581c06208040e102c0e10f03000070090750045450010240d081140c0760302c5080009003006460703050400d100c4c41175142400031f5402007480c1000864510450004516010416040307010b1000f03060201c84034903019540c000d0100c1e60903007400200020248084071010f040c94002e59014410f02e0320005420090308020404914150b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916279550 1250 916278300 916278313
    0x12070920190f12020c0120030f0a09020a0806130c2709140d020a0203070b030c0304150b0d11040b010203131502070302150309060106030203010f09090f08030414 71
    0x20300d6240112403101c46007942200400c40d14a0044a50510007001401e200f0b42010070a0401c2080e64860314140c5426510303001007807002e40407000c42c091000729000415041d1714190090444400005000b0300c82503883d001e002c006c2d0340b9020015005450180f060343d695151142902c051002c140208a0300445600b8001a4040d070741d224058140e410700a421820f100f078211840068182c00c90242c0350f5080b04202c000c00c034141001003003030080950300a0280b20403240105410805168854121901e0800c00c10201150890072650f00540c03040c020301155034204549401881c0034600141c001414400800900c410141240402c400c101c0d01881400591401203840303009100c031003122840102d0042c8a0321041c14011120000d4620440f001c1c140d40385c0000b00004109284805110000018407041c07075024050f079030142c04142810361455140900103110204588200c071103807943c0e070013003004002d9501c4800c130003150001070307660f160704244c00e00c5c1100d1540c01c2d03c01c2040e4406c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 916280800 1250 916279550 916279601
    0x60801091a0c090112020c0a0302060901140f0a0e1c050405091302030d081b030f091009170c01140a1b03090302070504050612070801050a200d0902120709 68
    0x9421030b885081c40903815810415140c0041d1640510905d0403c0c07078a800707201c0d811000d40308101441040307000e64003d01c401c4c18a051020b0031104288bd044d80c403051600100304180b880019100d0704580d400c800011506040c200c1282081c02d0030b5002034040300c400c00c51400980d8028040c0040c1d07001100c01c200d039500c81921540010300c0c4460003d4043d040909140651801602d14603405002c94220404000d07030202715541e141d200701c034041c00c1c0ca00e0000c01d0004203a07040160080700c000b0cc003800c00807009541c0319030480141c1e0300350f0070301c0000300054201d203014000e40003001c068650f5410505181006100321000d007042c5413240840d11354250210408602c68003e01aa80340c2640151801c641400d0070b0001074580203040542000d5450325440d514501001a0b20052903c40d00000d82c0d82440c64100090307a100d049842c451680c2e41628a9130007940504a5125004001001a0490f864030200f041c10010351004200c2d4000c400c00040c0c0c0c069950003950349400368559400f2551100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 916282050 1250 916280800 916280843
    0x80c060a030e070602061611100510080f0607030e0105060a090509010e07080703021f0909090807050a050c04050112020604140f0d03080906071d0d051002040f0509060117070e04020d06080109 84
    0x8c40c040d0071050307403010f840004003108640c030942e0880001c0a95942c4107827074211144c80d14094406c01801984800304004074660b0500c507003541c1d280e00d01c000b84a14240400041e25241d0300e40901010395540e80c3c003040540409510015800c0090415034000700c0d81c0d8281c10f03840c3c02c26403200b80d0007a00075025440307420402211541c20a40e40c1d440322001c0f03c1c10030034000c0c000c00311501c0c210b90f070090030009600030400c10080c401c8118451030042450010b031505003c1598010703440b61200003d886142e20050f0341c4c5000791416500c0c0710034440300300c040030300008442d003094001840d0440c450b54400c100b4503501440d058815030035102140c10540b50850101c8040303e0403401032004110204000245282092406181078000c0c411034800308034201c443e00803a0700c60b6010300b615000032038040241c2d0500101d0031380d0210007400d01a03442001300c10030211100d801400e900400c01c1903c2d0620895465505407035040300905820410b5689070081c0383c0c004d0204840694001c1e0700c04064800d410708 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 916283300 1250 916282050 916282067
    0x3050d0807052b050408091521040501200721050403020d0c09020d0f0b04050906011a04030507230f100311073801080c060a030e0706020616 62
    0x1540d4441c0d25045120810201d00c54000c44002d0104015224192a0f5203440c02000e002d11b004101440d9102080d50801c0030180e45007a00340c0400e04240000700900803e41084401c549480c44041071556030351610a005002075405000e080c1402c112004030700030500040d100452142d4042078000c0010802250401441300d032203000107200304070500c01801c04284042d1071900c6110394211094a40300e5200580e0046810742d85540d40e07030f007002e03940008640a0180e090304165401c112a091140103152681d405004480b41d000003203014101809108044030300440c0c01405940c0c14549520004a0741502240d81500e12182c07051508a01d2800c003414200210008020480c5075060f05070a81c040d100981e044803807107400b0b0182d90007003080781c000c01c0b0030700d03104001c003448500c00ea11000f14410075010901c6a00548540140020280044c980e00988021a036594076000005021406045450b1031803c0ba8082d14600144803900041e00350f00441003148003210421441c94111840341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 916284550 1250 916283300 916283311
    0x1050610170606070305090a0611010609140c030603072301030c0807170603070503010f051f120b13080705010605090a0e03030117070b03010e0f010e060607151b020703050d08 77
    0x200c1c4000300d401ea242a10051a00707912904066085c2042d281c0064601c0e4210b6210002144500e0300c0100c2d10802880b402014141041040202d200a0340100d040d02030002c0550004600000c085620b660b820480c030300060a0708034a8000c03844954104082000190b2042c0e400701c0c0c248149030010034054901503205580e240c4d900103000340f00030401031804c82c0292106825019609001c220340e18203000d8054400c10002002c5503504000c9001c3c80d070301200b14681130114000007401d00203801c00011400b5825008a040b000035204e00c050102c40e60301400c40189995400902c50781002410740200c0212501200c410599944e1411850180c17080300c0360100e0150820001031009044100ca29108400840110342c1020384401149a0b90342c000c1c4c2000c50051014010002003054002046000d80582c3c101d10826040100c08107501c1c4c0030b681d100900d200e0303050403005000295507001c008a540100038051740d100300ca2a0194032051b40d40815569400303000c0700403800d1800780d5642d50061 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 916285800 1250 916284550 916284587
    0x1201060801150c1b0e01030b0610020d0e03100f0906060e0c07140c0402031810020a0543060b0402030f16030e030a1d0406060f0309110306010801050610 67
    0x11142e14049402c000703c0803045546403440f254600a00302003061900250981ca0085502075055041c40c051019006260900c075800341a01e080c0d0480d40450001c60260700c1c0e0401c19000105080080d00f060890b04040c510a440d04001403100642d540001900c0d50180b2020070001e40c5940c400c548130781c82103420800054041200c2d1000039500a00e407284075000308203450b81c2940480004007664020b03503c01328040740040143c4501001800422902808084110702c0c1142c4040040c0a07405078016586250703298035006e6005445074018081410050070034240c1c4805092010b50407002c9010303040d1141031030100c0020342c40c01c0c00e2080b00c9c042d4503507000c501310380e542c1c00c00f00c0b00c01c01d80101c405030308068582862105940c0104090411070103540c46075000340000004940c064a00d000e0214400c60919008004540e0440300070014a1164a00444c0c80b4020741498008146c134826002d0f090300c185800010480c9042d03024900810781229a44103856400348110341c245290309030725089 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 916287050 1250 916285800 916285829
    0x150b01050f07020303040b0309060907060c0203060f07020102090409050616030623030f0a11120312160e0306040501020901110a151512050c03060a200d020c0a081201060801 76
    0x25100c05409080b000f84001c045a02d016290300f4000b14903001600d010441e513020b00c040c8105c040c828003900300581841d10b8050329281c03460300001d69501d00a006c07000c00305407500202e050a4400c1d01191503500d03000e80140402d03441890a16a81c10080301d440c50421215008122030a12038010030046801000c1070759008403c0d601480302203005040c0c0161705100301e00ca009200380c02404000801401402d86003682d00d02030b414042c420f10b0420f08081103800030003081c1103002c1c240c1fa8040d004bc0c2e501c1041e0b03d40c51003a80c01950303a50f000c0c20800342d0500c100802c100401030150024001b500013030303940b1450380b050051220741d10314903504020429a442004141028000d40c001003001180c05081e00c607807640c074200d48010700004441940d1a40200042d0412410204070040d0402443c11003000807591901c5064030740c44941a08281d01c0e2400580c03c00384c0716454041d40c150046007070940345030091520300041c0ca54000881c034080912120700006555002d030210504807502511510341c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 916288300 1250 916287050 916287067
    0x114130305010b0103092f0d08070c050904050d0e01020f0a0506060f0d02010f03050a0603061805120a09050d050f010c05030a110f0d020c01090633050a0506030703060803070c03150b0105 82
    0x8290131a5107000d401c7c4841c5105d8450b00e80d90382144e41074114003840c14a681c030009401c1c04005580700d50400b60051600d0710520002a000003550a8012064508600c07401031510040341080768060000301103205256050b0709100021420301c1c0a0340e021a0820318080703404050080c807241c041c001a003c500c01420020aa41c081e0300400d5100f00300c01800203546841c0d5980380111140004401e040407101c01e034000802c002044449034440c18040c2141c20182c0c50180141400701902034107000c0c0ca1510481800c10008100302004429090001d0000304680c44004000350000c90310010202d00700070841c043c110f0010308540000d06061080703860101c070002c819000e940700322081410b40d903803060200b0100d08070b4810f1002c54501100e16451a54a00d4101103c40040f241060a04500c20b00200700590b51114400b04540b029291a80c0741c1d0341c0d1840560040800c2e51081c0754074000080e01004200c980c84c0708105a9114415030350880f808061288100c82c030051002d030200e18100030020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 916289550 1250 916288300 916288343
    0xf020c10061212050331060b0108100b0703200a031e022d1c170c07060903020307050613020a080102090a031b0305030d05040606081b040b0114130305010b010309 71
    0x5510260740002400844202c0310032606d422000d241e400006402c0c6030078074040000301e02643c2402102481d019440e41061510801b00034814852140017050010b0400100350054085a0302c10030038148c203d1403200c3c482c0e20140c0340c03101c6010490028030805d01c1c004101e0300e0040c1c0111a828964000c4c0541c1050745240e02c100c44048a140903400040c40f4103460b051800c012488000c5404041700c4003501002c00007400c1c91803103904024040314401c3c00c00601e4030321201904c501607005080420a05035905013642507210348400a0a00d015501c1003092024000e4a01c1050030310a4642e048800ea0701c00f0360900301e00070755000d2940410507410410100b5840d40251440d440606496000260780350750b030301e10f03603401082e05c5003c4684070070811081c071034544140001001a4005012a040d42e44111401c0e428046400d0380f150743d5900d400c50703041e44160b0001c007043d1076216001d1354802c1c8100581c2c008005900c812540c7c0c3d0300f083c1080d8919403090007806111340d4061811091b01809000b0070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 916290800 1250 916289550 916289557
    0x4140303070f170c011b0806010f080402100c02060a05120a020301080a0308041b060e0315060a1814070804050c011805220c2003030c0306090702010f020c1006121205 73
    0x280602c0d01c00d1200030740082d404c0c81b038509040c10700b00680c41c0f10310880c034010f0f2020b0001000075040c0404080700c0d01001d5040031140354072035411a80e8082c80403100e00161004800c240c070180d00400081220040d80303410100801b01c4281c10215995143d84101451041c1d100034041c09842ea004076184c040041e0080e06504d030424403130070110b07500001c90b0800040d2010603a2010300001c4003541d840d10716040500440e402034100031044042c40c070380a000b1aa5200083c0b00340101c0e84c140312044140b40055910510507601351b082d0804540c02e0a484c001c241c5001582c1c155040c7c064004505600c2d0b0299154000c1c4102e80b41001080903d480c003000b030100c002c1640b181c01c80c07454454029800e09180704100082029842e842580ba41499030b554040d0249000301020b07500810600c03091040d17042c15654401400c550050450342c401904a02501c01a106950f0040c00410780341b40b10301d00481d641c0e181400300300b01044541d5948203154501356481e00084d00040300d640607031300b800d40300d44010b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 916292050 1250 916290800 916290833
    0x415150923060a02100c2307030f110708030a0c11030a02090106030c020f0706020609070e0606030a02161a0a0c0311030a022a0a03030c0f090603240b04140303070f 72
    0x644203100754401c8508140d515018101000406940c011f90301504084e00c50240d003c2c031090300600b40300d5950360260901d04800788044c103001094420a446c110104919009001400b080d251540c0e00c4010241030124000400c0b0707031004031100541d529040002d4100c11450b001018408241d1800606a00415005078180110b01501010001603001013080000070000da81c002c01062a02418403400d0109a4000500d03032a803000911900760b413a44280e80d00800c1d020b0303005070303a000c440c1d800b15081540c01900408441296241031076402a8407500f91040001803403d1041ea90326060890498041c1001c0031448141880806c8149006a02500e54410304c0d8071304901c01c00740050070b448510030303034905034105900c65142c01c020543d240c09101d00c4c0000c2c0d4200740c6440e0f4a0540064211215806a03208150341d440300800c103544007581e900c0321181401055404a07442c1d0b03000d00031b41c1d4441c2c02941c2c0d203403c85140c4900700b0b0400004951040741c01a4100c3c44024040c0d5070512200048540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 916293300 1250 916292050 916292053
    0x6010e1807050f0c0a0f0b060a030302152809060b0102010b01121d03030f04062a140910020f0105090a0b01090504050a020405130b070206240415150923060a02 70
    0x42070002e44080041000b0703071b80a0b03c902100d00341c1c1880d0a03114010018407007801b07405501010000aa00020003070203100c5151607032202c0756500400820040300220700c040c880c140448440c00c0101c80f40e0b200001c024024402404070001e80001a400d80d40c00819143c0050581e021700c5180054640c40310075004d070220f50707401194900005107443c541042d41c540091107606814041005681e04c120907281c8010310700031040360396490230a422403556201e00c500340141005180007070100c010413100521001401d0410303403010040002c0d40d80f51480e400860301d41c030303101c0802d10050300042d51910850b4011349c0d1404903030070301401c1005031070003600460302407060084160040ea168040c4904c65503002401c42c1c00b03007806041c9030140d440b0103081e450a54004c081409100c00c40000ea410076241420000c036111030700340001c5401001990142e02c0c031403a072a41c02154081c02c06800c0202d0910300c0e900c1d000180c0d20f035814004e02e01c60b4078461102b80f0461454024203030506502421903400c4a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 916294550 1250 916293300 916293307
    0xd0215040204020f0307050307110a080a1b051b0306090111030402060d06050901090b0f10081f0b0d200901020309010e0409061a10020114061c0f050606010e1807050f 73
    0x101300052075003043c1d42050210303002000f00302d601d552001c1010004950301006110b03007201502c1c1d00006205000500c3c04001084c40d0240485035100c0000603e00d501ca01111950700303038041404407140c0741100ca10322038010f10010408000050062007081c10701c1c11112461074455908001c00380c3d000158280480e915403130005440c0c2e64580ba0b41d402040c0c1440e0204544601c1405c0105215664151912900650289591407540004c0300c1e9070101440a0b1a003401d00620740401c000402540200112000001c00d03561450040c1c10480810a0052040d100c98840e0200c400341c6000f02d0350300034010303031091000041562280130012001c0502610020700c501154441b80252245200c29048200c10b000e4200d65a041c0383c9075603960f03129144000c1003c400144e4070305080e0803010740000d10400103080d107802440c0881d4555010319600c192a294a07401a00d007498492100315102404076006c1e145500031810131b10541e819507940558500800d95500c00b0603121900f041d1b0620500700700c10b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 916295800 1250 916294550 916294567
    0x101406030621120a02011a0117010315060504050a090b06240304060216050d1e0e040e011803020604020315010315051021021018030b06010507200f030d021504020402 73
    0x1004080704c810302d41c004107492034501e80c20401038000d02412410400c0c4400305007070003052021468150f9034850041c0e13411301840913001c0302502c410f4001d247e012b40b50400388000d940d070640c014900c1600c281d01c490166510001008008070016526540085091844608016954000b903601c41d1044200504015081905105031003080b5011a8154081058130b10000e410880501c00080e0340d05040c507001441c424002c081d00d0020301c40d03e02554a581d580e524580c400c0d0405110101c071340c1c0c1014020340303407414000d640e41001d13141a402402010380000d00b82401d8000c2c2410f0365040f004c103440c55103200300324900912000307200145044510f400450558840e410b5003105681b8030381f4842c0b810b0b100d030042041128a544d5440180690b00d22205403e07005800c000003120313040000030145541c0c240050ba0780740319400c802403e0f088070061510b400c104d6000c0c84600c141065039802c440e0344011040c0360b601e071440001d4401603444610034151440548025a5100748050409424072600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 916297050 1250 916295800 916295833
    0x110d0b010602030d0e07080d031e0c080f01080604020906010804170c07061d1507030324090c48051e0102040f06120212101406030621 59
    0x7030304014016040020403003000d28680c041c2c44030100019000d17140183c031b0300d03141c0c3e0ba803502c9240d00764050540315181800e038200e2126000f0601210a18180a20701c0321800041c0000070462b0000e410316496000850380c2040000c507148641d0f8050002d408640390078005403542d900052044a04400d400c003201074000b0341c18041d140161074880201011410f0a0025098140b00e107404880310841030341c0d00c1120ba071101441e42203d001d407030503643e4070320f0320381030480240007092110a05402d520311840c00e405180304140048a65054003080541200c1c0c00c21070b000121240c524080902c501403405402c0459142003600c0142e81108101d8080d582c41c010303c00007c01a802e0700e907a08441038001c04817503210b40c0c05640503207017002140350600708496a04480c105020380c2040049a00359501070820580c100c600d124410300c4202c440d443d16026081184125008170721b410812001208000e0408500340c03405805c00510300c081c428220f44510840483c11002e41e0460303c510040d08040c1001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 916298300 1250 916297050 916297073
    0x60c040e0c09040e03270a0303051e0f040f050d0c090506040603060e010b0325030b06010c021201060f0501090b18190329070519031b0c0b0c04060203030103110d 71
    0x1a40b0061502d65003106a030074a00d02000d4680381c86d0151000400d186950741c40001d4003030301e505040080c1c80d46900446130040c0c0d14800c803605c15140000405030310a40c1c0060113002160207090043c000c1d607407260705002c080e1641c03c50040030204c041100340400c0e031007600102d03800b2002420028250380d8946403003041d10b11040c0540b140b1395440c58030850074201071002010010340d01e20751802c0040061100002c4007a948000f07001c2d58a480c011a2650f071003007941017000d0b034004102d030f600c2c100000e001030b0007084107116040300811041e800185650140400104403402d010045060480c100c14043d070400010f05c40507404a0b0700d50354186007000c5584c01d8070107136000f0352500910031000070341e0348040c2019140905d01c0904500420a5055014040319003110001d049503408440c261025400781414034400890b000d0000b0840800c00d5200c42004e044070701440d51025191501d01075a41c1502ca05d009040050700304000520100e580220b4140107040c0262140894404546500c10b1800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 916299550 1250 916298300 916298321
    0xa030c021f12140106020a0b06010309080712021e100504020a0308280302070c26010219090b0915070f050a0303020c160e27010612050f060c040e0c0904 67
    0x110540065010942da502c507455003c42c100e41501019418408003075556203001d00020b00202c035860005909034400d412201240d54030440845d10b80303102c1e2804030398003a840c1441d407006103e030f140e0440744003020441e540c103d181103d02800303141e0b040b000c4180c05440e00800698000001110000004030340c0070090103c01c0084d0719040c5442554445001003210728043d900c1014014400274020034810500d000885070b0314000c1d0040c0c03d0320f42546400106155400e51829440030465100e80400d10a0210207036286031b40e60210103840d001c8a0b860ba0049a5107180c01101c00202e0900321150840244074031380c0600b100d060811038554034180342800084003140000c0d0046165003100c03808104000c02034140d803500d2000d0074209904801d40c1c20000304040d1421075824861004041c4405140141420340780083c0601e82e2149910f100600710302c4412290f512a000d00c01e403541070007141d1240103001c180403007450a0f1a24204401c40d9001420710114010104003044543e99140300300340c0e111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 916300800 1250 916299550 916299557
    0x10031104030f0308010b120610110d02101103010b0409020a05040306060f06031406030a12140c07060f08150d080405041e06090c171302120606090a0e0a030c021f 71
    0x528103460000c204d0001a40400c14941040c4411020949510000c0f64084010350310802d500da00c4490072501c10303400d002420284d00a129181905550201301c0740e114801d02d2005006000100c6600003c40c0b10900c00d110b40c00005020070301109506400800490481e0b01d07103d0304043d00e0342c072960f00b15a00c0d40d1148a03444840a030800c0042c0e007502511444040c5c8002c403000b1858141d01094990b160884010585407000c1a00000140159000485464100f50258885510030001503640441e4041ea9003c5645d00c3c40140c6603500c0703000390300c0c400c155102d0301e4001c0385003580602070101000c1c0000c8507d81d074103200200e00c1e500c482c4181c50480c81c100346001d03d98011149510b04442e60381d040504001c0c103001c0301c0c1c5903050300b189001070082961810607205a83d000c11040c0d40041e481d400039800404c0125000900c1400a0454090300303086a641d55180c46107060f00b01211301402c4009c0854020b0132554000c41d01806956a440c4c1c00030307120741d010464280ba86002c0d1001b48030048c011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 916302050 1250 916300800 916300823
    0x70803041112190b0703091e080d061701240611150901050f060103020a02120d060e040803070f0f080112030903060609020403051b060403141f0b0909010603020901051003110403 78
    0x388a20300001c585c0001c218242045410425103c1c2c010040803640304034001c81d800410f8200b003014040c21070b807140b102c40108008aa8440c001b60907070b103070881507220196080c940c44116481000d900c6220951648092030b007030a180400035111039100e2000100140a01020000400001444a03200780700c880000529460801c044d040fa5080160807241050700c14419022034540000d000d101d84001b10700001d8590404448400c00707040702d0b4000042124040c4240001c10140c803021394083d448503210000d06d403250303c0b0202c8400b07032400a26800205404010012240c2405da10103440c2c3c001e01d003481445407282c60b00c3e025250b4548c0091a0356500160400c14820244140141658041040c3e041440901e00040180c041c9020240c6411103440700000346c1c4204100c00d08100a5032510145410080e0501e10000c0064421190048802e08000341d10f001040c41421b0030780f82d0003020481142d0a0034140201000104041010305648180f0041c2c4030b03a0800182c001548102d200004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 916303300 1250 916302050 916302053
    0x25032601061d0303041809050307050f120f34050607020706020a200a080109060605010305011527260114011a0a14070c0f050607080304111219 63
    0x141e0318140d0030110002c8250300e21076803a99002c8200c60403110101150709482c1c03d08110007005180ca501d005000c1d100005d0800c040000109107050000710000c01c0e518181d0401c010b000c0c9500c507104655260000400c40f41c80402c0070103413808454400071120840100074141e905002c01002602501d595010a0422003065810042c00c4050025440604000360750755480510305080c9241d014000c4460058410182d2a840608001490104001e100e2280d4900703011006061074040e03240040d04100021030407000100440e1a11079441d42c4101c40b681e4058490624036122001d0085c58040030381c0d00040c4c1c0e03030303040c45a600003001c01c11b45d03420488c5c00107a110b821140300e50042904c50ae5810010041b603d00c2c620b120382c100345072045403592401c449004403990200c140040d4107502c40420304005000c06d440c681d5080e20440490100c2860300d0701e041220314010050010031100081001900040040800c0c40d00500042c101d044042881b1a01c20300f0603841108261403500c01440400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 916304550 1250 916303300 916303307
    0x501050a0812030f070c02060d0b0301150506090f0f060f04090e07030c0b0a092102120102030603101a09040f0615060507020120060c070501060b2503260106 69
    0x40804500400050900c00d05542d81c41c00001d19030121081501c0005070a00e000d9022113504660051109030f45600740b48040c0d000304016822507019601c0c00c0003621851008012407401d59000801c8103003042001000c003c00d180800201c0c5401030301c41c4204400c40c0e00d518020700280200035003025103030b078149038541c03048405400c100e1100354040281000800c821400030015906003c640654030303185100140d03000c4e240c0d5031014001c1031006070042818903403100341d101c00700d1007210755990f55142d101031103090740401d0f20001d0b450713040241c2c0a00410004d910880340d007400343c2d1550078086103030f40004145950449040d202c118003004400104041441001189402d0342e11038140d940c00c2a20041ca14061f0003402818403040000c0100540151092884103e40e000c00f00d51192030140050110340d00a0300e0116419800c4c0310021444401320000d9510600c2da0500341c884191859011084800500c00141c050010301c00d803c02d06120075249114566220044488c025490220000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 916305800 1250 916304550 916304569
    0x815130e1018020d0201050706091a07121401060c0c0302181b1201090908070b04140706020304050d2310020414031b0130140708390d050105 62
    0x80542001c02c540b07100607600d9151442030030b502807030895121a484e00c0c100e4020900b0741c0b4080c20000e084002d001150303460500113407140f00b03140c0c0c1d004498130b4101c61082c01e4868408584035966a504018081e103807045507550f009500480c48110b81c19920f402080c041012207c14000c12254002003112050800d004914041c036006001da01d80386404040c14071940060103000c1c22251560300c00c1c814000600c2c1680e00321034024245844a0a1070301d421aa011000c029007440d03809410000104240040305581c21078402800c40f0301d000c800741d17840e8160000030711540000070400101c0040000e104001500c200502404010f82e501d090810000748400300d88080d41c481d07407041d03d00800148015800501d648405c4c04c1002201c5815070b44c0d48051a42410b04070202c1e010380700340d04401500740c0c00c030038000342c03020300c00c0e001584542d841180e40000450b003c103d030004d101d040c3c1c02a0405543c1c0c01001451841c0410007815107039440070059404422101c1d045511100103100928040300034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 916307050 1250 916305800 916305821
    0x100f05010903030c0b040309091e0507031512051e030904140601020a03120209130f0e1c050f1623030a0e040e0705090903030f160815130e10 62
    0x1c510414990b68004040c00c2c1400d900a02e6503c2003004101058010340165000d0090010240141001140700c100d4a40c08682d40b030300c1c1e107400d010108620398040d2061035000c1c07244030707041e4000c1c0d402c003504100340c0c0018420488152003090142c1c080403503504d1040380018043e5014540d81c1d0354820800080d221041904120000d5000600080d130382c001800c00385160781400c22021114400200100034007801405a8010000c4c9990151049056001c0701e003181c0c201d801042018003280e00c055592001c54400d10302001e10003001c448180c01000540014045405c00a00d46652596146110300c024a0122201254226200c03c510390f60f80d40c1c8050b05501100850908880310001407079080c41c20003180c011a65403203240d118140511801024110140c60401d032030405a4840b566540200d030002c582809500100300c0c020030034000c4103610882c503a6054116202c01c008201201c0f0741250b51079000c0611000d40303243d07000c0c40c0522003000362890301803d1200030510440040d01c08240b02c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 916308300 1250 916307050 916307057
    0xc0908070e0c03070305070903141e010504080304030810030c0308191d1504080d080615072301090209010e07031802030a14070e100f062d020a0803100f0501 69
    0x104030b41080e401065a80c8030190f441c0105c0c503616044800e4800c8946a00003420040d00150a00800080043c04610380700300c644e10340d12810050845107089440c00d45000703010090810215011910071280b450700305441e140c410f002d15a0780c0c3d4501c01c3d82c04e12039100f01e0701240c2c04510f01102a80014503100c4140c0c82342460650346807007480b1070b51901b0100002501c1008401c000300c152070280e07010b50700038201c1402115550029440041d001280850fa0240300d0174000e0100444c0f070b02e1100c00d40f41ca180c0e0016501c0d08070f0400290000381600c2c05000b85039036650b90b00d82040035a490000290090811402107234450034101700080076603070780914043c5081070090b403901c0141c400103607820020750842440c01e03280000002079800e0003000e03407040c0e031101101e07070500c000c11a80020780c20450340c80d0b540170b105180e0b8600041c1c0e0080d4035100d0803286401c000070b40c0500711422001d0344291094500c10b40f60f1200c102d5603003810035013090f41d1054070b041001d401031003070f00b4000e0040c00180100b400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 916309550 1250 916308300 916308329
    0x306091101110606060c150f060411040b0405010507020f1f0807090e0604090804180b0f0a0b270d0804050a0f050a1503090804030302010b0a140307031e05010c090807 73
    0x11503030f40d500000c2c1100780030740c00c002401e44540c072062190461110a100ca43c00d568100719012030841003055580d2481145030403041da5001c40e8074011641281c10b507801007820146080019140fa42203a10709903004200c01c2d032409a9030703484414080b590712200c3d59103895003c00410052429200802500c248814100e0500c420032a80502590010003200c01090304580c0e450400c526015507480580103c0984000788003840d034681200901c05000c0c4c803504d14103c41d8504219024180d403013900c0c18118104440c840c00d6a000301240e11200c0081c501c00c00802600000c07911481c1f0b0f890342035030122001b09060019181c1801d0390001400c200001601c0281008005410b00c02648118041000391500e02d50056000350041901780c2c0d0819125a15141e59007000390180010300c090754450041c500c4080b41c40c014112001c00026070150092920f203086950301180c9408104034599902070004003803000960034012081e815082c2d980344403a4901e0001000d02d8008180c002480c0d100001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 916310800 1250 916309550 916309577
    0x12010305060414011e0b0d02100503090f06012d0b030a0f0e010905030a32040e0a1514041d01060e010909021e012601080d0903021302031008070306091101 68
    0x408024824a4480001c003a160140011f41003111224001c0d00711464600101c03903140c000c000345203e200e2030411740d1103a4800c6c0182030b4985200f400b03000c0714010340c40454480e210030300c200e00c005030310940303d00c0c14215102d03591103c0d02c0d00100c8030b1403020b9448a0102001c1d04260046050789000d0303c0c02030000101a5407031944900a140c240410400c40d010030b0142c01ca000ea1000c5d0f01ba813520039840011240e42056151190b00901402401c80a140e011803110820b5100e0319141c8944001d40c00803080c01d044070f1615040004980310f034030589410386107070b403400261910000d0350448000012132500c0d100c0c480b800120140c0c014010145000580d41c0942c40b1071841d43e049041d0400c00d084801c84010042c0e40440750140d4044170b550891059240d0740052810b03050581e450601141d00260b51814101c9680090f404005d410a91907100200440c91940165401805402c450300229031101441464210f40f64002e40d101926031442200303004444030401254802880e050701004240b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 916312050 1250 916310800 916310831
    0x90501080c06090303040b0c0307120c050709240f080d05041a030604180b09070b280309020315040c050402040b2d0c150109060e07050306061201030506041401 70
    0x90361030081c0208400503c942140d1350500c01c8802405074603a0003610f0702080e00030140c0e20340094804980107060b80e4104072210303010380c280702200d55100009004103800d1005090140040402c030442c40680d5815004842403100c902002524250302c84100075403400403050715040d81c00d1042e40c01c0c0b080400090160b440c44425140415200703101032342d43e0fa1641d01c0440c00038050000d060144424078403804c01040140f18905002c0e800304c00480b203600d9280c0c4140c004c1849480801d695000fa507008440d01c2d08020044441c0c0d4003101c4c00c000070709940c1a004281004403101c0e0b50351007510940f080104021018040001902c016181107040c02d041c058403060500c2800c5078541d00380d8921140e0100c02600079401e042400c58280626111001c4184040d40c41d00503070440c14903020b0400010031003808070b100c0c6104482014050309843d450381041505c04d41d0004e408160080c90400c0854070501c6540500c40c0218801e0000b0003032442e01d414010503606034170aa01c0744507414000045c00c036007074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 916313300 1250 916312050 916312063
    0x12050c030c220f030f050f190b040609080703090905160c062c0a0b1b19021c08010e181b19092c060c1606110c0709050108 54
    0x109a00100070607105011034a00e90704081c0d100440581003e2004002c0101e46440a40558800d40c04c0b100507001c0d000c1c01c503464440010110303020058038911040800d550607016600a4050b40340050783e020a900c49400aa001a0041c0c022549049080240b071840b0300c101c681c40b406100035408080f01070f20b4000d01a0400c26009084181c03120030201c9403401a00815502c02d40071012017221000c90b00c4503940781d241c0b10380e064411074903038070001d10404034230045c0b10300c400d9206034014a00301c06605507010321200b104264045200b090480c240b5454003842c0d2a880e558180c4402d101076140c180c0300340e8032100042c030b2042035202c604040300000000103501441204884e000003c248004800303d0801400c154070080110415400040c2030f800c0b42d8088000000c48110441d181070b00e221901c0e28404500d54400a41d1f07110380009155111001c001c0c001c0c0891511642003100e126840b20810340701e040101e00e40740400020041c0740c104042008d10010156244184041c0d80340490440e01d488 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 916314550 1250 916313300 916313317
    0xf0c030708280e060703050c160f2117190c0b130507180b04150317130302090705090402131514030c0901090518040b06060f3712050c030c 61
    0x28000c034005c020980180c1c00e0360004040c4d00100c43c0b82200c100d002411000f22403041d4582e0650410000c81c9690083c0b008024400394030500c0410080169605240d441d8214590040402c09020385660b849440080c150201590b540300301b49480c02d401c01d8051504003624041c00c00c08801d10072000103e001c110303801100c02c1c85811140d0300d0320341c500103000b4141e18034044d50304c94034005c10000340d0000c8125000680b4002d1029441422007500e8881281c0b041c940700d03c02160210000300b0061421642a0761700c40c806107466414203480c01e0100c1c00340d03000113946000360341d0240420f0041c0d1103141400101303041c1901e007928181100c628500201d10000d420340c459980e0004034580b05900520506004040c080c00c003294180415aa00c442a1411760307085502140d0040428a245083d0b81a07500c120f200110403468101034030a1340942c00f031031007100240060102281c1700000e1450100f010050041c0e29421400c01000010100f200d10081c0303030700d106080030710901000c038008030700360350106 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 916315800 1250 916314550 916314559
    0xf101203080619060804110d051504050109080c030c0c090c090d0203120406210c050a0c0f0203010c0201090218040b01030210030f110406110708030f0f0c030708280e 73
    0x1a142c10000c16118840404103000e02d5844040c009000d42d40000342c01e02c03d07401892494030006062003040081c503281c0502509070380c41414440700030705000745010b8205210f44000110f00d843c5070740c1e07104036030040000c00350315400104200f4410503080c020043d104604807400242403801d01c030000868050308044a0107107200c94410401c5403010051501070444048003e5103c6544007001400b00c250b0303280205081c1111405004433207041d0080d00320807003280d140c0a0034901d10342c0c422240c02c40c009009450013641040c0710405078a0070320403500e20440179400410151041c0c014885880d101b26005003145103504100400f08070080c4240d070540342d04540b100180311654504038094150248524505840d1221802107000d900006004540803031f211001103031448007642c1e0703d88020b80b0984803240c1042000c200e0b01c80c019070040c010441e1800f080d41c104141c1d40c02d102c0c5550031a0710115a45400080c84a02e00d204a4002c610301c400810040c0700900c0180c40000c18114031580140d009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 916317050 1250 916315800 916315817
    0x10b150d0b03030d090201090b0301060c12021903030515090618040503070516030218040b07050904020f0c0a03090503070825050d0c18021201030f0c0b0f030f101203 73
    0x409010341c2081c99001002001c4070340303d40b8607000800017400400012404a44420800199094240305880c100c810780c0c2c0303c0442155180d01e0b41c0050f15103a0300f82c901107009103184014030010203081c400e4581e01136500002c0918084d500c6400280c2e190b40128416001041040503039a54141d400712321040d804156110350f112031802074a5401003400003001800303241403100c880d0703140310100b4040f00d000300c80410a1040514203440d071030b00d0542d0060081008100003d903114003980042203000340241c001458401c100300301400e250040c80c22000340b0b4010403400810305a00040c0d0350041e1004901504000d46000c81f115a81c4002100200590656101800c0e540091400300801404003400b03010f003c480c3c900e4440381300040c6024107414080d4000150271120301c81d109680c03004101c8100350702c9031b908640718030b049401031890031111a22194404200c200100010341410441c03101001d44a091444c12141c280748010001c8011040c1e00704100304100c12082e00c00d61054141c00d00050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 916318300 1250 916317050 916317067
    0x4050a0b0c03041a0d060b03151207050a0306050109050a0c1d010c02060d0e0f0303061c060f14070e010c080a18090501060203070510050c0304080a18060e01080702010b15 75
    0xb540a203501c800744155035401040f000700018401042450100e8108109290b2901003104413404180c85090005159100003141810310500300c80085080008980340250358000050400c8141e4208844458550f8010030440d4428020326030042c503010011311041c1c0a40c10001d040340f0a0080506c2e20303030604421400141d02038001129400c1d0040c0c401075662480c1e00c104405080001a0030503035114400c1004495503001c020350b80a400300801c210703007460700a40c8d012144600c224003616802e50b580321161800c0f403103200300042180e06450ba40400e1a040c0c1c809032500a0f03942a035414030040c4d501508c002810711040b82e010b906142461404003a03204644c0000111039080100c1642c5004004920280c0000241006512a1007150380c01681e00680d68141c1e00191498401100180003080004034000054900040c42c0c1c9803003180504080f41098205220390700010200c0c081104111481d41c3c0000e180b507006c6118002445003092141c0072415410055403030100242010a0811 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 916319550 1250 916318300 916318303
    0xf0304050d080d0f02280c050606040c12090b0702160828170d1104050d030503040302030c010501060f030c0f140c0f10020c010c020f0c212b0504050a0b0c 68
    0x2000080c00d41c0d0846d12130700303640d4910611411031141c1d184d00f1003200c03400700c030b4075403080f08081012580039028040700c0c0c448405100240101d407104c0001d0240130303d0701001c4141c3c40c1c03007a62003a84c001c0e0300d8041c883c1042440131b414107001b1440b140000340540c50a0042d40c1d0001032030950380c400498030307031b103241d0180071070440520300384800400e000404000b803841c400c80240501080c42c2e0f0110104002e51000b61aa0454401c611481d50004139003012400400d0040024550080c02030068034603006910385000d00b110802d0704039001040758410603070119035051048140700305140c2000391090000c41005004071691050342191207400068809003900305002449440b24404107e9401a01c0050080040d4221150909440d840c08400c00d0340c5510006207940c001c5018009420b40400050500554001c0c0c00490308842c808400c0e8048221020408400f0040e80a0702c80214404154800f0b07040e1805d247d0403001f0008140000c3c0842e595081c0c009088030001c03450f80d50b5070308501c00c074903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 916320800 1250 916319550 916319561
    0x71e0c080d0b090108030901090905070302120f011412150601180e1f0515090d02092d220c051c05010b010206130605060a05040e0d020f0304050d080d 66
    0x91580d000030072407503044225604034280003981150141d0b001e030307240e40c42c0990340d0248549940c0003482c11502080050041c0d07010310380000780ca00e8091328161001000c041d048005075000804413400034010000c40d40c02c41c0f040780802170105c85462038005441c070303000e42e07901e11b4060071032581242902041c0568019417601c00da401076031703d4a8036047d5031111002070004044030085a0104003c03501d40c40a100008040c05880c8001c00b842a40c0280d0440411b1a0700640070446d040307485c0861703000140c1e0307489000c40c1c0300d941200c400b0311140602d1030180407500c001da100d18028900d0002423240300485808600401c1d0404039507141010b507281800032600f4295070000390406104050b0007c1c064008810303290260040c402848014140001241e540c04200c900c244c804144401030740000c2d4660304034036003080340100000340c425140c0000501b00d9034804c25608080d4400644110600d406000c90381c1140c50362005182071500e0100031442c0303900d0b807400080481000140c458841000d03903012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 916322050 1250 916320800 916320803
    0xc1e1b24010f32040608070815250c050111031807081903050d1a120f06060d03030b0a06050c010c0207030803070f201f020c0c010305100b0304050a1a071e0c 69
    0x20302c291030795031001540703a017030034010232415000d440ca00400c00c61086071000c0c014030350681d40350041c00e01c05841c10880d16802d000071080060100000000c907109010704141306100c600003580e6801e100b0b040e61b5064803407074000903440c0c00984040000c0c80000c00e200203103443c40401100c41c2d18140c90119001e101700c1e103043c1442407500a4581a403418880e81c8440d1143c20703600403061070060907015070744080340a22620302f688440001540d6080c15020280c1c01ca03c81c1c00c010900031100c50020381c15455a400200001d0380120700c1c694045403d00a1101248250024000706401c40e12001900e03c0001d00c82000d03c10030341035141d04c080c440d400720a4003101141c032491005040c00c2c082601c0d0717400c0d2188003482c2000301c80c8034505810944203ca1070050403000034041c1190910041d03021b0072005240b01a00440420009071a059100085210350300c6080a0b1640410b6441c03c811320b80c4c052100e90207440400410001c0303598001d0500e80580000d0704046030641c0c50010107d40b5000c0c00d210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 916323300 1250 916322050 916322059
    0x80c120103060507181208070f08190210020a02030301140a1521060b030f0712150503010f0513080702060f070303140c1e1b24010f32 59
    0xc14080c240d4001d83c000c0c3d21580d80c0c4020041792030031402d0090040e01442c811200e01c00c0304580040d010f84010802d0354498610600b0205030b41d1070340281900a59134551704400031410320b004480e03050101f01c0403008001d00850030214505802944c0340014041e03988511800c441080c4559101003a410090800e056418a414a0680c00601c43c10101a0314200741c408000d580c29a001140940b10545150142190840d503980040d250008170141c241d4040c4081c00340d1090a9600301d000e0a59075016072401400f410b8505410705085a0603155080e41040c40d050502240c0c410003243c40d000a07401c0340015442d881c0c41d00014059200340d400e000444640040d02008068254200340310040e848400c0803c0d6540310b019020151103104d00074140301d440c0f40d040f20480360030803014010340c0d108042c01d900355000800102d49407002450341e011110005030300d80c0150400381440940941407800ca09014a8070304140c41e0f10740d040c00e08e4030b02400c1c41c0d61404400303e03501c00032451312004801007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 916324550 1250 916323300 916323337
    0xb210c041515090e06030303010b0a05070c15020c01020601080d140703020705040218130923011506031407020d140306010e091006020c04091101110f070305030a030c0f0e01080c 78
    0x42c00f500701c41e0a8407a280000004100044040c40c022090b030341210f03001c019407440c0520400044034264803000040358000c5040c500820311803041103070300c48440d507160020608071000c0e00c006403406030140c0c410f0300180e101d01d007194980380c0e0101d004a1610102c020031512640c9629041e03041810540025402520104800c0d42c0380460b03041c0d4107400340c02503440c10340c1f400e020704a82d4150340c00b607880a031516145888c10100b04034028040507901003040e0001606400040c151030380900d4541c0034a0000e51260401848001d460819541065490009011240754000301504502c840351506080140100c000389d41c690044c03c2e002e5018030010321030805454602070115105040340038050040c440c0c00e035055514100703807148ac04c0b4a5000b1403c21171086648004440d01080c0c180035401501030701143d800201400c201c032402861058002e50b4840108620040407548141290703001c111407404a500002d0b001621010b414000b841c0012a0303649800081c1c01314465181c02200450612 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 916325800 1250 916324550 916324589
    0x30e1b1c0b090606130209010e0906060c060c0304020f100806010c080c1e0708030a08060402030403030e0609010b2e030f060503030406030e0615030d0f0e060d0b210c0415 75
    0x4035415105010803105c02240d031150103160740c124003c49859a0200301d88082c0d424003464180380144c2e00030402404286030241d0001c0b00b508060042e12032540b940c00200c14002180382c451814035015606035112045003140c4c00380104080300180c141814040c51410762424003600d00201d0720984e03030b20b10845821608040c0c007000b8003220011000098000d034440420149d02c00701c01c8900d403080c250f40300c011680340c800400000f940042c1049088c103540e604d1150401d207091190382d118620000c00040c1140c182400e01005015480607201110040858104408588880101c0c0c0e4241403800113910300030500312100520b50351300a0341d418440818009505945a00700c40800041c00d0291200364803415140c94a8000004607264190884a16001050b00c29000c540b10103846d0700e0104682103d81020804a50052440d00c14080d102d04401c6910b041036600d49000c0c62003450001018603441102c00e0721403040400c940d10940e241e040a5046400700b241041c041c0c412a4904000744000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 916327050 1250 916325800 916325803
    0xd0b04020405010e010b040308460e060d090f02060c030d0e0309031f0f021605210318030403080d021e07020a0909150608070501030e1b1c0b09 63
    0x1124201d1103542030200120350629508401c81c120748034901d449040c18196500c01c40140c00005544400e86010320303000c40320841a91461b10840c610300031141000210049850303c400c0d841042c0814071691680c4a4182d8480d6000c403862100c034030303d00141204151401ca000000303d020060740c04034000c102c400d111000400248100428000e007086140070078801c890700ca0003842801036040d040320103584d0881407040c59034101c02800420000e5100c012241201c102c1e040311703144030b0003810714454600401c10304100754003031510729043c201c108e140401342d14116403000074080d001c0709482904a80f2204420015503014560052100e80c4441c80050900001d410600061980d11541920003d15016080442e45440d80290400700000c0c00d102000d0b024107103085d011504c40c603500002c020114181c0c422030000e404842c0c0500b990501d4200010300f43c0e00005207029980e041400c0c00c003c1000d07901145081a0000e40d0350f401030b46140100c031025841c1000c0c0280810604400704003c2010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 916328300 1250 916327050 916327073
    0xf030d0e03010e0109080304020907090b030705070b090610170a082701050c1c050c0d030e010f1e0f020f0a090807060507030f0e030120030118050601140a030b0d 71
    0x3000d40082004400294190b42079404180014080200800109000d0304103004075a034420003504006001d6a91741c1c060301102d600440e500c40004a020894004000c522143c440d00901c03844001d01d03d40c207080d0103206041949105030741004003502803010000805009089036290042421a22100d0200d05112a1203422035150202107584550000660203501070701d0981d07041c000102034601100508420340e041d903101e401c0c203014061240c0f02410f0b0040140040a03022540d01090500340b1680217401e44102c41040880e0509108050303440401d070803450503042190200214044044c101e85c280280f0520400c0700007840b00050340c1c00c0840c0c00118810484030083c0440303009a903038000403140390080c0f082c02070004607c1c00305144800d1042040100e117100042c00003034109146c3d000130000c0c00c0794554035584400080010042c04401d1003c40c0010301c4222014803061801d8070008140315480d5100c030f038603101d0110b010440c42d4442d40c80800701c0c42015114014403c07880c20b20f10341842c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 916329550 1250 916328300 916328327
    0xf180b0409050a061505030f10050a12170301120206130509040f0543080d0216080c010807140d020d0603060c09062f10050907120507060e0f030d 64
    0xd08040c0001008544c2040b0704d4490240c5d41e441e01d0454540000085896101400a101800400b1004125580d4400d4440c00508d280a1100a0100345141000c0140d2840d02c001c20006030074001002500c0e0203440c0d04e000c1c6641116841e40d9030f14030303001c3d218000d11160030071a013120300c01e000c00c410400d0005a240301140608111199001c0d491210b512455034070403201c40c40c46804056400788030b49150801c0c0440c03078000d51300710065220183d491030880a20455001680a03003407a0840131003030102c81e8098102d40e40504400815400040c0c403d25028082d0400c0110003c2c0b80f03201c0802d120f080d2014042c00c21000c0d03684202c01060389000c0c010300c1c00b0980f8aa45801c541414890082c0201000c03104c1c90340350003ca0007032403d40d8100080c2e5420300103108214501c2009d0720003c0178845a00d0701064540d00207a0303820070144080c035010b86a00300c81c40c50440c4c410050046400044c0b40741c01c54815103060090301c81c244003c0340040e50840b5841d5094030038400241c01041d0018001a00ca2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 916330800 1250 916329550 916329571
    0x15050d020c160f0b090d03201c111209030a0501060905060906090f01061407060608010501030b1f0b0a1704030e0111010920040b0907080109050c0a0f180b040905 71
    0x9403611009103d410241c46114407096080100010740e00304445010340c81c81c00390400140b181c0c1190b8079160010042c0c1c1030000ba80e00143c80390102d080003012402442c0c1c01d0307032078410340700f203001948207a41e0820340c2c0c0e96506140c0007041428080d41c04105c04e80c0c041e540000203000c01c0e03583e11a6000038044c1681c020f031040f84180c001075101e041c030a101c1c501c030311110404115140d20b068030a44800341c1040342800100c404000c504045070860050200410401c0d00004d019895806c0900d8560809800d0314481da00d120100004642c04001175010b44544486e069a11525034105584641c180404400c280220b10300b000b05261f0466600c8000a0b1300ba210f15071580300000c0114200d40000b0030060184000940b0f040521002444062170300b20081c01c0044e00e08540800640c8561088501c6000545d07540014031a1207002e01034590402010301c100303400e00c2c1980700d02030101e640288030174003040702107140e0703c0d414541503200310001c040440c070b21941c442e04c0b0358092001e880d0071144022013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 916332050 1250 916330800 916330843
    0x3c0d02120a0c0f020a121a0c16060b01050d1a0102010c03020f04260a0b0405010c0e0a05100c0c12110619080a140a0c0201141015050d020c 61
    0x40c4620030085aa8803501079440d00b1501c6403036a9200141a9090010703a0080800d0b40003003407a184103204242c800b0b01940407811038006a030040400c8041c020200c80103260144a424140120b40f00382c049401d60149020a503c420704004a48500880b03205800c0942001c0d03d40b100701403010302c0c0c1006d03100207a000f031120032480c1d5429024bc5c840d0b000200000e5404000c00c00c640c201080103000e0320f038205085803905c44100b14006141c111010b1050303d4001c040d0045c482001424890003580d10401d00b4141d101d4003408002414040b018400c060145505c44c009659040c451245812600d92050f9210070300f9403070f51108520f50f0710285007100ca82011000001c454a00801a24a0311000c81d950390b44680c100001112400000350005d0141074a416103415010700b5070010b10b20030462947c0000344098040c1d0000e0039110956003021780d01c0001d00c14040818580300801c019118002004845546610404c031984d00c80d44449a205138400304924154035404103c002071041000c030f1030030740c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 916333300 1250 916332050 916332073
    0x20c0a060f15051311070503121012020603010e0901090605010915082b1202070b2401020d0305100816061119030f090509270a053c0d02 60
    0x21440828003aa6a1144c4994280142021180c21204480706184041d6003070005c5581c60924540200d0b20b0801d1664134041001034400403442140000c043c06c1c42620000080c41d0007149aa200600990000010708800100d502d0403d40003003090310b50002041040390781da581000000d000310300401c44500e90740745000070070510000e0880c0903c4600d103d61000d00b03540850380101d1780f96030601002071008515002c0d0201145202401c5024040c0900314050300d48240104881c01c2052100e024182544503a1240d90340d001410002503242d03420001001c3d19401c00e8020585c40a07030100d01c051140110070b0700c102d00b2802c1d242045407074a0300c1d6240d41083c1130306030301d8035548049009100c500c03c1400380c0c00440d00c1f440c008c00070b02e200ca0900d0a0115120740c003182980200300c07404824003091000c142e40c000d9440c040c8104440802c0040c0142201c039039245512405900504607526569803c0c0c0b982c1120803408101001144426250100380741050b500e88400720000c41c00054000c0ca0401003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 916334550 1250 916333300 916333331
    0xf07050705010206010626063001230f040212070609030b060d0f080f19020f0c040203100302130f061205010f090809090702150a090b061008061003020c0a060f 70
    0x84207d000b00002020700c1d8029150079520345001003406910030702e50410240c004611442074911950050b04000038140507010f03150954111010b00344000403030480b400705540c4103180094003c511a54081c44a884a0002491b80c1c041d01c25803290074042c4c66400901c1d0b41d00f000226045a206001c80c00080e902c041c200000f880c00c03007038094004c060903600da200280918001b8181c6466451105081c1b03823280c1350f0000f134100c6507001d46002d0b0348858489001184100004004444221415855403420ba070022a81b0708882c840240140c6050700c0784c012010081c3c100b1030000c681c01c5c01c2008004e0341d841c2c035101c01200310384e400e5866501e070160002c503184090141650b5036130403688040c9000082402d014510b00300404160460044043c18041c00070a22045400340560340d101160035500340c189508415000b1740001d20484400783c003040341c80d4002c0701c190b07400042280c6040b401c0d48204000d401900c40e41540724030b5401a003140800b08810b5500c414501c100594080180d82a4400c0c5d01c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 916335800 1250 916334550 916334567
    0x1a010305030405060a120f061809050706030e03071202150c041a0307180303020d02010c030510060e03070e1f0b0307080606030a060e010b03010614070305041a0f070507050102060106 80
    0x40c0c080d40040100344040e0400c0340041003241100d1801d080b60002c0d098801d000c403841c414070b440c203141e26007008220848060041d4110550743c0181004581555030740e01d5650041441903105264454041d2200c0550a00503a460540c004590314414508000c00075212401910800780c8034a00c07002068445001c9000d0b941a40c1700214103036000c409030600a44a80c0004004104022440c01c2d41d011201c03c40b4501d0700250f10a800504c40c107605108064203407180018107104151501040140001c0c0210801045070002d04051b03260071040d20100c0d0500c032880e0401c4c0003105048041c00f421102e01a1403112000c02c2820b44d140881d12000700c01c81621080e9807000c0000c0c0054007045052800f503004503041582140005803a580c1c0f01d00110a0384d02c01d078007000c010308022004005103a0030220380600d9100d500d441e10314000103554041c0050240c1d0090310400740d090101802d00c404500100d40d106040700c04402e854504900c0c02e580d0307820b190701a8500500481340005803160007036440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 916337050 1250 916335800 916335803
    0x108010c0206181002030c270301050a1401050d081b160f060f08180703080c01060614120a0204090608030705070e06010516060b120312090a20040b04020c0a1a0103 72
    0x5400181391168900c00a90000341c00007601d020100401051240740203180c0541d114801e071041034105a500801d8211071004004074903c6080c4520140c0c810400d042850544004660003881e948082c1420310607401400001340081780d0043c618403c400c0000f5540310781d056050302204805454007610320180c000d81c400e01c4003103117103c207440c0102c1d13014044855104400b080e0f01c01075001c4030030013540391003586d03030040c0c413002ca0010f0f00c681009820300464010748514203102500c1181d0a28004a0344500d175141d9070a42c80d481c0101d42048902d0301110001c0040d240e05001940c0c0310003545440740d21000c411112403040500010b401901c02584034415007050b11100c0c00c1c1140703815240080f03032401390202c50b030039500c00e680b030415030350745509001001d1a00011503c80312051401c090061002c1c0043e8860342c082c3c4503540000e41e07049509007402c110031120403090295031000c10702811500f240319034007500210b41120240c07000030301050040c0c054800f600300644d41d2a403682241a0a010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 916338300 1250 916337050 916337053
    0x30106090810110a03021b030406030b0a080a02030607051b0a1226070c15020a0306030b0c030415240b18040b030325060f0c032703080613050108010c020618 69
    0x12030007014000c6c0c0c058042004000c0d040c20700601500c0c1d0550640d4019082540465a10f900081c0c00341010280f440241420038000e004c40c1601e900045c1d516200241030350100100021002e03010a81090700c420095906012202c0c01e646501d800609008002c504a00080701100c40100220b043c2009000503412078807403800c00d40351240222520000003c0a540da80400398101c1c1482c4103610007040e03500c00a6a000442c10300f1490221300e0010081e2100f48075450500c01e110204940c2e9125403501030b410780e800100408001c2140c51132007078a8240562111800c40001014a501002020680b25440a4840f0b52880c20f00304421503010050084e016070040c400032220120911700e541d5101100d80090840d20001c8c0e0301c1c9002c0c1c4040400c0d00c6000f9842d00d1100c0d0b80241c25002e0303030100c40300c8803203817110300a880c1c032a032140c00000240c05010031907504049020390b21007407074030341d00609401e20038801d540c1c40d400039030f001e48070301e1405400520506c00040c0b50391a40c28840000c4505890 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 916339550 1250 916338300 916338307
    0x110c010e0a110603042102031209071418010b1804020d0504060e12040e0702120a0504140a050f1003060b0c030915030f0a0e190b0618060d0f051203010609081011 71
    0x1101880c10f864a21b00103500c4100710503c03440d00391003e640e100d400340900074010307903050109410041e0014102079000c2c4443d400681030405491200505517105020a41d071110125030204100b240350301c0e809a0014800a03e0102285403500110f10450182c1d4040c0710102450b940d00d5a28500c0d107403250b400800c1844140045008404100c0c0c02191601c100c65018603401da40004039808980c0380004100005020014580e05000c848111f40007180e03410305103844c220221311800320720232000c4c1c0329440889802c81107c0c000d600030005045261a920307102e44804000c180d0302c0e40301c2d40364648500404500c18110803074290861b0300c10010351000e8582500d40c1c0030b001c1c014007040c00000300305000c1e0007d18818646001d81401c540313801030304000c1d0750342000406c0c441408031418076130107040b01e401c0c00c124560f141c140103801000c2e485824880382400508216080940580c0d0705507074140000700000300301c1d501140c180b00344d40800041d1058044031000f43d0041790a00d4810003840d80050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 916340800 1250 916339550 916339583
    0x9090d0903061113081c030b0a05040c090308041818021f09081203181c0e040906020c060414010c0e1e04060e0a0e010204050a09110c010e0a11060304 66
    0x143c002108145541c140c503428a03180e0040b0610910040d002450141c1c000104c8100308a06e141d5a4000400e070760500304004401040485d40303a0102d4003491303020b1a00c6502c00e841035445498640000c0d82c100711129180e5851b0400e185680104080b0403c00c00e0500140189200600244050059000700818070410403802c2c04141c5540307600068040c4103454000060180c4140a10b5107507001481040c0e41d02d28001280c482c803d010f40d143d0303504036800030031400700c0104009503003441d645c4241081840100040e00040142c01c001c480282054004500c0c000c000000050305801107114003604084072158901e0075007244c0b800140c91001a20f080130102041c101281401e01c82070502c913000c070031091103401150070b4030740e00d510003c80300c00800108141d10303002e44921140d9649030802035140c1441c20000456141a40c0110201d01d41d80729080181c181c0d20320103e56901200701d0003800070301c40100e4036070344a491100c0250f441a540305034001d41450000100c038482c039032007980751900c140ca0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 916342050 1250 916340800 916340813
    0x11401120c090c0509010318050a060213050a0807030302010501120c0513020c010e0a02033003100807150206010f030807030c021c11150304030906231809090d0903 72
    0x14060255960070501da00841c030210301c0c0c024048101050b46415940f00c00740341c00107041382c1c4841c582c515012040301104000442c04101100700c1c50300f120780541c03a00d9800310034400e140c0039584103581c080c9407940002409600403d820048074000d40082029a903982d103458984019001c00804980e28424140038500e00302480064541034500c0c0103003000640d00030b0508445400e8802e80c440e80c020342c1c100d82185010008540030000c04202c10b0b0540d8980c10040882520b07080090b050701d0004030015000b2060f07004010001c20750001103603c600c0d920341007192032427005128100140115800401d00c0c40101d41031004890f44035216900c1c180307050300d080711080c1d042d500403070f4060001901c025400c0b0590f14050041801130100c103110b901c4c1d5100b0001c0e90040a14021940c2d80203200b048007107078000a004040b00d009003807280d003644603508001d8083e0301d0703070100c2586110003040c0700c5003042c600001020326000c1682c2e00310752520b4822509a44404040d8442c001804401050002941307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 916343300 1250 916342050 916342079
    0x1d10060c05070e13120e0d021309171c05011413111306030f0b0306010e0408091809061f140a0308070f020102060a0509070b07030c0b27011401 63
    0x42060350311054580c51031812100f03041d1895603e000001c07021009004140b50100c403c0f50701c0d41060140c240b0000041028407209200183c825501408039540340380190300049015940508100d440e6803619000707641d19004100e02c00b109a0300200c9281a1008620440d03060f0b600039440b2088108190342000380780380d441c404c03d80c0c4654881c0c3e61100703882c103d07101900300410340d07280002070305060020007800c03075071000c3d010303041c541c10107013440f00e50703200812910f0643c7d480e9405c070703c141e503034038100340c1181c0c4a000d00300c6402807920804014403060320b100c02d90141440c0d4054400c551166030014030070bc0d00303000c02d1143c18002e10108010040c2400b0341500c0c95540a0808001d180d40c9440c0e010303040c0c20401c01030b03520914905041d0708540c3e0500c0b00950000b4603500401031824403011982d500d810500038201001b00c0019010300b41401030040c0741a09034880100d240a160000301113031401c00e21182c0201d45000c2c481c04101054040c06104c0c7c0808c0f40000e02d4600f42c0c60b0110841368040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 916344550 1250 916343300 916343303
    0xf2601050d1a042301020708030a150305030f0315030a0210052a0109020307050a03110d241b1d06090d02030316170301210312090b011d10060c 63
    0x50b858030340030148014000440e10a034056200c10b050070740f00800100502d000000100000d034810003031030b030021b0403002c2540c0e00808882000201d5050a42c00708010001d150005003d80c84045001714000c00207000a511a0104441c46419a040c8c0000d055903520403200080d440803814015054003841070303000d00351101c4032104040c0c005030b68596060ba4140e60307041903095651070fa5851820342c201007005100420003a82c4400d201865911145044281c034540c0070b2082502c0c228071800c2c01701c194a159500603078000e925007070000300413040300141050b24138005502090207000315041d01800781040404c0b105100c1c46261011541000f8003580160801d80d0312601014245000d600c041010f8100314615441c240908245802c004c21a0300c00501d1a00c0380714001c00061080e40744000c0720394031402108241000224082c6003e03980101c000b852483e081c1d01d0403110209000c0004d040074122115840071088009800c030170300400071000c8070001c1044a850004020302c0d445000c400c50f005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 916345800 1250 916344550 916344563
    0x5060904061a0d03230f0403030305090120091f05041a130b0a09080d0c0312091403180a121401020d110a020d0c0302100902030c0904030f2601050d 65
    0xb001d6440c00200400001c0105070001042c40084089207030361740b2030710780d403405101c02441d00301008165240290b20a50100408250711400850000320094002d2191215802e07003035000000e68404209140d000b060a0702e204141107551168100142c1a08034001d25140d9941c5d480c01d1705002c00768405440010307815040540c1002041000407907008080083c2c0140da07402da550300312650300101000c2050f08006215000869900e44035034010081340c0a80b541428800c01f0500f0600c1c1c04002040905c9000d460004c1c91031a5940503140030004100804c1e1101e43e03c5100c1f107459042c4800061580900703082c0060200c2c1c0c0202060010700744101a1041d100058a00400d40140c40c0c00c0c0c504402d05d045d042200401c81034040c036018808250382006d1032401e040c100781591402599204064502c02060355600f0b41c0c1c6065440c10f01034001003030b1020f041a042c50a01c2e2400510800103111640c00090071301056107001d680c90341c3d8030b85144903041c10740d07061642420200055921252000c80e9074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 916347050 1250 916345800 916345841
    0xd0305100b13170c01020706050a020601090c03021912110403050307080c030d09060c09090207030815010e0315041712150109030b040b0103060e6601030506090406 72
    0xa01400f01c0d6a0035054801e03001c1e08254803c4000a0b1603c030b0160490824003005000103034000d9400540e5604507059010301181400c48801c00740d00900c0b490109600d43c0b54804003070040503411208440480c003400384100f0174508003141c1d80f003143c015804000c080350401c1190801158a200c01741000c000301e0010340b07151012035036035a002c46160003011111035403100c1d40b4042041c4c102c4220002018000802e51804505903401405010010720030406040c11040408442c0d00c0340c00442c0110601808807401030b0290500541240c2085070112844440207400300c2d80e007217881080c1c2d540ca001045d10030019840b03640c400b408107046040c0c414100844044004041511216081e00850140a10102550444c1818130507a06241648030065005600d1100307100105013802d29000c03105410b4007801c140d040e8440181034215451449682d03210b0b0303a0454000620b82c8400c031f41c24062811705c00d0b00380e11880190240c0310200d4241343e20001c40400100032038400c0d00319a001d40d9416081160303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 916348300 1250 916347050 916347059
    0x12090607020102150a1a041e0e030d021b0c01030c02060103030509130914100b031216060c09141005030408032a0a020f0f0a12020118060e0d0305100b13 67
    0x60044049695414068861290f44090340511b8081d07801460299424002440f100681541e0414404243c40380a995050207a54004050081e11088400e000e821b5554000c503080c4088a9524050610300e5800b4505211500b98007074030501100f000640c01410303a680c610348003587c0f82d400080c44103400c03075004c0012102c0d0703075444e100701004c49125141d54501040001451858203040d102845c0e802440e0038210000341d9400210100d0185c440c643c61540c070121810845040c240440d0000c00180c01e1040d5020030503089112402540d282c110118040c03100041044000c00540541c400400c000b000854081400e0400035548a1104d02c03c0030960701100307041c80c0c0100819000001110070101300c1101c1254140014111444544000c1101c7e22007004000d4407805c900e44d006054052425541c80030030300030340080c20580c034003040482564030541011809801e80181d442014090303500d401403154047c1c8100381c040c1c1400b5003030f4040d4030306284102a00f58400790001c940c0314041c020004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 916349550 1250 916348300 916348333
    0x601031e050307081c0b0334030b090d1404051215072006011805041e0c17031801030f0e06040804090b060f031303110a0b0f0912090607020102 63
    0x51268403441c4d0407552403810307410000c8199249400e404040e8103121080c1110340d800500e070b40c8880e02c4041c2014101d1032024401c0900b803400e105070343e07100e03024400010502020f0300d141c0d48110003113400d03a1121036201038100c4014506032444c1404c1344045c0000d010604048a03070b6001c1c40c8601003120340c0598990030b11500201c0c2120710800188130f01303603503d450310f401d41540208200902e0040640754180170204035121200c0000c8000103984400140078018440351000040b42d802e1400c442e40e0040b0b081c4810a000180100c02c10080015000d800041000045031000001e486003480590b51a1004501400305902c0c85200b080d100c00d43c045c00a04240241030203a84180a5280d035035140907006006c1e1900a00418847c0a0500101c03a0b0511031504a176880221b202c04007405a40354234080d100840b1118460241d4031820235004100454081118001e48012b0510049a038a00180550714100d2600e180b10442d4140151100b9045c502e000e004094414016690204440900c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 916350800 1250 916349550 916349557
    0x70605181306090c14190924020706020d1e030b1807030b0d020f10030e07060806040c0c020303030f04080d0608100f0c0903080d0b03011e0b030102070804050f1305160912050601031e0503 82
    0x3801c2c9110f00700b055235940c0781c041208800034140d9001400a025144201401403400c400003c180b07400141d9032840541c1c800d46c070079051f51000512089540307008425100c8081c40c1140c504020901e0000b07110799a16000707a103548510340c0101040c03400d00000f01408412601d008400c410b043d1214034400c0200010b121341006040c10750b0796090301d850210704010584081c2d01c0c1d94810301c0182c80c614000368030040101e0382c0c4064003140c020400c0e126480e20080510610b200343c0c0c0d40510345070000c0f40c0000701150403042000140703000e203c5c10201500c3d42e8101c907800301e1801c011403110181000003410310000790030030389000c140c000382244042010900f501c000d510200001e490540e4090107501b2544220b0880e003000b60000c5041400d0f954604400b441540540782c841c4202e18034030303081903442b21001503503c50000b1040c80700c0c0c01c11141824502d408012408082075030740c00003182e8400781c5c0c0c191000c0180c01c50001d00c1c42e030b403071515040031780201d42c1e4200e01200940b032101d001058081000307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 916352050 1250 916350800 916350839
    0x201030b131a030c060301241b0804090f05060307051e27150a0918120305010f05030a0803070e19061d06030603070605181306090c141909 61
    0x1212160340d82d01007014102218961441d01c10742040c40140581d14001401d100206040040740b9641c09010009480f40800581541080c8070304503140d404029004001e0720803200c0c0458144200c42d04400040e090f00d8040f03d9103038165003c00010466071901000301c0b81400d01c41200003c0c0c225202022844031421130000802c1ea411000f807040b1a080110b0780164071410307142d40301c0e003030344140800119089054401e9109407900c034041440c000306840f4054030007a0b4805607416007601e8084014024000034071400c4c45403c1154400103d900380850380840181c1e0205085103150b480f20420b5a0540408905941140d8103400c140001000512480050849501c1e01d40d407000b6518018110010000b610302e0080c0030520a00c01d564a0029203082503a190b4204141c03502d40d00e040d810000d460306402c0943c03083c41d800800e5101c0c28540c0c404000c3d60380b60501440681040d03a816644010340400041e81c1520400c03143d100c48100b05515400e0a0082c0713070420080e0340d038480749000020341418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 916353300 1250 916352050 916352081
    0x6020a0b190e060c07030e1f0804240b1e0112050903040503100f180f0b1510050706050601020a08040315140702100c09081b0d050f0a0b1e040201030b13 67
    0x170031809054101d081d4614083c0308503451003190111802c1c0c0303004030103018400d200344201d00010808100c00d00390015061007800d0180004000420345c1d0340b0281c0040350900e801107596000c1c40420b410030560b000c5080318183c40d810848040d0760b601d000100740003040001a40400e100224480e80c040c00118019807542d48042040020702000d4411203080351990a4581c1c000b800d030000103000b407000300c0710541c0c221203112070a586c0c40c03503d000205180424071b07a204c1201c0209215841d0000041d001c07181c045d4400700078070756a140059130390748107980300540032540030700c0f0400000f14452800c01c41d442c0480c00226107601a0001000311034801c1d10a0405030b00041d6150907002e68074402c2404440c450b04d000080c9601c2c0811031612916840541200110707549007880480d25041503080410b54864100ca155040f681030454031840e11680c1110017001c0800455404404440001c040c0e8050b0038400c082c0d500c423940190010b024002c3c10a80001212041c2002140c1500c9910710780302e955030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 916354550 1250 916353300 916353307
    0xa0b06040305070f0b1801050a030f0606050c1e2a1e13052e0e010b040806010e070203091017091c020609030313020a08240106020a0b190e060c 63
    0x70502c4407202503500803140c0144140241b0001000348070809035402001e003005559041c02a20880281400d5800800560f0912000107100d0390b0000081400715420303016680121380343c019142c00007800440e1842a40e000310080d200c5040414400210000842d0303c4140100d0000c0104640721a1604050109580c03000d100c01c0f1801c00000c2e071201000d04040c03c01c9585000017100000d59030203880d1748403040080b0182d1850040210032417000d002120b21200300c0b0340c1d40d01c00c0c1c1402507100b405200043e000d401c000040c800340c0024142d001d40e50580207141015440c03010301000c0e00610016000300407900380b1885480209000c4940545216405406108100303106520b02e010074006600031503215001708280083c000c8162500000001403154002c02c1d6400054001e0400342c00021b0f46028602850008200710740100504030303207d0300c070040700780c0c0da41c5402c3e601d400d46141e0143c41500380030000340b00b400e850b001094030302c07200030000503100e407805c121f0303d180100403108508100b8001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 916355800 1250 916354550 916354559
    0x131103011404020a12020c0304090f1d060f06040c0516030c1403090f0409050705090a02070302071706152701030b1503070e040501110307180506030114090a0b0604030507 75
    0x740114080006035415898440f003601e00421043c00c5103264040b056012552118001003032084500030000201c090000800000d000f034000e002041021510145200d001c611010010420a04c101510211515180d0303401c4248406000800590404c101d8100030f0302d03885641303080400103524043d90b210280e540040c80c1140456400000030206544140100c044c00e544044545d00d512000382d07008146c000551130010316298a07500815171103425003041000615190740a0400c1d81d02903801c07502416502ea1040c1d00d8032300c1c401c8000c0306a400c00c00c0010591141c060901c44110030103800481401c0c4a10302850301d44900090b40100009030000400c04d129503600c07100e80150400c410107161103c040c00081c0c3d28081c0303120b00c80c41802c10500081c2844029071154005003080004a070b500d2402010003480c088210100300b0b00410611004241402e140d003e40b41070b00d0b03620350650a504c843c0340421165080090185801301d841c0c0130400080e40340e810240c00110700c640d0040400d41d003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 916357050 1250 916355800 916355819
    0x1a030915010b0703031d0a1401050f0609040308090a020909150a1b0c1703010e0103060e011a0103150b04060305060a1410030c1803050601172a13110301 67
    0x224a169110499000042c0a807807111411280c8aaa16003000542c2d040d240c0b41512003540d11030420004c9026840b6100c080c008000c81051801b11400020840e80d501d0728010480e44200381e6080380c0208041000400080c02100b940b500302c05c01808032520441d950f400290301034002c40c0d501c00c554020041003800041c0c061092a080040d0480620411031400f81401480d0408803040c0208a5240d40c900184209203050030840540098407a95a41c1c4038000b0810030b600a1100301e5801d490314800445e11981886060004150400000701c0c0481e20360044010301410001c10108420981002406080d8100100003d040301d44000c121850000100018000164441a0b075800d40740440302c0c1d00c0d41d441c5180c040220150030700041c100d510500480c0c051200030352b80c0e0244c40c048180030061200010b1428122078036542c0d5541d10075010078620303480d2300b4403210038025002450460b081c14450451401176022010306182840b035080c44100c02070380c0c0900c01003800740500000500c56000d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 916358300 1250 916357050 916357063
    0x180114011e06140f0307050c03031501110604020108161103180a150203040902161401050105041805030409090f08030f01032306070806031014100509010f06030902030102041a0309 79
    0xd2800c0c40303120f80c0210032a181d0640f00b1000e03102c00c41040000081c08040c002c1060341c203480c03002c02c21039841e85003c1e4030700008040b065150074081403114140a07440f0100040d054030980e41a5900fa040352940d02507600c0740c40845e2100410b000d0b029000f00d0742c00c6401c101400000b800241001c4114990109000c00320060380c2084410544955958020b42e03000800c81c2c0c05c407a550a401a41d5403111084082c0003a84c4441c010540c40c04040070241d84017054120b04d059030b200312000c000900340324440209910200f58018900d800910040200c1c251980c401c000d03850058481076a60711182c0e4494285030320483e8140d00401c6400300500034400c02c162031a091b03688001da0903100030306215289589620003400102000019000280c040e1010311003102c1041d4601814400b002c4002c5841030300c40c604a6900c001c1c1d0032514800559442c1c60080c160485007030f51041c103407090074103030118040e103150303c0141d8156408000c0091814610310031990304000105c7c081c0e4072420304180c0107082c0b62 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 916359550 1250 916358300 916358309
    0x90302091006020d0f02010b09010905040c08060615030901060f0305061b0307080a0e1005070f0e041a091b07030f033b0115060206010815010e180114011e 68
    0x70400030061107280e400040c0e1030a0040241002941c21690380400c034094015001020f41042144000003080700da035411560059114038000810a0341750b1180d0340d03031030404448066000c5d404c14848800a19400300458000020000100360745440b00d09800c1450429482143d00ea8440000c0048454411041814a80110149078590304080b04000d1007003102130a20740d0001e6440d000700d041c00c041080018401d01c014407091203946000780024050140300c01d500c1c00850081d446083d00741c90244143c1c1c40c561a214882005584000103010900e440200486d06001c0400c1e00602e10720514030190501070f00c6a544c01502c0c40c000d40005040d100550a00c071140311401041580501c1804010b1040f102024901410114403100890150550701001019201401c001180c0c843d404602c00b416112444100e6100180510300c043e2950740074401c40c0e8490b400c00021460f80e460301045158a955410004903149104800203400d900c001c1e40300c4004400c00c4000307101c495201c50054030080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916360800 1250 916359550 916359571
    0x91e0a03080a1b0b011406070501050a0f0e0a0f030f050f0c061b1201030308090a06230609071205070c0210020a030905032a011106040b010e18210d0c09030209 70
    0x10810f80d1404c8000806000d00f504aa0034000c1140440d201c120540f02d405400c640240407a0034200d510720b004001c01e24071025440c0c01d143c207200d40b40c00001520640d00e0f502c0303081c82c078240d4507540b42252841840d00d00c290400500b0484440b84422880c06088803a00c01005800f0324108000c0c0b004560155164000c0c202c00140009c01d034821020f09014112a01403c0c0484580c3d59a02400d0901c2144000140018503050804001032490343d85d000b40304491280c0d07001c094982504119440a003140d0800002c0e01c03491030704d0380c3c0520039040355401217201e043c845001d200f00e030b0000c2c0d48072401e5540b09005a02c101c181c0028503034440080b20050800780d01800b004a0100000c001c00c50040c884005118800c903103070360140e44207020b100304140d000000e48545042c180b9040302d00304001c2c4a604040c11887d00803c604002d00c0c3d000340d0103c105080203100303032800c2a1038003014684101c8030700300c91002030280340c80c00c3c0241d0040d5505200c00c0da80b85141a4190b1041026000000e07001d011807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916362050 1250 916360800 916360847
    0x5030a02010221011809030e041103010305120f0313020a0308030403050a020601060e06041e03140a0b06063109050a150f03030e1e06040e06011e0203091e0a03080a 72
    0x80302e8001d094034000c172000b43c00201d40f00016050a40341e002c0b0b800c8101da001031034040803d040c64051006141643e00c00d506031741c0103403c40d0503002030724090440920209142000800c11a00b1004030003002d0310b10150070899810350b00e403102c6041d50400c079801c3d000300b840051056641139040c06a00e024140c0c0b802d00c007035107403070b04004940d10b40038900a04a0760800d02d001d0318541c10017840058001d560000401c098401c01c412429195840813808840070702c010801b090040ca03060f4140d030a2403503c2c940540b0280c6000c8541ca0800860905145000f014580040780c500034034040c2d184240c0d10303028042520040703600d01040888503640b11f000403181c00101440002d51040d420407084d2022540400410414034107810400ca84000b000c0d070200f40081c00156003030000c0d01c81403088000340c8403c803c2a05284041041001e0620b4100c01030300104411800f524024030783c8150000344d811011070f50900e0002007080907421b40c105640c01900440c52103c041d5004400105a1b000403c03403900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916363300 1250 916362050 916362059
    0x106020319030204081c140309060a0c03240f0515030105091b0a020706080133020304080708101b0206060105090d1e020a0501090e15010c05030a0201022101 69
    0x100c078001d0700c0e01a0601411106803454a920070b406450103072104106a800c075041101c001c0c1c0b62644c1401030b40c400b190032500c00d01600159501941c1c491001d09002c0e10980e6510704401006000c0c1495480506940d1440044607000c0e04810710301d42c13990b006002e00514140709030f4241400059101510440a5101300a5000710701030540f4110781080e900280d19840c0e00100514242c3d900648208503203000c0750881c2420b5000034000103d40040d01c6000c10703640c950040c000004012190b5600c001001c04204000240c2c0308800040b05c001132050f2814641c544d41c1c41814410182e120000c5070717001d002841c100008a205114850f032501605c5041c1d070200385006900e0790402011f40d03042c41750116816010ba04c1d6140500595540400404c0c6900509500002100701c108001da000c0e01c1c503000b012869502034900b04081d52651040c4c440e56690301421140e0754007201e1a258104400c10005400181040000d0114901c01e82c0025850b10303d41c442403a59002801c1040d245841c10400410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916364550 1250 916363300 916363303
    0x141303061b0c0b09120f04050a0f12030c03181d0603010b09280507020a060605010305090c0f0a050d140c150a0302030a060509150306090309060316020109020d0821010602 75
    0x70100d0b0344000c3c0e00c5001d039101c218584c24a0f086030715101036100f0000d0070305031040144000300260b403011641d4220480d141c4d4203044a0340d0b80342c01122003041e005240000840e004265608a0f01e21070b00d0f1182040d0040c00001048401c1d40e440014840385c1007045100d90031605400982c07006054000b00f2400d01480c2c000380311400080d0595a03201d0000602c03c40c85120400701150003451644140014101502d009544205109003618260b180000c0482c9943c481c0c013400e406012010001c2021a100804200680a00040c0c0c1507104006200000d0141c560340c0700d1910003030240d0682c49a481040f5220b6040502c0d80d5542c42c41121014200f4444624060039120520007505c4c00584030ba5030390390504001c01054001c660700a0544013000f1101d1142c0070490b20041c000d4081e60159220781340156542d01404c0d1421740e104e002400001c0e1441e0503440c3c0f404c0003844900c0081010482500802d06819885005030360810000420a2801132940d0707851181d03034000c6042c05599894210002d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916365800 1250 916364550 916364567
    0x302280b0a231e031f0e040308100f0512010e0a05010506090c070213021605011a190f122105031b070308271006090e0703030f030507141303061b 64
    0x24043c610701001280c090898100c41800d0020f00c450041c1180e40c03510000e00509608450840c0010310900c001038502d05104048011107094404134460b05080c1020004a801d10b0455800709640c6d03421200c0c9003810030011006c2d07550103540005110309041c0b0a0140c0f5a100500403100c0d200104811001a1210030b28030a081219402c0140c9403501d0940b103004921050402402ca5824480081c2d100c50010301542102e940494405201c072a1504106550a105110b50407403c101180304125074281c001620700020b11450708582d2104183d000802206001821040012804010440074414541954001001190004d0b040c0121a0350081c06500e0090159401144494600403403030b50000715001020400c0054407202c01d40c0c100c40c040207184a20034031280a08100348a08181d070302003500c000f13a03909595000031598000301c0a50203058050314040030400091141ca0741c00365404080d100e40c0107500d4080035114030318144207003502c24040f00b0788981c81150400481064008140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916366906 1106 916365800 916365847
    0xd0609140f0709050a0e0403050c030f04140915210a1a0a05040c030b15040204120b060a120b0613050c0c1203010302280b0a23 56
    0xc45420f08148183d035003081161200b800b94510305509039078403a001c0c3c10304501d8030729058211071440c2d0010360038000303c00c00404e050101199008080d8492442114945054200600c0d14103200c20700b41c41c21441102c010241c00038210400c0c02255004030208180c03801e8008904011902060421120350051240c03000100044d1f09881842d0080340c1061040c030855080d503440d0040c01c4406090000c02090303010180713031755a0303850000b4400b50075080000e4041c0d0882d450310f1940ea040280925104070403c40090000c40f80b0399224514030b07034102d102480c0c50748595004c03d4000500b424030581045c00c0400b0003885030700c99030040841100d03032800c41d01ca070402d0f55030a920307502003804004e5100000b001965289418208107540402c0303141c14070b8003402d66500c001c60150f8082c40718003012034100004410300000545a4500c80c144443c40340d86000e280c04811031003d4010010f = true := by decide +kernel

theorem cover : BRFrame.Cov 916187050 916366906 := by
  have h0 := BRFrame.cov_init 916187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916187050 ≤ n) (h2 : n < 916366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
