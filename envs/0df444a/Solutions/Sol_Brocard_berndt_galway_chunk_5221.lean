-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:08:49.550552+00:00
-- url     : https://prove2.me/submissions/9ee7f960-800b-4c4b-bf4e-b5d5bff1f458

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 938848920 ≤ n < 939028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 938850170 1250 938848920 938848927
    0xf0c09010c0f051005060402070b2403071409060a08031803070b04030602070209100b0a050c071a0a110c0a05041a060301060507060606090b03040b06010905132c030a08100f0b 77
    0x10300c4d018455180e01250071641142070400702d48411900300f800900c0381e04003429064940600d9501242c9400c01c41d030313000303003100d12054450014690350746082d0409801000044e011400910b48140c80e40141c0d03024100650400c0342d4003120300b0092000300215901801010f2004c40c4c044000b07002080614064040940d588801d48107200d1502d8008051340c80e92142d642081c0103060080c0704603041441c0318a4202e89985414400c14280b2005038030800040b5102c0040100f85450000a000500040d4603140100164420341c40d88404103c01195409060340905210920b425401000030040e50703450218104040404503101d540207810031000b043c0c0100705101042024001d42014154a26100c089189801c2c501001400007610082c90401d030000020342e030340d100d81103c1000b0803004028280084d52411400001c10040d070b030b40c4c2c075078000c0c411a08000d9000000c44a0755104400000d41c50171011881c202e03280396010b824100c0544003054006815005160403078040c140c00981150b4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 938851420 1250 938850170 938850193
    0x3091721161d01231b0102181302040506071101030506091611070312030501030507150f050d1b080601030b01110706111002032401080708010504050a1d030304050111030f0c09010c0f05 81
    0x5036174003030071158040740e004202d800903014200a81101541c0140d03200140b0881c8001f014000e0f0290b80c000700e230803400201e06c910a01c81c40ca00e101100c908203132810459621030030140103198908481c801044000c0b1210598058401e040195034441d4040c10780c0c140030b8a82d0750702034414104029420000b52100c00600a018080c440303500204002a211800010080c4019000341d0750103290500340074001c0f5155141051580241410405055089109107425400039000c4107060300c01c3d0340024500114001a54014000c586440c0544002444107518141c800c07114051182c03000c000c0d50040c800100304604003400550f0142c1000308100e00c08241d20038904003074030311401156040050710010f00c9803594000a00b42d05540050fa80440c1ca5581c030071610010704050300e0003486c0140c609001c0f003554840800590300841c071a0300244070740750884405410b64082610140e5805800100ac26244002440102014041030404540c14a00d0741c45d203400000070180150740030f4002002e00304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 938852670 1250 938851420 938851447
    0x103080f12250c05070b03130503030a0f05100311040506120615040f0203061f052a210d1815020a030b100203070303091721161d0123 59
    0x84422a00d041d03204144551613990303481100c2c0c49103403281500003010405d0030001c41010340c0059001005c599070703414425800402000d4076180046d4607481d10700840d200844005000c0c04407500a11580c840406d544200030060001900f516132144612881e0342e1107d8040c40480c1c4a180340d01007540540d400081800155100720b115050300343cbc810410000507503200e11380c0701080390609034115641c84400505803270300d01c11101060210034043d100030303440c0e41c560f0101d4140c1c90039081c02d481d0040050844464520705040c11340003112014815007580d40030940c40800390840e00100e044444200340c5951000b540f54a0f820010140c001a1903c40641c0500800c0d0300100207940511004094400c0291640a070a000a00709034450104400740002035004840343c0f1940090540d83e0500c00c074400c0116900c403000c4464001c2c01900007113070400403410000200116032905560801d200302140d071000d00701c454060520843c540074424800f06203005c298805643d80070903546802407003000f07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 938853920 1250 938852670 938852731
    0xb15041d0610050901030b0907171b09010b040302220c0822030206060105211003020102070602070f0e091f020a1b170c0a05101b0e090103080f12 64
    0x1074441401042c100000d440e080489030459810210540aa84441300d0b0541840c030140c0c00300007980e00b1000c4e802c0c84550086001500110f01030140da02d50060342081c0483d000091240c3d40010f00b01f88020030160030030707071030007004800c02c107d442198554940200c070440e000d441c01140005d500c40100000c42004045002c3d661030000c0680c1ca500419a8000b551000010490342c10860042001a42880c40f0801903900103100c002c9084546040341c08150301c000f0b14030080c1c0c0140300d841c2e070010b88540080f4048003544c0d801749041404500b000780710070b06031001605440c907500c11100c4075002d40d038261181590307038200403a001d43d54040b121801403c07107070345000904041d076003074407040c00160f20071b40e001b0b4000840e6103d07141c55184201d030749410300c406444090810b0080c0c0c0c0b0080d04000d040d600c0301d08450600001a076424542d810b080343d5101c0c400c03042d203420a44800c010320206061201503c80b008104055500e051000c001410340e48a064401031092001c910100c04040305d2022031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 938855170 1250 938853920 938853931
    0xb18030a140706031103061e0a03061b080c030f13031403071e14160f050d020105010602100221061c14060a0203060a030f0305160803060103060b04120b15041d06 71
    0x12503003141842130000c0d0710301c0e88d51058050203000c030a2a9154039100c3c2801d500085402c44010071089101c421103a50b503030b0421a0010000c4d40c6100005c48591140007a6805041152a001c00e550f031140148409540c2000c415403d101000c0c191100700302803d0021031191b0301075a200d0003880c0b0102400700f80c031010500034105000202603110808035580040e90750000159403000038031001d5090640c3c00c010b4000001c3d00c5809040e454008668054000c1d034100c48155088420300400d10803a01c00f01d00070070301002e48280c01c0c0c1c1c1c08000c10a1b00c11107044c1d0403c0c401415014000e2041900e00c003004e02d400e0046406580c0380b50301031040c2905103c4546c4c4076800b00c400f5450351801e10b001804613030fa20b000082c4451a500c40e000c050500c104141d0340041d034800d5901000c14043d090165140c0c000300c0d01903001a08080340880c4c141e41c0c2030142c800300c91343c441a881c0741218641d600d21182000908100d6040a60880908030f96118080d044401c62180c55400c00109590802828407500510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 938856420 1250 938855170 938855201
    0x7060507050721050a120e070b1309050c03130309080f0a05070905060901051302120a1a0a03031e0c020a030f02090a02031b09130608250b18030a14070603 68
    0x10000861508002112100101d503c0e01504111140010030024514803001f02050f00c5000030210300c2c828550000c0440300b15414907608a00d95071a408030a95000f120840e00d501300030320210b134030342a0035a1000c032190303c641001d5a01e651640c0400380f501e449801a4180c0d54040c00b41c54003442402d00410026254015060095250800c0440c5422006120f26400303405200082e0074581015815138000c1d115032318088285041c981e550ba40500300050003400480c0740700c022009140340c91801001102e50680320404c0c2204e01144a84450200c05200350502c40e04e40349102c0141d560300300e40400b4600c036400e50240c5240300e0043c0402100020700494003d881007052000e020701e0701c1d46c00c1c031740ca610341031a0b03580d2002c401020468074214040c4030b4a2035400c00c00c01240007a000b08010304010403003804a0bc02d245040c0c1a80c12182c400d200311305407c40100583e034402c0c84007400342c0e6084000503088810700e031380340ea68143c0c60080b101c201d050f203a0400441400b52588c107014050b0182048103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 938857670 1250 938856420 938856473
    0x1203040f0815060f031903030f1a0112150503031218060108070e06010c150b010f0f080109270b0a1a090f070306120c0311010906020d0e06070605070507 67
    0x50b0100b00c550010344030034495080a01c3c840f00c43d5134200071240742e40c00010341d80d202186647c034010740503001614003070043e141020300c80c0311440e44403060140c0d0003005039500c031030108421080c04001d0508100d0f190b60280c4c06500810281c42c100f0052003042c0043c020121ba500e410b0400c10b1480c04d46151020302500544010041c080e030004015040d108088901d101c50303103502006a0360f180074141d005140c100c505030071003810210390317014030031005003a201c054080e000e041c01114a02c10100350103020880740030043c001503400750b0254111010f1003010001034009911a0500d00d110180708503918440031081254441d80c41c000d060409c400e00c981c10600090b1200041e40d104001401190007a00850000e070500c1e07c00d800c40402451100107040184541c1e0400e05003802c042d010940d01649030280000c3d265110350543c070219107503170340504102d121600089590403000b544490303001c01c09209d5407000ca50a481404d01a090a49407140d8900c0c4a00c0c020481c80446240719041c0b0310181e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 938858920 1250 938857670 938857693
    0x1112040b01060908061602071a07110616110f030f061b0301030b150a0b130302040518120705011e06080c0103050912090d060203070e21030d020708091203040f08 71
    0x252542d046007104413550215003982004034503240c40c2e1340c04084101c0b649803400b99080c41400060080602030340c0307080301c8bc09080090259500c9400c440c03510405040740070002203464030a06d42c501550041c5440000d2030400300117481d1002508181c50b1942200e403c1c48890032030090448201c0e04041c5256003107616549500c07442c108010514000500d031f21045038201d50340c40d40c8000c050f181070282c1944840c1d494003103416080c03003408100d0060346000302296030140d4050208005460b03510040c4110b48a07443c032440d441e004070b1411140c0b5901e80da02e1410380004004282c100328800c00c1e0015440349002c520341e190842e0484078a06041c507010600c02690b8010503098403422001c0d0f40b455a43c80c0c18004501e450002c004042d10b01d030300c04803d00c8585035010181000c82103044442d45444400d400f031202c220640817900d010030350b208102c446840b00080c3c02034107442c1e0242140e14181900e83c00461b11001903a09092842e410002d010701100040210032009800110010240404034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 938860170 1250 938858920 938858923
    0xf0b1e09120d0902030d090f050607050a030c02010909060b03060406060305090c0111070302060304061506090815040609060207050a050f03040303090506031b0c0d030c050c0c12011112040b01060908 87
    0xa00c07500015103800050048111030054010300b4040e54040c0c1101c2c6d0740000c03400d00528948403405040048070306401c00040501e0a4402c2d5581250040080c00c81d071186030703509841e2440c00f078400700d051061085000400301958400c503001400c0e400d050581e6031800e003040004660f120f07004602410710307040c244a000c1800241d26480d01c0c8003802c0c80910001c488000710b190030040c0d031000b503228400100300400c11040d9046008985014610b650405451701016101b02ca010f0003480b455511054640b000840c4200c0e441d60007600802c800902d84800e40c0b284000c1e64000071040c0e0b12940041400c50812208008a10386051200065420141540ea00a24080311031103201e218071004008500e464085540c448091511241002d43d06c0d40c44440d82a1255110822240800d16100c403007030415000b036044500481c40c079009040882400e00400c06034014160355060290750310740d4400480802c1000902e62110503105000c4249440c0c40d01071007040c4140c101e582000660ba1303040021020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 938861420 1250 938860170 938860183
    0x11e0e04031e0f0c0b07111212090a0f0809010c0c03060504050c1e040203150406031b05030d09050613091a0906030c09041401021303030c0b150f010f0c0f0b1e09 71
    0x2030111406885483e00c8404813695511141f5001c140d005035105030001010744402028035401d104058107035544e40001c4207480b80c80b8124041e1403440c090341c00600098020380240f9201105041140c0d100300309440314070001069800071a1816039480900c0207001b020041140c0d80030003220101c0c032400d00343e582e503c21513404c05071a90149402001203011034841956200c1d9940340a4010010103aaa040890f41200158550146400c40d0750010078242004140340498003c00e85420800031b190600340515a80103452062004040a83c04180389907240503c1c0000300410a002d04202c060b5000c100c43c400d800b8044a01c664003048589200d0b4807403114296010341c02131800f40040000541850191081002c84080400f00032004800c00d50003c006076843c600900700002d8950320b840c5507400480b410641c07242c0c80310100c6c440c01306561040000c641e000c01d45242030100300c6415a601c000c607000b21142255040240307000c000c1105224110790310171401c8111500300760b04126419070746412 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 938862670 1250 938861420 938861423
    0x80d020d18080a083705070606090f1b051201060e0d0c1e170a0204050601051603080708060103050609060f0402042324070818060d0f1a01020303011e0e04031e0f0c 72
    0x10740424821f09000c0d541d0709c000f0041c00c61640c14002c006040012400038039800144d00000c101ca001e03035200041c032443c1a201010120440366000c2c1c1d0138000b05440300704400c141030380d0003c00d54415000044149511000600c0c94031280003101035042011a40403215400032691a82e041006052030100000c0e101d0289405580016090f1140f80040701c0900c038140c024407482040c0d58490003055030051a0522426184d038a0240e96240e19004505989c2c06030b43c040c0d4000380c5c103000300d8135910701100303150100e01c0c008000602e0b15a850002e014031100c0040b0740e05010f00c0c000c40d26030050402580440b00046030051081042d54201e00d0100c260141001c040c241c030b1001b050f001140ca442c200a203807610401400d040c3c44d162080f00c0e00e4041d203050341d000340540f801e044801044024162310812103800580185041d42e090072100f070196080ca0201d10158141607000003502c044114016000c0c034000d55403c11044141d91200389400700c0045414100500c2ca984845055400811401200d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 938863920 1250 938862670 938862677
    0xa0306020f22032d0b0a0b1306151e0809030d02070501020d0e0d0e011116063504060b0409021513080d020d18080a0837 53
    0x1001c600c1004021401140751500410301034210700030b48061459030000c1164420301c0c00000c2050421011402c000d04c0e644003005082c9503e80d0b030b5000030501703200d181d44040504030000f244405500025041010400010000396a555050042128003d200903100b03280b81001500080c00c42e48090320345d1001c40082c400c004d078803004038130100b500307200f150302503441c1000c2551501d0441c1440c034002e6120b1100090000d10340301203130b502900d01090110015109840c0c0900b940d00c6400151642000e107004080240100c000240c03003041c41e1140791002d010140d54441440460100c207101c403a01450381c03106030603e5214509580c00c0c0311203486601c075a02c20000f081d50310000303012601804011130025804180c1400000b00c4007040c2020b401c40c20380d005002c03070b060703551a00103586528047c41d003400180c001041c0030400b103014060508010020f0110071120b02c3d030b1495840d0406180303034030442c0d8107040080e40c00300000300500408000300c0294654080c80004a4038603041c80190307225078003803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 938865170 1250 938863920 938863927
    0x301050d0807081306030b030a03020d030b01120515190f210501050f06030c09010f140316060e18190c1b05030409200706050a0b0d060506100e0a030602 67
    0x400003410705544080e9408003525488406241c41e00907103400c00c2c010f000019140c07206140c650710f00019101100390701138000c2c1580a601c110101c014024140300d0034107208416034440c2c6022181e210306840b44400070075044651070002c04000d42c0320102444011380030b9036000144007108003441503070112a110f03008100700303881c0c0042e02050103401030005040c40d407030041084601c8d0101c000030b9200e11021020350f4804000740742085594682801080c50742003a1050a2041c0505540b189240700402021604001030303101241c1c002d941950004000210115070030340440c05d001a032407452000c0031012101d146801d8035008000034038610001c000035100d404200c0144e00802650349104000c2410a46042990600c1952684648591000c0d513180c0b000d042100c400311400d0409401c0710320039851425070252038500145c40c01525003541c442c1d0300d8000700a5503035500d640c8941c55220b510089014940b010410104000d080d0300c42e002d10900d9000c07207845654403003520f1306403584100010b84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 938866420 1250 938865170 938865173
    0x20408160b0d020a17090f0c0301020c030f070c08030c030405180f1329180c01020709090203070b0a18091b03020c1213031103280204150f030b1302060301050d 70
    0x203c100407104400b0171040020103009855201040c0c44012040d09011156082040b40506080303104090510009400c1805202514070446000b05105d034001d00510341c1c010b8948440c0b0303045610085402c00b03107620001d000c02035424900091000c04070741d84400c0506150100807940101c500a0003148001e00401c002010840e40e9100d05403058111015425040980442c201344401c00380c814010300080e000c1c4500c07003d0700009580e5020350060380a04482850040d001e03014050704034049070b00d40580344001c81c19441020142807110565a03030300030540b8103055141e46407010f0781c100f10700d4141000c03050f01051a4224072002031203024a001603031401c0c0d00d03054506185050f00d41d92003403000010340001c41680d0100d05810349001d4845a80104080410075660780606400c5c80f40b820b86111448108204120340f03110b00500151011a0355a002c000c03401e00142990808103181915900510a0181e900040780e4010105000074946081c03940011785070740014840c242c401e030031003d00d600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 938867670 1250 938866420 938866427
    0x3150406150504080115080a0b0721061403121b010b0d030e0306100e07080405011b03150b180d05070e0703290a03060c0c15020408160b0d020a 63
    0x20014820350303048034a107454008100b40d000f48204803096092103402c1c0360010703450f10700d041150450b100404240401e980c5a604104004280505202d00c001204400c2c0c852240304521480100070002040b50425640000583e403440c8580e0080e400009030600031043c96049400f56041c940141d4003111451100c14050448000b4036500645080e4406042540141c131014504800b00d0070f0399490303a20a40c0341440040340303100321880010010045402c15001e1103c20b078100740290004500c484280b01700000ca18142c0c0f91240009582d00c043c4070b1011031015886001e01120b0f01d1a9140103e000c1140d0016022010391520441900d05031804001c02000f043d8001e00740c5100029107031610020190040107101844000002ca50384441c5644250080c02420818001c0c16132800c941180c9a030707030082c41503a016030180140b1840c4040411000304e6a80a4040c0a01003d6641e80c1000c3c07140d410034649803035085242c48005401d00034020130380c00341d50300348106890050319442c0d6008103d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 938868920 1250 938867670 938867681
    0x5010c26190e07121a0c040302130e06040b04050f0c0d020411160609050105131e020f060d200403120c08070f060c0207052d03211902010b0105031504 66
    0xc108510500302c00040445148401100060040c5d070105c02c048280b241001d6094400c40351703085242c104100910062070b2001c3c0d1100740d4003034282c001542c981c550554904c0c02d2015102a52503080d25000c10040280c10440960000f0700700c400343c40410180c8001c034000c0e0703400c000300a101d5910b4407000c42285003010b0079030b25500c450b0303421800d000d0a03606006005248441095079694242000610b0014251030710301e444540c000070048440c03001c5803074401754030418141280e10190021031146c40c0e5849001404c04004019400101802566085001c040d5150800f007000c01c820721081002c20030745406600080c42d18244400c0743d50075890074030070b24400d07090700900141605c4060014020140c0c00b0841c4450241c0032981071f15214000c000038003501c004100b07002d621100b40c0b06800c1c180c0b5107004803000e10103411a80e44407d441240d40f00c01080881030040040003007440c0044100320881f001000416000070044000c903000001c106200082c20900814100c0c1d040996a84a9a014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 938870170 1250 938868920 938868941
    0x510230d050d050a021203040c06051803011109040f1b0f05090616060b040504152a0206041719080601120905030415030e2e060305010c2619 62
    0x642e0004109a034003d40307603403c50141000180311304550300b95148201c8040720700480d0040c0c401d1030000d14101080b40c0c180c1c44840e032164491100c00f103206003038909010b180121441e003c2141d44806a09083c0b10464103040310352500107081840c0100400c44808400b0710740d582c00d103000d061030f1004030404d442d00d10500d008039810a00c0011030350300f60048214041d0042e031143e07505018411a6008010640c0e42c03d6a01901c8004a40200c1c0e04041595106d01e441c2014600011003185203040b05020035044105201d015800281c00c101c1008050410709451510150201d8244845220060f444250b25500c01c0e00b44810300740410f016a002d00071001c0b085400d0b0805200b5520b0610307011380c0b82e0f00a0b2041d025889600051117415600034003d20921029407402010450b00d00711081807412042204001010150041220030000900440d0082c600070303130012410248400005218140114903191034010b10b0340c180f40020f001540c03842d00b0000c0a07900103407091041d142a8002c100103041d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 938871420 1250 938870170 938870173
    0x412080907030b010b09040e1c030e010f05150906030f0604020910170a0309060e01050d200408062512050403090b12090d0309030212031003060612060510230d05 71
    0x814200c5d40009080c2001d090740c050010fa103190600654030740880b002d0440b018814021a50007e109900ca441008000d800100322030f00310500d03c83c119502540c6101a0321b42d0b010b130000c080e050000c1b1aa80202065004121112440d103602d41c445001900092040040c03c01040e00300c250b000c1c41e02c0c040c01325603c00c0300a070308503039031415960240641d0440110315088400185540a4a88020740d844103844080c84c04d1281980d400c0206840c10601c032030b412594dc0c1103a0a21200c2000d88081c108000040625040c10031041040314a6020201d0305040b100052000c00355001c05040c03034410080350041407039162481c080d41c4605864011880c03401d0701081410b02c0310704040f011402070141c2015280d204180000403020380710302c0742c00076002d60b0021042103003421002c1d0040da48040001d44614070b03241c61365551800d80da01684661005410103100a0078071081c0d1150300d030005005444d51402038507019200d0030820802da19844000a000780c030840303a8550130016403e1642c401d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 938872670 1250 938871420 938871443
    0x30312010b070f140109050d110703080c1e070924090504020d02041505090c0328020f0a032c100f022203140a08030f04110d030207090f0203041208090703 68
    0xa40340c500801c6e900c03000780c07070720322502e01000d003543d0180100710104104400600055030964441504a0740060404102c1d482011041c3e90030740c42c6403e10702c2c181c00c3c000000d004040d241c0f103042c5040d550801c001640d82503908090284442c0b0300c014103401c4401c0c81802141983d11400000c1e9103903030900c0065082030400f00602c0043c6040450201500e40480f003e1150313444880c840030050108a80c042c0b9002205900b0708081c074081d5940c480c40180100015140124610401035180c00c90491040031945a103190f05620480d5103585158145544035906c4450401003245e60341e07400ca00c0c010344d01c0c039600d1550003600c905503011611014400003c0009801315102c00b8038440c4420f2005840b001d01105201101b80c402260844101d80c1105691b030842c0c645040003410030740c020703100f103441d00d03404103c080c0642c0f2000300d107400b981d000b9000352030510316041390001560102601c02410030f1040082100242a068400042007070620700748600d40d5512070140c0c5041610703000a0044500d52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 938873920 1250 938872670 938872703
    0x13150306020904060e0c0708031008071509090902030c01050c120c0328081501090306050a061e080303011e030b0f011a071208071e020604020f030312010b070f 70
    0x540007040c080700705450070088280d4034800c04000d00f00584182c6c0d8421020481c80e0082032440000c1c5810102c10004111a6942e4800c2d252030040c996201109900e81d04030b04092803034001880340020081400d0a104c41d50799a40002d8036030f1620400f00c2d060060104581d014040b007000501c500d1040c1c14003142e95001b1048815a80c4c1c2c203c020180304406c100d1102075403507450058210b0f00044151699030441d1568008804044070800441d070400400c6103000000c241c0d80d02410b4040c4c142c410700080c55908201032030100c4486800c01c0004083e5642041240d80c1e00002100e045503200706410030700c081034050005200c02e00f540003404a814140610800c0c1c0c200c042c1c01030417103852000320301b01c40304c58040d400002d0158000191400405540e2203000601592009506c04810303c4c006003030101301449000700991135155000140d1000e0104011400c10651108071b2540450003942444408005c08030769000501071880310740750228440741048a40003c13049800ea0007010507880d0303280e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 938875170 1250 938873920 938873933
    0xd2010021e01150306051e042105030108150a06030204060e01080106240e03120a1107052b05120403030e041802060d09050f0109030503100b1206131503 67
    0x2408400da106105440301001c06814030a4000091262042d03032081c5146456410090500a051b1414010002120401c1d40c445200140c031540c412007a00d13880200120403c402d40c0c0c2484034402c00d0001c20001440f5421000540f041840040360f825100d82da00c4a588001030441a44029081420200f01150500103c00342138107890810000300102d565881014400218021a04581504164000002a1003a60350b00c0748004042c0481c1c449024203c900c91880d07000e80485d50014100c1070090120150501c000740081800700c0e502c8013401d18007800f401d0640300d983d00b41c81d01004034065176010000c0c10300004101101b28105c40e2740700c6a0380d0401402d0b6400c5504031511491620700d0000c04103000003441e82c2c1940d000303000d480c14540c810009038020258000c09484901c031b10103404d54100404d01804940074440d46e901900c2e070504481d6003415901e0707504081e20395402801141c00c0c0320b45042c02250700a0084410340032900c507035030301280140a80348040102c18040040802407010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 938876420 1250 938875170 938875183
    0xa200d0603030f1b060b190b0d1d070603150f080106150215010311120709090605090d0f08060a0e07030c14121305031606050f0f060d201002 62
    0x2d484003e00914185011510641030400081c00d031200c0303030100d5001c60b0071382e80011641c290160075801d03400c032484c8490242814507800101c0c04000000d90911540350f0f40074401022802c0003ca04401c030300c9052164a5507030b18080c100802d680c0e04016484645400c02c4440180410a070f8a42040d0702c5400443c060000c90040b80400d921032100b0960903880010b06000d07254501204000f540d00f141d56a104280e0001000c40d4090f80038035681d03000040501c511703001070100841c00100780c2d80502d0100141da03401444030043d50003503001442a244c0240c1640c800d0186890942c8040d43c3d02030004112a03059040990722490401c03c0040454143c2d0050700c1503c41c40c8c0380c2140c070241c00071424000b0f101e010b014020301d03d101c1c4003044135045100042c6443c2441501642d080c40400102c40203500345802c800d4808a8654007886200454840165000040680c00c850030340b4041010440605030900d009003080c14440c8036552016011000151441c0c00600700c44c400443c1c404020358505 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 938877670 1250 938876420 938876423
    0x200c060a02070602060c0403051b011211070221070b03040303150e18071a0304050f0a150506030d0e0904110301060b1c0209091b0403050724020a0305030a200d0603 72
    0x208200100310000a1b9000b0307a400c40394064000d004182102e25240c11108010707400ca814010485100a000082801480e98554600b0741c01500c55040340100001e000381c50352140c07200d8018001028840701e000c03442c84252114145035a5aa480b6881e00b10300800074103680c90980c6800700c5002c60300e4a80d41c9505802500800c100d40d4024003050030a80d201c0000344121004070120035052340c02c0c00f00300b034080c640c054051422b5070019116404031500740342002c0000c43e4250032541420501300f02c5485866000902a0010f051614036801e002d0100503c82c011035105500080003e002c2000f10b450130030800002600900c1a1940c418461105401100754020350b903040c0882034002000c00c0c400d4500e40c84c0010a9102a501d0340c00540880003034040b201055250b0410020012031001c01c07028008200c0c00b858502078050307040281d03a000c01409891000c40d080031841b41c2c0403903801401e032608807004217000a03403000e9117030841d070701e07141c04022500c0e03011004a0720b2a1391740100d52004003200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 938878920 1250 938877670 938877673
    0x30f030a02070b150f010309030c080d022805041211150301051c050d0c0f0b0c09120c09190e07031109010618090c050d021305030715200c060a02070602 67
    0x41e2134006040140344140290107800c401e0046195515600c00d411920640d402410194110106901e07581180e600500d0b03641c00060300000c48001c507491a20ba11800f4401002d908035070354986440c014000d10841c031803030388142c103184515004e00810503119172140400074081c4541d01c0c011403030241c080e0000d11030320b032250205a41000c548003240c0b800b6043d0507441400741c241e2988444068450510340030741a81c807418042204400900111000c034000e0103440d1400380c8a140030420856041d2100c80e0414040c0c10142c01c0c01c006864001c5525008004140440c02c103140c81c0e035104e0001e25040224103064490340200000380007405038800814102a5125000d503070701e61200340c031096001111071000d220000c0081054000560041e10540b000b80b07001e51624120b4400700050360041c8201c0c03851006400300030407051130300300400b400070900c07a0039040108e11904006440c0e044441d07011608520303055608941d0aa080c8907403108454000d046513102c0c641050000c1d501c0841c0d00036039002d0f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 938880170 1250 938878920 938878943
    0x4061e02062a0a1722021314040f0b0c07110409060b030102040909150c080c0a02010603021e03301315090915030f03030f0605061b01150f030212030f030a0207 70
    0x88174041c0c48200c0311010003400348004403035a0900c10301405180e841800c5a80d9402612034102c161180540114029110301142070414241511401806402118071a000304429030002d1807129108003903da003150700251406642c00c101000c2c00c00c001003039034954030001d00450600401c0e40520a03140c0030700f036886d007002c05440c43c12088940711211840440c0d9100d000070352014980e8001c0510400910003c204560350741e010a14a0304040c0345030781e13000300005030301c00320b820100f1040225040c000c60101140104a404c4000c400c001c00202140400006007048012801c0c6040001044031080103142c02c20f203c02d004100c159240950400b6034203210000300f40e11200c40709402a6600801810390101e19070341d00b40c0091405c5910b40f20b24903100c2c0b000088507516840603000401c1144000c4c4280d03440140d102e400c4403440042e0618613241c4882c148400b240d000c86c00e8041e44d07810f5910404a40038800d1041ca540242c140c81840e501000040000ba070840b60041c6c440140f0503040e0350364 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 938881420 1250 938880170 938880181
    0x30730230a030915090b0a2309060f07060f020307110d0f0813030c0507080604020109060e0618220c020d1d091906030f0c050603040b061c0204020d0204061e02062a0a17 74
    0x480b0700c09d00b40b500d41d11034401e0200302e01001c0a680208030440c800c68001810104400f110000d0342c00031500280447c1444408020402003806010301c030380c100340b4042d000e041403450050400342000c1c040c007400c0d20028424004060054469484542d0444111002c2c05e42d503c0806030382d0b60b02154200e000406039240050194028006e81040c810014030381400c2000054038001080d4560b9841036000b5641040384d00c0c0e030300c90410b68504071110403501094903d040c0300003a14100d10540c4030410000f1480d609201e90004007003842c14104111082d80203078039110402144480c110031125852460004000b041111211050421520800398081c00b40da480e0104041400111030280084250600040a82c5420004190301003a808400003409030381e0340205c0c0c102c1e00410f14000d9002c1d800101403203041e8000d0703480c0c62010301d445000103030021503800c029205e001c01341107603640c402550110b4504119040115240300209112140c075280c0380700004091044412030f0001e0454104080354 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 938882670 1250 938881420 938881487
    0x103020a0611070b03130803040c090b2403090304080d1e081512070f030b0114030f0a1407150302030a0515030730230a030915090b0a 59
    0x1403120000020f41a22460500a80201d070300c001d1401490f0510145107a000a00d8031019500860198102e0b50f8a00d0800c0048011a4448080c9034814408019494880310599050303030300480b600394601e5102c0d00d541a44514500075900454213078047d80403a074114a40c0070388c11004040da890f42050091a110005840c20002038698441c184c00a40d06007087d0f04150750410f60041c000011541d2840d03032515440d403100c0c080c0c1c0003200c0c010401e0004210198041c800b6103070054046000e45800c140c0c2d08402076894852460040049604200c2e078240041c05110140080c00010030707082074003207501002402584107c440c40181483c100204081e52a42c000c55040c41001a00900c0b01c070741481102075000c5002d03a0728409038002e40030b0101500c4013100700302c45850300c180340342c401441c0e10418807070070703038945400780c1c01d042d40000301c02070202c2d40c0305000317004a840402c0c126102d0030055070101d640c1c20303664000041204001404803581c0e6400040112400340d810418041036860394440b8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 938883920 1250 938882670 938882687
    0x807031202090a030f0f140d031505100c050c091801050a0501031e0809030102040308040312030209060f030702031908070201180b0f0702190c09060605070f0303022209050103020a06 80
    0x840d0060481c040900c0000c0170104000340007800380c2c58100320764049980d40108210390a24210403500543d070320f0542c103609802180240c82040f440b608a41d070820012842c85103c8a1600c0d040104c80c0350308805200c41403021080e2204041d1026540d403804c100a40841c0c4214200521107619080c00251000028460305060340e074413481860f00e00340340e21040007040c815104261601d0b9010021500b60395001d200500046202c2c1444946075072440c00c145443c243c001c07070100181401001404150f607a50303000c0b150915a0003e000b038680d201c582c4200d15500601c00d400c407085030400c0c00200c0039600311a40600c12011a40203021103030039104a9520040c000000401c161041c80200b03004044101c2900d074802902d1044404000c83c940c03950341c00c0f0606400c203685440e1004010304c446041800303081c02038400da09000d17203804016038030364402c01010940a802c25070302080d216000b2855815000d20b0b647c0601e01c0d03603030f03241e101d84480004000030700c0202c0c41004002000500b00f401a8120f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 938885170 1250 938883920 938883937
    0x2070501021203421219151401141005040b04060c0f0f0620040e0c070f0506070507030e04050408120a0204050d08090414100e090c0d15111905180d0807031202 70
    0x1007440c0303041d455440d1107d040b01285503400094403240c0f002d506142504d00d0314020b000011810020316005014040c8640100c0807103c00c20504000910070b11224a04440c00c4907114a0710000d810f0740340c101625044168480109000a4041100c05000741a04075000c54800404120101304101d032685c141b91107240726904440b50b21030001a02c1a0005c8040c1010600442c0d40114988455845c6400e1900450b04500460350105a1205140e4030010625038a1800c1da0104858180398503102620300070b5034003421201c105040044c1e030a0043e82c042d90001c00c0094100e2454071071a2514000c660411442680030300d243c4540520b940040c1d0742001d00405241020103401070030b0198083c001c200081c007031031981c03007040003002044c0c071510309110a080c045c10088881e29414a03402c02a5841d0000d42040c41405012a00d02529960794000c0c06d04418100b0700d56440c2c44980220002e4209403c0d694030220300c800007030178444001c005010140c465610000500032084d0744504a000c1d0303021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 938886420 1250 938885170 938885203
    0x1021006050d11190602150709050f121e0c010810031a15060a0e030105130c1e05040f140c070c0b0711041b020705010212034212 57
    0xa08040340c5400c0310b6000ea43c1014001080280ba512286200078480358454001a07000f00c1d03158104140d0780c015103400990511b461001c0500e801d001425074211030034401d200b078146880411840e0070412210f00e14212003401001c00c4000d03400300341d44170801501803901052032000010007500210303100205482e0310482000142c14140741f00030400340010030300000c15154400045169940b00f021b010781c4000d81c1c1d80d0000100900050500755079010340b0b0031290348180c0c0301e03103400296400304c0101980c2642e640f0390b214030507481e901c0341020010b070701240c1c01a03e00100400701c1c0c03801d604155403000d80071009181c2c81d1105031710144188603011002d024030784091014000e00b0403403c01826400d0107030040b5404800300e10009070440320103e480380c030700e40304601a01c041d0540601c84000103040034000b910903112040c0303002c03445100003003500c04042280d1314044020480007401811180e600160b03090001d140c80b20b022501400003000c40e00c55880040f039100021000103030302406010320304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938887670 1250 938886420 938886439
    0x609030316050d060e190504030806060a090b160c06020601120b06010905090f0405010c0c2a170d020616020a031805130623090f0613020a0507020102100605 69
    0x7403006052020805040d800c0150030080c0003d10076441c040c000282100c009540f005007440b0303421803010350180402c01d0b031382070500c002c00c40400d410408450b4004c2044d100c40c0e80d00c409000003200c0c81405034105061f003e03400b10300004021030b002d2181d68120300c2138690036641901d4280503680d0304002d10406500c421030085441c009985049825080f107018100942400c2d00c0d100003404804007100d01c1c0000045040c2004207211007400383e41c3e65100c107801c010400c080f030303900c40031021003410501d1400e850080c4445450500c0e062007010040c0500000c50140d181112144d649446081c025540140314007030104800441d404010381305200760340c00401e035481031550107592050490880140150441e84001050b840d00700030014110249200094030700d050020004000100c680c980c41800b2503500c8000701c546407141cac4c05400511013907000e001582c2c0c210004031401000241d01ca1541e0001c0340208946400201424689100742c09560a80300c00071102070807960240b081d16444002074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 938888920 1250 938887670 938887681
    0x50706050c210909070f1706030a060207050601030b0c040b1c11130501021204031212090f0605040b0a150911040503030a02061b18130212010b0c010e06090303 70
    0x640040c055295000155202003481100b1008441160b94807146201400a40c201851134151000345e4815001c0c2818400b41e42000e10013029003040310040407000d01c00038003140280d83e003000041065644010150f6580400d4903065072681d0080c8811660f080b41c040c046000c19564078180c600b80d0b90081015810a02e04903800d66032078035903e85e0041483d0351522082074001c07548000b4410b88400c00d5189103028600000246410186100da00180000340000e2001541c0f0500c400042012490510841c00d010030b4040020842c42e40000c1111031030030000810070641d41c20851050740540380c100003958605003410240c3d4603131074111001e0715035031405000c03083c515407241c2140704a00d800641080d4072040868030f95409000c8203000b5a00ca1403c200c03100c420039041c01c0011005010480c10401c0101000168140c000c0e40d252182d60062640b803107000e05a81039030901420040c044000356516001409e0030b074003d000c0707000c41b5401c0100c0402e6401d00028500d024412041c002d61031590361 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 938890170 1250 938888920 938888927
    0xe0c160f060b1008100803130b0901051c0f0e0f06011a070605040602030912120a092906040b0301020703020a02090705070b0a0b011d030606090603010b0402040815070c050706 77
    0x860304803181c1e0ba5036400d02c0c031070351200c21007103a034118103032144941414041071901e503c3e2401c0c3d022460b140e00030010b0004135412020048111604d14410945030f511550040e42c041c0240040741101c46401765910019008540140d01c0c50101d00c0010410003203407000458940c111050700301c030710341d02001c0100110074604104101459009124034200000c0750b40b00810740708140c5080d0790f0a0740103c00d1292105062180c01c904203520f55281b0700e020b0780462030108028000b401b20241b00c0e41d840d01c110034070621061b00788544102504502c0000350b4a40c124020001c1594418096458100082c800e42414422540c080b074254005200015a0380d00b04020214010110010070006100b0200007400f02030445005584d0810045810060000014181c031890414503030b1f155200081e051840d100410401d80140054509090550b50b4102081c090600800352580051000800241443c4c021035852584001507400d841c1c0381d19501c10455680c4040030000d041600401d0341001220300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 938891420 1250 938890170 938890193
    0x303050313080c01090c150503190b0d0c150e010809031c020f03011203020d080c04050111010b100c030909020c030a05250305090301140705030a200406090e0c16 71
    0x32030b1102d0b501e040840740115080d20050401207a02c1440700000740a500d04044028a5180803468450f081d403410380d03c080321014030307000d1132001c0640d02c10f04a070740c071303210b80545209580d00001518140e40e40c91039a0a401d1440c007a08600261626400c00420340c441e5002a0083c2c0c0c0100003141001030010002c586032000142d51545550300b00003034140304081c800030b14000d1401c2004191036021a040190415108991b188104200b2070b04120312841c03040c0544e001e4640a20748000c90322520340a06004054002c0701d203a0210034400d80d040901c0c1c2c00315803000320300e20950360710391000d698404400076402011000c0611741c100388900c01c0c1041c403c80c0035003541c0e03090140900c10f000001e0100c04860103110001d0b0700003007001800f06040e0809001d141e062960000d058840d03031070600801041c0d40405840003410580314401007141210906061749124108807a0584d2156980000b800022203032283c030030b00c001b503200042d6500d0351510903212060f074000281e0076207003e140e403441e90000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 938892670 1250 938891420 938891423
    0x1030b0301090f0803180c01120b030f06040c171209010e06070c0e04120c030806060a020708030d020d0c080907060503040c0b160302010b041e0f061e030c0f0303050313 74
    0x660b2440c0020214081c100740c40380c19402040e02e580c0d079003420100700316100d0f817161651086901107500f161081c0d178002c3d05541030549400c0002403030a5080002800c14002c0603c44480e0b21443c0c0c00d201c1400b0100c071b40403040b100445a031961120302454a542c5030190440c20880d268402e024000341540aa83e0f0a48201c0008040524101c0907940d40401da04540e00810203001d00c49041104014040c1c1d51044203441d80d04004140d542c441d0340003009418000c00c80760060801040395104ac80c001c11102015103150000d49440344040c120350300013034102c4196050282e04101030394074054004d000c1140901000000b520b07a075401d2040c01e80749680044c000703c80c040ba81060000300c90702c0d807401400c00840001041840520603040003803d4400041d900c520031071924040c031881d001d04502d440b42d00b890728600030405505100302da1004052641c4084026141d0450403140c000824000c481a0b1f0b10038075412584644640a00c0c0d00d10405000050100d581040030034141141c0c0741013004810b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 938893920 1250 938892670 938892673
    0x501020c130b030a05030a08010e010e040203100b0613171903050d090c0510030b120d020705010311070c08030301090501140d15090c0b2503020309102307060c0f0e01030b03 76
    0x12032581d9446d14580c8075900400c0041c05282c0107000107020724442d07900405d0041104189820540c0010352161440100d4000c51551051000d4844c0c541a0540e07c007004440105c0c1000750f641d0068508240004150341101d025981c9428041200000c11408203905540e50608000d45a200c070320007842190300c2559409840078002600b0380e82e82e40700003000321242c0e8010540c103003c6024000c6600442880b581c039071b008003141c600143e600145d0741044900034030f030129040c0b900ca52140c42a02c030300f1202604445210760b0125149100100440c101d8617900750070020341c2e9130b43e4041400c682d00094aa0361000300d0f00c1600c1e011510707038584501400004640060152076566440ca022a100d5100c5112141c0c0405e81001c0201002011050707174100c414060f804400c16a002500d0b441800f88a601c13030f03000d07105038a00051003002c25030405148226494441000c4040c40360254100c1c1b42c0c111007041c01c0042800c00a407041c503850b07907080100e40320803118680b400015009088040c4000fa0503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 938895170 1250 938893920 938893933
    0x70809090709030b0a1a0a080303060d0c030209010e0f0c16080a02010f240602060108060604020c070b0309060f1f051002030c1e190b0103110d02060c0c0405010501020c130b03 77
    0x3245546083ca400f8800700304002808221b4107100c0038008005180ca10b00c1001c19000400145c01c0100c01c8a0340b01804840b4505005554030740368101031001d4101030341002e80d070b50020481190340740c2507a0266000a408124541d00d12800d04024070036000c400c04c100f08190881340009103050041c11000201d400003043c4400740c580c0d65400c80340308030a072882d03100351400f40184800c5411850400382195102410166060400d05035549101912140c02540e00051400b00c50030b0a0250358054203001414940da41081185a42e56403070942d10096100103101c0400c0c200e20317426081c5607a81014404006000d480c0008020380000007070804000e41c04104080c581c031800c24040132201e00c000c42e540210082c81c01d4480d0b850b005060402041200c6250151700c0440c0e101c080040c1102d5108850a00c3c401000000c07408a4407001802900440045082460014003113841c000805e810350b42000340340c6c3d880f4012a80d58096075a00c6402202034141d64500e072255400003003035071a000c0c044403074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 938896420 1250 938895170 938895173
    0x304030809062205011206210f080c03090406090207050604021917070f290705010621120318030c06140106020f010f1a06030702070314010911040207080909070903 72
    0x3d200310028080902c084851005010640c1c102001800303180149404124660a0075003540c803c00c0441c4420043d074820b45245001c000804042c2c50360240d01111864860842012581d9240c0210140d2481203080c21000f14074207080d4803d80c0c0180c1d801400800300c80c0c86580a00000758102c44207030201c44000800840c042c59620f504540e000d4049000b071085620380454003a0621450300503440d0401d14a2902200840514a2010002c0c407068003a1350742e0710600d010340c010160ba51041e118090b00c090340c0181440e0401c600c415040c06140140c02c0c40b140a00e0480850301e0211505034410030b0040c030580400e100b9126036406a108010010b10000d80040c0400c01c80f9003640a40c00581c400d17210741c0719103a0300b070140310203001111000b07004030504601c20407030318403164042c5e174020503011002902080c07007004a20010b5420682c0c3d0ac03010f40c00050003a000c3c0240b100d0030b0710900507240710000b09050602c02c4070a0b00d6041402d0780d0401501100300300800502800010411412000110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 938897670 1250 938896420 938896447
    0x605150306180609030c07151e0e03100c02030d0f0e06161710060503070509090a020a030e071d0403170c031e0f0406110c011406091305030403080906 66
    0x500516070142c044081e9110340918501c1c10800905003a0325410520181580f41c0000810000755101c480c00d88951180807038040701c01d85240c9100300d0358060300c05803c9110540119103080c100c4002da068450110035030400304255040072002d4001644100400c00441c00c8030362000c2e036118105800400c8000c0b070050101d24200098482e1144145240940c1380d080e07400031310244d51070b2080840d6100528104d022007038030100d244503002c2449400000502e506108800712854158010160412402c005100b00025000042c4850102e403038081b6440082800288080444115107114000706000c0c040b2101c40f030740d001d4011801d010783c1c4c0c1c0d03440340c0d000399404000e4810007202d404a41c59107005200310800c010034032804545018101c1c14025000e034840c02080d030040e00010040340410241451034450310800c0124041035182507001500300a5200c80d45000f91307030403030350400940c441e0000d05001405c1c1c038000401a40c070400080002510305006404132840042240e07040c4100e070761860 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 938898920 1250 938897670 938897683
    0x5061b0a060c031b0e0906060c06070923030303130c0806040b0f01061b02041d0304030f0c0b0c1c031509020307120b030d1112070c080607030b090406051503 69
    0x1101c1d1151030b0038411142c0d5915214003001e034203103210640810511280d0180c01481c10110b2540180c2c2a90009121030321500200e072501000700c0101d44d05460f12250040516426006e400202a010f590220520392904292800c00c0001006140ba540703030300c002c60340720300c0c1c100808882100c920000014100d0041c04902c2c03040e4010b004071200f83c546500c40300d0031583e058201c40280002200c100381038002c0448070742d001030303416030740001c1e4407050650301c14858455296588a0340f0000502008001d00c2401c0105c0052041d0001c0400e0340d1905901c6030325002c0c0920200c1294841c058440d041d11011400b8502d0700d1450600081645d01000c940701c0034026034200740000703070f000000e0140280d403010403442260303441c80c0c00b004802d201900080d141c8000307548150070050402c0009001c1340c401d1003100320851404000564500d103610304010b0700c44d2584107440d514011940000c2484d4002d01882c0d00d201700040110340150389580c1d802004040c090644d542043e401c501941e89500e080014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938900170 1250 938898920 938898923
    0x20d031b2a0c0e1501140f13030c061d0a0b0a050f0d0609020a0e0d030806300d090807030b0f1515030115030207020a090e030d0203041212051005061b0a 67
    0x5503c034915050800ca444c03c0d0441c2c4d021410488540c0c0503000c190800b40a07030341100c5400030101d680b00407001091000c0d40c0c00703800180c14075030701402c0000c8090700305c0002440c1c6440b030000302210b0150801000707001040d41c8900c4030b411108000c590310042c8900020311140094a06035400c3c02000003052080300c0503500700388404c0e6400146516150313080340c00d1080d10502110420510055540d004214480c05884a809441c804128421003502d88084000000c050100e10921049001c4525550302c1d071442200f0100d861410089030b0f0107004290f0134141c0b42c0000700544103032035001180004403401003001102040e000051485592000840d9030701c1d0581920458680d41803441c81c401c21140c02d0020300505104014490058a8030b1802d1400c85090040010305012001c08281c04c6100304461012190320010401c41080054101140c42c1380c0e650780c90791503000c481c030703111000c0301e1064580c02c6c9450030b060810081c903d8044010600848450850a55604904401482d09007003c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938901420 1250 938900170 938900189
    0x902060c010903080a06140d02040c090306051512030c0a08090a240306080a11090c041a0310090b06071b0b0a0305010e070c0c0308030c07080703020d031b2a0c 70
    0x240841315421b40150000303041030741010f81c01800b602c00060280d6a1101c00280a02d4940b0389140c1000c0c002e00740b01004580000c000c1c8440d1500500150388601c276003104500c9180400e54456074050000107813034100094400803d400300702911b1364401d039041840c00c60350000c3c810902203000c20a003d80c03020f12094102840c103450f1104003014055031100e070052480c0d540094021004102088442650841d0030f817002c400c035441b40c40d00d01d8254031560700b000c80c08250316983e00c1b0881c3c0e10780c0001c0d4440e00080b620400f01580720388100060750101c030182d980c055814400c45001c00c00c44400c049410314410f10340e10006a89400c110300c25041603500e2400b01e9070f87e00040281903010f01905030320800e0380c6170018020301c032a13545a02c4061386001c09005004003000143c1c07030fa503101084514107600321f01c04907103410191900a40d06c00080820b600000d0810000c00d60340c140341d00c50f291010180d502c80a038040b441012680c101041d07481140d04800710f0200060118074050041c0700504103e54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938902670 1250 938901420 938901437
    0x702040b060703050d0f050601170901110f0a08130b010504021321020301060e0702151008070e1609141002240402090106020a33050a200903100902060c010903 70
    0x3261710044a807142e003140440b03401c0c1810001a83c1e03112501e2011231000d000381004d2526805400c500400d64461008001c1400042d40e410a048000140c030320084c90f540e618006903550051b1840c0201c84a078024802d1154000501030b42c50076402030000f00c0482450403000d9982c0d242c1541800159117070300e100054044a01c41d0a40c10b003805140c000e00010320b2b00c64401d0404850007076444114030b00018180c1c1981012640c80503100c3e5100780141281e074100c03461180c492200c040e45400503903005501d2a00300e00440c02c0c0f41e00903500300084481411107242c021849005204403500c00c10780d21011405507003e1031424092044a501303800d10500e80c10340c8146410b1041c00080780c4103030003400542d07015004503400590302c007404200e103c02c807003e584150710010154122190200844038042800c04c020005221855400302c40c0324107070f04840035400400b032054035446100d402c0625401d50403107117620803010804c1d0042d1040030301c0901a140382c0300020240600312149803404a00003150b02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938903920 1250 938902670 938902687
    0x201200a0b0123130513080406020106090501050904030c0b06060d05010906090c0203120112020607200f060c0c06031e0103031e08010503060f07030608100e120306090109020702040b06070305 84
    0x11451041074600c441c00c0c0d0021640c3e010002500d221000c005501281d842d000080d00c1c800b08071a02d440d84540c085461512151a004040e010704454080c42c000589003000000c2e441c541a1a07031401160503403a4001100599162640d403000000c0c003072a00418200803201c06544240300b5140205405140010b64a0828506000342e82e090552001154810702094504091390701c1c00d907045480020340401c3c040e00510204000d4021887c01800d281442d03101490061051030623107240f03680484420380d600360840100956070040c0740300e0800725401001030703003820704000d002160401c015041d040c42c882410740303c005100900347c004070001104031030101c86848110b200710b0158460341c2889011513040a02003684d5040003450460340703c0390316004c100d1890190344054040c14680d07098a01c601c64000d0142d018005c0061704c100244503d4450180300400c95003540e01500d07000340a0561a445c1600a00181d00a03403800c0c1c0e44140d448010380c0d29135a52900800e13880c0d119407903042d204e80e580e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938905170 1250 938903920 938903939
    0xa1805101701060503010308030114010320070203010e0f25030501091a010603020906030703051b04060e0307120c0e0424090b0f090d0309060b0a0803030105100f08040201200a0b01 79
    0x43e84420144181032005000280040701a01e0641e0342107244070242c1180e0030b00403006004e10a50704c0d031450108901264021820708011312010340268001d000800c845803c030780c1d441c40c4a505e82c1001d6042503050440b8052101c0403500701207004508a005a0340741c1d2283c1e421102105800c03074440751110700700d000c43c03d400854540141000e0030218107105c80c0c400810742d0340c0300c0249440308155451002864280c05a80c002000c0e240141e405902c894990300060003404a604445d44244206400001d4044c100784446015960021070008914034001c6c440707400d05030141c8215500710034041c4201c1c0981d9681c02080f0021900e19000c1440402c078109140310308805040483c1da41400070401110050000d500c4003011040e241c00034a515190410382d0080841d5440141e01050240c000101600000007035410f035501151010440c00e0460010707118031840c2c694907030104020f440020055130182c0320002b01012501001940034003014142c83c204504204200c40c90001c00c1c0051001010307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938906420 1250 938905170 938905217
    0xb010609080709180c0b040501110f0304031419060b100f020705091005040203010323060907060c1a0f0103140312040f02041508151303050a180510 65
    0x855040c460051410a00c240e6110025030040d00e14168540c82540c8280c40d040f06040749450b001400c82c4121900c0d546041490390244c803c0b1070005400d403141102c4a040812031000d4040144000d601d040d1460742c80400c9110844008a007074055080f603e0402250b445200300114801c83d0001030326400c0104020b2501e400c4d052002c2000541d04a41010540000701e8105a400c11034140d000355940390588901111517401035034020b400030000004000f440705a140344081c18041c00e80b4440c011070b03000c5589000807a020400b9612028042250030301a0580038001401180c0401020140c00900380d60701000740d94041c881c00f02c100c01041800034022900314408103201c0590302c0c16104042d0583c903080007400c00341400240c0141d82e0115907456100c11460560410140001359403402e05c030b6224410030145104032424a00014050300300a440081400e0749901c450307080420103070003111403000070810410740707030130746d4202080c50b41d1603001200201100340c0d07981c14903c00d030300c181c1e01d080103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938907670 1250 938906420 938906429
    0x190305010603061d0f0c0d1406042a050f1b1501090e030a051803061303030b0402040605313503030106180f090b03150106051602012303040b01 63
    0x41500e1101c01c49a0341098045d810a980c4019107100741c036402100007440c401e51400c42d881038988880c0f0013803a5401c4811503c2032504407000c009032040c0403100c031155800c00072030b0304241031070b0441400030b02c0c001c80140c100c5000c500e4009051080b960200048504000c1d5804020390043c142c0c620880001007407c1e001d488000c5050044c0825071241035541d00503508504c0506c040030608081041c3e4544c43e03055003190040840d42141807145405041c0701d0f1042003907000a0030300342d0501d80ca0034903000b210308503045a501c4600c0c084c0803d8a4508aa0100d8112903000da15034420414070301d00e000d000c00c050b20059418134a900d040502c0c0c00b410441104006108c221100711070281880080306582c1102d0300c3c2d042001840d0070188032203041a1040d00141c410b1081c025010a0b020200e5200800c000001d50407a01d4003d00724400001d100300910030a1300023202042808888103c120b003640d02144103044c894103210591964060b810b40c008420125a0000310401c000d00c00c2c288403640c01403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938908920 1250 938907670 938907689
    0x60c0b040f061a040c1e0c0201180b0c070b070309061d0d08091003140403050f07080c01060302131b110f07180b2b1e03180506090d061119030501060306 67
    0x2030300b03c9250300d003150304e40b440d1b02c1c0a12207120a00d4055902440c28041201c10300c05401420940362a00307006203400c110481c40f002c1c443d400020030000c00c2c1004603258a501900c580030030360b18100081360940031814102068402c840007640311a256151220a09031040b100680c07500d9800e014410391003600300c2107008050508800186008200c490329403c1a00b501d04980d54001c2c0d448841c10912a92100a03c6104000340d1100024410740c844d605991007100d000320110a461000c03c2030718034002d01000400c002225026002e0300400350b0549501c0381900351005800d4803802e55080a5190b803100d80445c10b001e0742c001e44d0503250f10846580d07001c215111411440003414041035020f032440b00c3c800b50014640c4410034030a2041030181c410007004200d1401a005113401003003c3c10301809004003a0405401007030528007602516644c2e44090700080307100c920742c1c4400020300ba050454540920080100c0c241c0c50900340d6070507034986401d84000c030343c03945440802000c540e00c8d40c1c00361028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938910170 1250 938908920 938908937
    0x1020a0e01020d0311030105120319030b3109020f030703060609060b0310120f0b01080c24070206090f15030114040504080d0504112106010e01060c0b040f061a040c 72
    0x40178a0601900c1c1511313419a03030815404c2e04800c2c0e07180707140300d80ca806110241c42c0c001e08007106d44c0c0c0754111406081e0309491641400c4524500d1001620540701c00e1550030a150014400d00200b80d8055900340b400240b80004c0106040086418107201c1c0c1c10a990080d2070f0903050024480034050103004041d4106a01c1c80c615201d4940c5d44251041e0080c0307030013414179403007140910088203000600542c1210709141d85594803144a0f03030300e03502015061300400b10707585203050098030b90203035010f080c01d404c01c01c0e40f038501c1036800c020f1994481c11445501001c10480d000c03240d00ca86402140303e40041c0c01c0d0581e29410541c0440d01d00c0c01a122032807089040804100020388480c065a41400010801281c551114076000c070141e0b2818040c0c1d030708507680000b407034a06000c161942c3c05040c604801d8600036600d4200480c0c011000340a840c0104080402e4817001400082d40190701501945e06070f0b01840a030740c2c03454103850007510b0698140e403a242c00706900e840d00d0b02c20000b41d01002e0030000031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938911420 1250 938910170 938910191
    0x9010f060801170304060c03030e011503050d020c01021e0f010213180507200f01110d0c0903051c0513080a020114130e09070504020712232a01020a0e01020d03 70
    0x130380c0d1003076005e0041000f1912200c0303001c240c0243c000d96114001070000b4000580502044102401548016906882004541c003030990004c0340003142c410703046c0d000d0010820000035011101c01c1c0d0020544642c0724055001c0c20b000d000384042c03d105001600c1001d0028a0711441c4000145222076050711541703004c09000040303810114540301a424441c0310700100810071111810030300c01449000030341d42019001e5042d81584401000202c80300c1034100f003c2c3d410860102d6000e0242d0000501680c408501d1451410010000c010031b4942440c01e01d01d03048000f1890f0500e105590310511745680580c812104540e0800c1e0320008024001b01e0080c04c040603c092032014a2a40c85800d0b0603020410201b02041010302c45c81000e41030141055540394514502040300e44d6a44c0310392000500b0300004c5074011003500c0c00410340c1c84111030b0315500f400c0c581266184810901c02d41d0034800c090414a0342c4148038223002501001c55140c480c0e4516829100000e030809036146000010149030200102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938912670 1250 938911420 938911423
    0x512090a1103071401182c0112020904200a061e1106070e040e010207030810060201142e0b12071107090911061b1b0d030804030e09010f06080117 64
    0x7013400c240f030135000764440041e1151401c1d0316600101202102110302064081c1c114502030540541180e4903c00360380d031440200c0c0104440ba000a42c0509010042008039000c07007800c940340b072a441420f04030030b400305000601b0200241c0c094408100c1485a0200405280301d081c2c50307140c5a400c0c80c05110028541640d241c0d01c00600400520640c0d11000342d86844503400302014402e00b800865848015050281c01c0d800203d5802c00250345802011030598030600601c1144141c40746c2062807600c810302d008000d0f00c0040c4454002d100e8219070320000011001d030640082500c0c0144555170004010300e20394041008100078144500300034804d4202000007a81000c560b602800042e18030f00742d140082404a110703052a6003d0004140c0725209089034041508400748001260800b1a012015445c039042c04091668490103441c200c2021a0051032160b42c424403901d4003d080c0504a400981e00304020b0f00621a4541c3d230000c01c3c400503400031003003805094000055101c9800984049 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938913920 1250 938912670 938912699
    0x4030b07080705040f170a05030307030b0310060609030b090c060a0804053a02030d0f020405031513121704060221010503120a1101020705030306040b0118150512090a110307 76
    0x2101d0340b00c440000c071004801889404000b032340c01003e583d030780d09108100402510203207401d02c0c0301e030003101d000042c44400c2d44118000c4490b00d8490b031000b01d146449601c0319080040020000e4028000c15454940c0c0e01c400070f00310a00ca9449000d040c3c10325040442c1350102109d0780c00111190304c0102c0d1000d507650000048a25078141c0c41c240f8403d504030040b402c41c001d064001804504020340d010303032040b85401a2099805c180c08540b00c0c517880c040036100381c4805a401d025125901088503001c201c1040710144690700505050b440c802d580c1900e00c41d440d0f01102c0c02c0c2c4900d0f070f0124510000b20351050166017035039030490b55441a54100000603840e501485003c004440000446500142c014113034441d0b8084024000c544420903400c007651a584111a0700d48114984156207850b0740c0108040140710482e01c80c1c2d10a242d0900221150b02c41c0051003900500074148904058000050305d944d01c0b8503200b9016180c500036602d400c1400f00e1500603070f5842034115400c180400394143d0802d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938915170 1250 938913920 938913929
    0xa0504150f0209091305060c13090207080415031a030c030616110601030b100e19090204061e03061b1e200c010206062409060f04030b07080705040f 65
    0x140c0781d4600c0074804020f1190080803900300d4007078810469844082050340e04e0160090055643c2e135a0340400d521490300ca808000200b452001d0000e00c40003400364050f00b210343c4200d0015103890f842d200d00600203050701500c40c001940710740c00d030f6494030700040945d00403000907801041c0088070300303000070380b03071240140302c240504a00342c80b2030300c03561240840e00b0305000d6481c15165996100d091581208c0002c0316084140e0520050005030155034514840c4500c40c1004d4156810240011a1016107029101a03074401d4840c1800b03e24141d005d000014003070070465075040454a54900201951381c00c070410700c241c49216071201c40143d0044c102c403e001b01300d1041c0703085403413040d0300c00e0f5003200380303a0410f0031040140701800340380140c0001d000c090f51500760200c0c0c009503208020400004a07125480200007504000001a001c2110182003d844000c160700d060022590710340306160415401070f201c220701d03c030500c101b960300494034a8002a05180480c40e15040c50713440c408030180c0707105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938916420 1250 938915170 938915213
    0xc06040201142b0609020304121e0806040903020f100f06151407060912030f051506041a0403060e16060306030512031f09060f06051e0c0a0f030c06050a0504 69
    0x1030f004106615130b44135101820b48184115183e0525081a0080409503401c40001c0b071213540c03c0404107013401c100c0e40c50902d07455585507041d1703642da014400075168280c1d00300c00303510482c2c1002901150522400081c02d41902c40018145082d54000c0140c5e65150710100805100c9481140c510358044000d0109000b480e144070b80c0c50102d880c04c50001d1003484009012485e8000d150100b003075040e006000b9040f030b6010144071b40e071641c0b802d46095421401882d81e115004010800c00d5040b0f00c8415051008101001c0f824160f90341c498405581940044910302d40054603e03084101c001c8404402408007440c081028505580e038640c1d688102440a0525400110000d00d405120800c4841a8076081075840d690603541c49283c03010348028024283c4000b492000800c8c658412800d56a100d02003401c60410300240661015151348110121031140c013840740c901001c02ca56000c2000d507103101e603079506035801050600008841c009000200b400b0304000070701c40810103d400b07440b0a100c2400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938917670 1250 938916420 938916487
    0x4110910030213031a040c05041a041d06100e0f100306021305040e15010603020702061905070c1401081003080a270815130222060b0c0604020114 64
    0x4403020905580d5034001401640c3d83c0c0500000c141c41760344071a015030312841c205007402c0e0b100e03000c00068550b0340c1803550801008240120240ca0709400c44020007960105504203122410070780d509019049841c2e052000b080da50402003200d4990282d94050341724042007e41e81042c0c08580000c039080d100c040e059540100d10168a0283c20111000070b28001b8002c214544161a4a6868504580d230783c0311082d000d600000307000f50213402102d482960050030b9914000303c20f00f170314080210045c80c40301040340500140300010507a210400c0541540c003001916800c60f0400180110f800510b400d8151a440c00100b0000e03940c8020380c1c0c2042c0541c141890401050b400e02c81c071800f410b94680038144254540062681c43c00710703d84681c40200d444401051791641140c9203d00c0391f100c002504045143c0c03010200f240c841d4049083c001a4000100c0c120b0765030f0342c000002c0d400401d015442c5030401420700c0115a00b2140c03128403155035401c01c83c101007140070714a20000c020f94005003005c4002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938918920 1250 938917670 938917687
    0x30d0f080c031b1603021510030611070219030606050a05010c03080a110a030b150c0a0212010e0618060a0c081302030a0503070b18010513020f1f0e041109100302 71
    0x11003007903021800d08845142c98000ea015021a001e0b04d80ca010303009409800304d4182ca0040f40034a0900c101200d102e20b4903445d166030b0351003000700312958004288203c01d112160059450340765101a6288180c5070000c4242903040180480d8011340c800361054140003c200a45d9800000380c11015406081c924103540d0b42c01d41c44d102909400c0c040910040707000400c0c50b10a0342560280b42112001d43e6034200c02200d190201c5d2543c8120000040642e200004501c010325144170740c80b0381d2000102c0081840d1100c030629502e0301c0002d5034942c020004002680d80303c44000c1003c507330310800d40e05060040c40c24843c1b010f058000b0241c10740506055040c4000c0640d00e00b00900943c0715804402c981e600c01b4542000c0031410025581e10030310800c90030050160910500510b400390744030b415680110941da03401c00210504042e4016000090050a0300160061842d0124034608a445076403c02c1c040c4e40402c01202c0c06200c80903c0c8800034405401552600e84012050203880c0c10300594400b1103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938920170 1250 938918920 938918941
    0x80a1a060117070201060906060c020a12050a0b0c0414271f15030c020d080601360602010b060c1504240608070b0403261b0c030d0f080c03 61
    0x110b02c0e41d20b061a0380300307020595505610003030460f41010810000c8540342e1404948000f4000006035111038803901c00c0c0404680c0409081076144250f048071810031403690340300c000c10301c1115070020700c04001ca002c1000e407000140040903c00104c40301c004120018a01e40d05802140008040d100c100b0400261031103140e40e80700c001401c01501140807140d850711503a440d860300000f41ca0000f03092001150605000082146060241d5101e00b80c1643d1260f004441d561440c20140e50000411051342c01d1003105048004a449110340c0047d03000c900780351020703003502c20008850340501e604020810007640e0118119507800040070154440d511541000b01e540c0c5c1c4c00388451402c0100720301d084110110258848400c82d500c01d419907840d44d039200c03101003071402288400360084421448555400f08040212010f20030b2413400c460501d2a040044111030394131a0380714030540d000030403042031481d040206034500a090310389040c1c17a981c00d042c010244440a4401d506800e400700105072000030b07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938921420 1250 938920170 938920187
    0x121a030a080414090f0721110706150f0317070803010f0305060127020c1507050d05010906030c0302061602030109080901230f2b090b01080a1a0601 65
    0x181254038658560414150a40c0203101e94090507409003050180c6041c000c00181c0b040011200e04095542d0b8060143c4e8016120601c9886c0300032180d20096070380e800d5205102c0e41640c01c0d85181d0300d881c42454040c084503403105101d1101d090007541048000702104451041e281d000704200500102100c2501150207090802465a080840086603000000d900a41100d0252003211581d036a12020003520000b41e10040e090301c45c80c04081d600032034043c1c0003030115000200c00c4441501c1d4003681d00340903030f900303445210000300005005144845180582405007110721001c20150b0318603541d0480001c6503200082c058800070554081d00454046078101e4160060000e11180050745408049a8048002030f4040750300700c0755209450340711101007044000301c00c4c0c0c00c1e481c04040310a001459040281d034001d01c3d0140803850349546070306d0318070712010b020301080c003060300591468083c0c1e0340441600800465132000900720301152050b07450103440c41c0301407112921034684a004803030100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938922670 1250 938921420 938921471
    0x31803020f01030b04090803131a0c070303091e050d0f03140f0403110109150f0b0a030b19020f0d11120c0306060c030a080f090106180213051504050f06070312 70
    0x54008c02000606808107140385281d0344105180c03480c40301d090580403000b030015602000031010500101000138001d60001c40c07424041c0d102c2d203842e01d0401c01c2400b500710703408004840e00d402140e02e840700180c0002124000c0036450030700b4000c042e01316a01120b4654000c0001c40785e120070b00c01180034180180704003404204100028064022b081c184142040c6c080520909003602d030140c11341200382c1601c269200024014215101d4a14644609000440c007601d40c510b110b940b284900e5540c22540300504003083d0214899898409140d102e84c11030b907410841c0100d81500700008140200000d842c29800441d00000d903440f900c81501145050280d10950f200780e00c40051040f006076084110301d072140e802982c40100c95a81c1c1d0044500f6101c00e84500c007060b540f61170b0505c40596094001e0140c000443e80564004d550b144002a10b07913001c10b20600340301c00c00103000e20142c242246207029002d001c0c1c84252401406aa00400415041040482c035640d14444c070b003800303580c02134182c3c00c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938923920 1250 938922670 938922683
    0x120d060f03030302030f0606030114040b01030e0f0f0d03050405150403030b040507020303190216021201090605040b040b070f0e040c030e01020a092c190905060c07031803020f01030b0409 82
    0x160701d901e0080d000358015504003805025a0001030000d01e03040301180d06881c0308903c0400c0710358190080c000644a40e0a07290f040c107840d01c0071400359400400c00100038005820090441400408502c0d0500c500c0030b03110810581004100404500001540c001242c501c651b6890117540e07504084000f881d000b01581c0c1d00030304180c00d02640350742c00000355005070b541c036121a180c600e88462543c02ca200d03114400240a0311851a1005441c042c00b0b07076105c40203108004508030b0942d95580341100c00440302141c0e07034941d0368280000d018548000592150242c02d1460484280e50310151101c044100458070075030700c51400d0350009200f90030041110219400940d19140c80c55009041c000da140610220500398007d03180380305e01c10100c0310140c0c40b005a4842815203880c44a00303400000e500343d10807016100e01800c2c0c0012401c20146124415803c4540e0b180c01780c03868002d006081242ca60310344414010001d1001da510341d840c02c400001c090800291429500010901600391480050000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938925170 1250 938923920 938923949
    0x806101b23010e10021318050412180b2a01050a0f060b0403020f060708030106170108010509070603150803030114030606100509210f0d08130302120d06 67
    0x10803494038580d03000c0c6180c0030381d460003600c1e400540d80c1c00c0707904203d41c4005a1388030100400c040000c0c1d500500707840c40907843d402002903c0fa0900b102d03103c4141c0c0e20844c095078880800040c829401900341042c0554541425420302c0d4410146111041d405800800d031400a2008050203507038400d095680744600c5072010280c1500c035464001c0904540e0012083c1c20040e020380396502901c01c1d03c080c0c5510b000c00c0740c00e00f4210740030320000c489a900c030b02c0d4103e2001c000400100301c40e000518002c003d10754603102c560481423039444503810103900c600c0040e8103107402d200c894080410b00e101520000d01e40050402200ca90030200801c0340d0340b00724000d010000c00819001c032100b421110380e5209800311980b9454031401e104080b500f489070107000070000e0141010342d181c05030440140091016640107c00802205507040c2403c414000504c0e5200200c0c08984175044101d00e42e00c82d0405040c0d0a002040e6200a5107824620b00600058440050000300c10700b4140d210b1405402040c02c404075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938926420 1250 938925170 938925173
    0x6011b030c030806042304030221090406051221041e08010c0f0f0f020109020406090e01050a060b1209070b0c0708060115090b0c120f0d05010b09010806101b 69
    0x40d070150054294000b40340c15000403080c4c1801d00491154600c440b08001c0c10215400e003080120702e024000718118003035084498003061440c0b403000400da4480c10101d54a8008508000c22070784154019401440d4011039803050020100c2d08804000c400020040842c1c005102011580710315040403603410740c2e55408480320360241084000340c480c00d000802c04040c01178025903060300c800d8400000144202d10650080d07210388820b95607014180004281c650656000078261400c98000745000c0c1d0b540d20410308160001d0040d590400c030080001c0112a0824415001c00e00c54050740581c4501201c0102d0301104003040f000b40105110b004007a00c4550800ca2592910320034880c8a00a200d2030b00003190111100e000110310129507100c55260b1880d12003084429000100c20010302d01540f00840f007103541110081c00e8481100c0da400343c0e10512079884604442041c0c02607000c0c0c86080c0007658213640c215030002d8012b802103e15035a82c20020740b0407208a020503035030400550392000800c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938927670 1250 938926420 938926427
    0x503040c152601050906010507030314070c0302150f150d021003150806062d0409050d11010209090a0504050f030d06060f0e0102071a0912070f23010806011b03 70
    0x548098440010250b042e4208541d2608003401e0046a07172066040340483c0596004e803005000e11442428045246901e0100300481b4820032203a22001c510740741c0b0781d80201035040c020035062440098000c540b0f03041c001e01e6204411030040030343d41c1c0c004880d1070000711035890611071074090754000c084290f41100088000c02601041070782c01c2072034031400008644060301080452180340041d203040700c5000c0450b080c00304004200900c02e050300810b40030441c0c40c0c80303c0c05030404880c0a94001c00d0301c02c0c01e0010080c003000d181d40111034103900c103000103200d55072400c0d42103420415000c00440d55071140d00b050341c10954095070701617941c4030025481d21903661503001300c0102c1d442ca44803082c031000d824105490b8201cdc800362050040c0c101c0d10f418028080c200c26003c80e030114084a6600b40351241020804800307c040f1008403950001000f04010324444103200050180c00084002c0d0101000041c94498641c98409041c481c1700000120107034414078064200700070b20729803039807954007500b0080d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938928920 1250 938927670 938927687
    0x6041e020d020909060307060e060306010302161101120c1e02240402090a0501060f03330e070507030c03030e01090f080a0917190f0222050709030b070503040c15 71
    0xb4002e60b13008000a00b0b500e800300d034000c1112150740f1070004400d40d250800c1100ea0000305100c1c149039003403100071140342283c03402d20415031003660b1487c0040c40308000900000116007603130105600b0071650000495228160712120604007a10740c1241080c0311050303040c001011100e08a4088001000e02c0101074911114002e90080d140303501c86880e10458030003510024060000480c406280d0080218801d0344400d00002429084001c0c00c01103d000c0a0702040d801121b00002c000a0010b20201406070a1290490f0240c2071162402c121650301500c4aa0303c00005002e2699409081d41c13000000e4203c032108036030144280c802041140740c0f408554020f001950f0000d040e0b03290108041d111019a060340100c05d1004045c1d00d5002010310041d916000300841e680e40c85500c88000603195504a03151030a0464101c1e004c950214003208111a8001d14610400401c082c2c2003000c203030540c0c0f52035003200061a01a07600e5465040c10130040310742c0c6d4407091100c10f0440b90140003942c4103301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938930170 1250 938928920 938928937
    0x19021f0507140a0b190608030f090102010605030c22140717060a05011202161b061e09140402091f030c111b1201020412020a0b0a0806041e020d02 64
    0x1c2c0b1000c899032039252070b9100f0a07184002c00031054000442d22003450701c0d00042d000d440784200800c915480b0507060742160041d00300c2080d07858010485221942c1c0a002e0800a17090035002016040707420030020b400c699424024001d0201c1e020160621202550043c00d00c8038500641486c5038284010700828039041604124401d0081d04080f90040c5010002d80741101c105940d283c503c9644440070b08025400600100107003202035642c10300044d03030f00c1810260080d0a00d421892145003240c040d2204040c03140000280c06c202c0800b000300c0e40c000c2081e00540d420311740c1da00fa0888245e030104000380f08004d07841d50700004030011450141c0134144e0b001324810031540d0070711081800304400e940d6540c500c110000300d608186001c200008080100c000850782c000c01801c44443d03500c50960890b0b2058006280300018580e101c01507082540c0d10100400e0035000b01450b00070310443c01080c4104c080e0511344125216480b0300d40b04040031400c0c7c003d00a00c14406c47d0386512109501c0d0095014205 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938931420 1250 938930170 938930183
    0xf0f0315051513060e0414070f061e1103030a0c0e221109062214010210110906040b0d0b1f0302031b0d05040b1819021f0507 55
    0xd160601050320300410b405810b40d100308109015010040055440b00780024241c05581d828001601c000d030031030a81c0c0140d00030706c42e203022411441c641ca41481c8164100d8a51242111404c0020f95808800c0403809203a215240660344141d00b400c403415000030507000401d202c08002c1c0314800b01a41e02510000480d5191002450740d264140501420b102007203212000075121840010301c09508502800c0d102c601011b0302e006004000591903030048804c2e2442c882000c410041c040f00260402405085140d403242540c69145000070743e0b481d500d01c00144002d807a10108040440700100f0340f8087c0000410540d200d80e2075150300c1806401800f0000105403e01700c802c0780900f00000855a08900120142140c500c1c800d404d038041e40c000352842c10ba5124182800a0b0781d0744c0c000240806880014011600d03080500b440411510301034100820b041c03c001007980d100c840010000029038550514004200b028000641600041008410144102d210000b409039000004100c01841547c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938932670 1250 938931420 938931443
    0x15090b010c050316051e0d020c0f0132030414150f01050d0f02060a0e030c0603010f031719050a0806180105040911060412020a0b0f03010b0d021e0301050a0e04020312070c0f0f03 78
    0x1000701646a00062a011a5205408100100142812482c0d0394107034162020002c40d032910881c4190300c100d41c00d0760001c4840c640fe0000481c2405007003944022040702129a007080305d1140714032034046c49580d22407044c1c00700304d4040042c80c491054081f0307001080b203510765070000000351210b6503001100b4030901400568180c545001c5040d2410303075051552600b50706055030740c0c0722081c2c09000400080454180b00b401c240d81d0100f8460040c002080c1c0d10aa00c8500029014080d40006884140704a131040054501000c5d4040440e0445104840101c0c40f40000d045c81100c068101001079001440054003251041c0a00395110f202c0c2d10945d1000c1005661328803011f6603002d16102c01c1540c034070801c0100202000a03000d031250061403400149890300025001140d03420031045c2c02465400400100b2545c540b01c2142401080504104132091405034000380e1100da030300016030341c5000003140d500b05118003038680002805424200c60189500d0308440c2501c14150f1000302e44170350400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938933920 1250 938932670 938932693
    0x1111801020303010315020705070806100e0c0702011706130e0a1a1005040c09050306090106150201020c100c0c0b0406060306360201050d15090b010c050316051e0d02 73
    0x4201e90417643c0240c0d466241208240c2044041e5115003070503185442910404038002005202050160342c4502e510f6144601d401c0300140e221000070100010580280943c80160343c0004800b001e041030181c40c0d0070590790b45400152160f840b46550310b807407407507c8241d1030782490018030001c0c03071402035000804241d852040c10954a0007154001209018040304220b1424290000003a05601c0d00f0141196034882010a140c07901c202c4010320543e440d10401c024100325100305281904030b03803009618245070902203c5da1548070700340c0e403c1100d56078900c42415a12400b81004138a40c000748030380c2c250426040040103000c450005030f170840d1074004100c112900c2049170848100c5102c00d40b18052549103100809141c01e40d20581c107001c03041000041c04201445401c141c0c1804044038207040d400c02d80c0794400c6030032144502f81404499200e40e0702040001042c0c41460044685001050300b16240003030a184200c0f00200c0108082e684208080e2404140d02c016850300354225070001c1d550 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938935170 1250 938933920 938933923
    0x207050d0c0803360f0c0f1f09050409060b1807050a081b0c030a0f080f0105010e010e040204081e0d08130311011103041104092103060807030c0f0602210702120111180102 75
    0x401d52656401030b0054000d028408c40c0300f030035030744d050171341d04050024951721404102a80c0602d01c0c00c44542c1d5403914200c4a40c40c000042205064080d201110341c0c0c504944041d003a4810498010240051400003c80da5240031181d00e00d841c410000340c0d521030002c09030080d1f803508211001d0300451140900c0a03242886502e04510580d00c00d03201040503444c0c80019141c0070508102c4a040000385510810705071101c0c0000d01c02010910700808181d0505a0b540945880205400f4156005850b82003031041c1c1c400211a00a42400040d000b140b4651505445a01d09182c00000f00e50800003481019114034010314400c901480e030f500703041180141004129034498400030000300e03503000001c07841159610705440c0d442641c18001001502ca03407481e898502150320071074542c0502d04080c40303170f4425066a40000c241c980001e2800b5480f044056a001310140c982216070103000c1154001c0d5590f4048030f60b041e10901c0c000f00305074000c030400100c10f68800b940041c1404806014000d482d4030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938936420 1250 938935170 938935189
    0x4030302151005130b0405041101021b0d021210060b09120c01120c140403290906010e0415050907080c0a0605030402040b060f0d0207050d0c0803360f0c 67
    0x50b80c400704032000b0300340310070082c9102c801000e10302256034071400680b61751902e100701c0c0d010328011214402c0049082c0c0009180c90a0202248186940920341d01a01d4070b4a041005107a036040354030003000c0c4103140c0a140360074031782c1450a545504086001a02108140080200c400d055646118410340f08440e9651001351000c868005112a0b0800c80070a071203610411080c915841e106002d60a139401c0c180b1650480d400c2518013444a55230400280c0c00c4d004401d6100314840544c0a80c1c2c42c001c1c100c0c90301c070101480b034540e980451800280800001d641101d800b07220240040055003807034840d140c1d03220f855018030045403060140400c3c292030030070342d21005c0f120140d980a103181d0384d56080c04040e0952684841d000070050002c0703030f10a4620b01c0034185680c00c4800050321520a41811890055101c4d003042c04d1148200c02d143c0440e012000312035001c4d102020f1002900d2403079070107011500b850103e071001459000960b2004600110310303087d000c1881400c81ea180c6912504100b110178 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938937670 1250 938936420 938936431
    0x1090609060807110c040204030b060f040e07031202120301150225051c120203071a220213060f03050601140907120209031b09090c0108150f10050403030215 69
    0x50810b0001900035118004070f0348000c22107003c2d200300c01c41000120301a078115400440d02c1000300002c0011a042080702c620116200700c07000d100f24003c600703031151286440e010182803510700013801601c80f40200302000300b01d000000a40d55030b607907442d0a054185403035606040140a942910401c0070405d90491380d8100c94402e6150300c42d4a420104000c0c42c2c0c1c8420f107100b420310754440340c40100d521036201c0b91028000350055a07030307420503142c84922003031441d51082140c0c8800f01400856100c2c2c03034000c05100c0c06025a40c5000805000080c038115048000780342d00e03401e008000c660760f02d415410700c0071a40301c0c008a4646980704d0f12441c0d441c1d00c801d00711940140c240310016100d507100b502c8030541e0b000c81440040c0b41071091004641005182800400b003450805921022805c24841c02d0790b014036100040c01c008210040001e009100c0030b002e08840030b0352140c40c0105ca9480c80d1810700d60440041904001c0d8192541c060060707001840140d0140c01124411700300c00340e041e140c091003070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938938920 1250 938937670 938937677
    0x5010225170a08070602030925090504060b0d142a01050306011e0201020406090e09070303051e07121107060903021005040801021803070b070309090f1b0c020109060906 74
    0x1241850481d841d41e00c8001ca015a0074441e642103000800c01060041600c00c0c010500503a0340c0c81d00b44039040c034000e031b15044c0703504c02c81d601050711030111011001d44e01914913410700401c0300d8486003000d4010303016641c8941c1e44001202c0503002001801c8c2d94000b5032500541c21f50303209030140c0440094050305502d40d0101d0300301140101d8059841007000350750050050500140d060001e201015000000c140c4541c0980c1d80014244080c91b082104c070001040340f490291a140b44c00410161560200d2000030103002022070000f400c2000340807580c059000ca800c005889500906000490320402e02041012070b0409082d0740c1c180740003081e82020783d0f10b0f0b40c8a111303205245074203100c02591210804410800b00348800b1928490a000030000005010340180d60310201c0d4082500b01503495001c0100d00300200300440000307070007152040032a9080c0c0b00000b1059103a072541000750150114a0410303920f11405d40c15040c2d04404500e62090007030340e4040c00c464407206d05550005103800f074503010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938940170 1250 938938920 938938993
    0x5120a0201020105061503040f0503070b130b0c0712030e030f12060406140901030803040305120118050f2403190f1b0e0c090a1e0914070f110114040606050102 70
    0x2149031540c9c1d4010302ca200d80d089a240030026155409a5030050b104401c3d1070b061500824280b00d0000c1d805a08013081014031032616075035684107103404c0560002e4006040d100d2a00700348100341802a03824a0a905401c555182c10310b01000080b000c0c100c82c01c9100e0380c40e256021509041c41849410101c4c80a040c90045900710344441040d42c100400807420030001300000200c09022100720f80c000c0800c21801032480b1245442c200581d00d00034545440154040d00300188a4030640c50031000c0300d0f07a00c075141501001000030a080c07502031001e0170300d400d9204400c401040451342060356654010044030240e0385280f001285641450700c81c41c0340c45000780d000b14031160030b00c0707008140001008000361f0b0034507071380c0811140104a0041403039201b00fa86c0410030104526020300d524075404814452164a041080644448014446441003122040014050b4103007503120984244844007404514a0546031140140915001e454010b0088103541c1b00403540415004140c0d2002a11241340c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938941420 1250 938940170 938940173
    0x510050411371206120c0e0a0504051c27170705010e04020c1e06070906030b130c051c150b07020f1504181a01020d020d08060a05120a020102010506150304 68
    0xc0d244001e5800c80c0040e66203110014041054a48809005e803151160000c124030303004401e01c11050040c580f9500904000801001910118890103a02c02c3c0105030314400e005a4011540c441c040e070034904080416002844500010203521011510240e04050008498506003070315511544240ca01085540182c4c9480d46010340150680d1484d800849002d0070070b05540300070582c02c08c1e80c504680c1d080b28080c084840d610010f504080c000a040a010600007000864618030300240300d400c01b00e995000c0303c03281c98031440459260304900d10b844070405420362040790003408044482c01c04d0501401d4005506043c0b03a00340d030089500101075110540440c414440c0c1d2029080d080c0c2c46100301040301042c080c2e001c010a038647c1c250b241d8001000e2080002a803400301000350b6480c15940030404032205168001000c0000b0885460151070725140d46011988407402500410b0b444203400c2c0d01d42c100310b180020303401d1859000360300910032170b00e0f60000d000b12010210180000b00100708001030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938942670 1250 938941420 938941427
    0x114180705091306050a0c1d03030910260708010918030f090b1201030209060d02090a18020a0803210601020c0603090a0f12140f0706051005041137 65
    0xb5881040b0008401020f03941d607135500100c0d0000c9450120007940c8410507042e09901260080c061602176010010034000000001c2d40c0c2d000341542e1910500c161313180220110320504100888401040d00200703440c0c81c20301001c180c1c000480d01100001c007060000545e00a40340140d606c10444640c81030038600203501c0c1155840045524842401903041001840452000046c018015101c161540702e50440c41044500040a02a0f03486200400203010140e1742d02540b190304001c080c807001442902c1e40c001c0901204100304085c1d030000f81c0081c0041c0d11400800101460fa549486412604841465040e50302c0c1c01942c1c114016885080702401909240000355000a604030880710200096500d01c1240078103030504560880e090700790038900c1f41d0000d88144466030785080603410005445202d5203207000c0c0c1d440c080c09260312800490780c20040c075451100039000c01b600030b2001800d9481003003015801020600a40400c0d4400c000410910b40800703400c0000010b1032058030f101e07540048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938943920 1250 938942670 938942689
    0x6270d0f0c0311160f05060f030f090a05060c07120c050c1002070902040611060709121106090d050717060c1801020322031515060f0c02120114180705 66
    0x120140501048805141c240402541c11444030b9044c56403e00d5003030060000003c5195400346008081c20703c402c960440c441d10603680e1000d0307141450032265581c0040b441c60200042c60140c00da000f803405004034010781d0b030003d1006038010f0080c020310b06202c100c126480c1c008210040d00039000140084d4440c60609001e031180300b00b501c11a4251525a4465070403a88a54844c2c80800c800c81191a10386805010456108401c0d08101c0745840c5040e051500d110815440242400a213010580e440d0707441d0010358003041c030040d08109940c5498581140c0c1c407051405900780c03081c81d035491040308140009200d0b2082d1400030855080444002c0442c3c0e030241003c0000b41580424032000768181a43c1c01040c10700d15a00c000d1580651460800031240f140c031030f400c0301c41c0505000e00103001700440c142c00001c6605510704480450178a10080fa080480d10400a6006980103800440f40805401403141000710b65544104d40e201c005200c0000100c0c0301000b0710a8002d40020440c0d8508807404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938945170 1250 938943920 938943923
    0x20a1502090a15090f060806010516061410080102040311060c0c030f06040b0a050105011d06041701090b010803030f1b0708030a0c03110408070e041406270d0f0c 71
    0x150900040c81e000070500501500890501c81c18101100344007a407109031040103010000000b203000c1d00f0903c00809603000105107906021000030004108a4205d0114582d0764101c10b0130402d641c44103040142c0120305440f460000c1c0700405000ca40b8140601c2220100c81e44655a0102c0301b5800050081c3d0f82c0090074015031600900c1100c40d5251414082100c0002d01400a840e461819140001c1c0c90b0340702138134402c411031421006001990304018090341c1c038010004120480d07407139040002c7e4184129001340f26401d120708840050f451054100810b46032150034006080c2c2e888a5036141d43c0c1c00115085a90103001c000441d500100000d894441160319900b594581509612003074010b07801954010043d40d610140c902c8040c2d0305109000926841445483c07030540742c40e030841c0e03441d400c901420313403800c030f203c80070074100302440361403070115041c0c107041e05c80601c2e11703490020310400c00034442c4402c0c001c001402d0800c2000841c42c40340188054542c0722116080c020121584003070101e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938946420 1250 938945170 938945213
    0x51e07050f061620060708070f0807090b1e0c030c01050c07080403120c0516150f0207090b040b031b03070f0302030d0302070201052101060210021206061e0a020312011401020a 77
    0x4010404c640180311280c070450a945814015050040c00140703200344c2c042d124010000c50700107014280b94449184400c0300d001c1700555846081807c281020364000d0010070707410742000100d1600001021010b0700184903000c00801c004d0351466a43d080504c80c210001b09030080c02c11044c00051500c0c84901480003082c80d100181d8030b81591094a032200c4102c1e0500c4440d10400d04012504601c681143d54601d2440e00103200011150081d6030354440303001391089035072505018141c58445600641c16202c0040440343c03e541c60a4200640030071070100035000740140d001c0412414500020582200c0d80640141070640d0b084c02c04900941042608a041202c200620f00141078040b400d502c1c1500201d41400055140030000ba142030100c4480012180c010302c071403503281d5842c5511130341c046c0c0141c40701d40d520103906007242400120101e01040141000c02c0018125500002505144013a4044924241d0300c1e01c818890444003802841e005902660074140040c0c0ca020780c280c184800c408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938947670 1250 938946420 938946467
    0x9071b0803012303010c120f18060e07060503090c0d0804120c14040b180601050c1c02060c07020906040b011e0c051212070c0201051e07050f0616 64
    0x152104a6035100780d009000c43c001e079040700710101c40001d039901c440340003c900810100c95140030107000e000301c0e0070000f2000e07a078500e1070701c4844032280c1282c0ca02c11580d4404803024810b61806000030710b10844541d80e54401c2e0a00454146d0155044a0151009071300424020030f80300f0400400840786031089491040c240000101040124800d03030a840c40340750802d40355070502108100d40745c0321861982c07080d4100303ca0111662240426030444201040c141d200681c2c034540160f0f20b520446080071100d22449407507114020300744a4407080114030794240d6400380c170783d070446903414044c000c006540b00c80c0e042d001c01d002d0304d025400800c03081810b04100342e1030581d240c84000f2444000c01c00d0000f01c0c20b4207542100b0800309000103240701c001564002d00302016462070204a20000b0040c40c00d00000303045140640e8024015500c0c0042075011000d055500740c41d600490b81c00680041703601c0c2c403030115440410580030401c903228000c80e40c0803040181282c2d00485548040b101e00c002c243d02d080317 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938948920 1250 938947670 938947673
    0x706140a140c03070201080705040f05060313140a0c06090b0a110a0606120302060f0c070305070501092108060301050103121202090405100f090b030c0405070e0315010f09020909071b 80
    0x1c1002c1e00c82504401d0103503132200703038600001d4441003000b05000d041000400c42800000b1107540f80c40140c13041a00d8054581d0740b0002c0d4141c010040d40e4000d010680c2e041c942d902c01120018901c000c592007a02c88130620340c1d84c3c200070740d000407040c001c0380c042c00004e1040107003c510880e000f03031070780f451802100c0c0d1400e055182e00d000c840041c0c120406030218081880c040c55010080d4641005809051a0040c6072000401d00f960056410040402ca40000c02030140942500004881504008281c040b0750b003100040d04113001100d03082000c5180840020694501881020f048941085007080740c0c0e0b6022604640908160012030402982401000d8031511148101445450f40203040341d070460810700000220740e020b901031030095062802e0b140c01030b02c0c00b14032410312200589011400351100c05080d120758480c802815018420025500b69075054800340904980710142000001c944640008050b0303c50591401d030448d09180100b10101d100303454100384001811108070902e25107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938950170 1250 938948920 938948957
    0x70512071e0320100b150702060a120f0b09070c03020c041509090b060f03032706070807030e0111071a09030f0303010801020c1b100e06190201140106020706140a 71
    0x1e11035503c42e40d6020b0841c0c4541a04c2c940b1910f400c4403c121201b5581d86d401c8480210244160704000340108004520041614022454a0804450b0900600080c00752080403401404400c00c03103813142c0103a501040b5900e00401c80d5240c4076402d540640440318540080c00041c0c082102d010303450420307060340000c826455104404549100c1d0300071101c1804c020702000032a003201d62030b01e0f2003034104114070140030342c0450801c550040c582082600311444040000c80134046c1d51405850450f0025110040543c010101c0002000907281d00c00d85014080400ea03860300607009290000c2c1c4112403070700712581c1c040080c1000280c010b0031141c0b405a45c4007a5411904280c3c440700241e0b4010907000c4070104223020700c3c42c41400e50265114541000c000040e02500c0c900310480510120203240341d181e848240c202c0750700d0080f5241c0c041e007aa1804070024001c2400c0e1200c030703450180c018008260207201145403000c071203041d5540e80890440300015009580150b01c40014405a0041c103481d0502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938951420 1250 938950170 938950217
    0xf1805101503050402040e0f0a1103070308070302010213090513030302030a020f07050a11010f0806010302070609061803200a02060a05041212021e1207030e0303030408070512071e03 80
    0x40c41d5408920f0707007414818002998200940c0c84a990040300745000c04e50800204a1040c640000800f001030800f07001181c1420f00365040503003a00000a404403d1680540060402d90351780c080c10001e4984e0740301c142007250000d0315403100c1500d9071000c21001c607109401035074001c080c0070001440c1100d08840c1c1c0207260700100c81118a070701704030502000e01031b5400c0d581c50750b0301003820552100350120030b0041440c240209201d050540c00f0030a901800310301d911994900d5401001000003610b4030003160302d040c034050030483c00240c442007103140c40c00d01080000c40780c0c40000b000385420f0f140c6a00300507294019040240c104102031100003040810014240c4030640240303003910707440d55100002420160900103031041124903009036107401c40001407440030f0101000300152101c40a00e411901c11700460740c01e640c1440044144000d00045600400210b403140c0101c400001c682c000c0309800d40102040a800300d00c03c00d20b9280c02d03000782c14001160710301c40d1030803818245000c03904030b110a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938952670 1250 938951420 938951459
    0xe010605130b010807020313051c0b090102220f0504050c0c0a0c210b0f070201150b030a1409060402011b051b0f030c090105060c0c0a0b0703090f180510 67
    0x19142e074524100365810a440350380200b0180b02445c64040100905402103000344034803406200c3d002c00c8442c0e04440b8001c3e2090f082d9020f05400c15a052200110f4040c3d04004085502780d66403050760802403601c203040342c08071400034910340000ca01e80400c100c01864010f0442d924980e040040100214052012040d07040c800d26004655605000b026119507000180740450200519102404240d81c00580b5034410400c0030704000a90314207504134050440200305503600c11050794003107a100707000d82c0518032650480004200b01c84e2003200c0f03a4054007082d07a0510b1107401600c0802c01552154540310702c1c0002030031301c000c11052a6035942e0b20741940d0750140c1ea65017840402d00c1c0034078580b001d0200d140100072001018543c1c8a40300280d0070420606c281407155600181e4808014401d114450300110000c0c0004107a81e501e44280c03500d039219a4085000598111000c40d200c030003945641b0030b49241a021942000d13040c032a00005001c054008880c0c41c02e603400005001c0100d0b1644840074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938953920 1250 938952670 938952709
    0xb1302060403030203041e03111e030d03050f0a0207080a0804020a0f090f2405040b0406050405130b09030a0c1e0c090902190b19170f220c090e010605 66
    0x11480c00044890003410687c41c0400841c481604202091320b14a8009141034103d070134200050300c0d004161030f1601008101e0360103006804441c0489901940300502c1000d41003681410b654500302c66100702d101e2180024031454082c00201005031140040c1684240b003e13013000ca009855a07403041d11946540d022a500d96141c0030710910003101c50144140c150007251f00d21450880c480884001881c1c00d0041c580160f54640300030003903a5031070300100c00600c0b01401c100b00ca410242070083c1e60311400401901d90020403000b0400304280001191200700e91035840f100080c016a940124000840642c016552140f0401001080300690b400d002803010a8000810782e0f03007803040c080484001c81801900107084002040030140d80c10480360f00c5001b41900d40c00081c10803105649100300c110300d07641c00c0f04000c0208100410320100c4103010b031413200d02c00010340c8a15331700041609102540203208540031802004401e0300758000d00c00d042c5146001080890703d90700880c00140028107400140e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938955170 1250 938953920 938953927
    0xf030d270b0417010c03090c05040c030b060a020604021908060103080c1606020f010e03040b160c080f0607030b03010c120c090b030c120115090b090a09090c060305150901030b1302060403030203 85
    0xf24000b41305604044189050a21019156032541e19a5840f40d200740341c01103849070303102e00805119034000034290100410b40764460318035000084d900c280c1100d04a024130070303481e10344103818032880d034103400c075045800240482c1e0b0946c1ea034110300b608603001d010464403400329850341d0300c1c00c01500000130700103641c0205400704034416403e00390b90240449100c1d640081000b4400c86050800b101c04038941038242800c812401d24000e00005402e6001c000d0b14014000700c590b040da0040b4096025600301ea805000480e454070425080700d00d17209003040860898881c260350300c540e41c1c20523207007650141449400150340d105e000009074011100050103070700c000341e00c81d0051111420203002d00550190003100d0700c24032a0180040e50725004800d860070780811034186580c1d440000e0302c0603180700c0409015201e8246007024804441c2c2c0594030120381000002450540311304c0c3c102c0036400e0f00030001415039286851703405c4200e030060b0112101d200d40e0650f203030243c0c8440c0014070045110703500640d507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938956420 1250 938955170 938955209
    0x1314010e16050a0b180d052434031506050712020c0105042d060509030c150d0e01060e011503050703050c0d0e010603140a020f030d270b04 61
    0x1540001034101e0b911034a040e20013409090030b200261198a10802081e02d007048002d03001840444107990020b02620445800340a03000a00c00740d02c10401c0d0310715108100e0384488d00340707584030385a80600011011685581c0050481100c0c2000c0e1344040500b00040c0c1c1c0c00d19202840e041141c1d6803c414007181000800c041000341c07401d110400c5c0354892015240c4d128204000901030f220b644650710700410712411041182c4280c0e039414601c054482d682150b510391301c410240040e001000414468021814002c00703905102420104542c1d84101d15481e0210383c3d12070800030164400781d0911507580e0704000c02d1000c82c2d00300d424080d041105c481d102d2484031003002001c3e200010404003c05080c10300344070a880e101c1d0182d891141d01c5180100e05040304c2e469250040080754000341c0507003240322215485003800718144442900039540315950050b100c00781a0b4820180c00314000140301079180c02c0c5907200468100c03500074011003104420903039602000e101a00186c20196040085625070034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938957670 1250 938956420 938956453
    0xc0c0b06030609060721050106080406140c030c0c1c03050613090506132406060201141311030a14010f0605010e030607051309141614031314010e 64
    0x3a80a1001c900030465460244100368886030301401201c24402215948081e0381141e10300401c51808542d4200951b40e500c000c000c01c040c1c1c1c160340980310945400d528048100c000d000c060b20425020700e0407403940d1180d42c103190700350f0b20088280100d8003801d42e440003481d1011404d10b0390309901e50f4011a1904080d001c2000110781d000512a03054505a00382c1c2c0014004074240f640f01540000c03800146181d4100018180c98030209100c00b011a041c1808100d0025400035043d102254020401c0d0004a41603c04204e001d440d61415610210000c60003c2c4c3d00101c0300e8440c60026064900100307190351404141081c00c0e0315104680d440b40755004217900548a0003000701403d10340461400d4400011a880f00360142c01038003004000184a007000f45151030400040560101c100044036001540c0d01104900303542440300071000c0703006103410b64401c1030100206004414081c1c996158065007007007a499000048840e04081801c001102800b0301ca10241081c083d8003030b184004c844004007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938958920 1250 938957670 938957693
    0x105010809070e010b0702010e10090807170303061003090b0403120c080118151208041d010f060c1b1508090f1009020f0a0f0801110915070c090c0c 65
    0xc1c001d5101050821150068010650450320f038403010b103669144500040b2111082414000e8020403d0b01c12030f079840c1d0303100601808a80100003a1461140c030341103e8210755000c43c000d042694001d1000c690329107441c1c4551072090710281400920600943d4410740440130071141600440c01c085514042180d00f8001c0740420031031441d11108660405a058451340d05d0100524202a41d4203121005c500c0b0007510400038146094450420b42001c0ca042a0039611a02134500b10740f0740080795000442110b62424181e9440800403040c2a041010031074518096401c19214010b40480100d098041e481030b0f80b02416060300c1200e6480004000646460005030100060b0360049900c20914200460312203840200391401041c040c400d40002000c0d10400b4980c3d96100c0061040001e200c40346c81c51100c211400c00f030080c0711011101c2c08080090151002e01c5070010000324006903019266070060075240d100360310240403942c4800d106801c0310100210540401d9803a00040300340301241e90074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938960170 1250 938958920 938958931
    0x6181104090b0a050a0b0a18150b0307121401090b0301050912090d0201090905090a020a0806091b21070f05150a080c0c0102130e010909031e17090601050108 69
    0x1400458502d50300c2d0600e000004190a400f41c2c0c1d00c002242600c1d045411115084000a28148030329450390190528980d04c026440301c4c03280350030300d8071000a0098000310f003210311070720f074407421550b80704c0c0305031078001c014039000413010340d181a1004103540190049002c6e215070000000d0011019040c582111400f8040c91055030003c0800d091525880084405118050b200c0300c44c0e441180c070059034819003a4101400744c03400d0504005079003600003a00c124650007141c0b805401179450410340e45500c0c007900c112069803c480c4e18551041054a600a00c00b2000b03000c2920110301221300e4140d0149041c2a200c45801840c8100303e80d0654401c18400b0704400c40b428041040c5041d8130300e00e548a240d840d0702c1401042c400203640c02a011f030545440300c2030318000b595221050102c6001000150003000301c0c01e80002c0001ca02d00303000c0d03c60303100c4441d410f0f1500341c00c621500c851040c07a1700503a80705c2020003000c04604107440d802400f9560041072500020103803941480009070002c40001c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938961420 1250 938960170 938960179
    0xc1401021305041505030102070818120607081b0c06041b0f050f04110c10060603020a1b020a26010e0a030c080f0702040203090307120504140105090607061811 70
    0x890140440040a0181100d8040f200000c08400e080e40c10a2100034030362015506500c082068018090401c000b80100800c900030741c02480d070bd0030f042040301d4071140d60141507680f00100085200d0301804105400c00c0c8003440f440e141c00c000f5106590541d21103451040c440e0040702c00d000030042400c502075006101503107498011303414402810300b6941d462141511a41d1a1854401c280d25241c0c0203403134004608400660f90010080c0465480440b0528a84154500700d00021000e2191090300e0000b42141d0b100f01c24080140242800c10503448800c0e030384505200c0000035030000140302c107984002c1091900c0040c0c0e180b0720010f0f08560031318010440b075401141200c40003d07802680c40d810301c1e41c420500380e01c1e00f00310b40e843c00140c01180f40007508148004180900c611000024101040c860009640644c801c910300316810b0050b44541001c02008080001c00b0b5030284001e005405009080a0308065407600e8040c265002584070b0008000501c100c40b041c1302d90010170109902c800e45 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938962670 1250 938961420 938961427
    0x3080d06050f060d050a0f02030408040f0b031005040b03011d010c03060f03020105071b08120403120e1309050c06070c060f080907140d0b040312201b0307060c0c140102 74
    0x400318240344a0384071341e103400a96480010301040000d03800360500246000045449280074a02800703a98000d00840030b1151010500180d080942c0c002c4a100e0190380002c1000c7c00c0ca8101400040d21000c00c1d91903055490b8140c8003800148003505c800b4201c0d0440022949031a203040160480307150303400085e01002a0941400940d810100f00c42e2902c1d405864141c2c00241e94848403030480c203a800000450055a4076021341207252400b400170359000d50090600610f1200d01580c00b102d030403011035000b410001e210040781015920150b6114000c009540fa0a08d0140c0000c1080d0311440080303c0a080a0030140b04d5164860100b484030a40c1d41840c2c0100e04048264580d946040e00c80d9204040a2141c45d2180d61903080c02c88402c61740c0081100c110307081c5813401801450f40445d00e80c185610303010180144008681d80d2074401400390304854030b040e00d00403640c1010048a107903201144000c0019100050441c4540b601030301e4680d80c1c3c1d02100440745404405041e07402e588103404d03801807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938963920 1250 938962670 938962699
    0x4031104330b0c0307020108091c02011b080907060509060d1509050f04030c0f17030a060821070b070c05060f160e280b042403050408220302060403080d0605 69
    0x42185c0f00316809080201443d580d400545140800c140d0740c007902e42c103e01101444142e015002490300d08054404c5921100e015007044812100072180745107580d21280c02008a503004100420b41048007409091138010550303100816201d040710000410b1801c800100300210b2107203c1c441d00045400c840003854205a01c004000b45240000031b0080110001c1c80c03002c1001402c0810000300300c01d01865101d1901c0c20744440201058454800039014101106000340c40f410b076008203151490840c0307030902c805a2520007c2000041906091044440340c220103d2001c100c014410140640042a05e1a00c2c603515034619079501031f248280015112001181d5460039141c6198480c41d260040d081500b51369016450000b0f03034130414001c800058003090000c4c86030b00040194107a10030b04074507510500343c2141104c1045401914030a014003100482210110a0300041c4002c403078142c0100c0e48a4000400c0fa44c403540c0110380c0e10200198518101c0801e024210040104940032440c0c0342a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938965170 1250 938963920 938963923
    0x180c03141504060e04060203040201030e0606131d0708070602070b040509070c05010f05070c0b1b0f13150306170106030519021815121204031104330b0c 67
    0x18180c0c2202400d03454250207103480d940e100f00700a00825600190700d003041c0c10700000131350090b1030990009041103040c00d11300d000001c80754080d0fa4090000030b140c0460605503c020081c40010f0310341000c4850810701100420003414002c0d00400d009014075038a040c8002e480c1c90a26440042c0740e440070700040201d46d440140596000d4114101060510003900c0c15a0051200128800c1d8403403a00041c001266402001d40d20081c4c441c00044019484a01c042c80e040140c5421a0900b18010001580c1c290742c020007400381c500c444100150060380304d042c49443d0174040e40c02e00000a80d05c0d0310802924541d118464040c8003181c000308007041c1540c50f101d455600304594800031401c03800e8100110f480b80654907540803020343d82102641040200c0607440c140e013240140c8100000f50301038080e6180400c140794000380120401c0c1c98545581d880c108141605800300f58426628808000d14851410310440304841258004203203610181844c5544a00e5801802180c8018030500007003031030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938966420 1250 938965170 938965211
    0x3100e161802030426180402030411120a05031207030b0f01020705060f0c0304080304080c01050406021c0c0615080f0c0d0605060f0307060f09090b100f09050a180c03 73
    0xc0c507072000340c1e50395240d080040c0740790303125000310310740700c084644144400b070b001e001421048014243c4080449201d104000980c0410ba6002d070101c503948a0742c098070702d40041c4040601840c43d050780c0f4581e40e5900c42c1800c540000d4003140c03441c103102d070421021641c9441010565801111005801018480001c4d40c0d40484c0c0a12400751400281b10b1031000c0c440402e4648204061045956482e1920100e07602c270740081c407480e41a40705d8618015265030180003030705c0c00c1c0d8165500030b080b240403800750a02c0343d4080c0309002080c45038801880c00426400d01030903041e030502e4503031400380e14a40b01c515452320b20380201c0360810390080303200c040c000d40c2d41140c107843c015004000413035140c0f9200005080214802c401765070500c00c2d5480021840d41042000280070841d45609840e11b507189610004d485080240300d40c8110900f400031210b50180400d046101914641900a1921103000c220200600d8111642c0142c01c2120350803000d04c18000c905c0030001c5440c0c01d0160358020717201c002a480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938967670 1250 938966420 938966459
    0x30a08091204120516030807060c14180108060307080d050c030c0703050a2114031503010501060e130b010203250b0106050d0b0d15020a03060503100e16 67
    0x4a44000c11900842080814451884002915a210750310108814104803c0400b103505004a240f1440b118903006805003c90707800040305c0f072a0070115a00d00b002803958828403030511000c200c44011481141000e444401d480319607aa1034114044000340211100500061096024007414070011402140300135080d000303814403940b10181c24070098218040c8514404441c454a0000000e01200280749030045009811601da8400307000d070b809a000440300950310200b120468070400ea080d01c0002181c1c4210403208445203000c40000117402e60b00d003a8004400142c69103a1a0094500300030040010020718004202480e00400080c0d00c0e03000788a000c4620001042c0307291000d55400c584481100d40c08042e42e0800e40c0c5030b1001030103540183d00b0750f0041515003012686281000020800b1058110f41d00d22190780048017298085e43c41841c0d442c00b0542c492034009450f03201000504401150250003240f25882d0340d09991503c92010a503081d1b8007080d4104101d144503440500d480e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938968920 1250 938967670 938967677
    0x30609151b110c12011b050f030c0f07050a061e02180609060f0a1d190923040614090a11041a1009051003061d04051c02012309030a 58
    0x642d400030025041c04103032200c95400c4500281c400c0f86120066005054591078040021501c5040074811582130040d0724000c0c030b0801c020008209410701c0c4101070035085604100c018900203060782c0c0c00313042a989809c100c4070300d500e40e113200d044000150740f02040740301500e1085041c108140418030b100d0100d445a1401640b00050220f96a100d0108649401c2000c018041d81c8140d0a50003c1c80c444049195068901c4018204c44c0c035403804100d00d4025400300303070081005a09144000700282580030600684038203c51003e12170340e070322031102e922403030085000007400e409e14030016001c40030040000d0740c560080e400f040c1c0014080c00010016110582e4001041061140740034101c4092220603548504414000081161b0102403c026034134240d0300c03101c1500c25480c058040e074916014490000c01d00c2070610308400c61540c1510351203802101118806200c40740e08401e00c4810394030400040c1d4403019480c042107401010407502214109184025140103c202034490013801c2a08080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938970170 1250 938968920 938968937
    0x216020901060e0f0d020409141b04020a0203031b0c01061409011d0708130c1503140601050403030e13060609080115050616020f0907201603151401030609151b 70
    0x6d5440e2a0700c005c1000b030f480701c200842c0138031041a5607551815217608101c80c800c10b051900441c00e2500964504000a8009600356100c1c1c481042841100304d4034902c00450038401c1240c0c88400340900002015201c6044d6810341c00c0c0c0040c4840c1e40d00c1604450021001c0c01c0c8211404041403030b405030300c01d003549070296050f20307020510041c80314110006011080902d40105202d5000e442e1803c100c03159131410491234598444080750103504441c240c2c0410b0050100304082400b0380d4898090203030080906241c07200e11944182102c0094003c000040e0604205010428007403080210050800207c0040f09241000244040c4900001e260149400d400d85a01b15202c03002c4156003c1c00c010404011440d0a031001010540a2111030031803070844240c1c0c205003580441d03001025000c0c1c0210403100da00703540318400c091805a0842240540d03620f5001d0a03501c003c503a40c2d020b50700c41c03031001c20034241070700340486003412042240f00010324000c0300b040141d2005402000882141c03c12807903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938971420 1250 938970170 938970173
    0x3100f1a150a181a09011b0b010611011d010615050403020a140d0c15120501140d240f0c0509010e0f01090810020c240f190216020901060e0f0d 63
    0x1030811a40d13100001c001d030011024041031282c407000c0d0011410030784e5010a080d4000c8080c2c050324031448000341140070b02200601c8094400c100b03214004041c0c000200f0341900d20040010342d00d24040f00c018203139558142c140082034004500c2c800c42142464540d06207800d5800281d0b041629200d0070640a4150030b40c480c2640390b10070020080364005102080140d99018603a4441041103d03550000e0010b58400380d012070548a1581a90006000c031304010313407e90306010104c0394101055440d403e64440c843c407051240c60301c07801403012412000c00d112a07aa00d090341a66000d1440d501840342c03d200600c00c0783d03482500c00040210458004400022000040c0c61401092b0400034150040003c0303884800f0b0030340c00904003040c00c00103d1310040c1c05440c0d00342000300101140003d80c0700383c802141c1000354089135180c000404810300045407100c1100c0004030b0b400f28012100824002e030048040d8030f03220108074010301503410540560307d80070000030800e442c0c3d0308a0500c2402d0b030100560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938972670 1250 938971420 938971457
    0x10c0b01090c030f050901150b0a170a0b090112020a0911030403030b0406051c05070906180c1403072006011406030c0f040b0705010e0102190e03100f1a150a 69
    0x981110140700d0410075414140091800303030008001c0b80b201c10000900004a50345109d01300c80e0711a03115540c1082e040200e2213071810070000680450030054a50107800c1c00c6540c0c214010b802020f9603070044000c661544184048900c03a680000070313841c44e050700c560f03031120254200d0b58002e0b803516001800780038040c0020010001138000712741001d9074050680013007401491102041d406042240c0312142d40790031940595900c0c0c0100340891407403c03140280d40d921078000700344025580c28011030340e050004d841c82d8141c200700c0b10100001c000129941070a81c82a005010f6030351698007400680d81400302200721101e42449050044c0304c000b00085000540000303035600c141880100598440e680c4810b00074a81107800305494951038825030009685052080740d0360039108a00c3c128011140c800251030031581129080e8050095020881c4040200c0c030548140c94050704c00041e59411300c0c411038116034103d01c5000e000d5100b500320030706940c4005094030041d041a01e0b10b408044120325050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938973920 1250 938972670 938972681
    0xf0b01080103230f0d0e0609011b140105040f020f0d0c060c080f030115020708060f1305190804090605030f06040809150424051c0e010b09090615010c0b01090c03 71
    0x4140109000a44e11240110b0055040d03481d50b81c80003000201001040050700c250780c034240c04154035180d00e41034050640303544081d20b40039a42c00c1c03056100c0d4604075030a4900456046a82c030616404030011031800c040c40000c5074600340d0b031904200d000d642d110901c92003540240da00f4025044c0000c0104540801120410b9404618443d100e507035956100b00701441014001000d401084070110308000b00060307031441903480d042942c510b43c48000800d0700c0100030700d806483d98010407442c001c2e541600510050b40074420011103586514110000084aa2035044288242c1013203410741c10000000413a42d8100c0c1c2c01c001c40580c0c9401c050300050240e407250016224202012600051540c020f080d00208000046d11024200342c0140d0121454891119541c1d1410003c00b0042c08551043d408840c82158500002505400107000103480da58119903212103507018900700003035050b50020908041e0401e091034480c860003a510051302e50814011a45401c4d901c4000351100d81c4690080d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938975170 1250 938973920 938973983
    0xc0e100b032d0a0516021c0504210611070510020d0b090a05010e0c0702010c0b0703060b070506060f100525020d03030b0f0a21080d02030f07030f0b01080103 69
    0x50b0941804603691800d001e16088503c85691840e190020710303000c49442e1603500c80055940075000f040340c500b0b401074801001801400800c40d0600022610100280700841000480c200031031a0b0100c615041d02a203400da0070b9024030080c1489100005080000d40d141c0d081d07034030000580c8881d140204880181494540140d22418120500109013400d80c01181610703131003141302c55581d541c0d400c130712307010700c84c4082c000d000820000b45c2e41c2c0441c141600e401c0d00b0a1151030081542a5280080701440c0c00c401000c0d1541c0c0c01103401e01115281100040c8a00d4100341c80c10300b004001908090018002d4810b03014008200c5403144030b02d41060001142060b41c001c2c0781e03140056160070010018410b0303188984c0100c26113103400005140404410f400c0300da40b103540d00e40079050004100091071107107500700c0d5103040901c1882c2d034003080c0340041c0d07100b05100708a00303c052410500050070f51b01c04c0300034410000d1405202200d01e1b40c1c09504641907a400030034854034038030b07009001070b001c200c210b50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938976420 1250 938975170 938975221
    0x90f0609100f02150402060d091a18010b040b0109030b09150a0b040c0c0803160504080d080f0f0103050a060504030e09010e070e0a24021510030c0e100b03 68
    0x3007030341d070580c01c60504080c02c42d03aa42200d8a907a048115044d00c0314040d0342c0070754442000e000105440c074440d00104c1c10144907000507050a80c003d11110303111007040c1d4034100009455800c00051490903c2031504194086509100e00888500080d2200459000c003403c0101107000140b6070707240400c094500c24032090f00c4118549440c0c00360b10010409161340900c504c0c10448039002040c811040c091441c2e400c10401403851711913943c0442c1008080d9005824840b061000141d1040140901c0c7d2701505a0f481d2460140743c110303103907004041c005007220a004c00c2c00005001190000030082d0030640c0c407400000d01d42c3c8075800e0995004002c05a0300354451200e130004182d40941654043c01841a030321907041031114481005000c0d0740f1406806000140c0c410f8000d81d4681c040464070802140c0d0042c1d03540c00f1140d09017405030f40d0080b54650036404040c2c2c010405c10103480c450320300601410320903004c941444002100103520350302c500c1c0319a01010001c1414160900356500c210044500e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938977670 1250 938976420 938976439
    0x30f07030306050a06020d0f0e0a0807120b011e1a12090d09060302073c05060106090609060509240706050406110403050d0c03120c0203131a090f0609 66
    0x140c000d014090b0340c010300707001c3c0c801c100c00015503d00000300d5003004001c0b900d60b80413401c00303e4011500b80c2c405040e803a0340710788081070008200c2028085040a082c0d600d82c0440c1944582c103003e0481e020603481083c0311400c0001e5040f040c64017000c81d5090713a501521510a05030b82d42d2129000e801440908006009a41d05002c0c01000016203006811115202d8410303056403007409400b24010040c014000014481d01d5003907007a000180424203445e00302180040980170b480c0d080a5400101e021112070344804014400c00350094042c0c001031605140c5400020f0504000802ca40100c8242c0340c007a00701c003a821410340d41c408250000b03081003e8606900c0fa141810b000f03015140594056421038685035045030401c168108490944c0d800500414040c4810742044885018a100c140c080088400303820000c00c800c0e002d00014100030340d004548030101090160350082190b480001c0024051007843c040203501000d4a00010040781c15003040022980460311034480c3c8148a9409900d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938978920 1250 938977670 938977673
    0x180f02090604060f030b03030a0504090905030c0a03020709051006092303010c0f0e040e03040e0415020d1e0c020d050906040909050303190c0e04050601030b040606050c010f052502030f07 82
    0x100e00420280c0045ea01030010038403050515803241300d14140f050000c2e104110900844a03290030002400d80700d00202c03460405414a075904089c0121300031401a040408100704501c8c03207000c0d003608217643c0c01242c881030345402409841480ca910458200c00803040300c402184502c032080c40d05484000c1c001303001004074001c0003842140701000d0b560108009844000c52401c003403280b0341c4500b2400f00110714040c180721090800102c000c1007200c10341c005c4012000005403030b0000c0d2001d6585500041864001c1112482030701d20482e481c80503a91801c0e107180c038032907400211400000141d091455903629800041011442150001c280c0f4604000c0e070384041180000046204400850000f02400041120704081d1070035200c02d00002038604240030603a24060b4401c540018050600092401e0744001150944105900c50b4020070404111404001d03002e0081041c0a42032032000c000d06d180249242c07403150b500c6914030190040718420380520b18002c10464803514220709400c2d445600d503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938980170 1250 938978920 938978927
    0x50607090801060807231c0819080f01090e070503240c0f180f100905330703021501090b0a050108070507151509020d0b030601180f0209060406 63
    0x803807140150035807a0010009168401080f400b0544034850240f814440c940c10b04001c5c0944c0c2e1342c0043d944080f080a8202010a5405040f80383d103200f94003064852041c98a107000001c9000790240a02c110181041041a517011805040d00c402a000040c2d0132a4424000d2401505420050301441031100034140c0b420344000710b40f5140c24551070207204c0d81d12561401c0f0b40c0d00458130141c248200900032141c00c9003030501e03480d07591034002d07000c003074480d000d01c00090120074440031040129208180c00d2100d4104901035550214101d2595010307400c1c00010b08000350303a81908a810030304042400c1c420940b0910a109401c415080d40c040d1950f102d4107000c00420102c58120700c52007004000290b00e50103811502e103e00c0c03003030301c6080c1041d4180d00c5180e490706c2169451044940d0300d03851020300e00340905008002c3c0085180050300c0f059005500400c565140018a1080c0d00c000300401941c10740310149a900c0380115004144208880c0f05072019008125000364070860104003c52040d03030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938981420 1250 938980170 938980187
    0x9140a030921080403030e06131e09020310060804021c290c030109051e010f06030608120f070827130b06030a09141b0907030b030a0609050a050607 65
    0x40c5400d81c2c0c1494800000724100300e040042c41403609000800101c1d01030100c141c2a003002400840c030b4000c0d401132105589207240c02c011081141c1040c11410240858010390250941802c11465400c00f0000480711210900c03907001008021000a000c54507644000740c8029a0007510800e07000151410b003203911000c5079000e58041078024605c482081c030319000c600072520082240d255034284480c15001d094028214204074416103130102c940c04099035140c0c000e0074007030704218101d41017100060940307038503902c1501d42d580210640300300321004038100d42c456403442030200d0340d030891351608803242d0061180e507402031803003100d03859508000c20b0398601714464101c03890301085030418030b41000c83d440c0422a82e008541440003441d240340c0750303109407481400ba400000000c0040440035261800030312480349171070025850220b044c248407403442e400251a00301030201c070b0314002c0400d580d282c1c2d40e04090039090301c4019002c14840184031181000750401c1c1524500d14050308040c00005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938982670 1250 938981420 938981429
    0x4031a070203190c0515010801060906080106050f0439120c0c0209090304090e0a032012030a09021f080901090213020d02160c0602150f040609140a0309 67
    0xa1040005100910100c1100e5100d025600304402105040d88201c884600080c411202c0b0700c00d00480701800c030700400702c0c9030003440c1c9280086180b03418920101c0644215034001d81c00c51781800e0092140c0e80c0d40ca01c040300d43c1c400948000841014500849960542255803000d00304d024480751010040d00303000d050444103160319000070f4900200688001c9420507801d0b440007529680c4958018904034800c5078000c0c04440c212802c0c0764640c80030808803200c07040581e441d580002d51984c1050740200e1142e4251004140540148035038441d07203a25510469400001d00f680013001030b000281d95400410b07056005803800340c0c1d1294241c1d903d202504000054400b0802c2c840004110b503005001c0c08929a601922810f0b540c561904010080c1d080140819480c42d020b200b0701d400303804215400316016000e4160000b04502d46034000c1d05141e03400c1c0c144070050a0398030401504060000d003840c0c015900c03c0d03000400d900c40d401c20307062194000d81c06c01c0540c0103000400e000d2651018118090301e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938983920 1250 938982670 938982713
    0x1e010b0a090603062007030c06110a030e0607020102070804090903031d0312010f1a0706021e041a04060503010b07060e030d09140307170a0c02060d0e0606010c02010e0d06110403 78
    0x5000185000310902e1701c083d840c03031081c20419000064403440e40003141d907101d0340000c01d071030041d2a80e0703200300e401c40d9400030000703540c8110004410303100b0030942d034101c2d003a400218503020a03a100d0301400c1c80b560103108020ba071100410402c1500c00d62003a030b12a101c10220401d0b0622594245480354011041c461881d00d0745400801c031041d20031001811107022284181070300d0501c0b00c2440b1540c00185c0165415542801020066071506407040017507640000d00f555030382d04004078002c0004840b408411020000d010900c641a0001c040342d0540740707012519034030391986103031650250041820f022007900003c902015400c0040d0040040c040c851a40c0c0280907600100550362030107100750103000c1000858046c00c40403104001004044460314000310030100d980c0100c0d001e030340a444d885520076a15840007501c11028040103030000f42c2480d010041858580008125a0054407400c0c42080408004810400194405600f10b80000011503c1e5582c2e4144030710300c0c240000b0b0401c01c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938985170 1250 938983920 938983931
    0x1e080109060e0d020114130305070b010f15230d02071505220209220b01061e030b0a05210601080703030e0303030103170d020d0207120e0109081e010b0a09060306 71
    0x54500601846c4a03114080c3c44511a682d94800351381104800e400c815802d200c0c0410903070000c9410040c0d407502070a0648001c01503c0e1610182c0490380c52160b074201d0400c1a0861990080104c0642d107900184940d180eaa4546249415002c000d10811200400609000d40c4038202000141c1155108500250b5111a02125901c0b5150900242c980c000d61148802002840410100082c1d059011503240400c401c011655280c15149400303802070000311b2509210401e103409079046400c410080d501d01801054001008207007102030b1401480d100d55007100404000032403001c2c0d59480003c09030116002942d60b8a00b141c1c650500740030a0340000d80b111007075010b07401c001044034100d035031108404d004c2d2015500b007107409400085414407025000c0007040c0003d21280054900c160091b802c4810300041490007030111500851114140500880108226880494600049040518100040700c4020700792801054040003040d42700300e07038850106042c125a40900240c0e48240c004100c2e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938986420 1250 938985170 938985193
    0x70e030f0706121a0303030a020d0b0a0e0a0c0521011a09060304060b04090c0b222102031504030f03050a05040210030b150c030901271e080109060e 65
    0x11075007414080c400c003154604031250b61054443c0e000e0142010700e480c2031080541c01e0340010b81140c0c0161203e503042a0003084d40e0348035032104d01c181c01d00440c088410b049080d140071151608110014002d80300c60b941c070150b02d05807a02503004c9030014540c860012111891605509021400a0103628541c001c800308503054a0a08001c0359810000100118196a81ca55900d40600308540106402c6520341c5c2400d000200b00002001c05000c0c41c48180c4d84541100103016055001000d04c464a5000741d54100314841240c403c00e030000b81985050846d16035240003080c5060403404441d80803191380f20801080c10343c0001038030b0004c0001d0b602071201b0b80780d6401c00d1003618020b4401030f510100740031300313221120b00a500c9030340c1100700900030405504402d001024075030054100d14070190800078074031401d0b43c1e00c84010b5a000244255032030350b1340c0ca180070200380e00216008801e50300d207003100d1030b001c21018407095a0003456030380000d10005503180f034050058820503240800510520f508a0f4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938987670 1250 938986420 938986423
    0x80a09090f2c0f1204050112060614160c35072c100f0605030c0d020a02030408060a060e0c0a12110f0c010c091d0103080901050909070e030f 62
    0x392402c00c0d018920002140c0120345a040e01c0d00c0c5911118140b00340c918002440380148024040705504814058940389008000f400c50648480d00440c281d00d0042c060111a8101ca1101080c0c410284090785801c600340903100340c1e507040d00713000c1d01010140c0360002d00a046a070203006090102058110102031589c501988282e005225250301c0d00080f40a000b541d0220080c1444501c45140d0740640441243c1c0d046030030328041e01d006a0007a07840000b0b101c00d10207151001c0080c0000d20b020f618509e07125812003070310f0090401145603690000780d424110384c03003002900c0c040c09503a400d43e00c0e1418807031000001000d440c444c180c0300e0680000081c05403031215041d60301c04245500c1c0c5a00080a440748030b0b0050400980c02083c0320818000b800310030002c04003030803001041a000048030640c0711000390043d01150300486a80c5e08401c4815800d4150288260441e640304c024203446450f09001a65a4010202150380206101040140856002011000c0800d058050b541060f40310605103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938988920 1250 938987670 938987681
    0x1509060b0a050406030506010c0f0506060a0815011502010b1008041a01030206090d17040b1b0a0201020a150914030702040e030c0703110f03010e07090e070303090e070c080a09090f 79
    0x100120b00d06100c00c02400d4080d40040781c0c001c005150044001e0020340d502042070f080c46c0b80a4450f68401c1c010000a418501c202c2c1000e0f000d80c40003000152080c3d12400c1012105024589181007a07134045401c4900035042900c03c0340c0000d240032050b0120400040060504850503078844244035141140450b0111245040e01e030064a250300e0500c07c1d0742802529080c3c03400403104140140760104072042d220303020f080548040386805e5912401c038004d000b205029170707440b00c031683c210b21050070050fa000500e41c203410354406200c9080fa0701c00301d103440050021420240c61000d0041c506500c0b800080010722541d44203d804000302c0d401100d01c00c0d6240140120444a0f90006006001140c441c0d000c0c240d910034001c2805082d0721000021a003074a8107010000700c0d0f0307880344109124107a50303070003030308641c0307000800030101c042c0345450040901020740b140000003a2440b000c201d03024800c2c5a02c5011907004035020359543d05a0b81d0080c8402eaa80c0315201c0d33020710b8141c0c00d0240d00128002d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938990170 1250 938988920 938988937
    0x1c180806130606050f0f060c0f010518070504110714070909290f0c070609021e0102060c0720030c04060b13290c100e06160f02120d06091509060b 64
    0x11b02c228a0300c42c03000c0c0940c0f50f01040c0740b00c01c10312074000b281c034242c9024010743d4424402610512003815403c85498600036454226500c03480c02c2020300d40ca51102c50301500c4080d50849030400e86032010070003c40c2048420740141e1107041c10085139009105070034801c3c1403010414141c002214080410310318501406892641c80700d802c400101d800d6402c42806040914003400700000e0f00e100c41e0340002c22194115000b61014640c1440c00251503030144400c83c0e0200c1c2e40f105a41c40d2408580d42d1040c05081103180211643c0d00130354013070707450701c042000405841000d00208580b40d00c9511946064100321f98038200084d2111001c41c2d030036881082e040b02034001d4944291198801890f01501c3e07045404ca0140e50b125410301a100c10300c0b540580809032001201400f4541400038410700b03030104030050f034000e00c40181c100543c807550010b582007040b9018501f058170b4850088135074001e0300c0d0661203201407504000c0c80b452174860626408007218011001040a9035490b9003008450190010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938991420 1250 938990170 938990179
    0x80607020618100207110a0b0c06060d0303181b05010f0c0227011512020703020d0f02030d0903020601080714060a180504020304050d111c180806130606050f 69
    0x10903104070303503403440000c011a07100640e054140d00d02e5400c012600304903002e5401018241006c0d03540d0400c1240d01d0003a00911500320b18103040d10b109140c1d2800085c2c01d15014140400149090501c030741e100d02d01c42500d101c1400740c4002c0c0382c20080401d001d02d6000c0300e0b03ca424241e0010701980101c40100809540740c442c0201c600141c0c0800a1001c048190f01e9900201201100d15801c44d08642c40c0c00b8240c01454619a1103403030344020185906d064049209a104200e501302003900024096254100e03031402554900030311310100d04600518000b400b106003800c0c3d4140070180c000c01c0441c182c89420040b0f42c0a650348820410800d0240305040b60005010080101042e12454004800d580c1d601025403c00b950360b03000c50100da000310780599442d00005800345440380d100c07003c0076070440d1950080045554a0000000b60014204024107016500d06a80011211119100003c0c0518030070b0b160f0343e02d8504408081aa0400022252603140c040302103840d11700b20b0003102c0100300180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938992670 1250 938991420 938991433
    0xc06070905030d0c081603110c030c0a0308094605060f0c03070c06030e1005010b041202030a02060a030c080c0304031707181509080a150b1801140a08060702 69
    0x103c007501c2441e140c102c19182c0c0340040040c1a0985c1c00f18010b0344034a482a40c980080a003caa441414403424202052284e0029888503100342e039150000d20075a50004003c0307503150140e074001803140400c10204441c1002e04203482040190b0044d6a5804006a00b00ca039103810502940c1c8403d1141d0340581548550113015a00c80480f058024042c1d280191089916040d031688881c06c55288a90110340040d07150003200c40521000d00c0200200148001c06100b0740d41441081086405903002d440041c0c0c3c00d07030928009540d410007002d0f10309a00684803039542d441c0c110006014003501c4c4d11140108000801041c05112014100ca10840d0144c3d9100c4030750101d20480d559461000e08a100bc100014a40e12111000110390b80010494548540f80e043c080030405040101994400d05c82034005ca804031000c5144140034820803d215900054000c5003034000411420109404044001c002c90000c01d802182e8007c01016582c112a0580b40c00c2d40e0300c1c0120fa8440b8100e40c400300680050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938993920 1250 938992670 938992693
    0x40501050d0b1314011a190b03070c08030a020c0c01020616080408190f02120903190305121302010305370623040606110d0c1e080c0607090503 63
    0x20007402d42000c0c1ca60594881000d85031156131100000403070500081e59a145541c2d0100600c6081080000054071902842c0003051414200e00100744a0b40034070310300000c001911240308452420f00b460344003480715142e00b01445050004e401001c41c008907841000342c5002c0940c0001001c5119074060030900b81c15007034014048541c0d500c0940216070001c814003408200000b1444000400b00042d40c1d54505079040f400b000b4070340801e010404103144030030040302c0030f5610b001c41d6115641c33007069990243c50007039103021686031040d01000040a0500e0043c40b1804c0c3c1c468082c1c852140c001d980078803454030b802c9482c2c5c140540d21451018001c1c0f004c08542c0315040c140603204041d80c4803035000a41c07155107682e11500c04071441c4220b0310070030380280440f040e13107018441c810107020585010301d07007107100410040da5005a024270505004145010742d00304640c51081d80e64201348028010076407051450448416040206943c445006100001e002580b080001c4012980300038020600751094 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938995170 1250 938993920 938993933
    0x506040f030f021f0e040c0f0212031302270606270102010b0303030108010c11070332010606030204140f060301140307091508060114060706020d2d0b040501050d 71
    0x100e1100f00e1308240fa04580748520103024a80c0881070000d520b944007035901a0041008442003000320780d090244103285400030390ba00256520310601c00c4102c055803515980710306103000c941213000a50215514851003091407a201d62022554001c050003e400e03101c3c4020070045d0301030765400139104c2c01c10144070b83c0300d000740c3c0850110405040c0000181c2e44042d40101c2e096510907001100306a440380e11804d00c040d88032220154440424014154050466440e201e0150200c4440c0254440e42c0b01044051070000700d4002a11038503074000c220003603071b545000c2c010b50802d07c600c06407443d1500c1040b0150a18603040364419400502261960303082440f1001d1902d4000002901032261043c085000074041c031416103152207140c141100c0070716060003036140242c142c002c1c41c000e05101010408607215a400e8400c4c080d408100961590b0746440020010460138201401000d56183c111000c0090304100c55148100c501d424803c0112800510080e40c0382842001c0c1c0003086002c005010805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938996420 1250 938995170 938995193
    0x60306150305060d141c050304050d18090e01060f090b010806130908040308190c0c0308030a020f1209011d060c0306120709020d050a0606050304021e04090503090301060506040f03 79
    0x3e009084482c1c0104d15180c5180510b084c0010200562024082c0e02245d8130065020b080d42c0c80038584681345251a548140d211140a4408130511030803000f142000a1050025000340012000c1045400c441d0400301e40a81110f01c40e58125411000b00410416410301500d820010181c40f42000c0b0b403601024130506680703003440725005503903e120540c0040d80020041000758017031042551203c49480c0340795803000709034600d031091080c6802003500080701e5107013000c1100e810420b1992a85e84030300512002e4840c1c110140025200060b1003c10321403a0054240203082c4000200300d84034403004d516200c4800382d100c0b0466580301c0c00010f410441c00b04004c2d90b124001030215400d08004080081c600130315900030a10b115004104204040c00c903124055121000302c0d4140040340c40d00102a24910000e04064001c000009030b00c071098201c0341c10521003010181c4200420242401c01340d440303800c0030310003501c6942422000149881d04106450030358034041c2805894606d9940c3d41030320b030035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938997670 1250 938996420 938996431
    0x1f020102040803040308190302030610030b1503130b18030d0207060b190303110c01050403062c0a0515070e12010b090f040213110a030b01030b0d0303090c060306150305 74
    0x40d020000401d50800c144042c00007544600d40254a803140e0120350981504010384900426206104205666032003108000c0954168240001c219281201180c01105840102e5000c45800024069102003100041c420240100440d400ca6140c001c54441d200781020404451648140101e0000c03288942c002e10740c8030320800f40010780701020f078042175487c02c54001800140004450800601d0740041c8a4001041040c001d000301c0003241e07001130f20034040c81c00007a15251765607044860094035207014000c07285003c003061114105a51105940b203030138000407141401500700e1650303000c49264100d80100d55036103880c200c040010091106011494424030746079034883d0081610364948849280c0540c1540400380182c2c500307401480101005441c2646410b85003040582412040700d054400501c494a8040b030441c0b0800300480140c4100001c10f03901c031741014205410150103074056480d591213000014800c40e80c0d18010b5007110384d54441d409030f03210205010150300388690b20656000c2d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938998920 1250 938997670 938997673
    0x1a100e01020d2a03030b1905011209021903080a11030301030210080702030d0513060b010809060a380f1906050a090b1303060e1f050907080307060225021f02 69
    0x40c2c0c00d0014258400f00300a00907008030f03958101c020f2040c2081015080709040c0364036821529450a00020f11001c5c03030514081d105599110400c04655840c1302c00060042c80c0b408140c00c082c0c0740e0070084a1584503044581c04185a44901c881e003540c080103403412203030002c08081146804e01d6054440f401c009140400b103000820400c5203880951003814000c0640584000d101c0c5100c0c940341c0212441051481d051248035800c0180710600040c51a6016410a03c04205291280703092000407004d0800169101c4003110428078110002414140160084401d1110b4004000a1100c0300300c203104070300d078110010382c0700b4029280500001d03c0305499503d056a0724540c0c0e540001c2154100c070707c142114040740d40e000c10621103640201c59102c0c0c1c90308049d0001e41c000d400600080900c03420140303203503601c5000056002c907040c4888002424031109880c0d5484c3c4624120009601090181e03d01160840000001d2210891081c0003070b0b0340584680107070800110464200081000c619085 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939000170 1250 938998920 938998967
    0xf0308070f08130e010504020403120e030c0a03050c040b040b0108240d0b060a14030c01120908030f040c060309080a08040c030804060c0c05040e0703030807030207061a100e01020d 79
    0x1d50440300034142040e0f00300300c4081e41d60070280f07140d00c24078040e8001440340340140320a00c007003503014110004103141c0c0d0030030300b030b40c0d03040e00010078141100840e2880c0d0000c6500c10001c00c1c8107020401c0101124100c404110802000041000701d64039008064001548480001e4541040300d042e901443c021410a0800b0485240010381d4601c540408641c03030368201040c0301b0329040950113040a81046081501d12000c1c070008a50b50783c19070f807402410044003e00c4080b0711a000d81c00601c240b50843c1000c0d68926041c90030a414034000d032000c4130b0f500603020740004c5d900d11034880e00310101d41c4070302032070b140c005030803012034410343c02600c1610350342c410180010005003813030020401000c0a440d404100351640c1010700309600c0580c86a4003c0b030600c00681030480c00494404141c1e50b040c00d10461036241c040c3c2c100c000f8014002c0060555140410810003100303c10485403004008030b807400401030400b2011a0382d50920a02c03a805684140440640c42d80285481c0e0003441009806141 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939001420 1250 939000170 939000173
    0x10060203160f0f0807060506040504240e011104080706020f0a0605060f030f1c0c0c1703040801020310090606020115150201020c011a040e0616030f0902130c08100f0308070f 76
    0x2a4001c801c5404c03103540700c000607028100440f50050550041d8200c81c100002c1c581074540c0f03100c0800300d60000c403981c1001d42c04a403012a1551041c4202600300001b04040407902c0f6164115600c03902800542c2d102e4814002141c510018000400a40400140060110b6681c503400a0300c0041d160700d9010b90071601d00c0c86151010420510840f040720010080030359090404106038105031221410003540c5080c1d40e010945810307039131080301c0038140e101c1e140328041d03541581940600d40041e07046500010034041c1c043c0c1c100304040161000300b10200209580e0300e1080e4200c0c0c0960946146044090008011000520104004424030390001601c0c011381240001c1c21a070440c0d040b02c0b1008240e0540c0d410604082c0300d440e00c000d003600300030704e0390b41007408481414081d182c008204050725001c1c2081420743c01d4206042d010340c003419042d02e80c003071203508501900b10145524001400400060f0145800d407a00c413040714018424555801c1c03c0d40c4856049503c48541503407440b445286140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939002670 1250 939001420 939001433
    0x12051b060415060803040b040b1612020309010327020d060b041d191a130b01030308040b0606030705070b10170610060305190c11010c05040e10060203160f 68
    0x103204600c038040300404100c2420105046951542000c03503154824402800081e03041f00886042e240c80e000200e40b40c400058180c140312450900003041c8400c2d81d0103001e110f070780007c043d240003007090702c013805a01441c1c0049201d9444825881c40c1802c504d0f40c0c02000340c20503000d40c0c5c9002e409103c0200b081c2070404042000c2d80c81c0c8000c241d4003001407110410005005001140340c401c00524100c008801c00d072a01c2011600a00c03001030391a034000c0120303a200c4805000341c842a94005c081407200c3d81d5030304010341030440c12107040c3d62400e104800100d0034540141220300c1460161259402d080f481d4640c01c1141c0320052113003001c0030038000049110341c041c0c1e09090845440b80010015850300c41016800c501242d400901803605203070602503d002c0c41074032000419081540010360412003130381240d1079400c80811070748a501e0005410061030f480390060003039584481201d9069110804080c0c4404102e10a0b60010b03002400190718406140070104152400717103280c2c4103060742948a41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939003920 1250 939002670 939002683
    0x6030a12020304180603020d080f070c03030509090907150302070c0e011212090303051e120403050406020f1516090801020a1809150b1b060f04110d12051b 68
    0x6000d607201003000c2202420046413024034001c02007040c0300291843e404222000c2070a10300038501400030510b10501e81c401720960710060b4010b0001c1075010741e01d08000c0c000b940403c0b4110f005060200c001520b0741c00000d4a60111120014141110710007071804500a4004582c200e8100d4160500010109000041c0c0e038041d11128031a00038220b09417508141c0c15400010342001e0040c40b102c104046500305c41600e100e651a40c0140c1071403070031031100c60018801e24008081c2c0443d6003081c0414140d101018106680480d021600742e150b601c0d0405da0b03600c00e520300540c405842d5000140901c4034151264500c0e1074503081c4800e4454540040768260f800c04003045000420418101022581c1180170400400d90b894080110302040340380c0a800f01e21a01502c000b40f0790010700c03050901040308450110b0b51540c0c0c241c40e298102a20042121002075800303880358807018085400300e00c3c02c0500e200420781c1c01030810800c44071425050701c05401040b4030603e40400441121103944091062 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939005170 1250 939003920 939003953
    0x40509090618060c04140609040c0806150c060a0b01030b09011710273e15030a390f090b0702061c02070f0b091902010806030a 56
    0x1401c4546000351140030b400d00c44040d200042e0784443e040c07101d40c0c03043c0c0301190140c1d00c400031503502c5140351b8404280c03584180340c0410f03003251401c0b2407041c1c59030f4001180380c02400308991b0004598180c0004e50514010004022640d07003024012540121196005025a041c1818045180d6880c3c0000411300d50703099100e80044032043d0308a43d03082c0000d200a88800307481038400c1140603800d6102c202c0390b072040450720005190028604052004c2e29007205a14202c0413408160806110712070328918a0194a00c0b102e200c0d09043d00e100b601c0d1642864040d1000c0e01141811a03944600440c0601500450104003181e41624981814601e40c003c15082c50304003100c100c1a98a12070044c03003e11000044420045d14100c140103850601b01141e40403a0100d407010b8940001d000e4502d0750482171000d0404451000880004201030180b00a02d035070302645030608180c0c5d40031881c41d11422007103c014455483c1c44102030040d8001c482c0030790480e0b005011150071042aa90b00d10003a02c0b0001c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939006420 1250 939005170 939005173
    0xb0a0513120b04110910050d060f050901020c1011031906030b04140c010212030a020d0b18071206050306010b0c011b0816230906071502040509090a0c06050f04050909 73
    0x2008148124030304c416a08202c262140d403510710f0724044a0110202e1401481e120740c1454850728240326194001e0704040b03c078170004004074140102500d0003980a0500398641c2c2c040c60300300b542143c1030351244510b000d400c0c03100b152a643e980c4401c094000c8440606210307040d6070303d00220200742044049840740788615013940301c69045d01100c0e882c16482001081c11540007441028000d4803281c140d90700310030302c003001607107460300010a18050711a40c02c1890b0401088285a149c0105114019010340607540300c50304504a40740d04a019150309004003030309a44540010400d00c001500205185d01100000082e0f41c4020172007140d82c852816035410004807084284655031090168010000c0c00070b062060b040a0800c0c6000340d004118903903519a91b001082403281ca4482400711100e1075408800f412040504003101d02c000e4006000741c9010b1450100012040c400004003051001c1d0890095006103161040403105540200a920308203036050100040c26110301018502880e0703400c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939007670 1250 939006420 939006443
    0x11030d050a05090c0f061617070c0f140105131706040b181b061317190503120604063503040621271109010b0a051312 52
    0x40780c80e041e20b20141000c507660b004848041c801d0395803801400c41404054908540b181c0640100c8130200141c0d1102401030001c3d286a400740e00c500300c3c000d0a00d180314030704003035032a41c6404000c1c0c0761000600404c09804080c92940f0364a41c001c00280018510030b9134030f1101070f070700c0d00700c3c0502128031100c40060356840301d02803104010491400c4e0b0381c810140d0580d21480340b8a900e850ba5640384000e09500d040e8450034903811142c40b000d080781c41a0324801850b50309580d036403400030030443c02450301e15103d0261110105041880c4042e803c1c0c1c040e002002142000414980642080d8004c1c258a512039076410001a5441f288482020110114a26100303948100a00023216030000b90700d20040e5001080113102007500b0011300c030407800220351400750649211616030000c5c402001c03070842c05c1aa060030304528103c50f049035503110b0310500d920700c50070342204244060303d0000c0c0140d140f01841404410ba0b42803084000e4110001e2031000e00900643c0e50882541100c0440c00c00c2e00c200c1001c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939008920 1250 939007670 939007681
    0x1e0d032f0d0609150b0702131b020105010f0e0a0f330504142806030c030302211b010921140304030c02120f060c0301051003061a0a11030d05 62
    0x6102d140020035070100309001e0320b200c8181880780415140105002c2810105520055494032012484034000d82e51081200c8111103011224030102d140744000190700b802c0000c180b500324000780104031507174404600c0f043c6d00ca00300184064502020100c40441c2d032260f21180c0309036403d4051400e2a003415003c284644102a46d0412001070f800c4280030302d01384071920b004c01100d42040740d40048800003030108014111114103c2c00f404102442d42e5a0804e50080107112001980b0340403a4404c1c1c007106d40024034041200841781959401800c0701800340010349983d4001c0d5002e01c1c04004000000807100c01560b100c7c60702c6000c0e00d00d09074920304d64020100b115038101030785450300d06203a100241580761a64006101c4850220000d0140c42c5110244545080c01c110002003440b5030310950351036190154804030144c1091281510450070b4600c50904103009200c0c140507078104186145a110102c050010076a000031100c0041003524542c035000504240054101c04000510105203030804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939010170 1250 939008920 939008947
    0x2040501201f051611030702010c030c170315010c0b04060b010203071a062b11040608151611073c08010b040509061b0f0c0c031e0d032f 60
    0x200880007040c45485c2c2282c03c0c003214004240e8046a40c24604603882001e0382c54200c680c204207120040a911100000d00340142001c00514401c3d0b4100002000c000c0d201030045032000407081c3c001c3c0003613454030041000f1a495410813606801d041c01201d140042540d144401d060484802d08901c020f10010b02103245484101400b205402c260f02c44102592f1941420380b1980c4980010600090071045405c40d8480741c000c503005000c05c506403100c494044503211045401120700e400301905110303602c0203042c02b40c2ca1021000300d0703010080880b20704100001c01505803103512460140300403009100b42002e1021105400c00040c141000e1481c81c041400703095480d0300c8651403295007404104522704030001003803644030095454071318180315039242c60007040c030400c9918902850002503030300713003100b002801d540504401c0d41116030300c42014942641040041030008103a4210f81000610386110b900326503214503040d8107103100075644041180c4103240000c51500140c1001c203248600001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939011420 1250 939010170 939010201
    0x212010807180c120908070b010f0f170a050d2a030f03021804020a020c1305070c0f0821040b090f070b0c01021e1c02040501201f05 58
    0x4200404000d03040c0180d41d6030042d556807020515a90b220f00b003901d081d00c56200c4405090a0603001c004084d414108288607511007001510030820310000042d00f80a86441502141d8140d04c10250b000d04048110140d0316050100a8891041c42d800801243c01486645a41030a54072007480c905005c011000e810744072401ca07901c540d4440c802c0540440d412540c40745410405103401650351071040e18071548080c0307400d101504540b01007541008c4c60f03000128134018134402c5800d09480240c25140c4001c3c1c0f0411154000044c6240c841a40050050784035031042512400b1043d080940c94500b1190301c20070160303540c844900600c280301c1030122511a05e500100c544010301030381005010040c0d41c030710840c0301c1d6000060000076000c51080f0207605440703410030050000620b40c10060043d0801c0c0e0000286100c21101c05d03a8220002405442160101c03541a12102c0000108131601520070000344102c01d158014032141c10600f05000e014a6003c0c50185400101401e010400706003450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939012670 1250 939011420 939011429
    0x609080a050c2701080d09330c05030c150f060a0608090109061a10050301030f031d0904030210231303030219030c031808180f060d021201 61
    0x2000606090081a8045809000c000e403d980300d040c5201402c034102d2001256000700724034144100004207203032101083c04a03030942c056035003031260794544030840c401c0410b0388807481210f0015041100c2000700045c592003091500d0600c0d400b48070b05510703681d003568880402008540c1050311028000790b00030026a0b00407002d0300c1c2e103290031303d001008240c842c06540501e2050100107000540345a80940218003140c0d84800300380802c2110152880301d400300ca5090a02c211002c1d0b0410b4600c80c41041580e040360741041210380b10f004c140c0c03019500c1500c028040d05049203400c4400b4919120032040c0c50145100c0d0b40204030104403540c5000858903031020495909620000141c00400c2114016801c64a914248010b014031444e06400a1054911642e020703130000e40c080c00e989030160b002c09001e040c9514288521410541d071404031044003031004000200a00034064000001d284412000c0700182010a43e540230100098013600680229240c030b0341c0010f0724082c0321140704203150050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939013920 1250 939012670 939012673
    0x406031e0b0c0f07060b2107080c032b03060506210c030c0d0b1201090510060b040f0b071401020d0e0c0d0f0b040c030c09062612070f08040f060908 65
    0x50030f0f8803041400f038442c1d0311018003090384030f100356050780c0d882c00c15130500301901108216540c200c104509446010703d21803407449006424070800c690501080c010200400d0311417420b150900d0651490108111424800400d541c07036001081c01c1d02c034500144041001524071480c030010304803410054040007010041921418030500184101940a4550000d280c1c000842c1c082c441002103a96101900740c461090f6092640a4087c8040410034880e075003030b07003002406030313949600d5058540d200794481c2c0f0203e09000c03c8100004a0008082c20550b4820500208810405400f241c02d9810007450394211550703401070030016050400c0780345040c0c401036802441c1d40790340b83c6401c5640c941c8414041d0108480c140014100880303014140c0140d54052054031480f0b80700d1140340020f020f540500140c0540605481808040d207203100d806600c1554002d08100e841d10075546510f400c01402281c4064281c0741010000b0004400740010b481c6486011070860b25086001344080070076804601603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939015170 1250 939013920 939013927
    0x41d061c050d0f0507060c0c0b160c02090c211e130b091903020a0606360e0f0c03160f05270702010504050d090b0301140406031e0b0c 59
    0x700c001c51510702c22120342c2044600c0c680d240c20140c40f680700304a00184402d00e4070000940160b0050340807240b00b4011010107c869441e08801501200c19000100100c3c510107840b0b001480c0c00341000358000d050000c8642800c000c115040303150032a044018180c4001c000c200170204002001f90941030501d80600440340c180b900c4002c5140440d5580540344841020004038020401c00001910340403038100c804003d541810000c2d118110454121882424200000341603d90201d0b0107080d40701d40c2600d4010402e00c1d0040180c888503000044800c0d47d103031440c4130340e1400248190000900d40c00003401c910b8202c82f0803d0300b09200c1d404075884c0c4440c04074060010301c2c8101c486000b56042655041c01c000d0810140300000026081e81e222102c200f002009041070341074000c00e004034854030031580b40c40302d410000e585010309030050200020341840100315402d5043d1481402c0a000703000007403040c3d200d840d43c00200201c0e00c1c90a902012030015002040b441c42c400e15488074950318103505 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939016420 1250 939015170 939015173
    0x3070b030a09050c0d080a081503030d0b040605150403061401150c060902130f0605010509012703052a06040f050103020a090f092306030a17041d061c 66
    0x1098000540068440e40d51540c6240401070100300b20b100140004014031342d041e849103040300d02a40440b00e03940006140c500803400350800d041120350710f408020091402c3c13003441040913006003916501243d009468440014840d11214104008102c409514958071415418090207440d072000620000302900c0380100000480090341142540322860302c00c0d00b010080c10150f0103004d0b0540040d40c00100c048a505a959059128090740c21401d001408010764800041d5080e0090500b0745d40480e0796003030401c2c401c02e113000318640704000110b200d0003026201e4a445141007080604594181e0580e0b2080001040350a8031160524042310814030780b6060104000c1c000303025108150500d90041240175030180211049806014500c0c20448010341d030706c82441c09003101200e00480c0d0038151202101600040094510640019000b8041e49569540741d000344883c070301d201031940900380720109619407131808a90320040980212800307402e00104002d00404082e0180901380c4807444080b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939017670 1250 939016420 939016439
    0x120506010e10093209040c0b03010f0602100e060106051c090f14010b0d0f08090d051c03021809070504080d020303100816031101020c0d060c08010b040e060d0618030206150307 77
    0x44c3c4c0042512200a1500c6500d0304141460340c582000158980200012030039099400c080c00c2194029404c640002d4007001e5640c2c12909641c0050405820880060240c13500600c02055544907000c1c00024503403200d00c81c1e508031130300d00c40c00300c82d03400c4800d00800501000310641503040b500200200040725544000a1145444c040011b2209032884000814810b1940544000c00c00142c04084c41030710514040c0e448ad2904010981d9010242207885c2e4980e00c68429507442404404901e200d000d1840304020315944010045e1b402c00030b04104c013092468040c03080140c40c500a800942d101d00740300c6180b19618546811941d940e503c010164034003807111010240841c8d804c06203d01c8000b1261004071300f0060080f4810381c2250340f48400600300541580960318200d11a51461860303600c807034010120b441144101c042595804000c075085150201312440ca0500c1460009035008041003a0a0b03082c405500960158110758100a844104c006400c1c1000c44200c02811042c2e05101c5880c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939018920 1250 939017670 939017759
    0x108070803120705070506070c20090a020c190c14060906070312150b0408010e070609030303020a0e0405160207090216110303071b170d120506010e1009 67
    0xc442442c82c003c07503001d501420460b0050b6802c00141c0e040b924140760041c14040e0b816008640c81c1030500070713170343c40b107060310001c0144000000d240300c005803190f125040117504500d0178440240900c0142002e003054141803d99030364480e002400100f803038403084d50404980c25100a0041508000300710f02d540e25041204c0403103900d800c102c041007a5481d0103c006180c042d4803001301115071074000c1400450310000c0c00840d01e10000900c4003546590311107440d21030502ca440d004c120048014800030b4000e4002c0d020080c810310b010300b07040400800103030640b00e096444030705545000d10180714071541400624041d005248040d0720f011548070a03403c0e40342c3d00a1003d0f000610044c044d4803959400c2c400c036840d490300320404014001c03e410030001e2810941c440c0e10301c135000400a0041c09080810076144071091506c031888011030510020010302001010075040004131444000190750305a90012a850389945401d445070612a80101030300c010075104401c030000a070703500d000c4900e00b10300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939020170 1250 939018920 939018937
    0x1110412140a110618030f010b041a09190f091a060102010921020c1504060813050a060209041508061012020f120319020a020a0929150d02120108070803 67
    0x1020b644e020881c413900d0035410551796641d414003c2c4032100161100540044102c1e10040390104020880d032101003100041ea0503926404c0680400000c0f01c1c041c0c400c0c01c1407044041c1180214400c102d2000701c604590104000b200c581c0301a01d001150024140c0702680d1100080c00200561403080d26200104080080817085480f0200c1d1900d4a4070f201340020750f4100c8014002000321000045010390390b4016000384000203107a240044e4034503409840e56002160004003810160300c107611604040d602140c0ca01f80c02680b03412020401c5036016140d0401020243d01800741420000fa0303081d088107540e400110441c1442041c00003603275410040e801042d030115109200d08188640880c1903010780740841001d030704601c0754840e80d03a0300490701600755442210003944007600c0782c000008540441c1019080c2c50ba24440304001c1840800f155204220000e0000c0c1c11440202c04641040e070040201024080d000f0485a800c2511100c40a000d4035060b400781c0280e5040c0303c0d109a0324080c3c0d001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939021420 1250 939020170 939020179
    0x70b0403121125030b0f01031e031d04060e18060c070302100507140c010509100e0c040c050f0d140709051509131a130b0d0b04020301110412140a11 65
    0x14010f444020403401500455001141880b9031030501c00c440548074003403000341c43ca2815815a8522110070380814130744994140c81d440189000f0012003486004491002a009a510200030500d600c00030101840703a21340c540c0800075201200459420003201829001222005110610000c0d40108501c0e022014000000500c3da031402000c0b1103c41000b4101c0380480000281e5544011043d080648034004010446503400c0305a0b040400b1036154920500c802c1c0c000c020036032034a1500360042380b0018113500d4441d050025020a480e116031000c0c0c051800c0c1562801d1070000e62241c071240944c00802420004c01c1545010042424000d84050606240c1c00c00505121580c0da981c071100319161031040200550240c0300d00c0c411840d051a44000d105080b100c100c1c0100d48094000c0c8a01c10744082d0955204200340d541e1030dc20a10040c5c030803640340d52540300e000300000034040600000c01f000c802d510980c080340e003040c0700d162050300203810183c0c000d81105404141c1140d00d210f010082905d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939022670 1250 939021420 939021463
    0x12020714090406020f0a09060801060203030c0711040623030c060a0903260703090521031617130302150310050603040f020d03030609060f181d070b04031211 69
    0x80c000000f41306580003e0700b01175000c1561a50180e0000b885403d0b121903031204100c3d641c031020143d0f036a001c2201d00002c3c48408002a400103020a038085204c07150141c000700c0d0450b01d07444080c008040191000040c2150030150099a10701045900e505190a0303406519140007090001c291409900001d40000e402c0d00040d8102a00502840c40c0210000342d0551038a815180c01003d100c3c0c00d11503184248412801000340b829040c0c1241940096800254a0403060120074052000d1025040d11140c0c00303200c441c5151400c60009006483c0480c440d03101d85821031042140b4040c80350030042e2001000e00030040d01d0201d420880050710b808580c0c0c02d0f00c80ea1750b86056600d0380d06000000b0340203400c005840003015055009802500c3c0800c1c0c081c02000c0d120008000241d0a078841d443c1c3c54015554801e0102c42180c1c0702000011003002101482180d80b1301840c50202d031607114803442e0400060401c140140b00030650300744000c91034846c030341140380f03900f1039650079450b05803000140341074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939023920 1250 939022670 939022673
    0x521121b161b240f1e1809051302090a02040e090102030403032d09150e16080a02130903090e010e1603020712110f0d030f0b040e030417100513120207140904 69
    0x100d9036000704c0040000d104540f5100b94800528002c0d0500e00300031001c6c2d101001080d090001d001e41c6200301c21000011251469940030004000c81c060034050311503508100202d0041201016503205040341000903aa80c04e05160050807650030f495812050a030106044d208030380603c0c80c8185000d5414004902d044441c201841c9803c040301000d45601d103000d0b100084501d01144074800380e90b9441c0360040265860700c801c2e40b0b030fa000f0344000b03500414410044181c1100c0382e0181a44601a01d8400e0f0501d41310480c03800c03000310030303000740018610b0001000401b00709002009c02d10342480c41c041d4100b4103a56100c40003a84044816003e000140f0550203404074104104160701d075040d401c5448030025001c01800800c408102c003200e850403c8034903000707410180079003506110f442004524043c5071103514103250820340c522100c140241440c21480031020b0040034022461803804040c40b801c0781c075100b00ea2001070303e040800d40d0001c1c03004004050700341118a820f51780c103903800140790f03856 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939025170 1250 939023920 939023927
    0x1b050d2006091008070e010206100e0c0921010f0b0603040206030a090c17060603120a0f090305070e150a060906050c010b030a0521121b161b240f 64
    0x1102e145640218010291258240d402a0030380c1c001d02c0350b030701c07500301580001c401262126801c691804030701c19800d000300030020708494144ea02440d25200300e030500709451b000500d26040c1c1188507200281c2034402820119080c03103080714684410008120300c0304504041410360000400181c0b040b440171000a00385446078029020056001500c03903030050312401030315816100080b031998a03225210005000742400a6407900d21080c03c484941807403004d85040b0343c000c0b51158420100101c504000001520810002020f0b09800980511a15040e1001413142401300440d9104480080c1c04100881d00100382e10160707511450225500c00f0080041800f4052030341c98079405114100070002401804038108015000000c0da184403056941c10f000424001c15020880399000140030500d01500310380348107608414444105e052009110202d0310000312404284c810001c1600d0340351000f0080030010004c4c0665124401c07015806100b03920540c2e02c1c26007401d085c040c10341621810b8a01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939026420 1250 939025170 939025177
    0x6210f0b040201170c0a02071a0d0e0a050a080415050a140904180f0501050f0f011509090c0f0e0d15090c081009050118052a0d1b050d2006 61
    0x500360307445485170401000310b1079a944003808080060041c0c11020030b0ba080c1c0221201170b2043c084c51074600b840c2d010302d1a00010000b19901601c58804c0108580020b801400f00341e0600740103c018940f01c0786804070011840e0f00300d4a03034800300a02000203003c0680c1181406894100e4100429180c0158101107030086c01400404001441c0d500b88101c200318508002d100d8043c4150001e0045884860a0141d100419540200c1c1c0301e208600502c81c00c16921109140c403400ca142c4641e02030b9481102e0411a102c9042160004080c422054020794011840ba40c100d01c058982016100c80c980711040005003030691400700c4e0b92502d10076014400c40d8075094020b00443d1056500382c2c07408001100041c012080200c4195003007401c180e851403c007086010b031040c6c1102c040c0810580c095140204540c105034400907030f0201d92140070058886280c45030255203d0b0340c9020801310700c05180e040590041c0d12052144150660000004155450480c11080c41c04400d00d071a20b02c00300021130500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939027670 1250 939026420 939026447
    0x50306181f0203160507020d080702010215091e0714060310030c0e0106121a06030915010803040306060b0915160206030a050103021f0f0e19060306210f0b040201 71
    0xc01c070090851071038860340d000b54003400300384140d880003400103e0b080d11107015500303000c2d6000d0599468080460300180082c0216072052041d41d101c210303482580001c421090741c2144c061380c02400310000c04440308030002c000800e03900003440280e15080380c090441c42844400f9009a80100109415002800c450400b846e44890003031480c5031a00001d0342c0d00c0380700b4800c220010381e1203211600f112800d40708814184082a003507030180b143e43c100340b008950020300802041e00c9540020341c05915a032154a02038544100650340c1d90b8035609003c8144e62064101c1001d82c20b0411103915940e2311603000c1385080c060310204640b606480d0640000c1c1004160002c2c0d003004d000400c00407030082036072160f030603648219107036108500065100b0b154012460100070110703da00601d806810b000c3c1c860340448075002405000d030a04080807603031b14040c4a40c0000042a01d4450622907400950840e001d483c668001e5030034040034941310507000c0400c0000c003602d444034400105007503901c5440341c4260b44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939028776 1106 939027670 939027703
    0x1a071121030121051c0e010302120f04020105130620010c0c14010902040f02070c120c030312021b0c090a060f1a161a1005030618 57
    0x3600e070709040500c4140f61040c00c20000d84100b0480c070002c5811001c400e4046a00040609490040b83c40b980c1414014000810110f0440102a90014021615184940350f80c0010380d8244a07003600a0180110003502141381500b00110766990104000b00017009410409850b08071641000c200c0c1c00515558509008540106240045c005200d40001781e005040c3c0d00190807a0300c040d105260352031300400d00b113080c0104c0c40e030443c004155880c85000644120341e50280740358500d00008050220a14050f20004034960650b00c41025039210040311803031902d54a940c1300c06942001d031044642d580041c001e1819402034008407499500c1c041d03011800c124031282503030f011490400d1090401e0281c190302100062440c2d130b13010b0080100a207440840c03440d089141100070101c0000280c40c10302000f150300d000500075404108c6001a02200321845082814103050000d8052803 = true := by decide +kernel

theorem cover : BRFrame.Cov 938848920 939028776 := by
  have h0 := BRFrame.cov_init 938848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 938848920 ≤ n) (h2 : n < 939028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
