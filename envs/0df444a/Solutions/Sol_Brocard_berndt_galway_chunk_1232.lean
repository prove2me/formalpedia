-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:53:50.564548+00:00
-- url     : https://prove2.me/submissions/a157ba2e-dac1-4979-b818-067c50709241

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221402877 ≤ n < 221582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221404127 1250 221402877 221402887
    0x513020306070809010c0305040b1f0810091e202103040303033c090f050c132a030e03040320040c0f0c0510060810060e040c1208 57
    0xa103081c40520301c5003a01d611105500e10f00f4605182c01e41d2540c1410400301403030301d8100400110807500240e0800c5005c0c0500303600032400d22402e214620b650f000a0201c1c440c0380b042282c680c0c3d0300c2e080500b21500c1344000c0c40020b10204500c0032a540c0440b401000001643e0442c82c1b46101c18507065943c4d40c00800f90460103550031701c1822403038210700e203400c03003900002028410b154050040d0303065110720300050064900d422540181001e44183c804600384041055400c110481d6049100b04a0b00240c0e4228000d5040c54201d60b26a98102c0340c0f401841d01c8102202d402c0224071400501400c080210201d4035415480c107401851701c48502400d042e41c03100101100c4000f08041c00246220f00b52a40324090907410300e6203665032516101d4402d5041803998a40998441043c901c1d201007800c01c40c04038012490443e04002034400050556890318ac40040ca01d2400100b0100c5a091800d0401006440704a07512552400701d502400f42c02d02c00804100c200c00c1d810f01810342501640b210781c141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221405377 1250 221404127 221404129
    0xe091e030f0409061d0408160c03120201020703080916060302090613080307141902090415020a0e0f040207030509060f1603080601080603070302010e130e01020d020c1203010612051302 81
    0xc1d0300103401c1041070035540c15081c0917031484e1001d041030b181502c0c14801150b1a140d615016584940050344005401c10019081084410f01072000a9a440b0175611100360b00d03418024000d420001c010b50024000501241032010301040c5039a402c600341351601d114030b080c01300550295108801e12500140704210401d545040b40101300d000e44078400156644600341c0c1000b8490401c0812694441d421558540d041486201c4110b02136682c1a2524400c980d25410f000d8040c20443c4221100c03103000046030f074420340d072011000141c1a4100d9115002c546080117000407401000d03401004150208020700052500300080e00314450180d15880c5410140d540300d82091880240442c0440c1a00040c01030a40e004003000d54410b20681c01881114a035800007403c0548107115240541e403140c0c036500340d200e29070300001405d00f6520025560703801801041d01c005d51149080310702c28007868052a9150b9601c0c4201ea04131101c950710200015400a0204001d00c40039021a654030380c1b9440c00c2c401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221406627 1250 221405377 221405407
    0x5040e030c070b0a020f030f031501030b1002030405120f03030c13030804030302070504050f0f04080a03140f06010f170601300c03060b0705030f0c0c03120409060e091e03 75
    0x604008440940c031484c42d80c0029141034118000740c6226003007400f6501c1445407c0080e6a403003c00341c80b0081a03050b520f00140c00400300101d1098001c0109419000c905800000400807600280e400c40380b20381c3c4403400d0780d07120b4001d44010f08090700b00f0404036110300a00d801402d029209140a000a035960350f442c400b2941c42a881200580c002150400507031901c2c2c840c3d1640541c010080000c02d1a00c4116075241c60030040008100e0300d0013183c00b5101911076400854540540c0740c0102660811071152000003600310350103400682d07081c03181c8050606c42d0603c2c1805014104042c0b105448210064541c594818042d0b410842000d580d4020110300c1840f014030000d60b4800025042c2440c48010305071040740d08141c0070080304001500c0012400811110200f00e0b060490740c50389800204c1508146181030b1540d418403407254100301320b25080d0020310413100440400c00c40150303a11500d681c010411150810b10b50010383c92980030722110303d0250f01707203c16003003a2403801c0c50b2881180e00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221407877 1250 221406627 221406629
    0xc0207050d03110106050f010507030f140d0213140117130c06080f1006050d0b0d020303030117010c0c02010f2d020321011a0f0405090a0218040b060405040e030c07 72
    0x800110008070f29901000b00f8400d0314050a020b40710520250154800a080d0f4450500000c04203c2d840b5610160188030307510303400074140340000c45070303450340c003121400080d420180c0f0b1b490307940c048110009140003c5c81a618058401a11800b0803601581c07c1900b814030018038042070300381c41d8041c0708005400155001c020300001c0c0c45041c3d85041107403143c01c4da050000c03c90110780000350b000f40101d43d040070945e031001014441c04580b98240001085581c41c904000a4040c84040000b00c1e2000300500502d0201041d00004c11091100316803c641f124682107000e400704081100701c16142d0320401000407449a00307142842c24100f510a617410141c0c0e241380010058101150003001104912004210340444402d802e603e5410909403c040300705d0030146d180c0a2100040d580075441281c2c06450050200030486440b0b4601255004085e611030100c1010b0a83e801d408a500c0b4500340c461414400006010f60b81418200414800108050044030410f44410f020701c54401c003003005900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221409127 1250 221407877 221407883
    0x1315050408030a03050906060a030201090b090102030c03070b011811030601030911210d08040c0608070903330915020c01060515091215040320100912090b030a0c0207050d 75
    0x82e051a05006c07103424900c002d8422485507031560070420242c0e07840346020007503400d40f0440c19a40c030081d0780143d1441c030501801c2081070001103040001e10190012160483c1c0a055100c41800780032071001c070890b51540c0c0c2002103640c0c288041802540710b030340480d004a1141d0103903045030910f0301c0000e481d004e034a01100212140106075454030407040c024910140d4503821711000d10b0501d541e5400c3c07030003480e0189c00f042160007000102c3e0244121101802107800502001c10600d501180d4048038032a2082c903100c103582070040840801952103004043d5800828400205100c140500003a50108541952a640312500860142d480604030010f0482c60700015684500150a1000d0a0b1040b10a0100c030f412640300c0404078081d08031055409980352810a000c0c1c183c101040000b4060408089640d124840040446240390ba0204410900405811640e420388840032079848040707000d00764042609102044513040c103a001122700100724010303600416280c038003042c8940c0484000f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221410377 1250 221409127 221409131
    0x1302120706140703120c0507080406050d0b060c031812010f0603120207030b1503030d0c02010f0e06010b040303120612210206060105040b031915060e061315050408030a03 75
    0x10029103030000c0d000030001c03011280e41e41c00d0403c41d0b20081c0c5411501140b40207170036165107481c1d9506220750200e41143d9405481152100e84880d00108590030413003007503c4185c81d100a01d809072808000342d1700c003048c40400446c40c03d130022414030040c01070040d00d41c7d00b01c23130602d031401c100b080d080c00f486601c501900c40000346a403550822100c544400d01c03807181075400004003800403910010100b684080b03010036101003401070f000481c2c40e40c442c068402a00c185496100300d41c481e0306402c10000e002480c002031114050300045182c9918080c41682c0082000b0042000002d004040a035011400c85600007031807039403104d01c25000003954408441145501c0c5d0600c000f4441402005405449840101402e01d018000a085c0c0c0c4a50700071144440e00220010b60300302e00e415000d0810020110003840800302c9110201c044454900170280803c1c04840d0b82e46403401c103d400d6481c2c0c4546884c014600710b14202c00700240042441994081000401001c40c80301c004000524103421070741d0300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221411627 1250 221410377 221410379
    0xa020102090a1a16031206030308040b0714030a090812090102030f01080a0305090603130507081006091a041e020703050403020f030d021f0e12070317090d0813021207 73
    0xc0240c0704405030402121186002c5807001c0003907149041e1132000d00c10340842100710200d8202940d003c0d510b183c8624205017040c00200c02c01d58007034100b0340a6440f480000400703403a6240d003039513100840d0030f03034004400c400e00000d6048690754001d01946070007516880d01e401c034444240c0c0071910701120000707010781d00081400511000c4180c0c2c207004045a50103000300006940c0c1c02400c0d4815420040e2242c08044040384424429640000019a000c1c080b100d0082e42d0700216629280070f5031003000d280d4680314000078008aa4000e0486018280501400c44960340c41004000c058440c61940c40300e052401e407188007021407009100b018040e40390251198a184108404151250949402900070480800b80d5503000202003254110f10601c0c0d40c001c00504000c00014881c1c110401028491180a0503065010b44003d1010900a644071300028081004690f84004141d178111020762200781c94400c881d00c0761040300d410120140c0041c29084880c1c00041201560249081d101d030803200b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221412877 1250 221411627 221411629
    0x8160e010e061216270302040b040608010509010b040506060721020f1603200d14030d0609020d05090d120e070905010303050a1205060a0311130207050303090601140a060f03110a02010209 82
    0x20030070003180080003a4207a1900170b81d5007001d00952100a000e2a1161040c003451303034454000002a0000000811180ca040c000150282402c08010b5000b28034001c0865114205070040318962034108005824000c161000f124541070112101c1d1f0071030094200c400038112090101c13a0503064640c030340c509001c1c00c50406100e00c580c900c8200c4000d1201c0d070709000d0291030b1032480d40c030200e4022800c4c2c50000c0d500940c260452140c4640c03030031401c0c6840e00201d460001a0302414001d000403500700025510313140c189603207000c0e0204031800b0178000301065a60b51345c00d4000d401d4001600003030701c5100d40d550803100c06449027a0002c07004030704085008420650b100711600148010744406101600306400880c0c041281c600000d440c8801c2544c0b00e4a141c0c45000c00400000d88610085541e40000d04000d6203e0300256500d131064043c0c600002200510200c250b68003c2c4014141007249142c52415141d00012048040034161a0044414092604006440001840c0d000940c0d6031422030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221414127 1250 221412877 221412887
    0x10e0405071d0a0207030c0203010204080d08060301060521070518010303020d0305010605090d0512030a06030210030519020d180303061701050c0d0b030312090d08160e010e061216 79
    0xd040000d4012a82d01407400c034a107a0302105803c03101c103c50040ea03d141d1403c003200d1003a1340c3d440294140d80001800501e8100000e00d6040710f8544d65a1814540c40e41010035081e52207500c209544071403d0100214145030100c01e0340004000f0000303da03e050790b1000411242c41c1e80c802545680449900100185501489401c038107030780d42d03c6d08020b5981071150181803400303070a402c3d42c0140300c0c00a00b0000c100d007c004064454602003602c40d12860552008405440c0a000890240b946016000e03040c0b0300034000c1e14080d4101c150340e8502e402c81e160800c0001d40100840201041d00c03110342c003404d40800c61115070194041e0f50085040350400c0691159000340c2000c1c0c44040e0b00d40010864007461440984610240e131000101f94912560000380c558020425400708008241003485610000080c2118103218242c072482d400e80c0c0c49500180381c1c9001c00c61018045410030a03021002d620640180b060b6440c000d01c26400d2400d40011045c06541c210b454100c054208002e803040e8139040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221415377 1250 221414127 221414129
    0xb0115030e0d300605090a09020109030308070302040b13080f07031212090210181a03040f0503090603100617071b061b030e010b0604030c0315021902030304020a0e06060909041109010e040507 84
    0x60400303004230b98103513000070300c1071802d4030014007048040c00104600751b200c3d030110740080054003905a02c408119040340c00d001540d200b06c03402481220030004c4401804180b02003200d402c51f14a00c0340d9407840c2400d071103072044c110b26402115075030f1f400b03600140c1d40e241c200c80340f00710320396118101040c1c4081d814202c140b194000403941540d104001100702c04420131241d119900450b503d4042d070691801a00e1802002202540042c0200812503100c100f05e021004545050f95080b000c500b44004034100d0075000d0b45c0c0100003e004032200020041071504000c40b66104440006800d0315860f040142c00b80000c0c2c90400103a00e42900c0e03820142c00b400740200b0860121400341c589490b594540b08254158071005103500040c0d081d40d40d11000f1681554501c50740c2c0194240c4241c0c2d0110001d40340e500407070303049202c3c0c007070000c0118040d1206003400744101409010540b0b020402c1c3e040108014006204a6090310507080826050b12000c42d164001d00e00300b50000d00d1803c00d4a000c81c03d00101e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221416627 1250 221415377 221415391
    0x1303020d0b15040209060706020918040b0405010c091406090f0a09020c010506101709011e02030f250c05120c010b0901120b040210110a0b0115030e0d30060509 70
    0x18441170080d6914141200c4025500803001650b4808407030118400d070080407038203140d401c1a10b0030402400f03000c854191140b0702c03a00080140d404010016a420361040c001c031a6a40e280d21002203250401c00c0050101a500412110170034019074000f0b4188072807500500c611503004a003c4140300024069140c0212003210309107890038410030010307c0c44420601e03420001d42d00a0102d041d116080d4040340000410780e00c425280380d02c000581010b54000d4507100c1e118a449000100410459500c0308020b99203025078445140d1001c4003229918603042040c1d0b000e0260901462641e8905001050003101900010441c038603007500b00300d0100c105034000b17510881400c1d0200000f510001510340d0180d0b0482c0d98000d0140b410604848105010115260a05c0f90420300d40c00e00c42000c10840c120313042100b0010b00d040751440100e055800b504660750103503000f50000c003081800b071210707030b5034002c6286207803408031a800740311603000b80360039100c41450f56071494144120700741414540da000c58 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221417877 1250 221416627 221416631
    0x7060501091e05040b07050f04030804080a021c051c050f030405070f050307030305040510110d08160c02061902210301060207060c0503030402010f0e0607060b03160e010b1303020d0b1504 82
    0xa00b17138541c4981c209004000ca0204000060840740032400c80701510003454121a0440c2c40d10307254281c8075920b03109224180d1240c008184840114006400c07041d0049a1003000362429594440800c18050846000b01c0280f01c0d0034003e14003894140b0001d903204174002e6000301a081e1400c034040225003501d4224501a0308070000901c040383c1c12200300c40844505031402004884081c104a80b420080030b81c100c0366000d550003c042c4264426a403d003e200c642c50455008441004140c6da54404100c00941206c01404084407480f181a440c4d200d1988500550f00251742c90414070320096010407502020147c0440184140340e4100125006402d890400036074a101703a49a041d501d0000800081c10800720180031006148192855036100350054949911040d1038034040014096040d0b840d400b134400c20b03003d0140340b544960b2000031a154035403103a08607400c00350903108070381c008036000d44401ca55680020040e1141e90303803000e659019503040c160394180a224140ca021803042c0300e45c032a83c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221419127 1250 221417877 221417881
    0x100501020316020409240506040b100302090a0b130f080109200a03060501091a060304120f1e030204090e070602191a01120b0c160809010507060501091e05 68
    0x80d800004407040c1408040b81c02c03200544a100040150107030b03120062042031600c84824011210700682210300140350700c103001c182c0da4a410300040307401c00b9041561052500c40188c0140f4025401440262030180071000e545465800c1c6044540c01283c1c10b83c12a6400ca04c2040160302c0303c05c1750b401030512407009220090007911001c4c440304110700807207469880950004001d60721700e03202c80c00943c0d100c0400d101e07641c1d481c0c034980024112044070300201140052502400d04e08101101c2c0324562000b40b40410740e5680400f260b204280000c24024840503000412800c0d040d0140b0080c040c80540d400b680e0b80303045c0640380381628101001044030741e04c908004d104c03068000c02c9002e0740c0402d11380d905107001c10178100621041c0d0b541070070b524200714080c004501200e03010500421140100b40302c1a20752035110a41302e1601c1544d000740d21804503007003406c0c00100d0391402004081414500681008810f490300d6044500aa10681c007880c0c0c0d9512002e007a5110104917a040700d01c4480401480c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221420377 1250 221419127 221419129
    0xd0306050904080c0f0d020c01030e0a0b0109020901050f07060501030c0b09130e07050a0b0304171201030f03120f06050f0402180405040f140102120c071101030902011116030b1005 79
    0x854800740000301003803c04030329022110000c204440d41c0c07031802c2088a00c2e0002091000e91502c1c0c2840400c0d000038208003180c010300ba0006101130944e5800302500c0c40980c60426004001c1d08030f014401c0c10080708004040c59141104d0107000224061440001c080d45903160640501d141988a649082d1003800b40c0102035558a12000515070a086c011410100c8220b1f56410640c6c00d0308041c1d03021418080c04161580c0603009103100760b20940c80380c040303240d0070003c0081901481d80d4400740f807542d020041c40080c6020500d000721611074100300c505d248a0340030300e00c2690031804081410980e80c441c108514900401000e003020f0058400718070f0050304007082c202036003017543c026000d103840b000805c1c100400100500340a540140e036160605808900480c041d6000042881c500a000342c007184801032480b0840e810940d000d40c011403003005400054020b44000f490076418081241d0590411000030b200c424a108000002000998110320340301c203084002409565400c1c540a03024481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221421627 1250 221420377 221420389
    0x117150f0103062711040b0c07091515090e150f01082202060c0a0b1005030705011d010c06020a02010c181202131e0b0f040504050304090e01090609050a050d030605 72
    0x2880511002e002081d000089241000c0c5c069030348001c00b030305000600061100103c01c040c080c181034010554201596590340041a648031300ca0744c280103e10617208010701c030010340c1c0355405404581004020b241d580e01c10002c805000721401c24030390501482070303100d03441c0c007100303e00e40d00e00c0c01d00f0141c4a6080810059018002886078540440c03e280c1003103080d5a244130a89800141d510121001c4e10542c0c80c10200506007070f01ea0250340410440f0106c3c4500e07001c180b4005032203043e920000c1100d508141800150901601d00b41032000c4c0c0804000407581d113000a2040303080d2500040313540780d90a58020071040d08520b410042000c0300a003804038000f04c08140d44244d804850540406a8120440e001860803880031611081e144a600000c903041c0d8200c8100300204890314510341031b8082c00d0109a6500300d500400d29003040100748107102940d80141503152028000041c80e8407207684580840e80c2c500c40a407580d510a07000c3c04c0411108020f801707102c002a2034207200d55490000807401e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221422877 1250 221421627 221421659
    0x10b0102060c03130f0f030e010f0c12050904090c0303020d090506090a0512031303050106140108040b01050103020d0207080c0604020910030b070c06090b070e010206010f0b0f090117150f010306 85
    0x5491013080408809000326101c040c103c1c0c41d0410b41010111a281c075001d0000c0b07081510045c0820100d1418007162406018540c14482c1c00c081c100c0d50655070300030103c945911410302d00340d025507030312019804581c1d82e0b42454080c6201e1b40040600608444003c1d00072441c2e0352100784500010001c082264451501d0a002c80b1025030341480c0d1030000c4a103403401c40c040e000c03059041d4011040b000041c4041500208200c0d1500035100b010300204c40011104040100c4000d82601130400040045501c00d9004044405e008080103090400c551f40b41200e90b40203e0818030350354050002c2c40305510705a80226006480301c6064481e1900d1aaa050318048008240000b84503207004800140030003034000d0717401c0f942e20494160741407818030009030890f080080180d0062040c10004983c0204600610064410004240d801c0c4030300400d04210075800340301a54104503032401da10b109a602d40b070041c1d00514000001080f80d0403050240803200c2041c0406034105801c0420030004466107030b80170743d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221424127 1250 221422877 221422891
    0x70b092a06070614100e01061b1b050a060e040501080a0213090618060c0f02010b1e0402040e070c211409030a14030d180b0f180717010b0102060c03 65
    0x1e440e01100c0c1400f01c02000511181c00e10400d99104024094808410480950310400c4a40304141d032104021551064000414000301e405150b00a000c0751b40c544100740c4645101540b1440141c945020805070303222540b090002c5001004240814030309406501c2c090b14556009109481058000900795100c001d07002102c0795690400e1014000140c20240040d002840748050304d00701464840c004095001d001ca001490302e40700e0490440c4103000d00005220010310591040309040700c03405007040c0d158000c0d80d20941c2040000b07851022040390510506103900c030014501141d05051840300381d5010540100e074882004607000a4100c4c0c8000b1513080305000250311020045e0104c1d24007140d07000094480c0b4200b240e06015588000003c0240390480001800860740070700e88180700c42c031540002000008020000b071030b8404111196584003224200c1081c20303050f0402d0711800c100c036a4200300308500300320078111003c074424020100c100800f0710003001c1030300e03207005084418040a0405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221425377 1250 221424127 221424139
    0xe0f06040f0b150301090f05010506041535071d0c03010b0304060b04090b0105040f110906131208091503060a0303030c020a05011805011b12050615070b092a 69
    0x3c20300030300c200161055001c1c000340c0200800061420712004441001000300da1039801d110002c0d946040034020000b001d00d8141c00c01d00224101240a9a00c203a030400000c4094428107280c082044860510f44800c2e0f08040a06016410141c030b1170034814070081c1074502400702c40140b24000040c00300b2a411541841d80f01900c1c0d480e10700d882c0d000360140c004200d50290034038613407401380308941d69040d0403034408840402c101549044c91800f61040f403440c0c4c0c10740314001d0190302824280400148088452104d0f5042c0c601c4d1038101d442e00b061207000b0269189100031030b5029250401403981074200d003580701014190310b404c0c0000380d00c0e800203001c000c0c200b644809508105c070b402000012074256021000388261004c0c1b80a04022280d03071030041c0d91960800b8162200300c0010302c00001c2c202d010b941c400c0c242e603600b904041c01518001d0002034000520b844140b003c00c01c490084d15030584100c95002490801d101030341d14203400e08040c10750402604040c1d030a03d19203001c451550300410f48603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221426627 1250 221425377 221425381
    0x60f040b010e130609210306061d0117010e070806040b0306043806040f0207050312060d0c0608061e011b171c1407052710030e0f06040f0b 61
    0x44194000010f0744010015814480b441080011032040b501964600704aa05800da00c41c0c1411410380325075100d100c0200308150580f150b2181101c15203600500d040c1400880c0030b036611104c94860340241c1c8000c81400c40394003031090781b951280040d074014400721814001e01b4030071000261503441c05080100100ba1103110340560351140d603c004522607035901107607140c8518100207021140c04441980c8164640006040c9410462099075180d542090040d03090100d8148400c0c5840405814607511032070440c100c600003510000d0240107040c5c907a44403e5181080c800384080e41000b00f0300010742ca6100c04030711034507036848040340c814540c400011500d240740a061501450204032412403d10b00c1c0090030800010840c025010070700c00c0c01c00e003004072002d03011152000e20401e0350200d00088040100c115400782481b41c0e8401e402070f0151074032008040c0800290b0b84d20201d084040030a0b02e81e0070030340d100704082c003c1d0f40003150004041c05a40c0b8140e0b460015107201108001d2000d001000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221427877 1250 221426627 221426641
    0x102100507030e15011401120608010f0f0f0509190320151b09040b1206100f09060305100905150906220201090501050f0f030117060f040b010e 63
    0x10508a5652050108001d0030a00c1e00280501040c80784450301e44a02d4891000440e4107020141c100e40341225840401021034004482c0f000d0f1668643d44410f07101c5502007034180080c4035000504d00314090004d140d012a042550a964100d219810a0b6240c0410003212800c007064a031003507505031503e6408480540360584494030841069419011042035403682000c00040010718040d000e079980246950706403500c403100448101941f1202c2c014880c2c40c1d000d040c0f50b0061001e180f4024610180b211210342035620300001180c1c1a04148448501081004007c00110020700b540702e80c140419401d64030356a0303817501c0214408001550b1030228400344401031020400381840b0080840550a0082c482030350340703405648060b480e07200b0b100449860752107204040c4da0198180c4405081c9864600156102d400c19500180301d03402c1005000104842c0100444c043d200c0b030b40d460404084084d00003480c1c070100030303d6222a49000000e1001082091403914112110700700302030381c1c980e5500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221429127 1250 221427877 221427883
    0x507051c12060b12162a080c010b0118050913060b10051909031a09030c03160b072c010201020403060e010b040b011e390308010902030606030f04020102 67
    0x3541c1120198980368000c00e04290704002840800289040c1e514a030301e4800c3c5c04414200d0505220f0081000319003990041042200341045080c8516002d0201c0700a94489034040da0185400c8034007a55a01c14a03034942d03800889070004a451801480105400c0101003091004044c02200064035200f01110411000b504030b034007014000351800c40322406051014080d0b80264401d1001900d1104150004030702c62000c400880b030304035002d0490182290303104a0a5131016090300c0c7c41c1c2c0020402c2d0849800204000e01c0a00b109940440541c0824100201c800703d0160019040250300c000d090100b030403a00311802841d00e40281400ca1581000040c1d00a10840c2e02c018480c1c2e061142e01213840740b065001643c1c4a10541e41840300003013150045030b11580c81a52520844000318406405501c5481e5120803540701c04130010000008401c8000e41484001c3d50324400001c0c0c9440038109940b00c03d10b03500500d0800d40c05c0d802d50400c030f40000c00c2c80c08020468129003a11900040039603100b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221430377 1250 221429127 221429147
    0x10c0203030f04030c18020a050403030c0f020a080d020f01060b0403080a0507021305010512010504020105030c07110a03120f18051c0605240312040e060a08010f05010905070507051c 80
    0x365040e95078a82c4d4a24000004080c1ca11581c001007040c40c941c50440300a81c021110307400c200307a86607482c05066a8081e02c0c5503400311421f4507040781500b1070074010b84074028848043c00700c0d00c004011107440068001d00d4050200440c0c64640d04000f02006103070f030040d05403015254031607140c5480d40c41c3c02008440c90301030040080e50008500b01101200c1280c0d07480300d8145c641c142c0d4240315090499842c54241d60090700d001340004c0c01040011650090030001d400f1142c441d48403415403402c040b00092480c00560819514080340c7d1003d08816600260341c0085402c513400d05c1c14a00030f8420903a100e854092242c5800b90b1240281e10003a100c0014100c004554096401c00c074034140251a038424031052040c4408003e08846628554640054215401c500008045203800e06154269440c220b02421260300041c1044021a00510038020903604031408080094217625100c070040948401404140900104000304004a04003252a00918121540140d050320300c540c0219846c4100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221431627 1250 221430377 221430397
    0xd0203010b0406120506010e0118081c02010507020a0506060105071103160e072102090307120b071e2003040b0f0c06010e130f110a152c010c020303 65
    0x40000089152000700340a003080d10403658513018545039002c0b0440482e00d041e2903550114071100b0852081c0c0d8450340c456804241e147c0a4002455a01c04000c1d182c0510340c65003948961094140b0b0950981c24800c02c1c2d4461800d2000380031600d0251907240d02c90002910b4281002000030b00c0509003c81c2c0d10700300d4114030024044903024284451a0340b0303100c8203405415082480c000100b00c10500c5103511182d21085010003584951110030301000a40c00440d0b020b80501a0f008000342403402400814051401031145c0d4589292428005201c0325203a5104850040000300f0004800d610080c02d01d12484085081e90001c03e4070302d6100e01c0c50203544d10002e0004400110000c2da0090321001c2e00c4007240c0304c41156926600c6241d4a405070400321182c01c003903480010000c022625400304110780c01d0040700343c2a0a040803d0200300c8802e03031500051100b5014884410b801036000039844540341120ba840c51403035451808510890aa1a48607410001103000c40d50030b540d018021200e10b028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221432877 1250 221431627 221431631
    0x7171003020d08130b03060303091c0f0312230402010f02160b0a0905040b0d080d09020409060204060f0c02100309140303040b07090605070b0406091406190b1e150d 72
    0x200c80d03e4099116800808044144200900c00003100711482d0162406001c004001e1405d001c112410f00c4840f90120640301c244035088801c001c04941c80707058001c0400d000356118801142106002800c4e01c0c002c191180765903280c0e0b4515940c461088800a421950929082c03090501e440d10491800c2640b40c06c224158600260001c0d003064a50014180e05180c2e40b150303480203507181c0421048862004666800a5041312180e000a40700f100030f2500503d10300c0c0010f031448440d0040350880b200700d102203885642c0000c040c00b4598203da201c0c26203a04610f000040410319a004c600010004181307803060688500300c04040194105141818104140440b52207242a0a1101841030141e90450110b08142e4000c102d06106008640207140c2041070302d00076803100e684160040010010903580c41d0610210744a4402090210312302801c0c0c2600345404d0340300c801e5024030484070221a440d109201c01c0388050b41240f00d8020b024504c02c01198420889591450881ca41e0300c030301603014483e58 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221434127 1250 221432877 221432899
    0x402150f04122f01090602060115030507120501150e03012003060112110406031d030a0819090606150513090b030307080309010c0f0918050601090807030b0411090717100302 76
    0x1e0040307103442440d500340d840071170590b500c84040e80c880b28280a03980341c44510384402d49041d4000d400850300070903039250840c0e05040601420084820030707000881c0300c01c0d601d481e40640b9644078500a002d403000324002c1191641001604503485001c04000c003184102100040c5543c1c091000640e0051500720103102d2272604c03141c40d4a0ba039009000307190200e4a49040e00c00c41ca40106c451400c1e030040800190302d007909007001a40d07d031f0301c01404c2c18006600b01414040ca0440703402040f812038818103010907094140074000300320054869a02081005c03e101d041d800c040c49030181400c80d0210040001d10040c181c010a09510900b000a06141c2c00013043c006c13106015070110303400000036564034141d404c40030344c1154500060b106d014441032200b1b4140d03118001c0742c1d00050b04100f05060084c0c045503070311425420041d1a40c0142d54480c400000c0000b444000c07403011400303d80c1200c020902e450498009440580701200701c208c0075015000142c00b566500e00118051900100481098 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221435377 1250 221434127 221434193
    0x2150c1c0e012f0702060706090204200a020105150a05010309050102070204110315031b09180105070917070b220807030f110102063705010e0402150f0412 68
    0x24299000740d42d031a56801d60403d03a01981c0343c203492000f58000c001c50310b40030007a02c07280041d1210600580c1e02c5a6610011030700c0302d8044088940018180420f280c44540411000c0c4c01c6400060100600c8844005520b10f159114001c0c08103580003403e0010300502c2a0400d0f80c02030047c070100a4210345401d81481800c4032180c0990302c500e072031080c415003060514040c1912a0300c11001103401282d900301200700b6241c4000c0199000c0f80c0007001481e2918281c42c501e0a6540c20380b80c89010840600c02440240130a074600e4860003d600c004003000c5d450310540c04540d205e5a41e800c0c00400e0305a409440122070945640c0003081c00341d088032500c6850303081c0601c2030048070030f00302c2c1c013140d03031070b00111055002081d400c1c843c15111030b080c801000514103403540301410103c0c090391000c448050b0700400700c1d0f0b8494940640307442140c40c07a06150038810700000d8181820f0f08184035a0601c003942c21165040125410348003080c120380b4842c9410314120140400740b00d400e000d6417001d0070301101c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221436627 1250 221435377 221435411
    0xf0e03040302100903020d0b0903120f01050a060e1f051303080301090507110c010e19090507020601050d0510090f020d121e0503011716080d02150c1c0e01 68
    0x80c0d90084a00801c0760f56800d80070b80e034000311440000d40042652180c030020510202459038489034900640f4030703081d1000c00413204c100086400c0110654240014845400d0403d4008003800b0b50b03003080c01c6280402000075001f107012008020b41a1015401508541d1140c03090b0b680f103a40c80d034030700c18031a0340ba49480c011b00d030002d0240ca1180c602d00750004806c01d1080d4900c94003404903101506044105c0f800444410b020040340503040152080c00d040d021804494040c0146094100020981001d074002411302806a202520030395800b000c40005c0f80c00411480010740500e1400203a0016516000c00d10341115000030b503111100c150248103000c540912072814980503a80c10104e100244d000502c0c040218401030000344081c401405031048030303460707013451807500e10458021142c06c29603100f014031540c00000058000000401803070760101b0012030000c154407442d902c589851030005c03005015004000c820524001c000799811542030b840a030f01e4600e0040280300e01000a80c0441f2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221437877 1250 221436627 221436629
    0xb0a02040303180b0a03050601090b1804050c1314010c0204020304050f062503150308041d0601023c010c020703140601080c0909120a0305040201110c060a030f0f0e0304 74
    0x1003c1140720202d0390700d00c01040304000542e400d0350301c0e15040c10b5120504500030a002000b032418040d440001180200446010345840c50040000115400e508400d01c42a140080c010500b5a1014484038803016a502000010b403014041c26200b0300a40c04012680d903e0502e40180d0042e01c00000c2c07005000010952035440c000b001c0c12600b140d00c1d50344c41c030100ba2030840308010801c21141201c2940341e1003500038442584c08080e4030b0000c691280c46200d05503200d90701440b92041c000d242c0344100140681c03039a6214200f40080c000400045050f040950f140300c039507140c4e50b100100403902d0300e80035a607080150090ba4008110860107040e01170350340c40190200391500050300c40444149100014198140c40305400504482d500c03030004c1c40308001000d0103090080c01100c1c0208511240c0f41d02920414405503000318650416000141249162040488080e00700348032004143c0c0303440c011500b0014545c9000184058954072210042001d8445024090b003000001c46103c800080608 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221439127 1250 221437877 221437883
    0x609150612041e0308070509042003070f0305010302130c180e010807081b0411040b07080703080108010b09010e06031005090304150503010f060309140d0305040c05040b03030306100c0b0a020403 85
    0x115040750f15418446004002100090024000c0c80c00901c0503480340c0d005d4402e0b5107001d0300100390280001c800400b41c4208840c60003154001008022b915617100300fa4910707590040c1020030441d4110b40209140e117480400c45180d050700c0c1c2e21003c41d0988544c810904000780f185840c10402e8450307410030340a01080c403501c80075204050010548820104200582da4088602e956803410810309200c0038000c13052903183d24100130711000a8040702c8000074079000c1c1c0f0842030b00760380744400c0c60094410f030303010303084040700b40e00d4400d07001c1581c0c071880d0b401c5040d540621502c03035265580c4000a85003008030310008941508080900c52501c0c00000a0003d403081c4202441d581b2800c000e0403262030000344180721050074100380410000d80690720040b4154001c00c180020012241c01a03840c003d45626560000b90b620801c120601042c0c400703080242404650503c183c080d9600002d42e0390001400240c8219070502c09168071030700560713200e04c440d40e01c509014020b11f003214200c0020340148c4002c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221440377 1250 221439127 221439143
    0x90a0b0c10051e01030b1f0b090a1203020a0f061503030509030606060901090e040819020f070f060203040303120b0a03200f130914030f0a02010f050708060915061204 73
    0x4a88484202e59040458070800300400015030311703640758510700700400341481000d0011517070440b00510a281501021f40b1711100c00c0d42e6240c0460081c403103a85000c0e07104c145c0b1403000d00112800039a020030220b00e0701d60401c0d07400101c2c40c2c0500300f40c401084d69001042ca0790520f02c100008064002000d4124400b007141920304698a40f4140041032080028080c00181c03001c40c03d01131144040a0147c110b801000720505102c10079003a080180007030700e40300c405603004095600c03840c241000443d018001d42c290700d6150324a4031002950328040e03070100509115060060061042d40d0b81c1c410001034100410310443c19640f03003000c0108101241c419101c0401c5082100c0d941d00301400850607486010704900420080b6250580c02485007103001c0b01c9038101314580c60403d1008001416001c0c3c0081011551341c041000043e08540700c80c040d52484a04000c204005da03a008500d80e5071000007035405141c00c0e6501044400a01c002010072548070002094a0f001d00454010740d030320880c420300d22 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221441627 1250 221440377 221440381
    0xa090902030705041b0807050702040f05010e09070b461403060a060305090a050a030224010b0a200a03180b1206010e120a0f05060601051905090a0b0c1005 68
    0x1030100780e0340d0510710180070740554014000414403c844440e40049123240c0306003440c40550001d003d407501ca9460100750340c1c0301c2c0014002d12079030a1a890700001c034000280075031454582040321500400c201241140d420305044104002c60035011002b82e2407120304403821518803d009400c00030351642c0d250014419018005958140c5000c5902a0f00c0080c403202c2c4907490b165003103000e040d000341420094001c4889500011304100f00202d442c0780710f50050314030780301c09130042400040103000c2d000e09581044010800458860102c40681110707180880f08401881902e515007170403002d22207240e100300081c90003490341c89030341c0142040d0551100c0b041d40c0e039a051001640c0c0122444111070301504404900d141d802a410340b403407270720050140e0720a4000d13810503a0a0400d068000d50794101c0104a8000b0000300344107855102c0b0302402c01508081c0e403a40b8010501c83c400da402c4060143c0019040f4960b9100340f101070040001c05e0082c3d513141c0301807814070b4075000c5a050414003e428540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221442877 1250 221441627 221441629
    0x9010b0d060605070305031b0409050f01031b1a070812090a031202070506061e04020a030515030d0909050c0417010b03010507020619420608330a090902030705 70
    0x70888500d643c15071b985e281181c0720308000e001601165800e41182c00e004000006500c03d86001d800d20034441140360418a6166081609840924649138400643c2c0c5020030b00240c140280b01038020f0000c40151500da0707401c3c3c42c0c00c0c3c14920800400c40005040482005008440000e9041e069442590b43c203000040700607210090b405010402002500604002929403c182911403d81c0a610184070711403a00d80700460100d074040500d0b940069120810400320350810514112030b0f00d07082d00203101b0248034080003481095640240b012240d04c40000c100051106415a07010304104100d425a451200364201d00904d030b0340034136600075400c290006121500200319244030384c079006c45070700e104512000704c40c004001e00340d504501000710210080e559140502c41403141ca54048074201020100900c0001804156111104026102040142e1040ca1066046078200c810080c2c0d220150307800105c0c0a078071708105056030001d0104c00002003440c4190004144075009409540703400391900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221444127 1250 221442877 221442887
    0xf010203100b0310030c09020706051803030f0915100806090f0d0311040b040f031e020f010305070c0f0501050a1103013b090a02040e0a0b16050909010b0d0606 70
    0x3148001c40240c0c26004004201c00800150392005100c00d40859640d10380d1343e0302e4076000a64208001541d4081002c80c10410284103454110701e090341e0b8583c20712501016155684001800d05010400080c08644400c030100144180009a6180c04015140008018030703940310724852540c1504c500000300303503202d4021580444100f001005040d2031058460168054100e10803413082e4068100800511007481c84003410161540304040d10620386181054800b8441c071018000b0781001c0b82c40e210f001684d40790400c0d00c80c11400e00f030100da595100082615540038596019004035a2100f402d030400206510a51288440c4002000884404100304000d40424000d500800042e00075049503039852924203c6e031880121103440e41408540b035101403152068034050082d50203244080114034150103a0b803c180d080e8401841c1420640d2141c107903100000e0b00c0304844241003912400414403650031a840508090805c0b021941d5507046100300350700c40040f43d191503240c1200440c03030030302c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221445377 1250 221444127 221444131
    0x9050321070f0807090807080606040e06240604090c110d0e0a0b03090106051e01090b0315130f0905030306040b1807080705041203050702040b01080903070f052d0f010203 75
    0xe96200803503140307400801d0300e00d81800f80241003404017401000940d24400c200d0b62028098900280030380341008018081640d00303214210110f038107d40100501a0440c0b04403080034501c80e00450300e104010400700340300740301d60f81190b0072a50428804554050300112054181500300040b20b04034003e1160031600c0c070350460140e0380e025103140d00800c244003680780919013060007100002171096a0300d00180c0c4100d100541c0b4035444d0b4040c80307115100e60700071901c18010440307003210510b50710f041c0703035515031085000035190311915a4110222200d240c5520129840b0f012031010045003066051060340c94004490042c031a50400070603c080b81009010300307040c0030300503200001c152251281a07078080c0000b000e0000b04032082c000043c1c18008400082c90460294071501c0d44c0b00224014031082d500790343e0245040c03094a80500c14450000803c8806d4543c001000000a40641c5003550400850070750500280b4062081c462504004000000b091410007045a5036010144400c81c283c2c041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221446627 1250 221445377 221445391
    0x421080f101a0d020903010e10110a050d1808040b180f09040b1302030a0b07030b01080910090606031403030106110f060424090c05030f0a0f022209050321 68
    0x321503144000c1e1000b20001e401a10301c0369a000d420100c4200100313085416246007610f4561011440c8500c0d002203105407002100200c0442d842c1041110024140e88258030410f000f49940d100d102e03200f00284401c46075650742c091b1441e980c641d550203070960203800031003001403d42c8c0c510005110925012010040e803d8015004200581d5192112030300041c004064580c404082042da800583d4107009890841d8400c40081303100b810544401000c44002d0038807075040c440c010003402108680010aa034191111f03480100d0700e00c40600d0707c400a42426031000700b4040c4030f00c131040c042c2c0e08c000c405103041e204166078804805c0b9169075040d9582030180d50081080d084000440d0100b020b0309146e000703c0605802c040342c10002440d003e403c4884031441a10383c021003600501042c581800120303240010b800c010500c0458603112000c10040304038000744201c030400d00003440709041c04034103c01c80039406010089020030341401e0f03032a6407203009420a41d9000300d00368100f5501c0c00d50381c43e0007000f07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221447877 1250 221446627 221446649
    0xc06080105032b18090c0203030f090a02010806061305090103050a0303110708030a05250c03020607022a01020106080f070e010b0403050c04090618110312120f0421080f10 75
    0x1680d01007a80d1403005902c041c648214130680220350b039203481c01500880d14083c1e004680d6880c0c00b421039001080b01812b6896550080005a000350781e02c04040c1c3c1d04103a04030750a82c3c3d1584003400c900006030300c0d68442a04484800000810b1140114040e035032603001c1d0f203052201c0d10f00912625154072908000824210007440814811015035002c20790110b00c21034501e40c502d60240010740605e150440c42400100741e005880f003016414001c81e034100c5c200307000424460b0b4007035100524520054610185515110340c0c10702081c0e2003504607100902c00c0409403264074104202e40c80d1101c1d250301038141400c2a00d0000603618402c40226011283c1000162107410300c02c0042102600d1152400e40d4166201c1c0007002401801400c09840c5078800c82140b074088141206050401604405050302c02900b80050400301150600341940910740d80c510800c0d0f50340700e140c00a5030400d91035000340d4074005c01e02c40f004440d40140d4050b01030b0030241c05000c1d4560340e03003100390e103c072000d4090198034030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221449127 1250 221447877 221447953
    0xc13020c0a380c09040b040203010306091103030309120c0c0d0309151b02010302030601030605060f0a020714030d140f070b0a150501020c040209120a03031d07061e03090c0608010503 80
    0x40c0314030f001c3e0100800c01440811140c00d20303c0082d050360020303001621500e90b60b105020070401500600316000c10154007640c10b41c41c080301003603100c800e81034480180007000103c4034441c000c140505003450300e004100c1f080103816410018420191070081007100d0700f0803641054001d002e03250704109440d440380400f03030480c03403a4011400781d0400b628080c14541c65110100d600c2d0746c1c0030060100c1c07600d449030351922815070050003032800b001c907408901000000583c640203614045501c410703e041030305025814940f00d4019070301c64818140f1021500c1000b040c04070402a5406009000e0000d40d2028010f8400150000604c00200d110ba2070150380080c06030030840c01c141c3c02504d08424010840803003003244e0b0180a0400000400860010b41d584003103003140224a0304044440105100803c203250130004003030000203c02c524110007003880a00c040b00c2d41d11030740101d0102540150f0000e181507658001428110382130141c0c1d482070144600c8a80e0b074400c080d0500f030701c0c4040490740c15054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221450377 1250 221449127 221449141
    0x120703052502150705090a0e100902070816050604030306080f0607182c180d050904021b1506040905030f0a030204031407030c0b0304050c13020c0a38 66
    0x541d4890075500254050410380202c02180401d0003072044001d40c8640da42d80c0b015101300410507486130400d108043c1100148540f5541000646094561205006070340d4910341c00c0030041c82c001d40c83e28400654000c1c10580c1009004030b07080740600e00c2910103006582c0c03210015901d4001d48611042c10b6408100000c00f100e00c42c81c80c28400c041c0240046031126280ca09800b02e045060384102014210010700d046071f840c607550169480414170442681c031074400e000054485021546807000c021010928860a6940340d040350481d030840760001490300a6590225101d1102400a1b00d0302a440c1c000252103003014028003080f10fa00030059844e000380222010600c3d0000f002000400da0b00380030100002d0440c90bc019040c0c051600246102403440c90140c0c103840c910380200d030103100c0c1803091100062000070303043d001034001c03a00360000f0f10005190000a0184c41072780b000e00d104040c103410521004601302c080a41185000c000700c8114030174106e01402c0d03030589480480030200002036070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221451627 1250 221450377 221450431
    0xb0d20030403030f0b0d0804140613090209180406140f07090302091b03010320150406050a170a0c020f010b090f0a02040902040b09130e030a03090204060302060301080312070305 78
    0x241032a404c00060f1900066001c264a803805000c12210001c0008051200300e26210081c0c0058808503209441e15031303400f1611048801038440c01c80181d401084000a9075a088a424142c1c10354035020011442d090030000003900103c87d40682d106807110216001a858280891141c012600c2c0c1280f4203141d5824008814002490050210780c1c2c5a401c85491030a1002540254003811510b1020801184000103400788405030314070401e424000c421100902e10182e404860050404640301c403408041130b20384949030400c0c2211451045c081000d5042160f022260507000c0341e00312200100c0060030320742200c1d130b884062917010340054000341c0039408416a5a6200b44101c4005d420155a10040003d03600103802c47c038001c2c107000c556107465040166a010681d111100c040c4914400c10100f1920303880f403604c0040c201600c40c0000d0084d919590000c03002180d002e0031065807580e440341095201e800c0040120f02c1040c1d19004540310f50301c41c3c02800d0003440b00c1844c2d503034868034003212251 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221452877 1250 221451627 221451641
    0x14060106050405150d0c0e18130b0a1b03061e050303030c07030c0506010609030b06030102120c0d02070c09050a0b030a0510020706060909030801050a0837050303010b0d2003040303 79
    0xf4508104070440010320705c0d0240345500903840d2114086111300004120801c41010101400b00408008001c2141c0107206100d07800750f0004000040b9854841d4800050500300c20018568000001980c0d52568180e002100311070101c1401c2e076016410a03109100d4156902c0790640c5a4804e1021595040f401380040c4070081c42410a1452080d5507078445080034405d034005404108103900030020300400012942e03000d0801c030000c5241a20001d0480c3e00c0c00e0001e03007407040c0c9580100b01a070300c1e94031a0b4110b4090640000c190645e181d69445050054603040360101c58541c200310440c03407603040004450f03000e954030001404008481c010078100030f41180d002a10025100c400019440c0c000d4880c890700380d03020b5910422203604140c05d101120a05034424642c9500c0300e800c449840c0c000e41e440701914040b071700c1d085103261b0f040c000d48420400450b01c081d1175800004000100381080f50024007400c00d18450501503562030300010b0300d21003502801d00c0b000380720800004000038481d070f1000b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221454127 1250 221452877 221452909
    0x62d03020702270109090816030210020d15050a0515070201091706061008090c060310091118010509010c03053f090604020a03080d0f050a0914060106050405 69
    0x181040c101ea000140c2c030701c50b041c280c003407002c0c0c400b030360442c2d6108070f108194003404040c00b0500002d4000d42d1a20414403410100301d0006000c0c0d100d0304105032090001003201d60120609544a0000a0421000300030125006180740c0811000149500f00f00d9071600031074500030f01c5007940c00d070100e400003041d42c0700d554100d04003d01d02402064181003030f11009003000ca400000e041c24907007502407000a8115984560a20090408010080c0c100154210714543c0070317074040e51252034940c0b10003035942154002c065030509122648503c00b400700083c4c403000705043c000c4400f409070400159400d22401104900242c140045000440e0040d0000d004a0040410200b1400d0348da000c080a80ea24442c04081880702c1c040c1d52081050407904015004401d82c1c0203069642025400141c642103030b03100003000b035140401c80c5c070003012069104148201002e00305000c2d501d0100062002841e01c803c048032502d07410354034a124008000349a81c1600c81945541d844e140c02c1004020300410184500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221455377 1250 221454127 221454131
    0xa05030d020a0816050304030b040b100e0c0c0109061406011b030801050409150e010f1112041103190b3702090d05010f0207050c0111032d1303060501062d03 69
    0x81340c005a01000104000d50080408000700d041510f041450076074090a00c248980e2074500620451840408458101c0c11044001d0703960744556080c54058040d195002d00641c0c549500c2d8088064141c8045100e08000d0781d51840e40c5c1c240701c0304008851040c1e44080d0026001c440113100070b04141d84488221406110f14202d21207010103164180d441e41c5040c109180d4484803056100c0000b405800700c29a4220383c0781d410070f541c1810599025074000d02c042c0c010080d2040c0e001642c1c4003030060807045543ea0b4400803041c002418000c0b540e0800742c2d84d0140c039803200300d45c0800d02c100700305070100c1c142541031850048083c2c0e0a22007010350010000e16501c101e130103511100103072003407149200b01e0540070390258440080d82800c6040030f00a1104a06001c440c0710710b003082c50340200445840b0450f42e00d52a01b1141407004207103c0c0c004118560003074a41c0042d9514412080c0002d45085900c00c14041c402681c0341c02e811075203020480910f0112138040c203544422144072250184201c40c1034940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221456627 1250 221455377 221455417
    0x4200423031507030b0f09190f060806040204090305070b0f010602120304110d05030c0f210408061909020603070c12020d021e0c040501180510030f02100311030a0b0a05030d020a08 79
    0x140d0300c000c007a6201048003884040780c16114205006418038100b82c40c0080206604e402f03030303194903141e00800082c4034035944d5450f03070205030082c0180e070340c1d040e0012425002880e01e217842541d400e4083c02070300c0c098802d200401c001c03d080981200d214130340c810b075000c0f028907103441400b01d08100940103d034640810300810f80d031143c0c10041510b074440742c4002003002c51503000d008111607444034844001d0420405c418042c0d441d0018507d90407010059510500da16144000c400400318000000d40c031003c00824060911762120042d0101c40c05500c40e0241180052400d82e2348001c12091400581c03c1305c2d200f44140118010b01005040084003940c11628003036000604581c800d821141c03d80091400900242d404e40c0b140590100e095002e0910003811500c4610010b0300039500284a0140f4280b082071407840f941000240e4945003000c0c2d900c9080c0328541d04081c0280100d00382c001c460803900050306250000340d850240015401408500c0055250303414a940510a001008001002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221457877 1250 221456627 221456629
    0xa0c02010e03010e1b04050c0a1112030c031906030b01060f021504031707110703150b091819110d210203040306051302010e04200423031507030b0f 65
    0x803481c030420740c00041c0c00b40d2400f40580001d0161700000700c1d40078918100401c00341c6413045084400e1036a1b141890460600c00501c114034059180d446102449000307c03e0148080d8624061409078a0400f4400710411504110b003003190410320020300701820140c010044240100181110304d00c2c14810b507114a1618460351000000688003200040d4a031031010611120340a18140c02c00050f190440c035840060301070303550340c0f01140030283c0491060381c00c1c1d810555031640b2614901401410f1283c0ca8a4907461b41b92185080ba418132000380151800f0074039041390044655421980102c01001c90b6840e5003c0c0601071050010443c0c0e040794841501c1035281110b034a054204804d0380c000c3d5500c0742145458070036200301034400c169100304e6516880c01030303800c0200d000c089079003614001001d80c5000041d16142482c4410009000c0300000c0124100d04c098601941042c080d41038903480180c0d400c1896510f09481542d22142160580802d030303404d111b50801d42c1ca07038800034001045055054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221459127 1250 221457877 221457881
    0x1203030108030309192d05010509100f060b0403080702060403050304080303040201120606020d08150d06020702100c0b0f0603010b091603060605090a0902131208030106080109050c0a0c02010e0301 86
    0x703000494554000300801c001d0f0801001000030125001c20035000880b15580c46040700301100d02c1c044965107010080a00b030300065a000044190404028456410309040b9640c0307480141803048507190030103c101d901c861443c05440c003100c408200b2545407a29640303544419420248040740d00030010040040458010070103440078000d000c3c042c599a0030315100160490000c5000002e5081c2001d030300f009410703008281c10400800314146a129a5540211320000c18400f01760700c0d03800956a0b84090503c040ca034060652640300350f8590f0003420140000b80d401880c0300c80000c0c1150f1141000034440740e50004403c0c0c1051020300049030000e120400205840e60440d850040b0b00041030200d00700c0382d070501034900204080c0c10424a45000c54002c95010031070350007160300300da8000601c08600c0c82030707080105c01040c3d01d4003d2000704660f450128a15402032041d000040e51900011442d04001d114179405050b0618034603103014080d031000c0d41c0040d104072007030b414804641e550380740079107081c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221460377 1250 221459127 221459129
    0x10315030c030813080a0b0412021e03120903031510020102070803070509100306030b13020102070b0409060807080c0109090903031805010c09090b0f040506061e03010f1202030d0e12030301 83
    0x4506882e121416a07880c801449413682c4044920b910101c900c80104010200d141c0d0019082008800c660401000076450041010000a0107882c0c85407804002000400074021504002031628255200d51201503524042600e402c1440313200e22003849207620b8265800c1d83d03028201d000141c02d04217240c4903c00182c01c100c0342000416000141c14a00e89031044e0a0210342800b824108032842c01e5850384c107800a0018440260030f41880c0401c0c05681c020400c21004285c00902c01e959070362541c00f12000740100f842605a0707071203205c0003c503011001007408a8450010b0396421300180c58440888040c00b84000154285580c8808805c01400c52002010250b80113900120303040180030f600070b00001f09a0b0115500c0c40c07425003035903802e43d40c0000c421410941280c2c003140d41d8a400d00020103510842858854000c03011644814102c60000603504031001d105402000c1c59070750040b00d041d0000301c00700035410341000f1a4400d185009140e050301140001c1c00420091440548a91542e0b0003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 221461627 1250 221460377 221460383
    0xc150a020301050f04050405210f0c0a020306060907140a030204050918250b0901140a0314390c1207150e120a0212031e010e01080309010315030c03 65
    0x40180f0103820030520030b101d8500203483c2000280340c00e4450a417036603000c94411103480e610480e0300030000d001c28103442c0c1c034183c03041c0003644c2d0b80c82d00d40007a80d072541e017481d00328000d029410006280c1d1414100080c402c800d1510365440326124510b0445495211031032500900d5402e00010071642c0302d903001c40344502d01202d5046451032150300074616000c0c4e100d0b40c0e0034000c00c0420f56800400001c9809404540020394003a031105400001a2040000721840032210000400c100052543c50381000d201d06001841c107082e140c0b4cd0620080b0380c5a100c0c1880701001d0300d80401e00c1c0d0f0008404d10300034400402c200c00135040080340c440890500380d2440c4155281000800c1031000d0110000e0b008660180302a02000242450214162500c00403860004400000b10300b90100360300034880c10b20b140c80190b00751603403860444251072805900c1c258003002c01102600100710003640d0500b56069400560055040c100c402c4011400b4210900410300e10004500d000800211402002009944 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 221462877 1250 221461627 221461631
    0xa0b01030807030207090209010f0c05010b0d08130608071403090f03030a0c030501090506011b050109061b080609090c0d0305070212060105012a0201080408070210030b03160305120c150a 82
    0x10b00d400e009242c40c0c000e030070070301c1700510410850008d6a00945000c0859015060444030711540742441030040c0300070303110260000c0141004a080280c40c0009119556040c000f440410b03440300c10071034048208995481c007082840311044010190304001d1644485480110f45226003101c0075076066420990fa5915550388440c060090a6014040c0c0ea0250102d810204120324161000a00e102c490200002c403c00c808401482844000e401000e120303500907200303014004a2110340a0900310640c4040f0004d80000040f418a00c0c01502c404d00405d50400100f04400300602089180301d8184d50480500c0401c0003840c00503114980c020260076962400341c00c40d50f151400141404d401d10351104c6034020103007621030401d0384806134441034640a18101c5059501c910708620366114080010358407030301c9040e0440525500d5004213948420503025686000000074180140040702d001c000c0c0950090844254200016009011130320500001c0369420341d50344d100354280100a5441d01401a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 221464127 1250 221462877 221462887
    0x2150405030f030c073c12081e0124030525020304050301051003110607050318011209050a030f17011415040303090302150c0d030f0b030714130213120201020a0b010308 74
    0x4600d09030703001255401e04140981b640f000d41e540c01516001001d000288150741d8040f95401288601c0d00d9410010402c131540c2950312203140490104c054141108508844010082401c0c428003440e801800041540c0da1514804100e55130a101040d1b000802c5100030b200014159409016040c007a140c0910141c03079041c15820144500300b6111609401100204901ca0000b00000116884040b1401030302d18540c08450040b540034078113154400351503061100ea6411300402081d101c0c44a8402c0d2130b00380412102900c2a213010300c003609031400401e070b83d000401141d5040010802100c00050000c01000c04401907040350b50402c5d0000e40000c0d0340c0d01014000c600b49001c072a80c030007030b2861885041070f90403000701c0d94a800396140202010b031150180b188070750f82a00440614400202a184555210f01018a01400c00b000562080410030b1105855204905c2201c6200341d603100143c8010303003040c010444001d807440d8124110700c2440780140c0801e064004d05406540f00da5003003035440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 221465377 1250 221464127 221464193
    0x190e0609101706010915080a230f0f150108090106030c08060f06060708030103030c020a0321031d280602030c0c251206060e150102150405030f030c07 66
    0xc02c900a081d41c0c180030803000309001ca0b5003c0c490848080503e0311341941d641da0f80114036405088424060240c4180307040961003140031001c1d503680704031001810b102c060343c1c40e00da10351400902070320b0101c81a60b500030098929407246030030707951001c079580c0045842960b0f80d403944001c94043d0b000c489580c10941c24800c0b01401d4001d407640001c011a101400c00389152580c07140d511041c4030003000d10078884522021512034081d4500115084480d1920016802c1c903001c5c22032040d01640c0c0006031901c41d41880e030001001103001d46c0b90000300180460b2541079020381c0b0540380503612651812611800100041c0d8900045218504003980c550701c4240c03404007946801103009141c10030100c4960040f0000c41084050030448510350f082485514040c1000d00c002c141b01d4100400301015001000070300481d00070103c046000030390803130b1008141104410041760b829a801071558004014100404040002444e000a00010080e1400741640c1c1c2d4820b4000f020031100307981c4440c07007600030a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 221466627 1250 221465377 221465417
    0x90b0901020f04050f030c21010c09180506011806050415050306030a030813021e180408030a0203100801021201030c081b0d031b1103010c05190e060910 67
    0x11094020081d03040c0110b02c484901e4070b014601940340500c8158004844a41d4100200208401e015040d041102229092580310941e10000e0395401d609101d42842a144944242d42c101d400c803107174041382410302c50f01c0310000d000084d095504122403081c480c505440d0003200040201090740700c0f2680d581ca020110010409008000340c10320806108100c01600c010074000910341c1e26142c038001d140d888440041c80f1503001000a90026030a5140c044022440080c6402c07070071045500869020070a2402203198004860040c201e4906001181203001503402840c0c000440c0c0604001468640c40c00f070b1b0880c0c01207005105910a00c7e001003041c4001b2820807400741c020000600406005540e19004401e1040750342070040d03103c9158501410300c0b5581822600320240181a03010383c1b64207229007401503401209111313510746000290800d0292045038200d1702000c041d80072034078010074144d403000485d1000d141c100c80108081411030f5520001899544d80b9900c0d40d040c444540703451042c0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 221467877 1250 221466627 221466631
    0x1c240b0406170c160813030c050a050303091c0206040b07150f0b0a060e0a030204060e01030b131218030506100303020705030a020307051504050411090f150d0f180501090b 75
    0x1c0d20b603002400d00a101e0450070860b543c40c5490002024145842d01e0300e03c14610524403051844422003001008001440c0f4110080340c000b110841c103100c0c0c44004041d100e100f000e01042d4051900b03840700301c03580303400103d02039a6400109140c2c2030941d0354103040c51030b80c804441110b14001e082c8080840d000c103445a18500301a5070703000c220700502d100104a4040c514085d4909000410706402000d0303940c403604002950340500140081039075190840392b400009e000031101d800500700007034500105d0340a8807014903044180c14640228403603007524881c0154518003c039040c40b0740c1c04004540100700242c014081c8143e400100ea1039400d009042042036001180302c1c7c3c002da01c844e0007580d00000c4035003c3d614110790150044a40c80031510551141e40e00c00c0e0b03080750405a1141c2041c40c1c58015140e0028190340100d0007003000c43c1000b80024600340074510800c002c3c01000d0140d9105da0000000c5802c00303100044807440c0c4041d200c03170004401c000322a0ba03074550041604000c0c40b80b25880e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 221469127 1250 221467877 221467907
    0x90a0f06050105270a0e21030708130f17130303020c190f0605160605040b040c05060c0a1202100e0705030d0f0518040f021b01111c240b0406 62
    0xc4c8155120038401c080d505020f001045500d4503001c55104210301444954003005c03240d0a20040561400100e000b030b50800c8078000301045203640000c1c20452100e14505d0700b03ea1040b1040040481c0741e490b1510203190082080218205220b40c000703680c038030592030019500980003007404210a60401241780b08001c40800180c400310700400200b1040340d030903001d892850420a445070608582e170a28a01600c0020304103a04010501007404070182c802402a406005880d04160704d0301c0501501d4459240c0c2c0d007100b42e1041d40d80d0b40100d560340201c51400141441541d40d1041c2d0030b40684191508080303c4003498011141c10041840c040010b00641c41e2181814095101c508002070030b01d01901d402c02c0c00010741031003030b04103075640c5a01004810312241000c6445818000004448088440c0080d445618111750140154418003d480e2420300080400604006503110300d00a4031040f13520754101c116031401106120b0400d500d25000e001000c19130340c0c88500c2d200e4001c00b441e0b0344080c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 221470377 1250 221469127 221469169
    0xf0c0504020f0304120509090a0c0305150612100b0a0801090c020c1011030d021206040c020601080c040207080d0219080105180103031805060c07080f010204120b090a0f06050105 78
    0x20490500311003d8980c0b058000c046421380060940c0280e40b544a81c0681c261301c21169001c00400391950f038040120001195010096503503103101d14281d100e00048a1a0710507024020b07140000388003840720707a200c01040c030600c9500740e44242e0ba11140e044910038401007082c510052140a40b60b11400003046103500c01442902c48210100b0f40e6042c500e400c0000704002c8800c0d440c3c810310104201c0d84511040c41046541b564640f481c0c0385000d0b8141c6183e4811410003003c02101780c400915503047e240c500d0003074018900d900c8108002580604030031900071005108000740080301e480035055003ca018800e5040640e11140140304440580007a80301c2d4414040c9640403452503a07285042d640c0c1030819003102825400c0745800004a540040e0f8014000100750141420101c0c078081110607100c200c031041c070590300340c480c00c0c0d00450082d0001c0d5000c0c5a0000301003440b0686c000e4029440300240d83c8240c075961110b42c401107074030034280d1b046626000100800d082840030142403507001848 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 221471627 1250 221470377 221470387
    0x915090c050d08090a0e060f0d0305030105060a0903080f03071701080c100e04050c04090f020f03060d14011103042f01031d06090714010c050703020d110d0f0c050402 73
    0x60035203200c1090240a0044401e80b40704010091080c00311880460020000d62400382e81d03025240c140c030382c1100c44078080c044c4208400c102d402e00580341c0c1120340d45611803500b16803d10050011a41101041c0000c204d021140080407400c0300e00246081c0030201c07003c5540b0720740094098030507a0703546141c840c03101d01c50004000800d00800c1c05441c542049030b0f008002d081052040fa02d0462000c050f61f4400e03d814240081c4514100040c4226410160181f000c85620803000c4101d0081048140c0c0d0101d00700b00003041460074944d40c403480391203100450418207026115508481005040ba411200000184030030b101503038021781000c40d90300f040310012801e212942c608184040707500505041d181d4003400e04119807a02040040b0f1020310842e0a21700e042c154072542c8100b24402c1c5038490396241e000c054954800c41c405900642c00100506587d89583e003030040d02a5260001e40d40601015070031500c9130303981c1b0128460a0b0188442d080756810390b0a050207014900da110307500c074a104200e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 221472877 1250 221471627 221471633
    0x80c1c090f03080f07021906020c1c1407030b1f050604060c0b0c0c0d0512070305040b010e0a0b04021b07061b080702030106030203060f0f0c131712040801091509 71
    0x500d1081c0d951040f265a1120300b80b01c04110761340100c103802544104c1001c900c0c0c11001d20854080110f03103051b0b080740e641d070034508144a01c0340c140305072049800107600d2076100403c141501000d2104032100031101226030340c3e11000210101642c038201180b91903015098030b1035443e900c40010b440111178491400303107810b0014003020f4060724001d204c3c501c16030015904041800c280d41c4000c240005807800916202e000404541c4200c40102d2107214140100d41114843d02c0b50a203d103600100103452039007002040304c40084001d00d40710000d0b840310f0b5450020b0715140080c01c0d2600815806604450400710003504041e030341d411540402040300984041e5400c4c00036004003040d00328004030740c1c45101c0d0011901406150b00003035010f01c129820701885142c1424840e106a0981441c4000703a02c0e00d002111040c410003910316038506080400b0301401c0804d9030510021691002100d000c00ca5520154001d0380040d80105010703551000c3d400c1c180180c64808158035201c184081020005070341e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 221474127 1250 221472877 221472899
    0x120114010201051e10080d0504030c090e0a0f050a1209150f1407170403080403120503010311011d0307030305190503060a0303030e03070f0c031703131101020a080c1c09 74
    0x1401d110b140913400700d94242c00c0400303880003610081c0203542c401e840f000000303441a1b000740300458090005a0340040c25040c54407503e115030072114043c01b2018030540324044060b062a50545043c003071810004c000030504c2d00120740c802c003541c6030200396a1a00c0b400e4194010b006003d43d0600401030003e078204e03540801100c10b05140351500603150074960800d1841c80d01006d0805428000c001008000c2c81002005002128480c511004002403000d004a6050001b80700c024181149548000f840390b00a00c00207610700b801c1030724107161022000020307142a010354410380104100003a04007494913103d0700c0310041c02607810501c0c42c504009010401c020030f2071001070b00b0583e0320030081e085c8010610468481d80e030454103c0400c12881e060000c0c01401e544000c65000c40746040b402e2401000e042968400c103500d423489280110251181c282c01a064241e180c11401602070303000000740784101030320001d134111004003030b40c03d1058140b00e00c601c550150700092080c00017040001e18006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 221475377 1250 221474127 221474161
    0x1b010c0f110a02190b0301080604060c02120d0504061128030908030c0f04081b01020d0f05031303232d031816090e06150a0608040f050312011401020105 67
    0x1540d40444240d11600d03950803980c49900b10307403d2031100000008d5071010004585004600954040211030b800d0442030343c0e00c2000135041c600c00c02090003212030b0f26055602481d8401d01132070700880d5000c1103d030300c900d1a9101f054024915201c0909a5892400d1001006c501c0207090808004088a0361546001404000d010010b1590001a1303014102c40311403d5900500f80300080f01c0c000180c08d481405071000702c0c40004d0051149141d10800c081c8907090030091140d15885007032464951004001d41c0c45c440c80410307410301542c05649200710a041c907004144698a11b50151194014015101c49101c403030f0600d01c11015030950850171854071811640c01c580c0d41044860146009600503040c0a9034090f00d0001002c41c40d0009200c2190740c0100c503100c03000384151003980d550058100c07159041c414209401040c000c2050002c64002c0c6041a003190150141e031010310100d55946146500c407418050225041d207004201d00c0811241c55181c2d071b2000d000038482844c00321094413000b001c3c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 221476627 1250 221475377 221475379
    0xb030c0609130e1903120c0806062110050306060d02090f10052101051006020c010f0921020117061305180a0605060a0f050306060f061b010c0f110a02 66
    0xb4580301c41141c0b0400782e1003090f40003012815550315205210300c44028012444003030b00440e000c5012803a40400a1142c1c255008032600e940c1300c0c0b5225001441203e0700700e07540320a1040d0070b48040c042d00075404008548200c101924048845041500381818070102520413405065101c007200d00596401116544c00030210840f4815a0340382c41e28084a42c00c0b40d0f000c1074004208000e818803240e86841a90783c8000010002d0081e600e40c105030201103990751042c0702c0140c114030080320056100d00d020b0080d101162800d1040e03603407207085c4d4109000305491700c413a080c400f490b5818115600b2508030b1014521507100c44145180030700108001c285614030701068140d03298000749003021801900000404240b04464251059203401d0008010558441d8441c40d144240000c501403a0389070312064032800b0340505070640b1460305122003c950440e4240d4480001e0040b07664215842810300c3e4440707002d00000c9030040c0b10341d0001c1c0520b000d004114003048119141c641c445000019130681700781e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 221477877 1250 221476627 221476639
    0x280f09030515040c170102090a120b0601120b12030a0801290d06150e0307080a050a0b1308070308060405060901080d080402040b030304060c0b010f0812070204020f040303050a030b030c0609 83
    0x511850040013442c40794004070b003070030340b07900c40c0d0020301c1415400780c6070f80700007641e0007801d0989549010042e000031482c010300082e00d800000340c165115508224002c5e40604001c1100340c030340e50014000001000a6141e59070000c500c003a01c003540140400c0c0148070080110103c40783d800841c1502c22039220b40d40c1181d110018a03001121501c2d0b0000300200300300030382c51b503c00800001c010f002d80c81c0b5000c1603202c2e1280e4000428040380105030411804d9028000b00000f075034607600e0a41c0c4801c0140582090851040840301080d400801005480d12903a16000140741010030001104d00241241d0f000700c42550050200070b40019503011040103c2c180440f09945074400980a010440485a09800007107000650315402c4440358a00e544150082d40c0541c1c0c8408030407040b54881d21560707071035a004004a032026210000100590f41c009000507280c0f00811051861a9010f80c0c400c40c001440010b250303000c04d0f4540709401441008802034010314100c41d00040c0e05000307010407248564 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 221479127 1250 221477877 221477881
    0x607180b0c16032a21020f0901120309080a150209150f0c0c040504050c0d0c030606060504050907030e0606100e030f03040302011403040b0705070305280f09030515 72
    0xa0020407150008280c10200e1144140d00e03458070b1640c1c2041e2a00303130141c0c0040c20b850065a240402030303d105450420315032010200a507a03405080040b9a00d00343e030441c11800181c440c541701c013055180a008800f45902145005160040c00e100003981304040c0c40c0c00c079144140000e20310740180b0540340c0c9411009611349403070f1030000f803c0d1140ca2002e101e20320750001d50500c0a0780c0e002c0281c100740010f0750580b000c120f0a41d00340001d55504540081464101c019a0078681c074100500001050090b550032065649981e905000c0303030400e42180d800315001140802540ca40b0400440d8000c07880d207810300c960108003a01a030b4943c070140101d407003440d107600c0040c4d03040c3c49241c2801844c02c00400310b440e00382c2e660703100d940c585c0d029003c01d0340054884030388800403419580480f405903510210003e41661850011180da8100a00480410000708180b41d07001e0011410040e030004081102410400640b10280c0482003080e08081803212040301080810710201e0701d1484058200003003070712a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 221480377 1250 221479127 221479147
    0x6020a030f0914011103060609040507050708071a092103071b0c0504050609010e0f04020607060f06060917030d150b0304030201021314031b0f03070e06030607180b 72
    0x70309064800000568a0030340090288098031040c000003c0081000b0018440c02c074200d01590300c0104c5541d034200d002084040d80c5030526604c500c0d4040990b00e4181c0c107141440d601d40086034041641520f01c4803001001214000340d01c4101a0000308050040040c00903240500b01a4181c0c1d003640482c1e000c2c0800001e812a0003a04080b2561440f41010341d404000c91500c0c101050590144038055031801c40000d2a504000c502d1030b040e40c502d03501c41c10403542c41c040c0c510294000203004a8012009000181c0020250700420f144000500004552181440e01c01000b642e01607000c070484503507203411543c00c000044120340381e00c1c00a00300030513a410b80303840d404110351203940006040c80001040005140c1d043d40900282c0c88040e507003103041503441800d0001d04610080e4180e254103d42e20b6002e004114a0322103003c0d03031001e821028050b680b600002e050404580c40202ca4503e042c0c01c0140510f4240311050b80321900e800d100045840c8102d0704000c07450703103010700d050310040028080f4003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 221481627 1250 221480377 221480381
    0x708102c0a03120b06121605030103050a0b1b070807060f0b0f01030534140901121a0a080a11120c0120030d0903030b04051506130e09030c06011403070306020a03 71
    0x1d41c014102a55034a403081c401d0300b07001802c950144688003441d4803050f103144500103d9042f6a08180108404000c6032507507047d140300a4000f07240144116200d211104600c00a0880706000703001190703c0b030032503050100a070703140118001c985e5407921001c0e064aa960840c400d000240030b10f80012260399201111112800b070500c9031910450a105064440404405a5201040c3e551720100702e005404135040660145611550209150000703605068550764491803010b400f22041c8805442440003088821036a0741105d40e503504200040c00c14441d010488002070f03002503502e06120b5940598450726400421041d0b03041002d40240c0c2d42c4a00c10303040e840980300404d0b100b629036038510400028001d2800310303000c0300401d092411480851074584540c51044000340c8581c0310800222003040340c80c2d40941914801080c1c600710100e00800d215204900c6040c0c000003d40d9035140c000602403401c0c0c4140d1003441d402c4803080f281e0b05107480100748002200d0340301c2c10158660580c20f00a0300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 221482877 1250 221481627 221481641
    0x3190f090501022203030c0809060d0e0708070e0105030706230a0f080f0712051e1009060806070509090c04120507060f1704140708102c0a0312 63
    0x1045080a912000344a019401400c840c1c1e0380c10300da8101355500541050900845100240c00720341d07003c903d440401d114000501e000704004102c00c0c07610325010400c0d8100c8082c5015000e46d6401410248100d950810428016208421903110b0941c0341000180d40c410203405030404211400e05040c45102008076000e001c00031801d60191a4102aa0000c1017440b04d0500e0300c00186224000c03549400a051445000d0302c015960b030045243c181d001030700903120140403402c0204200401d02103814100d14050b000c2d014210008101d50306c3c00c101481568825004a00b1030303040042071000d08c54204080742da040c502600d4000c019038505d0007101b82401194002040e880b2680c200380204000400c0c4c9206440107900c0703585a407006500d0860350061000600c480c101c04507008031f008907940503d00d0454541035400c455540f0f1f00c0380d049a04001300c41c0d80310302c8115102d0303007030240a0850080500050000d41d1442d810181c040302a159511400d1002400b8840014201c100f11012a00310752 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 221484127 1250 221482877 221482901
    0x60a03061205010b0a0605030402010804030c020303160c050f04020a0504030b04080d020c0a0303050a0e120913110403030e010503060d02040f090b09030c21030105060d0f06141906050319 82
    0x180e041d180c07420b05601034202c40d000c880c400c003208070021441d10301840c240c0b400307543c060f9a61f1401da92580c2d42035594400a00d4140d07410f1006201078200d00310307001485d8581ca032081c49400061450030f408e014400b402e10351080e20550052000b40c503415070200641c0c0449401c802e6a8034183c685003001009446041015080203000081d0a04c05520004403509090b00c03a030f404006940d9410008000c0710f17010034134140a40c0141c2060703149010520f014000b40e103402055126140140d6801c0f0003119441716840ba090340c40824104240358002130441100c48080c2049482e526160300090b14a03020100c009215594440786005d241a041d800455072030303402030050100303041c007c80c410b540344c1000312001c50354441c40d0340b001c41445c2007881c5040004d070101002e5065908110412610b5046400d0040038207554004400c500b03503070b034010003004008003400340c103050001c0b01c144050a0101d440c0c201da62003442008001056100048079840b40011580d0300e00c900c2e008010b207024101c1c0c06c0c042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 221485377 1250 221484127 221484149
    0x102070806360712021c12120212010e070f050a0f0c0f0212011d0312041e0f030e0a0902120a0213180b030c010f120507030e151503071202060a0306 65
    0x1044c0c80340314201c0021010700803901c034105410401812689000e88090081c00e82c0743c603141c0f03240000d000f210700b411064042032000d4205a0000b29521405600360b002c1c000d6400318409000c641c1e900040c2c240800e1b041403038030311b01d0328081400c00f40800c280c50229004100309141c10034144480142c10103030250b030040010154958605200303002c1e1040038410360183c1007001140e0700000000084075040d030071100b01c10880303513699240e107640f4803052084100440e5a0304060300000f01a030440301010391003500c9482a600741c01c401e1084803c8240c2118184501c1044078034034034000c1648040d44000a4280560303940401120714002450b2030340f04400114412200310400e510682082401d120140c00300e920408002004541440030740c0700940202e00301d80d4144196085580091b540500c3c0c0b4113003c214642036080c0c59141545d03031122004400c004005002c1c400c001c600e580c10700c0d844224010002c0d6401d110580d01c1580c2510300082c0f181d8000114030f951603000e0b8210300001c10a210340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 221486627 1250 221485377 221485379
    0x610050f0a0306060807090e0a050c0408030706060806070906020c0d02281d01030308190b0d030c020405060301061424030702070602071203050d0207050106050910030201020708063607 81
    0x406006001e013401858049024000000c0d02288106000407c070b8808142400c19502e402515400a003000b0b460090070281c20000420059420070051444070b1182c0c10006006250a0b00036007850b9010f02227004100740d031141000b10b9075000600031540d050803152486070003281e00c00200000c45c01410400070180c1d03c0703100c410a182c0d95074807604071440180c1603000440b43c0c440740c92100f80e007404010081204100400c04014054140c400c0a80c4200c50000d560074428002135411545880224001340d501c281c1d81045081501490f6081303807040d8001d00c0302604000114101c00c0c0d6088603d405529505840020302c024103615189540380c2a200c141e69080c000c500035101c11407401800c0c0580b00d0010009038801d400d04a0f028000d4040c0d41e02414486c03003440840c083e40c0101404d842c95900da01c0003240f16a03454805038011200702004060840c65480060b0401100b58415502c942080c020894102c49402c803210000e150000000030000400f01c03808164015007038107825030711403410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 221487877 1250 221486627 221486647
    0x61d0a05091c030b13200c070b0f09120705130c05130e0103030207150815040905150907092a0207030b0f07080a09020f0f0d1a04030f0c0b0610050f 65
    0x110907442d42e4030540d00b54514405818810060383d1840305510685640c40f2120f03103001b0100c4000c0c124501d808400d540380b0a503200048696a08244004415107000040b0103402d1701c1e007109a40e1031412244003070205c0d02e190200080c02c0400581030280c9541d00c4801c158000313440713a4101e52601c200000c090154a032112108140c0742800d0000300c0151107001e001164440d030150700240c3c40e118aa503030a000759500c0500b402001100400690402c0d11500c1b5900022814814501c51010711480900546804503140746012100c0c0e2242c00aa03240c10200d11740c0d159412580500c56102c0011084c0342c001a00c412441c050156101801a1015500b88100e0b06800c0c02c0007400f03a07985a030380907410740b56038520030211415080029402a41c00c1030002040c200710100e10100034005002140d440c0040d101c1820385504001172464000c2e660042000b0960400b101d80f203c0c004929201d02502e02a9807408002140039004900c905607404110030342a1280c012500c0b480f020f40030090726103030880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 221489127 1250 221487877 221487881
    0xe070302090a0e0615070b13060e0f0d0e01051804020c03090307060503040c14010f200a050c030105010902040b0403080c10110a080c16170c030703020d0201061d0a05091c03 76
    0x44d641d01d20a00f03411948001061244081c0d440a030303000114003800341c82e03100d84500d400c1e084900c120341d640c2d19003040c68204442441168550300c0036001904048a04101c0109504440d202e460705026080c00b101c1003184010b92404c102d00d00035240181d40350300d4402c5442c9180180c024031503040c42a0364003c00e10640c45000f03180100e01c116070b5064800d84441e0303103114020700e02c1034090014605084480c3c54a1065010880c054010400300408034810800076040030446c1030b080e500d1764400d00d5110314070f00302445420300400356030794114101030410100b031199100e540f00140c1159804580e001c0400818403000c046400521406c104111458903554070581090301120040f500c20000500d07888541c40c00c07500c2c980c1030704450b8406803000759200c4804236241280d0f170125030414080c108806004000418034180203400628070462108002270a60f040c40e0041c4042031140d21400f410141014142904000451408103150343c40c02d0b00c0341d141030800030144141561150761206a15016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 221490377 1250 221489127 221489131
    0xf0305150621010b0a080f1806010b070209010918150b03070f05041401150507052508060109110a08060102160306020a1b080313021305010b0306040c0201090c0e070302090a0e 77
    0x45607018540c1d82e620810303031802c5e01070301d102007001c2055000014001d001c400b07410f40d0f10483d070301540150000754042c0340d451314800360011801030307100241c20300540c1b0380b102c84180140a450300178042c0d646c15803650390071070a8021004004d00c0803a82c80c0141c0340c029400c04007054001804441402d590350219187c801540d11920f03001d80c1c944624400d400b0000c0110b18180d0340808100399481240003400c4890ba48800002d94050148004c0d5641c01c1103407803590580c020052403001c0c0098103240419080410690103500e41030300d080c006804104107282902c1800307580741400c0d24683e82d014010307420001101d0a20810f101c1e0a1000f0080109990103060520480d030307200c0d80309807100801c0b080c402103007a002421500c42070000034241004030041005842c80038060b850641480c80c642000d031072003038104056405011041240508051107509890f08181c4024089009640c44108680c4034a000c1e5081e0300c00100700080646000360100d8051540c00791484108a0f502d0719030420070b0f401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 221491627 1250 221490377 221490427
    0x11109130506181e0a050712051b0c0309030304090504050d0f14130506030405071e0302010e0402030a09020d06020403330b041b020109060c08160e1c03020d020d0207060f03051506 79
    0x40e01000703070018540318951180944400ac0780600706005201c00c1980c02c1907450b40d0b0580710801c903000c41074070240042c000604643c20007003030390b04103031078224100f0050351030b02400c20003a50142500660b10070700400d8400d581c0d5506a90354801e01c240c041203903000b80c0005c1e07001300c000030500c0200100003c02c10202e524941041100748180f169660100a16100c064001081562030b1103070f5103007603070055401c140750f50000074000646034040307981412030000540c0c1c82680030a003082408240c032a1201c41040c00310080340842034200c1981078456407454059411542d82d00b0242c42c503180c544c0007090403055030342c00c6507603003008e411300030701800c0f000c60210340381c0c1c0c1400380741511180100a0a0f0103500da51204ca0341960f106141142da04d4109180b455100c02241c1403c035507e240168490032090095001d00104020b030040607180281984003c0304540c8071000030002c441d80704c0218801e0120b986000304a075280c40e40344442c26140100c4140d40032100142d90307800c010400a4051070018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 221492877 1250 221491627 221491637
    0x14161e051b0606060f0c07090617010609050609070e0102011d250303050f0a03061a0408010c020a05031b030c030a02061f030b040303020318011109130506181e0a0507 73
    0x103040400781d500c402040e2400c80c0c00c01c00500024001145600107460b05000c20000c56101559130f200b00c1007915419071080440010840048590900a004120182c800c4110a200c141070800100300c14140003030070b1000700821400b00c103016a03c02e402400214410000c2e080d0380b0000603031807076115009107003244204c4903062004004501841502e5040726015140d5608100c40f009201d9075590040182408040e9104c2d008101109810306c81b0100d1800b2000b256212801c204640742101c03140c0d8007800a6500c49621003000402c0002203c0b101c00c03001040020356800d4404080c6140100910301e10319000c0032480c0e04070207600003042813069024100d02d0500304082c1c0a506008105c601014140500200000f00400d010b0340085400103000215a4040010b4103600b07821219a96052029200300003565070040c5002c0140f4019550341000411650a0003000604e410034074588900f0010300036000514101e01503201c00e1120031265114050900d0039481040c007d10003160301ca00860 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 221494127 1250 221492877 221492917
    0x8160b07030e0703050c06130b07050a03090506131701060b03090312061c0303021305060a2321060102030f071110050705030901120608010f1a030114161e05 69
    0x30700700080312000c8a82200c003800915032131b1800c5c0b24442d1300c030b03200314440807402880c00101c0310040d400030007140d805900075010070411890b000340710341b415520040c8183c42c00c0c010b1070410051941000c00305e0b00b00b400301d00e00d03600503090482d0241406520296242c40d010007008404200840240290b4541c103c500700c03999141c0042004050440f110000d6128001030402d0019020707074001d00007542c0d6480944d0940d81c3c1c1e00d000134615842032503001c0014102c100e8890b401c841d003083e140b401c070079202806414480000d910400c50b0903949640009009400c0100f201c9900a10880e241d50403850035460343e81010782004d200c1c09400400040c01407800400c061030b20743c030940944181c0e5511001452030000c40c0d000450304041004002c580059440344001600c681c00d00c00c04020600e1440d01045002d28401c03004e0080350003d0310380b4001d9043c469500b10f8002c0350340a060340031000a24942c0000b0403c102241d0302030040c03c4042241c2c801d050101c3e1403c3e00034001c0c001d54a032844c130401c1d06c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 221495377 1250 221494127 221494151
    0xa09080708060c070809040b10030e0708010b0f01030b04020706020310080609031c050403090f06030b010305010f03030801030b180d090e060a0f17011b030624020601030f08160b0703 80
    0x60402103541282209080c01410f00185d59840204529400140041056a52180011074030701c1c18030b6232100071a42d03c15428008074018840f0000924002d4020003a8130300080128051442c0c585e00c0078101580d4135400c00c2c40395030303917810350f008141c10100071500c82c07038031001012246050f0302620405224503800600282000000c544100d01e0f58100c103400b0801250800380686070250044052128600b00840c01d00c91140246004103860307680811004203040c0058201c1e50b041c2c1213071490520a400500c0801d80008189045035405000105980d503244030031504143c0038121001240520301c1a00284d03648503504d0020b6800c03010620246880e8001085030052852103545042e180d198020080c24039905400200e40b0b4030b0000100700304e15181c84071f0a40c0d01058041c03a01103030f42d0342018449099080fa00280b01d01c01711201c003645a08508006e99148014132000b4101c1035811082c50410204030240c0f4085840c8030210404840c5a1402d80b17140c0208981c0540000d10342001983e034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 221496627 1250 221495377 221495383
    0x6061b0111071b0b04050f0d02030d08160504030221210405040614091605091801060801050d0c1a04090c0914030a02010503040f020a05030a031715130b010e03030a09080708 76
    0xc8804c0880c0d2140342c50f00d0001800303d010300080303001e82d000000106150141e10103108aa401c1601c0d03903a4141c1d2458245040400305560000a40401000380424001611007840890b042c0101c040c030040380c00301006c0400d00e8240041082c1c2840d0650951145403080c9940141043d20320840341804419191300c0c40703034070350380042c10900e500c1081000400c040d4081407005242c00c041c3c0c0c0c42c1c0245000b4000002c600c8601d0201e080c100c0301c88600e00100041075011400301e02401c030881344202d2104d011b480c1da41c000c0b101d6006459461aa444902c400e0222040032203000340010741c01800a400d1010010344001110310035100c02c610000041c460342d01d00800c41d0711203103038143c4441341591142d07204e512484288020880e086203880f4000300d61741ea07041044068a500c203030380b203032042005a41c0100c507204c0040c1c0b502100c054001200d40540d0740380c113041d07001a052640002140303604440100c0e00400340e10003164050000041d0250401d501400c0242a0f8615408840c001c03a81c401c41156 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 221497877 1250 221496627 221496629
    0x20105071d010807200a02040e010504030f1d0915010801061b031206080102040806011d011211012a110603010312080a02040f0b03161706061b0111071b 67
    0x100301c04800e103004656000b0600550450300310718001d1160301003100c0148081d000b900d0b501e00c0640c07203c10200d04629080c0265400b03680040001e20690600c0c1d9805480d900c0405400c106109000520484090744018100080d0740010300340c00c0e160400c144200c1d041c0740b0035040c0c0c43c0052240f0b800450300324000e41810090180d0002002c0c44003441303840c00c544603001e5a0614004030340359180050b066100340050000340c00c400b00604165490b250720003202c2d40a81030710038000501c00c6c1c0100422000c42e00780784209900110171905103001440102e030780401c440e8518481040740007000142e1007030a80b00e055168842d0100940094982081120a0209100050052010440801c40e25200b445069001008100c01605140e152603050000d00ba070364110304080070000c02082000c1c44800030400b01d9000e60704001180f507442940f43da1842070020300703540c09124000382c06c2c00c5140d031162009242e002c0340e000803c0400340c80102801c940e44550002d5031584400e5507203403c8640b16040f000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 221499127 1250 221497877 221497907
    0x2040f0b1c0510110c0102070812010906050319030c20010e03061b070201020f03030408121f0504150806100f0e01080607030f0b10030b040f0204060804060510121202010507 76
    0xc003031110141d5010000d413052903060007603c241031003141c1c1050400d0014001040c45440c1c0e8584900c4502d0085003070400c16481690400e0404030108116100800c40494496001034103040840c3c0381e050a4850741101c0d0402428405591240860694442c3e2401c070065401d030784580703107283d00c07008140d40d0342410390b040408c1c0103d4801080a0b0300d550390061890302d2040c01074940f11800c074122613085410843d4141d075083d070b0000b40d080f0b1000610321184d6000c8480c400d066928031445030007504180c1c03180139150103503903107140540c40c1c9180308000300300034540c0000304c80f001d140004150719030103064420450b1200070420081041c15819400e14160783c1640b00408a51351151001c8001e85030030390301e10700b2142d590022503104c2e4861400040a403403076605c2c0030801c00c00314014002141c09002c460381d50f0600c14401801000d500080c00342e0070a4018402040300e45a600403006011000e90201d10300207011500c0d0400c001c04000010fa64810705c0d0001c011303a0340c0d03c0b00103955584105c5006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 221500377 1250 221499127 221499133
    0x7020603060d170307081b04060e090403180303020c190501080f13120509010207050303030c0f21090d03060f0f0b0d0e030a2d092102040f0b1c05 64
    0x41c04505254505250351402a0101415a086442508240c1d40151180000151060100503a4002c40071340030901020355007005241518041c0024880380e5480002e521500c0c0c00302c007050038036100c0d010f0425034010644603032400964900e0701a41e46e40990360f00349d00422a103080f1a082151480e020000c9400c10307154405c003941e40b030b072883c0283c2c2d80c018000f18103002040d201c030022444150303410409001e213480b00c6175207903030503000a071403c0050380c0254460f500401c10026600c1e0840240d031000c81070314240d42d071030b030100d102c90455441a400c008200720075440c0801042601c00504004000d11640302084040d444020440d82c0030310303074002c0c510595248a01007060601c0540100034980981c4c200044200510b010b01c1c0c20751740900307140000291010f4050114100f50842402c00d0614500800d0f2150201c0303101400407000c1c0d208010009a94983d5505400000000c1ca110a6402401081910394001c0e0910091681c0c0d40740d40d0041691064500c5c200f801451192401d0f40c0000003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 221501627 1250 221500377 221500381
    0x2010b0a050f01050a0201150e1806040c150e1201091e02010f050904180c2d0504150f12110d11100903020a0b0309010b150d2309010c031107020603 65
    0x19503803a40001d17404400c640da075814000d2074150111428000c1c00e481041500182000010104003c2980391396048580105041c00001002c1d460041c0480340e4810f044000c417004d4840c240c48a11090090941020148803408a440c0040d4040c0700c01c94841c50811800202405003120301402e05800280032414918449900902034400f4040c0c0d0000180042403080308c4040c59070346804c0a1a0440b00321000300d07418400441c41c10b0807601c00c5160422900750001c1e803810716141d4140349119441c0266036a0b03d081c001c009440d803142c0081c10f40c2c0180102120340e02c440d50740c8500c0404102b5168500c1100c020340c1c051030f2a020f2002601d0304001145074000e4110f0070000900302801403501813009c05200000161140c3c90a00010400328045030b13107920b0146001c60a5810500010b486007141a031116409060342044c0d60214002e50000a240c00160729041c10306810310359080c81700301c1c40714100040c0c8001500003d64819141d5400d20160038039081d100b4a030300401500960004080c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 221502877 1250 221501627 221501629
    0x60709151209060b031c02060618060907020f06090a031202030f040308062101150e0603030a081e040f0201120b0d2d03080f010509010f06080a0b041b02010b0a050f 72
    0x40c1540500a5100003202600900060728140861100d907504046c21600c0c050b0319501444140d0344101c0c00d5411007040d00213500003c107034060040400c1d21612465022130150740c401c0102404811084003114202d08003042c0c0d01c0e560b8503160001f00c0004103035038038079616024580252402482e00c005203821a890300d0394180e4002500800c40d0f6040b081110f940304402c041d5002e00a00d003501000000348090316100c1403411021603400a804002c40402408200d1f00d0000c01c4440c50001403400900c0d540750100f10043c08009010594900311040d400d02003405060b01c0c1844446200b43c03100c000a0001c4c5d11b41d1000d5841800d0705940c00300c40000c4080129a0300903c0f080000340c081c0e9560030586035003142c03980c000303020030f01a00003071481801c001501e0f00d2402603501618048036050785039817501c5010110201c2500540e800c0101c0680841c002d5080c540103140e00030341c0200180003141c1d0042418003082941d459950066080030210344480c1410032092003550b50140460182004c01c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 221504127 1250 221502877 221502881
    0xa0f05041806150617060102070501052226010e120f040b0304060605030f07080606060d0b03060708100e04110103020f120109020a0305150d020f01020c09090607091512 74
    0x28003003121070303034103803042800040c0288114604030068200390003d803403d00d5001881c015109910b05420000c03007040c06000d0ba0000361000455400f407070541c0d13032056285c041303a1007507014026240203103405120100b403001c0c0d04040522240250f5007109044000c0c41031032400c0c0d60034107103030071705d142c2103000d003007410244420040824007500d0721050b00c0c00341d80391103ca0941c1d204603001c0d00c805641d2101441645810312034440304400e4200180400b9045c082410344803240074007094840d103000200b40313070401c005030480c0d20041c1d4018241d4036035151a00d0098802c0800f22010885000c0d40e010101e113507842c00c44414011508500c45840d0301e1102d90041d0000e50103903034180d8401400b0701290f041105140c16442c040d054a00015840303d04103040030b015144040c05000c40c5600342001c01c401ca49401d080000ba075501120b200090502100c010303030500c8800c1e0107090b04170b14000b0402250210001d11203001c0c48081d55148006942c0d45052070311a40c00c07000c0500010001c2980c112540ca041e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 221505377 1250 221504127 221504141
    0xa030e060a0507051b040b030d0504091a03011a010e030a03090909031e0f1e0516080405060a09150203040605070b06040f020c0114010e01050a09090611070b0f01050a0f0504 76
    0x14144140f409810781c441074613010f42c810102c01001c0c0b545034103c101c0d05050203002d45080e0180d0052401070041c02004c2e2050103036004c0ca000340382e80d030503580c5592400350007613810400020700208405d103800804400c040c0700700d143c480c1c041a40b1034001141c5082c0010840107090b01943d0304543d01d4202030314000a0240c0341810f40410602d201d07600c20f42c038a05d200c0c944c154512610703006007080d00694050031680001000c1500b80c2c0710b00449100e4250131004480760848400303c02014806c4900e0708209034001e41c0c00c0720b80c02060200f0568075094105826000343d03100c84c0024002d01d40c002c00100c1e524401d602880c0c0020b01c0034800c000c0080d040006443d000b40b0b00070008900e5918141c2c0d048200e8003c6420011180c2d190314924001030082c60640340074110305010703d4003660410001c180c0b072140a2007100d0350f10340e4449510041c04619401060440f4640c00b84a40c0c07455142840500d00c3c40aa80a20380120103c0c00005c0a2500c9649082210864161000c00500c0c0004010081c81a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 221506627 1250 221505377 221505397
    0x100c031d0a060203030910020a0903111807090f09110a0c03021f06140f03071e03021315060e0306010515090a0608090c040b0607171201030b0f07020a030e06 69
    0x10014010310140c1d14a006200503140e90f600854903403400d550080d25160b40a422114030520402446030016442081c4109803030300615400a003d03103150224401b50f540842020351074821806020114ad80030103002c0880f241000d004032115150300c000422151417644042c80b58404011036180d05009600f0750b040c41c0e0280c0140c900c2c0300d0201c0c0e14005c0760f40540182604a540c1c500090081c0c0001c2801c0030090034080d18144c060021040110740d0b146240e02500121903400155441c0b40707a16404808055540030300404d250300d41440e55031001c1d007141d02c59290242c1c1088c8021484c188521802122080f004006080c83d911700f0060142040f178071000011403103420400310029888160b4100018903455031580018981411150304242500403141c0c4110f04001d0080000d03541e00303007540c000c5600610780c00e01c400d5000384d100e40c451291507500c4004050010000062250031441c1074425402c0007264041540c0300c1388120303103440e40286c00801141655030000e03042c0c107000c4080c00d08000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 221507877 1250 221506627 221506667
    0xf010617162d030f0605060405070f120515060711040e030a08010513110c0618030708030411010e0a0609090f02030606030a0e0f01060f140301020403050316060b0d080702040b100c03 80
    0x62681c81e1303100140681103069030003507103c0c0240590741c202441440c1d40480280b43c401100800c404005140e45203081030b4005040c3c0f06c201151311404007020001541200400310f90b40c9000f640303044020b10305000d506130b104500d800195422841d0110450300ea44070076648413001c43e82003408000c0c0d1001c40203134480c903c0e5910b081c8280c0c20f006007001002c07401e800303070010042840c20890806078030600300302d401105d0b082800040300281c0c10a00742c942066000100a16131074030b10004032030f9807012080895116004510001e041c030380000700101519000380703062102d04042c01868040c1d00c420764116800c505c0800000d5090705e11a884070300d007104e4150699042c0100c0149080c2907450075000402c140989032030800ca0040c10038024154014180c0003503081c2442d549880b5243e00807000d8690030003070328400c0c0f00200540307640841c01005008169aa94804904116103035412120b4102d000d42e1800501c00014900a003002800c0b81c0706554084014680da1b404454100c1d280c081c2c1080380d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 221509127 1250 221507877 221507879
    0xa05090a0e090105151003050901180813050a030804050409030903022d043b060a0b0405070908030901030917030c0319090b01050609030f010617162d 66
    0xa034555a2103401001d10303810340466030a19071029403c503800604640b1580c1e02002c074407080fa0700c0e085443c07600d18041b8140044c26039600038459015001600b0002c0d2080000d152190803c0410001b0f0311072540200c1e070103201252aa018480041e000b4013001e4003203403080c00200503030300d040d400042c0d90303038403d242c1001c02c03d0b038a502182030b480d035650003c00340400701000a025206021440444203400700c1d814010310f042042d04c82810703552200001c80b00118020a0686921290054a0303015201c1d012203d0303a18020349260700600c56800c1280c450b0f414100032032440c2d0300c40c4420707209072030300c0314090761401d828100150000d000504040b40c0340701c0602c0000ca01000070320041c5105001c105800ca589180002c9020702916030440d0b80c6502d5484d0503458000300302c2443d400c42c1911816076150755a2004900082e04d1b0a1044590f1000ea40c00c000c030205020112840c1071034940c0090048504901884919041000b824002d601e610010b108030a01041e070018901000715242d501c2c410441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 221510377 1250 221509127 221509129
    0x80d120914060103060204090c0503010b1621020106060305070c0201080703050709080a0807030813081614010f150f0815040206040b040e01050f090f070e030304080d0c1a070c080a0509 81
    0x400380c00d84c401c2e5002d5038040380030004e100c4140289003001b2a9860014590340c10800b2605260042150400c84c429150500c4e104102a140c003104901c120040130142e203500c0c50700000c4c0606618007030310340003a0520012030300f054050180340e820903a05031030b2402c05560350700c0c0440c000e18000b0160010401c0603c0c2c0040d40b510240b0205400c02e0082920654a5030b450501404008026042c4c03d11030301001140c1700801e1048058980a12203a090180c00d032a00381024402e1404107074951010f5483c5c004104076808a50740014040c0710850195250b0070303642e54905030302504601c01d014854018141c17942c518898009074581c414401000039003011344a0606046513040781d0072031190500204010721141c0303040e407000c0013143c0040b6010313030702854001100c0c40c1001018001d0b90602607204100b5080740d8051040e81d029022140c00c9940d641d0018400034108403181c070040d91807103c0b424480544c2032401461500c81e01c425100d00f40117480b1382c0d460134480e1344590b034001c003086410700041e902 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 221511627 1250 221510377 221510383
    0x2070201020a14160b07050c030c0a0312140309010b0a141c021903080a110a170306180c09040509010e06010506030a06030606090203180a1e060213061701080d120914 73
    0x90030441116030b884010515015190204403c952340c481d034854a1140229601c0d01c4c1014140c035400601c000400405e00004d4910211240203046007a03408006c000d14804154480c104214003240c2c0c03074100a9031000c104d1103a141c5203100540061414030048410781a0b41c4c800600d0f02d01c09854240d00c1d424440f041107000c032507600200e07011400000c6040740030f9444610b10544944400140407126125601c144104904000402150340701000149a6586d6980d41000c0310600c210b440d1094a040f08403a4031507071001d00f11030701c254070b0300c0003155040805108400c1002c04020041c00c0503400c0408201c80c503000240901545600c80402000182442c0a84001000c1182d005030312810700c002041041040c2c1049850701c0c1e4407000c040008104211448490342d4501d55115220b000e490a08074068030036519807400e00307181d00c24000394090340416200606028144480780c1a6201e070040740c6c88001242441c0e0001d014504615007400c031031741c05000e45c24404c06020360401c14042007182 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 221512877 1250 221511627 221511629
    0xf2107080103051608100f1b020f011109090103030503041515050a1d0109020d02070609051608030a02030403110607060c02060a050c09130213030c0b070507050402070201020a1416 79
    0x86924004108000c0104210040180d580100251031400c140d5400c3d500c0d01d90103406c05145407941003c0072000d205610001c030005c410b40078050054082a000307541c641142a074081903600c0c0c0300c030609020341c0400559403001c2004207204400d910315181143d01c0c6c2c2003c0c0041e2000c114400010007010103c0c0b0841040400702c4c800c400429203400708009610803175600c04031840142401d07044881c2d040e10407070f506560105000607158440598032000a008111000b06407030302d820301c900240040007403a0a01e901c00040e282c5001070301c603036010b80caa0041c23494001c056807060100b03100142907001c9072000c02d28050541c50400056450b60010340c0d200c100b0307800c0942c101e04c060040341170f41030182d1540b21441030440d42c50b00304d10f02c0200701c01ca0040200b1070803095020420200402007001414005e5810000318224951200da080940d5400410119041d02c200000096141001d0081c2c40100da0143c0140100e82e03843d072105d1100820400c03003038120340500c8618890a20034980804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 221514127 1250 221512877 221512891
    0x1020316081b100c03090b0601081506070503090405100506030a0b010e0406240306080c0904080d05180c18010b07060b12010209040e0f1c1b0f03021b060f21 69
    0x40b03441c890000710f907011100d400c1003a10406090642d6507000c07901c003811054110000386042e00ea00d41c1d54540b01400b042000c600c003640024000b600c2420303c14000090059410121010070407a100e5000c65020300304584076a6802202c2400001c5903001240c0c0b02040801060401c0020403441c1d07000901101c0c141e8011039400702850509800e401905214403c0d03001c5070b42801c01c00c640c141011a40d4400100c400144120994000181007103240c02c2070f5002c00150713000900860a002c14076401051096260f50300b5445202000482c1b0326020f5100c01050443c1018464283d09000030044180d2011000781e62254441c0069102615800c8480850480b80400103888030144810002901c5101d551001c0700da004030b400c065000d00104001004001c8420315580000303ca140580d480f0f00c05240d4003004004081c0d003001400f07104000314000307500c21b80c01e90740c0e1682e04500c1032080d40608441c03550402002d01040308c0e0000c8190040150801001c10503c9545401034420b0300c41d00104d03160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 221515377 1250 221514127 221514133
    0x8011815060c0506152202161101020d020106060f030b0d050604060b0f0604260a060504031e020313031509080409021b0a050c0d020a08060403020706091401020316081b 74
    0x2d009110301807111541107031a054110780c003102440c0005e24543c146003144140c3c03501d031a800c45850803c540c1160303882c00b005901000c800c242820518404070b010015540940194182c441250b44184142015100c640e29001d41a0309800c904030b0040041c418170301d4001c1242010f14012903130420201e8480e520940000c210018101e040c00b01c500e0082403000e00485052200348104a00202c418120003502c255113180c4c45854141b4520380340400001501032840d1000380400d01d917109400e0444200300b0410b0b03005080c682e48049a41e403003030a05104c0790000e180d200744001080d6404034803003c4042403005c140170b00305444280260380a40d1200c103c542c1d000454192120031000d4421840070f03140c000d480c04c003072142c640720348030042820624410205100440110340d1071811800c040c0c440c01046480f286010f1a010755200410b00407030001c0340300207100003440d03100195280603e64040c2e0140d81844060240381078030400c1c1810444100e1000d010b5012516980c58403059100104401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 221516627 1250 221515377 221515397
    0xe0306090c0a06030c080112030905060d0f0c090821130b0405040b090108060c0d150311030c1e06070602090d08070b0601030903090b03100306111e0301060801181506 73
    0x801918202d0380d440340081c0750820129680b040c1c0c220b8803860440e50b401000034284500340c601119680041d42155500450106240361010101c0e4400d810311030804400300485001d5420585505100b0722404560b0350007040001181d4240401546030b482c81501882d0030701905c0040750700c1480098020115600e004581040146007602641241c15400d94009180d941010881501c03902c0c0200f05e41101a40080c00e440741c800d50b544482401140b548051000341e44900d0004019117400903028400e209508000e80d1a141c01229420786405611180c0180c0107510148150f41c1c0124405850080c0d09004c08141c0e502c1c2c24a051216900c1141815680e80031032812016051028184a041500d8441454002a0400e81c14002c1d03a40290034a5141d13510f807410520b890b000354100130119403d12403d04409404071000c1c21102610441d50b4110189078010f84220380401d100e1180020621401000603609422403081111b40f48500890484100850310b21040e15a510900000340c11400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 221517877 1250 221516627 221516629
    0xe03030c010902010e091608090a2f03120306010c02130501030c030209010902040e06010e0d05010c030518011e20030907140301020922060e01171225030e0306090c 72
    0x178443c64402c0c01141c600c0d600c0e080c0307459490140c03048881508140b1289001083d1484d0042010f1001c0c40d07070001d51060600144803106c0601c9402d110308401d0030116440d500101c2c40c012440100480d0203803000c50440da02d04004443d02d5003000c0c0180d070003006068194070311070b05a000740c40c00703940034510b0310080c02d28520500c0a1032405030b224017982403040c0400d100280300400780700d030040d1003481d04031034032032001000501d0100002e00051017580391141c0c0d440c1d2560950002d0344142d6103042903820544154103064240c070300480320701501400c0405e0f501922661684481c8000c48030201909a04045001e0001f8a81c41aa80100030380d00244041040080a0700540b0380c800e000c3c0c00a40c2048603503c0880c3e51610700158035914002070b186183e501d14142d52000b8004c00c00881c4800465949800550899645040340d22082c041e29030450a0011f80070304481c1d5a19083c120704400315031955407080c180b0510401241000005000590b282d9010003005000c1e0204001030018286610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 221519127 1250 221517877 221517887
    0xe04060305030a02240c0702040204230307121a0901022a0705010c02060a08090c04111801030204030b010b0702030a060f0e0114240f1012230105060a0e03030c01090201 74
    0x1440c10f44102501d100403010445a17481c9141c2110300641c20035203035481403001a01034000e80c1c010100c05810f12007030844c8561400c003520181003098060760f1001e071321243c810380134005401e0084e044501d2290151007440c0c002046644c4800b40000041c20001040d6800607004030882c03460b00500000500c40044120501005006090174202801c4c00e03400f0798089a103a002d50180c44050208200016100314810b20201001002c0144100715108001990310a1500031b2543d000c261103901040045a502074070032a4142d0780c11150100c501d078a0b080050030554891041240c15000b1090160002807950003140038102c24558003040d4000c0070010300b4211070a00701203800c10503d9909120340b01003400000030f281c0100b52907a01c070343e80075040030800c02d00100c82000d42184009241525040d40201c81d040030b080114010700100c0e540012500b001d011042d4410384a22890300100a81c0c64103200903d0361600e141001e03000d400c5100c0002e070654100172000da2040c2d444903041421580d003d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 221520377 1250 221519127 221519143
    0x20c030406140301060f050703021c020f010e0607080103120c080d0509010506091513181b06020319050a021e010213080307080a030e100c030c080105011e030c0e04060305030a02 78
    0x360a07000c0c2550301d0494001c0c050500400006c06010300090711109140c800d02c2034140300410390241503a03031100544002d50751804800c442c101540b8107800380c8030314080031403100d00aa00940d500d01281e400e5032030722090000407480070802e0000f550014000a06e5500c090112910742000000e081e01d820004942074500c0241114806c40c006402c0060b4007120441000d1100350075521510000c140c040e8142c000c162029491206541421501c1c08000300c0358a41c000c504840500c010103281d9504099a481c0255031400f10649020150000b100e4410409013000c840c1038812130358040054070a6420304c44070303059512140d035000613100e0651245c950b203550003000054011031130030b80c1503201c6103001d008055406c0b04054491100c10410b000401c10120b60880b944801c1104030200f00020b80107040c1d050340d010105010100008042d80144894146000c0188800701d850310415800c900400c111010f0005003ca901e03811030a070344035171150700301851040300299a074030400f0381c01070718013654 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 221521627 1250 221520377 221520407
    0x11060c0d0c0824060706020f0c1501361505040c1d040b0312030901050105010305070912110a080d020114060a260c0607060902151306080a0f020c030406 67
    0xe0803060140c1000122510003c40f10b8060619a040b115207001030181d128011026210758004146034414501590040180003511401c5454809610880c0c0d21030603070920417002a0030810380300c11801002e1401e1350480c2c0c0821100c5a5503c06545002030491340c5031001079406e10b500380740512203810303e0301c60b1564000d0700d820b242144948580314096940c0a02d40f080e401a5103400c50345090340c07400c000000a00e400011459182c2ca04800c0c114003d100912919000908000c00308002e0b50152a00c0d0f000d45800d801c41c941c02c287c20b030721400004101100309507040240801c001a4401c0103100010001c11168004100e40e8803c4940c0705c2c41c0e280103020107102c4e1307103418000c108001a1403505010449800042003031a815000c200c0c1c2001d400c03030302841d00500c001500204010082d4402c9260a200b21395003040a41003287d80586d41c00354181c07000c00d01c4440321090107017601030140c80394058808032001c143c0d42006028a0300703a81240c4041c920543c000326042c44800c1c1c000f06031480501c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 221522877 1250 221521627 221521637
    0x1211100504080c0f030703050a0b0a1b08130f0b0a02040608100506040e0901020f041410030504020105090d0f080c160902090306041203090c0308031902070c030201050a11060c0d0c 79
    0x10500c1c0d109a107440301060101d1061302c00c44101060383c0c400340034480003150460b06840f5840c6560a24a0401c0307411580d50320507070301d01302c64420035000300303800700c1d4130082d4aa44851191ba01d141c0000201c014200e02510a421110f0380d800004aa00b20341744d00c41c0f4514400503807a5413501030080d00b000001f80010b6548000d5590510050301c400055804540d9144041035854441e40196402403090940010800d04000ba0204050101200000c1d83c90400d41c0d400c0248640e101048080b0745050380c000380065010404089140382020021068500075045101348441ea82c0d038483c81c0b503200d408030b010180c0040c660000c0c40d0b0310000d0010f00500a04805600d0414800002910f45000a200030300720325500c6000d0b24414440d40c00a51506d44c8a620034082980b641031901e140d0304101c881d03100640c03014507905901081c9009981c22079600c461141000c0f8115401500c1c240c1150310003000300502820b5100210b8405c0121502407150f1109055071510744403414800d0303860003124001402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 221524127 1250 221522877 221522879
    0x1609060e06161403130e0106180e1810050703060b0a0801090203070504050607030908060a0b0d060218060a0309020f010c151d0d050904050a05011a07030201061211100504 75
    0x1c1c480380112150700b5448145050760000e03920b4803014400746440441d18a00c8041401c00c501e24a409021054405151141c4d106aa07200011140c0640108000e43c886c1251081082880d15000f4125040540b0f001441c072052a050407113441e1032800b0f45400d00c200d40300d60a1100164151103254007410000c1030940c50310f103550001502c1d0301c40600c100c4444960003c0060007082c820420f80e009810014a0700ba030711540c13801c0051002843c7d0052042e94025800851510300c40752044d004038200151890040700da260b20b80c80001c0d0810f0035014000c034800c5d680c454059072240002c0000405035200080c6c1c08500e801444404055a1540c0c0c1c18071982011020206101c901600d48080311002c010038101c17007140701820202050340b09103040c0c1c4104d40c010b03c8140d40000107030030f8411056400301701c280d0b203007118002610000e00c0741c0004e200400041c0200215444014144240640000300305142c0c0d0b4400502c003884e04071402c0d0740d0980c4c5500c0b101010700e05010340c80c000303030214078000e4201 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 221525377 1250 221524127 221524129
    0x3020c06340b0c03100e0702010e150709030b060f0901030f050f01090213050720032d19050408060a02030a0f0c140a0210020c0a03120c080103020f030a0b1609060e 72
    0x9900068800f070510740d004400521710800c4000300340040c04180c01101c1c01410301d010083c2c040c0c0300750041c400003070144480103180c1d4640507030030501c513100c00d0b51840348442c9191504c1d821248090551a0003032a99240441d00362101e8001600030f521a18000030700f80501e041c00e600b001c07899507000301c1d5a41004e8020000d41d94803c100c00700340e40103c0000174903464032403041d54070042910290b41c5450242c0c0c0038040c014008409840d03c0c901e450b13116000300e4540c010301d4410380d41d60280740710794103003d104520380581c420703004400640b01030410914054450041c94501001128005101c40d00042040580255401420810726030356400b0711440c50019400380408019114084c92079030041400c5003c40d10801c20b510058446542c1196034bd08440303440c6440354070105081d00850180c04603044020042d200c0d00360303040701079503c1f101c20380d003035038200071041c0c543d0385a8035810b10661140c02c001c030358080081ca000b050388a10b400d006510a55014018541c540d000500b03001407241801c510b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 221526627 1250 221525377 221525393
    0x109111507030c02151c0608070f0b0d1104030c08030403061103091f090f06090219030302030405060d0207050d080f060d0c050d02041b0512150d0f03020c0634 70
    0x605504490900c128085d02072107030b440f40104a80c0ca00b08451960b9980714101866100f64269010304055440e040d03100c0c50184c004006030711415245250410545204901030f81c0030440c001c1110603807a2900da0749403199202201c59402003400c07900000780c1001001442c1c4030340d041454280c540581145010381040f03450f040c10302e000c41c580e40704041095046c030580d94800c141c0503500a0344002c04070f5283c10900d00070502000704a020300710203140c00c007030046001100b5080700d51543c011860241810306100e115040b0105117043c45400b0710032140040c109200101c01c1068079503821189250024082004d010f01600744d5009015900140011440c51349002e4103503075054405a01a04d034a201240040c81900c2d4480300452100c1c0c1e056a080d64013100404440d69052102c10701503c42000c2d80c1140b07031914515550040c41d18414038005030080c01c02c3c4100034004c1c01a01d01484981c00070030a994807620300b591010107060341c07140b80c1c00c00030014005d0f0280d11660400024440750f80d4814 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 221527877 1250 221526627 221526647
    0x50301081006180b01030b041107050c0609030a110609040c120f0608100b0a0e010303170702010b100f03060f090c090b0304020a05090c090301110304020906031b041d010911150703 79
    0x1000f15180c02d00c04800e64001c0d001410a8070014104200002c0d10552a4503275820202d4106c42601584809a029160900546a242000501a083d80e03250341d5514007942000c1000907402075070900412020755101c1c810780d011000c0c0354079001411142c0c1d00e070a0048950402160022914000040c0009200021802500c4a80003000121003a007c400501795094580c03100401c11070200c000b2081650040f030001c0b12080c06029060a0b8440c0b0500b0382c03d9a00c03210000740c100e14001d20400c00c103807044010a03032803901c41c10001000d507142e4104204240e0303240c0011607038948400b0750850350b6601c2140740d401400c102941c0c0d070550070305a002440610f01481703128414040302c408503000310207505c12a8040c80008000300074009400d0700040e906d81048138240c3c480c0b01c403580042d412b401d002c52a20910740c2d00c43c207140e916444041c2000300901180740700c50300d425006151090211070074400d4024003800760f020a4030000351002003150031460782d903c0d20100ba1080c45400c0000350800c590364 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 221529127 1250 221527877 221527919
    0x91e0609170a020a0303020c13060b0a052203061b020604080f0a09180c0908030a090b030910111e12150d0614060909010b0102030304060f0b0a06050301081006 70
    0x1002003400404194600b82981c000a036220301c4000d400020140c00040350000c405d003e0fa012520300b0f0340950f04404543e0140701c1c001d000c0c1020804501e02910a10080c80e034140d4410342c00d070b0401c400107041400000d6a4004072804d517901c4694881443c82801101081e480a10090a00d80740c10796400031240601040340d02c5500e800300799802d200d8060620078000c1d200071200c000e0b070305004400400140103580c003104045803025802190282d00402110303c9035081c2c0d11524044d40c60401e1520031303a400101210264015140d0301c4003018568040c8517262500000016202c2c0e03411264a850a0548007003c0255070040060030b1a03031502d0070303246a05c001c144c0c54840341c029440000c29a1100450002404c1030320342000131001c440280c81c0d2a004050613a4084035130380d58035120508a071400c86000b070159000380001400505640c1050340c20011814000c034030a0341b2880400c130b2400d10b0750403250210b0408001030007844410820b030403a070910080c007440618a8035100b041c4444051b148a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 221530377 1250 221529127 221529149
    0x1020c062104050312040312150e060108040303021603090e090303010e1303020a0b07021c020106050312070609021804030f030b0d0821010f052403011e09050403091e0609 75
    0x190030f02000303000b962003202a0020320308281c0303040e2034001c01e0000704c003d2040305507242c1045000500901202d60050b80d03000c84130100c80ba10f955005651402c0e00500c200c0425400700804d0a1241500e50541c035600d101e40c40c0d2a000030700700040c00c08180e2000342505c91079072081c8010000b0840800b211500510010002c03c443c00c00b0f414120704000e600381c009000081c074034007071040086e40010403a003021642c255606d940401c2e00700481c01d0b6012403040c3d0360306601c141a805441d40c5080c00408c085823107440d001410116560108241c01482501004140b14410400c000d043d005107d00220324994a400c00103c0328480005484005200010b410050081503003d001070804042c050300200c8460b0300d0f4141d60b0744010000b0241c0180c010580118991000d144802e048107201a040c540710302a00d509603030031300e00703010302c0c20020f50840c0b1440c1e0b080300400158070741e05118007030045001b50344462002c0c0c00d00d52800e4050b9044c03100322504600c102002c1100d03952181c0742c1310a40d03840c0c01d25 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 221531627 1250 221530377 221530381
    0x80301150e03031b0c03010911010e1f020303100806060a09111605031c110409090203030f133b061219030905150a030519050f040201020c0621 63
    0x840700d01da000d1540c035070907120009140c60342c14551110340e0340c0449040c01311a10021030704241802e82e41c01e6003000f0642c6110301180a003543c000c84844a04180141c426020801e9081c50f0b552191104060000076800000c20700544020310014030014158540041601d4284440800d00940c1d851003100502030307540c06105180382c2d01c18212502659248a1001c1070205410190344030340c80030003030640142108000d2000109580114480b400034501c03401e05081c40c12405101038900e4078012680350000b00000e203402141038000e02004449039060306142420905a290380301c07940e4000540010244486c0031a18804822000740543d0300c250400b600d840389004038940864100e040d46c1c4500034142d03031000803880c20040c0c2c1112400303680c42c100c542e5a66001d10075400c913100342050070150108030302e4030401e010f50001c40c3c05c00c0c00b140c6104507109500c80c054088074010f0310701d00c458100900510007075685c1088142da80802c110b400928010403c0f039000c60712011860000700352801100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 221532877 1250 221531627 221531669
    0x302010e0609030f0f010c0f14030714040806070906110d1206121401060f0e01090c090e04150b03120d0e010b0d08040801050f01030b0a05130c090204140607080301 72
    0x366080d003038000e011100504540b150030340c1c680d179400c00112540c0d881c010340c01880c2e601c00c04210201041d6511076820480c441c05a14103035a00040521050101c503540e882a050781410041c401046013102610607401c21039002481c22040e580100100a40080d2003007005001080045140f001d5041c454603920703000c080c1a000c0d0100c0e502c040c18201003e00d0050a0214142c2582100c000b64002001155103581e1280400b6511b40a41e0021404100c014010543c1a9201c10205606801c252209541c2d510103c8088002140c0c112804040424007000c0c0d0030860040c803484031000ca01400344403210f8a24032129004000300e500d072040d2500701c42c0c1c501e03443c01e40c03040d860303401c0181801c50184c1d420f0500c0740e6140c0c0203114a082540c6400001000c0b40b0303104000c181030b42ea0000c0072900e1a2a03e1000b0b1005c0d1802401c03080e110700c504e1440070f00080456034280000c00c1e46180158031603283c61076504440c03582614a0340940c5042000d40300140c1a81c0c102c90540301c0c01000d03100c0304521b00c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 221534127 1250 221532877 221532889
    0xc0d11010e040e24011205060f04060219050403151a0d020613060306080f060106171f0e01090c050301080a03110a060207060f0606050c0a020918010f0615180302010e 73
    0x74284a00e14000c90111306120412004002c00c040c803030083d410a5030741e0b9200429642640725002074842c0d000503001c946500710a0040319003113805082e0140c10510420717030076400601c10540000105000140030070401c078071402d0481141c0000c2008100842920940c0000180c0c079810044c41211140d600504540e50310040d42c000c00204003558058035202c0304090700400c0c180c0140e40c40d622504881515052000904d40c1c1a111540d81d52052004c10041081c41c2036000740c443c50032035084948002001180028030802410750314442903603945021008130803600140c00300c40400034104014410b00c003002919590143d8589000540003012203c098181408440024241e9000185600c180a00303500030400a195500c002c02c8410303503504080d01c04c0c1c071544402c50144d03004901e84401500e01018520340c0024040d0040700c007401004011401c40703248040c0d040c25956610310501400e820240c41c103040058a050244408800c08041d080749686888003d040120541e1540d6054540d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 221535377 1250 221534127 221534141
    0x40b0c09030f07080318060f04050103150914070305090c030a140f10090c051e09070e030d05130f06080a1a060403060902090606090a0b0f190c03020c0d11010e04 71
    0x80150b50000c0d880c4c050481c1c480c2d0009140110041000c6031800c09881c0c40401c4465903208901c0a9191524050054018003d403c1d6080d2110768080c10010700540f583c004d4a4a01c044818001514a08200042d08554000e04120701985c03181140500f2501e000174550409504a001904400035006a03240b902c0860001410b042c0500300c3e000161540ca5085400158420a0b50704844c44c0c650003804040c810150411031602441d58010203641802d00703010350800b0462915503090243c980119107401c3d07000c02c1c0704c00000c40008180181800700550003010701540e031030180c0e5203480c12100030a0540c000c3d02c825a650394030704105c42103445164110040c8207001e045241c80d51340d40c0c1020300c01842140070a0307000d01c200c2e1000802602d000004c40d004c1080017009001401d0421007a003940350080f21028440313500070011984481900c501008440c074086c0d440440c07442c1c45290090803c0d2144003050b0003070b840000344138009014100592811034080c030300340d80c2ca0340c05100007501500e05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 221536627 1250 221535377 221535403
    0x5090607060e0a05100c1b022d03070e010b1c061203090e0f01051e220e0d0201020703170c0d0501030c09060b090604060503100b03011202090a05040b0c0903 69
    0x40c0c40b603004800c40c00460307a046000c1c020f6050700e41c12105480c01609a802c00d51000b000521141808099140c080c041c0700e44860018010014050004201c00703034840d0b190a000075000780010750100940b80402c80c200252a09500c1c0703400a514201c0c42c240710f80101d8280d95031800c1c4100250a881056500c058001c14880b000c03e40705d90103e0070058a0700f2224003c054403588403c0c0048c2c0104014105181204c10142c202900c0503441810071319140300000c1982d41c85072003504001012a501c4020700d079000007680c070008040c54030030303400740c500f01c0d41401800544e40140145c0c40070075004030b410f4404442c0c00c003c0111130341e03420324260021b10440e00081001da144c840003006210b1080003801c03d80f102141c08100407500c039100c01c220350040740d80c110f500c5001040284002031140c40650340080380030040500c890384a103003442981d007007600a001e550030124450000d615101042c1e07500003504103c1000f15041540398081d41c2c00700240040c2c85284c0c001011000c3da00c0c00c024191003050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 221537877 1250 221536627 221536631
    0x9090a0b070509040e0f0a080a0e03060a0c0e010815060f07150504060e211305060724230c0d1a1203030f13020d0204050f24010f0509060706 62
    0x945010701070000d070040758000740034a20b044000441058000740c03544500400030b00030302c0c038180d156445084d50b500c0b20807281c040215008038180305481c20411140501003510010408240c0c0b06001045641c0b6252100c1c100000a0244442c62130880c4a21820801c2611107940e9601e41600802e424454800b0040249051049221044c802903004a020b6446420248a42000b00d0310050b0340e80d01142140480802480348030190826200045c051a43c048039080600c50742c8500140703151b000000281d41c680ca1507901a0400741e814044494161007803002041035064071030940020380804903094252410140100e80380914220a99400d02d400110034081c8451440c0b6a01021074442e8825000c0c4698404032524158080300766071250344070b824403811543e104000e82c0000906c45009036001010400048090b8903039004142c402c24100301b1074005801d00c0101c18903e40c0c040164540150204020501e580c1c0e4424001300500900c0c1c603245840741d80d0040060545d11480000070729040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 221539127 1250 221537877 221537881
    0x30908040317030906010b0901140304050a0b0108060414030703090b07060f06090f061410080c090301090803060f0d020306071206050901090603050d0519080901020c071413140609090a0b 82
    0x100d1502c02148102d1100c01650304690341c908114080f0700070000a40d01150000d41016140700203040655032080c011011903044a882d52250ba2003558203800442854000ca010001800303281001e041030b118110008525110b22514014810714080c00780c03054002d000549074043c40b00c5030b08405140b100030710301004010355a070f02c0400108031020603070b01e0302820940c000581651101035458040b40c041c000544030403401c6000c444200c002800e28240301e005001612031034a00340319110180b0720480300305503207041450422510311500300c4014454400f40280d14010384010800a40104103420700d03d4904000080c0ca40140c0620b0304030310303004468440005500009034202104a078060416911039407460b41080340c1074441e000b0034200d205618498466258821840503074026101c100042c1440011302c00c0c2410500d0f03a038003000d031112040f03100c0000791519198900c480d140141040005054144140101480051070507101c0c440180000303125801c28421100c2c480e5000c00115014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221540377 1250 221539127 221539163
    0x1d1b121c0f120b060919031208040309080606150a030204171b01050c0714010507052b1701230d0b0a050c0a050d1a030a050609100b0901060309080403 66
    0x14107400e400c0001a4032410030b50641e00503032003a11005100a003429103001464070501034030721106805031400c1d403450800000454004109010b0b4506a0380d81c82c241424281001041d504c51074102ca039154105000f030201c581d44000900d000000482a465100d9011150503070003400385601140c01d0680003030380c0c09224040031464640001e01513030302182244900c00116114081d1801520145d80440070034803501210162040d0305402c14940940317003010a94071a41802500004e640d00400d5594580510650461100c0c2d03240000f80362665128240c81011450000706124408280d1401403907490004001180288510303006018140c0c4c40c00680340170400d5200498030108010314060100765404051012900392607055580c02e0b00b80303a016a4540010300e1000c40f0f1210391940d19000c50500d441c10700c100a5800d0043d0050030152400c046100d04081c04441400d11641c58050190115a6242d4406054410301d181c0041d0305200c52501918600c86c680024040c0c80e0207500640c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221541627 1250 221540377 221540387
    0x506131508041a0603160b0c070b0a02032704020406020709051302130b010e0a12020103050901150303050705030705100204060323010b160606091d1b121c 68
    0x2150411080302030400a03004044400c4941030310010032030250300d960200d82240c4041041c1d0405401003da0340d005180002e00f0300c0107031556100d8404040d002c1400d14002400307000c0744004003540c081d03440c03600f190000000e40360720400130f02e03000c080f4801c100039003803048002a240c1402c0c0c01410442da83e81c1c4070320020750f8583d828424a0821410400094141c2c4904005802c0b42a4007402401e0240f44002d5280003a00d0b06030301f070504000200e40440ca0594440000d180140140c4500140f4595940001001e4501c0141380c4030f000c1e030400d070405041e40c5202d040d401c1280c4e01458003036290089442e1190441c801c01401038140d110b032903135203481130455900400031140c032614100402181e101c079156100100e10000042e1401410042105031550f000400032040310787d1441e5890b100310394844040701c550350011420540d6072400720b201601640c2c1c00e11007948802d00104591404184250040b050348665140207000c166111510380e0000c204000c82041008480d0b114066020b4000301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221542877 1250 221541627 221541629
    0xa060302030d021203010b0c0c1008220f080304150501140a120b06060d020c030316031d06041e1e02040501060302040f12030203040803040306020d0b0f060304110a050613 75
    0x1c46401140b91669029000180c4030a03025481691a07045030b103402c04c8800c041d000b10f031440c5e0450144550724801d5a61b5245c400341d0821a0b5100e10680e0b0901d01e02c1d0f100b42148001c43c0500d1a110b04418102203402002c2800001e94400039455403a640c8d443c1207104441c41108101603103050000104480e05842130540c0350301001e5416020303242e0f079280f680114443c080c1018085881d00e8001c50341a01700300c0002c01140c00044009841d015810000c540742d42d0048940005d41c8413842e0340224000d84c94041d40802c1e0341c801c20000402100041004c0d110702003e04014110305c01c94100010000c40c1c000f03440c40306074000d2140e035107c4040c041100416106140101c0c842c5181030f0010469034028405d490944403004040024a420451620200d180442c001e6080d44401d00c00010440300030802000510310822026807200c44000c086800d481c0d604118501c1140300e8030010041da291a0240d80d440750f0403911014031886890301041b07900e12143c000d5a0440f0000401210740085022190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221544127 1250 221542877 221542879
    0xa06020c071d06100302030c12060a0f06080906090d020616030f020a050c0c0405091902030f07060504030507050405070c020112140a0b0310151e0506042408010506090607060906050a060302 83
    0x1e2013404880302c220b00b00d100071164030020a01c03d01c0f6141d0f603840c5490f2215444000544901342c01034844052150302003460f8080c000180d49402008070101040c88070a82180581d002004c01010304440a9114400181106036103d2001000700101c1d00c2500310344d4070091031400031982e440b0340e600024043c0e403044186c3c40c094400c14103404080d00305841205e1144100f40e0107802240b9988108910b0f042114030141c0c0c0c50b10805189050300d50042c0f16290003440715488280e076940c610310304142080301d943d001d18805c51501c002c202d440da4000341c000070070b0340c0d0900c1c0400005074007041000003080d8003a954000c80494804101c00c080d0315030f100e8100380350220701b194a0403025107002800d03103903620000008204544400c00041c40000c80b2124880d140182c0e81e50015104c40114041e0340044d03200100e46500ca02c40344440f1244200c0324038140c03d181ca0324071140d60505000c59403e103e8141900e0085c440015140b090082561000300d0003540036100388090304001c02e03000081c1901c2d01090b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221545377 1250 221544127 221544139
    0x30f0201030c14031311030f0a0b071e050a030207050a0b061c050c090601051603080a0c0806030604080901111002070203011116110103091b0f0b0c0a06020c071d06 72
    0x200e018014903c0c0c51903650000c183c1841c1d59102c4280b81410364030300c00c084501d40c041d40010b1043d56428018200704030800c00c01800c54000d0740c10310f41c41105024205c1000d00003107410040c1d05403002c07017500c0f81543d0a824000d0f0340c0c840840f0107c00138071a038580500140503c0c0702d0b400070442c0e480221802404102c0d42e00d115120390411b60003954202c00740007081031f4048004209181010001d0680c0042c0505040d0b003484403980c6c000d44a030585510440c0040c1d0344c0410800d0500442c80b0340110301c0c2c03132131510030001e2030030f003000c241d8408001c2e1019110b0600418100c046a200b9240480c6101550054420034a01c43e0b1880000c2e4108403002c078460350074922550201c006200070341c2c0403c0800c00d02c14a100303e503612182c4410fa455003105040545900302040032480d1403844c3c5070303a0303084401d4510b00249070030309044950303185801945c0081d008000c44200c01100007007260308660041030043e13403012650307a10313498440954420300b42c10091140c8040d030021044840c0e40b28102c00c0c5c8076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221546627 1250 221545377 221545391
    0x102030406080f070c020604090c142a07092a170703050a0207020405090a030e09060604030204150e0118060603090b0f06010207050303030c0a03150b0a1413030f020103 74
    0x5986900039070241c03100142c0404006820580c2c0080d600d9004403680c1002210f480729030b00850850362154101070303203507901c0c0c8408001588d401503d0710a0403903000e02c03041c10000d00000a1000d042000200e486a00c0f9000720302c82001c00901241c0700505c840002080340d5860034a00c04c610300c04100c05902c082080e040d0041402c2d01a002184030008128080350541d6200b04083c0c00400e806804065a550300388500801a100c600c2061b010302c0d0000c0040911806a15008048100f500c881c18000c0e8480f405000040d1900e0302a0350540307504580200381469114000c0404a0b515400b0a00c01a0a040001004e00c5c0342d0101c0d02d680507078004288011a01d4102c00d81c165036000400502c902c00c1c14000440ca8400351461907000801481a990310a6072400002e246400544241045401c00110815803581520802c0801e4500b048981c1c64076140c52a1045c3c103003d4901080d061146060b628444110424100c94401c0c04850151307007a5916070900151311440000101c3c0420320300f0702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221547877 1250 221546627 221546629
    0x2a1703030114010c1e0305040920030114060d06030c061404060c03050d0e010c09080c04050c091017010308040e1305070b09030111030903030601090b0f1204020f130b0906 75
    0x821203059504a214416550321448011694804482e5094071044000142212000d80b00ca90090025020b0796401d519039051014640c1241c111001500c8680d07a0001741c0c48100c620003013520f0450f80e29000d140304803c070410104e400c070f224010182d0101c61400c20040100030f0f459a001c4141c400c10ba03a10444a01002d114a0081c41107003c4c42e00402c41c8500c501c0000791182c40104007000c500100840d88600d508031450a6a509122180c0499403840742800340c01002c1050b000d00c450100c406001500703010300300489910421030034501540c0c601d0031060209000c2d000c41d94a510f000a89641c0719079490618180e10380280c060702c88a070040d500400d450400c0400c1c0501503e8000c009002500c0ca001031000d100d611640e00b054141d501c0d25869000b400580002c4c520500c1640c01030340d92860400e00041c4070981a0300040310070a814052240e11040150030790b05c0e0008006261000c980311400041c5a003100100b0320360384404910001c2ca0745040c00e0300800c1101c1402c0c0c0d980041a15200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221549127 1250 221547877 221547883
    0x303160903110609041b0306030203011b0c140111040305160518070c1104020406051c020412140c0402030a0902030c12100b121e100207080f03042a17 66
    0x80720140c550101070741c14040d00d2501400410703000c1d8009100140f0300d500c0101005021420802020100399682810010f5040030300a0114546207a1030588100200c01400790441e40c0b80980a044144402a188404142540000ea159459021040d141c9903285085696a03031a10900184584d02c00d9001500b400c22501c41c000304003911020181641e2608130032602082401801e813205d011038200d44910381c0340c502c01480a4001a551940c0d184010708194600d46c19806407101407901c100410440390950000300403400b0f0344560000c140040c4847d80920300b620190106520071f00c00024403000e01456886080f0f050b100780d05a411540d01442001092481d60910f0029900a0290300c5203400c1c403130380071100a000080114041a860340011072030402c0e2105e8103240c0d032289400315801d407202040204500c0d0401c1c9419441c124090b40e074440180501f060594100308044081010072540004102000440004141701240c1d0301c0d03101c910a1047e07202c1d00391400420710300468004004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221550377 1250 221549127 221549129
    0x60f0f030b1908061008060c030f150909030d060b0301060e150f0a0c06140609060402070f083015041e0e0d090603050919031809020307080a02280c0204050903031609 73
    0x114948505590794813150260700c0c00c000708021094001a407001e11107646000c0528041e0003204002c0d611680c00c4c0fe000022903015030048440d01000348010454103a00426407180ca010581e0009110030321180c22800501540300c110500391030104d1343d43c045d41d80c41107588941c140140e105000554507071440081040d4251035460f000025100000d01c1030600307400901d00c10b0320400c45c020151600707460f008130903080458020a01a00104040e42c40c0703c408c1d00204907249120701f0308085050502d001090311803440000c41c00385446a071801e0142c00300c002c031454811003189060104d00c1d44520019190110030707120b00c001c07405519020460b0340c42440307044e104560b280c0040906800200c00d40d8000181e2032021810080115084040341c1d140006640045c0304048016880307080c074100240550308010b02e80880c441c03050080622034411107000302e644030480702c0c0340040b402402008171040c4050310b1010350064100410321a001d030b00000250700c02d160800110104a0310400100c078041c0c41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221551627 1250 221550377 221550391
    0xd03020310051804170408030d02070302010b09010608011a09030613050d02011a040207020609060f0309011a0916030e0304170d0c020303030106030e03071a0907060f0f030b190806100806 82
    0xc3e00c40001c00056081085001c651042c806190410b07a544500c41e295600185140d003140340c0100380c05c0f0400d90240920b0340c3d010001c40d111280c0350304001c0010500c0c0750511825414200c0741d002c00003014000b00840b900000050241c0b021440c0082d08605002513400c0d045580740703c0d0b130100081081c070600c1490443d19480300c004c0c070210004401c10002e904403900c1641e100604000c213840d13a0341c4180003807403080c0c0721245036a100c0c540032460908603644a500c260303424108083c1c0d9a203d59407001525405000c584202c000195a0b44040340100000900381d4010b00c0300040100d00f0740020b0008110001d090740480302140718401d01160b1311a60400029010341c001d0005100180c0250064a00c2d01101400c0343e00703000f40c035204d52621900900b10b00308401100003e00404042c10b100440190061b030070300d40c02040820a00500c41c1c0403107144a000c056071030000e10415550307082005007000342041e6644c42c0b59107a0134100e84804045d54600080031580e1000551100d020503610300c07a0072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221552877 1250 221551627 221551669
    0x60f0a0e1f0f2a0c0b0310091515030c090803040803070c08191e1a010501080a05070f031d06010e01080d0309240b120d030c0207030c0b0f0c0d0302031005 68
    0x641c02503400c4083d65411012541e880100c0c80c003240140b0b0703d0014500c5108201c1100003010b00c0d01001104030381c02000790401d10030660b0024000180744c03521180c001c000b6842d00156801c1101d0041340d40c9042608400014000054000340d088000400350840c24019101002c600781d442d2010366035030308165000c0301403425070341542c40401e1581856601068030070641070311404a46c5d0b21007107d481e40f0b00031442884c0d480c0d001071103156402500e550f808825207900300214102118064050001c194481003010b441b550b080d004a03400b40d603181c100e0351080c01110110b585070544081d046500b40100c0d52941301d07910003060078034800d001e8448401e8100b949020044409a01980c00303000145600c540b00b611050461140d481d96808000724942d5400039003058070001e10014181c0f60491000e0084ad4003995080c000b05000c444540700322040360041d00d55400100000300c03175074011280c01c07000c41c0c0100c001781a4041c2e016002503104003410074540d0343c496125001c1114030462a10302a106074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221554127 1250 221552877 221552927
    0x90307090b130c051b0115090203060109030b070e03100b10050310030b13081c060603110f03040f0c1d0a09110904060b041802040f0902060f0a0e1f0f 66
    0x100d0b540c00300002c00d40c140303803807481d00484079030040e94010500389100080c1e6441d1483c210b01c80302d5003400c5000c0d0800107400e52550410b280001c021058500014240242e004040307480c0600070242d104221401070256281d1510604c0010000c200c01c1281070b00900016030107003441c920900c11244104049214005070b242944c49234040f0800027094900c44a80307540d80300010840e0030000d8008a400a9681901145c2110050040d10840d0740a141454148a403045960766003c1c01d40c2e038510204d01a03180c595481d410305581c40b450780c1d10003034620040c4810200f4501c0c0a40a0103410b0700718402d220407207444011902d021544890000b40a91480400c1c60205140121070b0641003402008089429510b04000130119010088000002c84200342148118100b03805032243c1512508000c204000c6540c01040c15031064242e2080881c030001559892140100c5848243d100301500c10780411380b0396a404906c0c14540d503030f26030110740106003900b8041d1051119001c0050300024101840d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221555377 1250 221554127 221554159
    0x503090631061401090f06091109010c0f0807050304030302011116020409050f0708010f0b0409050606060d060306140f090106050a0b0a020a080a030501051c020105041202040b030a08090307090b 85
    0xc10305414085030342c551030348000c2d00d000003a040ca26002e04010b00001440c4040600103d00b01c2c0c0607a1720101d103c9041c800b02070301100101c000c0d035060b0394085c01c08030013200103450060b0010482c0c410007081c40350086550b505102000020700709a9100b5002001a1550710f070341d0305402d0049039810180340240c4481a001400c0981048560b10300c074108031007030308021a15090414107540c02c50591603546072144d9800301c0071400f81c492201010b1310200318504081e1602520740700300402c03543c054500001c0781c02e442c1c079003a400040115040801044403036004401080e0010040e546c000e00802d49a0104022236018400c4404945004100c466203c0c9000704400300c1d504501490340641c0243c22044011074421401000040880d41d4000760545c149003c100070f005180200c01d840100008200c1c0041c2d80040484041d01c145240352000d002d020302c00540541828034034540c0600418a6402c10041c201c1c02601d1400001c4007580d41c03e513192003201d002c55a403610010fa01400071a030841c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221556627 1250 221555377 221555461
    0x13211101020f0d02160f1503050907080307030306050f061801030f090602160506070f020601090203150d03030b040b1e100c050a080706110f19050405040c05030906 72
    0x400006005551105001c1622a4108076040c40001d0250b004107501715080a045607411010300f000880311440c0e1400c14201c1c1e20922028404c61082c15540c0300491a550310402c021270003006c1ca10101c96a401051400801410040c8074a030f0045036442c401da207043c038050055031511000205d00c801154a0200110054200680070881c6c036a5034100d01404140b42d80024100e221404804a80c00882d0345050761905400420302d0b4100910380c24440c0c50181e01243c000c0c11158032040140c1c407034075a02144001100c41615807036200300007926074030805400d074001c685100400c882c1040740d540c1d040d0902c6074440eaa030031f0124180b42c06081c0d00c01c0d28981035039030900d004442d241510508603203a845d01d14021040c682590074040108086c1e041050358082c90303090200c48030b0801c1c281080300060f601d5900500c090144800c030301104121803e07110340705440003400020002d11200c1d011101c05049544140e4411710320740074020004500903000c40c00b5020b000101c00361541103080c030a8010314 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221557877 1250 221556627 221556653
    0x8062e030b28050402190806032d011a0609090406140f150612010b1c020f041e05060406110705030a11100c020306070c050304080109081321 62
    0x52559401888155494150469541d00740700448408607201039140c41c0000302e419400f152240d40100b195654031107036100d0f0602401d540b420050925211178000a04200c00c2c1c5001c0d684078425020701c03581e50504000184000d5900b10002c100008154020843d2040784544046d0030100c10010082c10707003072060703a0961050140c040040c0200c2600c05201e0042020307241004148451402c1c00021000c44005040700101264400d00e020307517492034170030841d405102c0c2100744035011444045521110324029030030080e211086644141d0592500401d4009014801940040d80059403504000c144020180e51004103094181490824100d0316200303031000320000c42c001c0c9240020542c81c01c11030410100c1c450009403d170560f50005000c40c00f02c01c0c80700781c0100a0b106e1800401b40c0c41c0419041c1e0405e01c1d0b4540240c42040900b01580b840c401c82c0c0c40300c2c0c0958070b8031851000f401590005400c00c180a005414401c55031003041d606212680035030030441c01010209680058900c0381042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221559127 1250 221557877 221557969
    0x6051f11060c0a0513050612060a2108030408070b010816050d0c0b030903040801060602060a0b031c2609030910050301060f0c0c030b0711010606030e0604020405130516060806 77
    0xf040f19140d10101c3c7c00d64004070251400003100c07900b4009545400f00001e000350080050784030403030442056074822072503031030005002c1e5a0004045400e020412007240c2ca8247c101c98401c1003035941e865010b07030303a0005040b03d40c50041d039420007180c5881e000d000c0e10300b07168000981402c058280340c01c0005c03079400680100090302c410480050300c082e0a0040c00001c1c9071076000b4160a00d000c03201c42e402e03614143c240300d10030340003a03102c01c1808440301c003102008251482c28800222686070904251000c400c16550004142010807aa0301da0001c01044200c0d0151a2080012841b21098400e030200b0302400d00405c1124540c403003800d124050280600c0e02607145a00d40b5a0b4a44a01000760820b440500c00507045041c090810282402050000d01162400700b00410300c0ca01c43e55180c0a0140c40248a5a02c4034007003014510329280700041c40740c210080c1c4038104920500c0d466141031a10804022500314000500c80c2d180100101c00901540361000081d01000d41d44403500c00c021482d14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221560377 1250 221559127 221559157
    0x70909030903060203100312020d1715031213051002030315060f041205100207210c080d1b080112080708071e0506010608010608040308042a0302030114040201051b0106051f11060c0a05 81
    0xd00f3307a6601000f500300718190030b40080e540c9403a180c9200307008400c81d0700844c0c05044e0700f082d202c2c0c7e0194000110380d44200030050b0401c45105240c000f802d54840e10044420701e80006c00c01040f10315059400c066071622403c00c44030b00c4400c480460060b0b024000c40605091000410080100c8992000f50740545051a0111000f06550384402241e001504400b9510745e46250f020784030311480e045a02c44c01c006007081e462070b42c501b15003c45c20310b0100038020b241c20004210b420400140005540030180c3c02006184c0c42035039403001461924821005848511654000280d1170b40152181d030305035121a0340306200b84e40c4545050711403d00251003141c0c0140b04c10481900100c1182e1015003031b50f6001031400d81c040c40c5004150271744010800c1c00d01c00601401c10301c40181e0300003040350981c19a91201689007401c0c140113600601281e0302442d081944148017080c011420385010320003200303a448072520784401070481703561420100c4926030f103100c0401c03035402030501500103041030070400081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221561627 1250 221560377 221560411
    0x402130e030a03090201080a060812090102030706020a031e0504050606060901020a0605190c0305010b0a212c0604020102060c030619030b01031205030405070909030903060203100312020d17 83
    0x510307861903100042c0c1030002076544441e0300841d030b03108a5050700480c0302042806142c0c2401c94841e100c0301cbc00c0c01c00300850b8100088156a03a4002e100303071144190808011074031080881405000707480c03519440c1800c07203001074104014a0b0288141c2c0d01075a0410010012552002c003840125171040700e07404e040d4400c4848140c0090f509001362403040c4020031100c1180750615000d00b098804c03482c07a1f6014103003480014489a0301000603500c902096280140080441c0036540e45840401c04980b0603803810541c4400000f032800025420840304d203a100742880503d00b45643e00d6010941c1c000740103806c0701010861070320400c2d02650304000700801740743c2111003c1d0b603400b010a03410784c42100c03040581001081072290f84602980c0e04210390400a241d840d0070741c0c81c1c81e218420383c00f038465017507500c800102c00c1c58800c5c1c481c00b029540c031031011592170400d4a24605a580c040c401152880303000001140d1243c4040b07407603100781c3c1c0036441d00d0310040c441c140f11401221000700b1002c07507201c0804c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221562877 1250 221561627 221561651
    0xf0c0f0207060c03052503181406030402182a04060c06050603190515010515040b1317010209130c0c170919061103040b0706020d0b1e03012003040213 66
    0x20b1b00e00310100741c1400000801803140303006002c41c4c002c407884e41001000444104449802e15a081e0504002220f4040c0c2c1d0340d807240700140c4610b20349121075001049003010000c11004092003038000c0050310501072801c00d41669400c0036440b0342d0142500184101c1241d400007403841d0410f0750020b20003819251902c4e1402041000c004617820705485030380c0720401c3c11900300e44100c0013501601d0252104401a400798141e92000c0c07149200f900c1c0317205e4002440c00310340f4550901c800c000c2c1407400c2d503c0d001c030803084040e50702079001034000034411903020310421140821407080040c1c00340c694490441d5000c0580b0b503014074800084251450040401c500903007503030f4040c100071200040c43c8104004505000004269003160020781d4503a0b48100002c2c04403003c448260748115502000160f603c074882083d540c054071000250f260130035040022014048411007400c540b04009030004c1106445d04246200d0ba026599450b5200c02410000f00d009414880c040b031400060124000c294610850 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221564127 1250 221562877 221562907
    0x20c0715020a1407030302150711010618050702060121020102030d0203010e041a0421020f0a030306061710090c300e0633030a060f0c0f0207060c0305 66
    0x264100005030080c046500400141014102c560943e190042c601c2a09540d0081d40d6141159800b5141c90542e000081e28580320754034031001214110000d004c0959501d22405400c00410601020f0a0a0200244115100017500f9040350500b083c2e010b1201085600d4041c0941c100e07200340d0450208100042203002140000e40c003c00c24150130f00307991301d45400c3c828040164840e41c3c100490641060002040d000e08001a07074036600e10075100d0f91041890141d19060016004840c80d000c1c0c2e9925205040e00741d4899030032520251103100b034401e520704003440f54110840b94100008001503041c02145c0003640007000700000f600380b1041c80d980d84c0d40718016898101e2050286c0500703400c03903015800500c3c0a403501c1340030503800503c6c0320304004180c40170700360041140045c00345444402d82083c417003454203c0c0c8412006015111510307403d06102010700010208460032038100307240c0e002128440c2228a0640070640c0c098003040b400c0c83d40c21144250844410b8040240503c00490740021003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221565377 1250 221564127 221564159
    0x210212010810150f050609120d031d01110d0f0608030301080109020f0a0509060427030302120903030906160e04020f070303060509100509180f060103210f03020c07 72
    0x54004060142d00391261078240c9607039040c0c150071941c89841c10060b0f0910720665038191401150b04a40f50304440c00810316451207056001038910500592109154040c0c0c010001040240040040c2103081090603090300c03000320748003001c00d008002071076070400103a0041c424600301d81004102c2d5a0340315000e6241d03810a8000d600180d5556040804510304003502c81c8040e00c06448070000d4903e4080018141000185031900813a10b81403c2c0030b4211006140c1d0101c1d2030450450700c1c00c0c04c81c90900070b000390064500d40140030b820700003090000d28000280d170710550105000300950761311103102000c5181001d9048080c0651902d1440565580d80040d02c020003d0791071103519105181802801d0b2140c903031001c2e00500e0310900340040800c1005092082d108141e40b1140191103039540500c03001075507010703c40d0500490346000313041400402c13164126802071415130002003041c501002c510f4500701440d030110b69404e1511100324000d8004d44030300f00111054404082d0381c0c201c186e1a14088c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221566627 1250 221565377 221565389
    0x8090c0a1a2116030c05030406150f120b0a020906090d1403070317060904110d02010e04060f06270302040c0c050f0303060a0b040b041e03051209040b0103090321021201 74
    0x3003402082a0044000c43c2c070960503c15140078000400f801d403001d42a8030014102402c00c0f074a030440c2d0010401c281030800d000b030122080941c2e40301c0d0b0320400051100c020550849800c441c0001182c0c98102c02c0c020f072260344d140100024a0300c41c0000c100803041d101404115001d0311084024030040a050000d80401c900a03203440700c28071440c1d0a02c000f4201c0091000d0b12801d80310042c00b01044090842c2e0104210613554403050380e4550005943c4007007131004c8160302900340a008603c8044901d50b1204840041e1128030440340102a1a03941c0c40c45141070440d103500d4908108090f1400b5040b40e0600c148a080c802c00881850f2540307820001c0d1800803070b5240d0300000c140401400d04006920044c29852285402c1c2810050802c0740c901c51485196128074403054200f20325004540d407040259480012541040c001495044060300300c0d5080c28400e030b24281074078171254001c0c000e28400d036525554200c03815405120507644030850f4603100240c20340c01d005091104551244940c0a032003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221567877 1250 221566627 221566687
    0xa030c090c090e0f19020c0303011701110301120602030403051227030708030411010e060a1206060c020f090c0d0f2408030a050903010b15090108090c0a1a 68
    0x7401c2075015080e10ba09a202c4540901c0070340810500340d00a0900d030740c00a2081c021080141c0300a81c000000c1d008201041c0e089000000001440107550381801d03e000121400910401d00b403c8206e01050000f40f041c07072140d0010350028000071f070300c40c0d008582c0f00344242402030809000d043d40304004041220460b0480340c14034001e0712043c0340c1c9000f960080d0148001180751061a682e01c10341d9000c05000144102100100081203a00815001e40c031004003811140d00c6200100e8014074204000c44015000d5142000c085015449250001c0c0c60580150000c000b13191007400b4054419401001840340860070300010721002902e0054000e041d41c44040882d080502084040f04000b122054100540c0303241c404114003100481036420100c65400d0842d210b0140d40d0120340581201005158013000f156200141070103c0c0000d4400c24400381d03285c5440c2d581d40f007039040ea00c02d00034000d82d5108079060010005407103c0d5610220300d03c00c1800290600140f41144c214030031181d070706046c46071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221569127 1250 221567877 221567891
    0x301140a23030609010608030901030e0a0206070f0b06060f0703050d14100303020c100c02100e0d064b0902090703020301080d0801030201080711010e070602100c1403010e04020a030c09 81
    0x101c2e04000668012072044020010280792041d0b16640c0c0c4504864079051503142e0888421285091140b0f0a046402400c800d03540d1040c4d103401641c003605c0c800221070090290001c00e10038103003003083c3ea60006c59259014900601a00c5c01d80303c2d03030008160840356586412800440b07410448140313008545220b80e100b8a5821450b029051802c129412409416203003000682c0c1584000949100c540540d5480c15900d1342c5041114404001e00e5030503000070040303540ba42041501c4d4041502d400c44d40000300d03403030900303000f541009180c070400303d89007051140c00011007a81140071398034040480440016152806a022498039203045405402082d404401001080000d000311803c4103800e03c1c1100c0c5035070440d80042e21560005d0161700c10410604003a084171f070030950041541c1080c0c40c088801455440c44c0081d45c81151040f885125810200300280c51030180120b416074140e00320340141544e00b0207581c2882038600502c1a40e00001000000000c18100045e010280c1000c0070089496 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221570377 1250 221569127 221569129
    0x3092a03101e15080303130c050105031303030507050706180303050708010b1603110a0f0c0f08280b090106050a0f0509060f060409060806090601080102030c0301140a23 74
    0x145810340450100c82c01c008200c0c11580c0c0d61074441420110030b20000030104040d1071044035025064100c61a64800007051021074500306004102c814800c40c1520b41c960780314001111280030a17908000064406a100ca00080c0240c0200ea40620a461300904200c295105c6000790b40d0501007200400744440c185034285507041c09210350185060401010a52401c0c2451a00d4030172070700c81c150305000074000381007058407030780019000000f0401140d034080d18608007000c04854200c011a403a4007548400505442c105024404603962500a041d20100300c1c06620b410400c0c015035000708880c1172641d000000c0c0c11041c401d0161490200000710348bc200340500031401ca454200d404001c01c50001001a903840011032030b40001b01307a07244000100326202140c2c050142d50000e02c4010700345000414407100c0060030503c0365119104a45036070341e071280a20300701e100540d0707140007848c010401070004a54500707000806030b40151107203060a5461188000780103201d0303001d1030b801510507144102d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221571627 1250 221570377 221570383
    0x108061c0614060a030317040809090a2f09041508030c030a0f050f0306060904090206160b0c1317071a0703030c030b030706030f0917030403021b090c03092a03 70
    0x102240690f4449211400c54602402103800c961f12401160013440024081002c51740c1038507010440500401d49508001d40140050703e1280389281c2c0c0c030322590b100080d08400c1e544505000c401c65440c200d00e0302041d1000c1c00090110400d0b620f141060340c1c000000c00300c200b0801000c1150000e000346884806024000340318140c0fa00d04003040103414040e1210207108041100d0b0422000c490981e500c08040740401c014022100f40070794080760100c7d2131920030103034002903c03056109680302c5040d950348400f0000385000e540d5900c400c003039200307105115010815103084003803540c0c001265121542c0310160810003103103c8611505450102d207640030984c050143d03004103e8242403d102c00208480800d42d69502f510451041545a110001501c84145c0c04001c1c403941204460b0686800c11a4800c41ca80c400d5808400500c40c0800250056014660340c1c03110210081c5040030546515800014a400160030581e2502440f0100b0021803054000701080d840700c010443c201529950400d41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221572877 1250 221571627 221571631
    0x1051602070e012102040c1e090b040504020c160602010912020114060f01032003010518040f020103020a090801150801050705041202060705010908040605030609010b0a0804020108061c0614 83
    0xe40d400703240c0c01d105004040010a05681d42d032007140360900c03902d0000190b80c26480c4400b0350003914050049800c643e00003414544185079070501003039691100004c40703815245100c2c00104402c14407003800146087e40003400380444c030004444201070404000c112031605540050b015030340da9422502008031204085078074440380d00080009082c1080c50340d1031b0b20340017044180700b241900004105a8066440340c2a100c0d22140000d01d54030b16a06c1189441d8000c1c040e90303204090b210542c0c1c401c0041102d407e4482d9620400798540b0108507401034000e900407101d8401800007010001c030750368100b407160240b54403042040d844114601030b000b40c04c40314081c04c2c0d401013100400c018800086a0f090080500d0ba043c0c41140c0d990400d41481030040c420036030002c0032018001000610140d002029600a0130f049031400c0781d41c2d90390854007489220314140d102c0030562110000d809903004d8040c10303031b0010026002d803c1c2c013404002c083c00c010303284403012280169184541c40301410894480e40e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221574127 1250 221572877 221572921
    0x10506010c02090a0b120a0510060504020c101112091005060603060a03150204032109050904030e04050603120d1d0a0302071503140103031709010908190309080c0105 73
    0x1000c0c81c04190042112a1401003c0c04c0902d45c4411954207141c4400d442c2d18035440581040c0e90001241d4a0080d0f1511480801910202c1c181207010600746414400c8805076840380d00109620300c444141e01c4043c0c1607440806551030300c180442c600102d403140d26240304040344405440e8203441500754608071a4080d00c02d0340115014810025582c0b14040d01c84107890b0006c0707844407150011a5800301911560704000c162800c442841c8800d2001052900401a100d07124003a10781d44401c03d00070400411075018000540300b00348104035041960006403c030034007406907500e44916040620a5600400740308510755aa60210001d020300c801300351038000d10900203000003124a0300c000f5510f074030502510b800120320070140403116000c2c1d8040449602e2030640c480040da502d04014100c8000c01c1400c2d00c052072a4800610400c01c184a03e42c41c030740d8022503040c1029070480703500c070201d070039030030040185690341c507203000411446409400914001000860103203090100c4140c0500322409031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221575377 1250 221574127 221574137
    0x10201240501050d0f0e0c01021207152a050a090e0408121f08030301060305151e0406080114040c060804240605100f09080c06041403031b0c0301050601 67
    0x52400003000e0400100300c0d07209190494139000703181020001095400c0c0c03018100303483d000160012070004500f00c0303003285007602070b1f076202508020380d88450300c9030701d03002402032007001a1900a44227640c01b824500402c10390280504170b190007030343d4000c02d001c2214404500040394400c003061784a0445000342c0840b4041c41a1402d099443c1d03443e80c040c4150b4019001041c000054001140500c00300c0d15010305625482e07100d43d00c415064072a402030050200013810400001c400c14504521080703024400390280e210098142d0700140152508941c041e40b20303132103481c0062100c03400d000d044d0500800502061172030070146000415446d05510800610062a0811022900e04444a0025402c1d61180d030504c1140c10400030007020690041a800354081c94109010380c0c1c4411500e000c84400e0b01c40e0b50089454464059660b00360034075080c0d100f00b00300006e104202d0072984991501344060226810042040a014202455902d814ae820383c44107621908628003400b40a400520030300340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221576627 1250 221575377 221575421
    0x30702010c0209040201050705151e010608130201120e0304081005040302061b04170a0606050a1a0c0708030c0d0801050a05090a0c02100c03020403020a140109062001090809010201 79
    0xe4074a034641c0750040e11401e1031a00050659015004a41006502c075090fa074850014402c6244003030025201c1c859050729182554a80c0c121007031409040e5607494031041c91a0b580c4003407082440701400c104074104030f45d40445480307400207409841e107d110400091502c441c00d10071101c0c5000001c80781c17034180905100038040403076008070707203d50460f0041e02d0381861150350080e240b4080c07140e507200b580714103110071043d44104008981c000d00c0500c10f090505c400c0e5955020031400620500076802a034009100c175030103510405004041035550103040c3e0f801c00c0d03503a150090454108042d20006500701c05068440c0030307400089a4050101101c0100c481400c1c032011490541e40100320071516651401c2a500c9107000300242c2941144206044c80400001c0b031000b00030350010722049014903840200459007075040d961001c500c0c03204ac2d42d174404503440c01c00304807103200c680510400c001c00c03511042940c0c0f10302070007503241c03113409811815079910302000024216034858030304000d11407081c41c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221577877 1250 221576627 221576629
    0xc15020f0d0c170f1603170a0903030b040b0307050609030a02190608090601180e1618060605160813030f030315060206150405060a0f0e040201030e0622081204051509030702 76
    0x10b403440f03491000341e5001c1c1c01c401e1b890160342420041080b040315011607020406144070741d40205407070700d11941d02030000328000d100f4041502d021504595064004807000d1001e81031817000781010700b100900f01c03040052140c000c1950b06c01090407003408100381000502240390010003480d001400c540080c00d0035890100c0c6070601e00f0000d0210120151108030803003140004000011050200c942058070150b6142101a281c0e1002400686000e0a260b00054014080e4050352400300d0b10f41c02d52824640c60703694080301c55002051000b4038091000021011446200304c1150052282e00c000a0b40403000059130a0308080340d101e6800c65008a080102284901c100b41300b01c60001d60b00811b01c1d84a0b60001a0b4100090b002090080f252060010780701ca07020600c1c501481c005e032410008039018261603034454504460f8004800410004810030040c21507101c00c071940205065070400c845d003900c00f5402c0b441a9015909540072030203140001c9400e5a2075900b21648500170752610200354 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221579127 1250 221577877 221577907
    0x6100c0f0204020415030c030f181419050d02010f090203100f0b040e0318040207030512041707080a0207080607020a0303050907030c230103090c15020f0d0c17 70
    0x46401016004014102421511550181d0f40a4182c000b002c110f60400f140c80200100003005901000908144520b81d040e061441001c0d4900420034001d03459401a841e01407086c410b0b69840c816138171a0560400010007003900d0b068206201d1000351000644040300203094039247d51075142228549600100140c1d4002615044290694030104850714070b4010403006001d50030304d00b604181010400c20f49103070084018099070004040f08410607401d142072000300d0290200040126404000c00d07d01ca504410980e5801380c412000c0055110380e00740102c1098024640c21030320554080b035513800103038060007420060804000248400d10f0320400081d81c8180032040a014155a07501040325110f06220360006160010b800900c7e02c0d545001e000b011440e1200c2c080c0e4840401404210158480d004c0c46004940100401001a060070144080d84100340c4122007581b0465102d01d000c000c00f4001c09607840b0185d1602c0c0381175815410400021b20b1941c1c211034080700b08000000d042d404e04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221580377 1250 221579127 221579147
    0x11a0909060108191e14060109060c0c080d08010302040c030911040c180e09100c23070f0c080d02030c060f06210c01110c0a090218040207060b03060610 67
    0x24649505107880e594601c03215000841c5144d821941442c501103040d80020082c080b00b030034125000c10000042800c002c12140c01566140e0014684030740c10400e45210b01c45406001d80103001c0d60b5500381c1e88a050b075242c8006c0007110404515404010410341c80c00d44500f071610102820140500c802e25039901e0f40224048415620560f43d03060340035a500d11900203032145134444001c1410b411780f600b2108500c0a42216111500e2241d00080801040703e4000c0e134542c3d141701c3e126100c1d11102d00c030b080c0d6a1350034039a421110310031040c0706c001d001c6012411310729001800f070825504c0031810302c20094280891910101c4c155441007240c1d095105002035896070001d118284050a84c8480300011080d11030656010017081d0301d003100107040c0d4004034140da10710070300342c039585003140c2e00048983d00da80c0f00c06c0910790302440c204020402c81409400030082c03541783c1c0c194504880c506a002600302d030807400d4240c880a60b034090903695801c04000a6400c10000c51310400b4070640000001c00e600c0758 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221581627 1250 221580377 221580379
    0xf0613090b1b090a1205010e0712062003070c02010201060b040b18010e13060503071413150b04060903060507081003080d1418061f05010e190806011a090906 69
    0x40200c0b158a20400301d03094036400c1000a1140190035594409210b101c03880140036a207c0d460aa01b041035400000b0310a81107407240c048401c20f0542070380f00c282c018588803485074a20a031440b414400820042c000750b100300015240d04540c000d090000908594507600302c050480000c1100703000905003001503906074003208901c0100c0d44070322001241c1c2c0a520864082d08010176100035004448103402ca041600e0043e0b044810300c0b5a200300032650001c462814540201a981d00b414400d1030030b0708105981e5441f00d407008a100e9030380c07518038805e5009034088800241c84c14418401c012041c0a41904140705142101090070b0076aa00300c08515a480300802d400d000040e05131511420f504107a140d203890f40c440a01074680070184604500408414405074050070b4001100e4101010168802c03c1c03681940910240c00c05005580d0b0b120030100055000950b4450104049000d0340c0400103014241d0240c022549403400c114100c40701c0c900c11000c06002400400c09075140c1440f000e41c8240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221582733 1106 221581627 221581651
    0x7060621120c12080402041401270b0f0112060b03010e090c0d080d1a04020c030a0f09030308070f1206030503090f03060402030d0c14060f0613090b 65
    0x103542c0c100400c241c900c902d401041602c5800d000e5403107071010300f00060114035580803448580c0240d000390781041c207029661001c10b1750380e400d40c449050180f00c24065081188000703445e58500c0d040c464100070240111400d200d00c1d50704030400078103d174207105940756101c0d503034201e8084048902c00c802d84220040800a405c0052020040e5900460f14906104035002c502c00a0310b810040324a03001c504400e0323540c0c1a40c6d10310040540070340c0300005540e034062056000d42921543d01c02e1409008140340100701080c1c0002c0000d0f400b01d40c505d004400f0b01d80003e010b0703e0342940d20402042445c50301501108100e000801400382c00411a5107106600d058400c1643d1054219402505500400100e04845010b00512503402d41b1806003034500841c908036803446d007901200c80407003d41c40001840b4060034146881444c02c9100c8000344001010703911000c1800401a0501010740 = true := by decide +kernel

theorem cover : BRFrame.Cov 221402877 221582733 := by
  have h0 := BRFrame.cov_init 221402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221402877 ≤ n) (h2 : n < 221582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
