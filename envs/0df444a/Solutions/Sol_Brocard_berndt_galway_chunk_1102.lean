-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:14:52.882608+00:00
-- url     : https://prove2.me/submissions/e3109988-9162-4c1d-be86-c91677470537

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198021582 ≤ n < 198201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198022832 1250 198021582 198021587
    0x108010605031c030b03030d06030b09070602120c07030c0905061203090906011d0a030309060219020d0210120c09090c020c010806060912060a02130b0406050405010309020d02040c02060a0c 83
    0x3502103900090080240031480c0e2007500c074008030400c0403800d055944020390000d80f8180000d0020304041c81d000203440d802c514090382003e4025003110f2655001c908140906500016202059902e09050b039454010b02c5032140d25000b110f40005103d804c40c070700005807150598000c940500400c0303d03044030002e2444a02c95803070140c0312807554000c50040101c2c110b940034601c101c00500c41c645080208227030940200d041c0d020b156000324005401d00f88100000e950601c20720040d00833001601100f071350030360000f590700040950041c4c0315075a00001c85225901408103421102900300e010700001e20724600c05800081c040c4140c5610504010103043c02c944046650001604161110752860320740100b40300d0282c10004507143c208001c0d0b05c1101400d081000443e1003940ea0100c09a5100c0c901d1510082c0300885a100c00301c81c50060100348101a00007058805980d028170b400504404503000260740c02910b070401a40280c501117161800d00e40c0480c0c0b140c4210350711031040c4803202c0341c035004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198024082 1250 198022832 198022841
    0x1f021309140903160b0703060312120e071a0d060f060f2d080a0f14090d050406050f03060a050414100f0602100207082104140106060c14012d05010801 66
    0x13003450245281107032000407050804141c006243e40360000d1003d8a99035041d00561000341c9a130007240850041c04c10512940c0142403640d00310708007034248103250102c444000f10000384140311022000c02c1c1c2500b20b4180340c0c4900d00401c004041c5600755940c408029005149804081e80000d2908a40d00500316040200b0b1030b5a0f0390003409a01e58541d6420201c0d02c61402402d02020540c0f00c80025507403010034000c0c000c456403a400b48800c24109051203510344072441481509104090004000700358102c0c0a0301c0f8041100c05140342c2e00d0b691b10f000541c0d020b5007600207551162030491800c405121740c4224504c41d4a00c40c14031000c05071115031035120b00b0f00301d124131070040e804944500c90483d40b980103059036900c9480a9401e00003059081d955015029218400d0011031100700b1040c0102c0c0c104203802c101c00940200f2010b410950014201803a550300034008068200603141d01000c2544080c1c070301d032400020300e20007015001c20b500c14101c0710800100f030755051900200d0000418841d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198025332 1250 198024082 198024097
    0x140712020f09040c0b0408010e0c040c0906140d0f02090f370302090f220c0b03060111060705041401020708030d200d0b041803021f021309140903 64
    0x1e01d20008190710400c41e030580020000c480c1c1022900d80060100115000b40c0058202040045051649400303920700d4a80141480c610039401e001910044503000400d11041e204a031404100c02c55200140821078825004c084d03200340c1c41c140e01401c0f00c15665000e00390740ca501b225405c5004100308108220400d410322000c0b60403030044100301801902d042c00020307681d00d4803c8102e01c15501d030001746031410110780744144032000b40700300030a107a50818441c52948a88030000940100f0740c48a40000406c1d0254104056000010034035503805401c10350840b03040c0c0c03001c581c5285040c060080903500648904010640320010390301c036940c000308500095401c204000c508010a52100c0c0f4050684402c038410f20080032920340314800e8002004000d403100400d4007103500401c1ca81440222540e82d03403801d002414816407c00000d0340812000c0382185030550381003100c5800c090701d0000b841010386882101d01100c0000a1824080e0004540390200004810a9a4640c0c5481d912845010b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198026582 1250 198025332 198025339
    0x9060907090b0a080115050438010311070507060e01020d05031501050c0d080f0c0702030a12050d090b06040e010608031e1204060b0f010207060e040509010e03030414071202 76
    0x280184031426070341e8401400c110000b410348020755540d00840b8210f8000802104c4491720108080c0700d18209800f0b0340b42c00300c0c5504c0d00c4030b420194001c2c0312842c03a280c03084807030300c05c1c09011780a002d0b60303100341c222614960004240ba607a400c0c082ca0220f0b56850340d4030542c1c0205c2c290000450a070340c004154019a0074031615110301e07607620011000b1240200650007070511400740b152401c860340400c02403401142c0c0b5200c04280742407850310b0180c3c40d00c0091419503020420042d480040e280411a003510130752046080c03050b00c8100c0816100d501a00c03100540103490b01d2144404d000073302c14038038000d19080d102048004407180e401c41c207807031680c040d01d05250b0040100d4055101145011640302001d941000d0a10060301d84180d0380d440e040e903003500d0103510b86a510102c3d1070518804c03079103c0d000f40004c18407103240c8003010f03080507a00c01400744116035402c00686854000c3d0020a1852060002c0e00e69900c2d081c03414040c014607544000d4983d102e40c0c4804644011f00c10000d540321038009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198027832 1250 198026582 198026593
    0x4030b190f020310030f1a040c0611030702010507081605010c0c150b0306040f03030603080a0306090b040b09010501030f15030308100e0621031606020a0f030207110d0311030f04030308090609 84
    0x15107612503003440c2600c045034a107241c40c0c01c80c0000347d41d0031b07500d5000b40c0c4280c401d44100b034a0400004d0060528844111203600b0800204005030780150407901050381c8001850b855070640381c1100c0007120740d9107000d8015400c1c0b45032007803500d500c41034440400d44250076460490308061a42d030101d07260744403510b4150f4002004a008224a01c40c8804540d200e481c020608984a80d100b420726040007060a01113600c5140c2032000041500034016000d405480801c1401b01303110001d5212503041c811541030540c2c0b2843e440c42d030680b5410050002c400c180c0030700e042942d0313442d0080210350102c0382c0c0e04000c005818003140440044000314041c41d40100307100300d16440040c1c82c0545205413201c1e00d245100c200710400a2100d004003002c111406982c005032200e10422024104a42c00422102014410032040f80092103181c031403988003100fa107034409a90000c2c6425501885c280c601484c0e0380c400412220101040c0c18001c20a491080d6913036411501c500604c1da41d54101910101100d8000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198029082 1250 198027832 198027839
    0x207120c0314033c070b061c020d08070201080f040c061412070806040e0712080c0102040e0109020315060f030411032103040b070906020307080f04030b190f020310 72
    0x41d80c0d14088280e903040305580c81c00a42000000714280080c520655140c00800b200c000c10249644c0360036a006130082c90740c0b404034036a03500c00c22280e0040a03180b00f10b003d070582a003804541c10b1011007059028102e00040841401c1080c4a500704040490000300c50100140303a110b403848a280c000c983c02082c8000140c01c1902c11754281441d4a4104559001446021138072003060998501440c0592a000e050341001c400780400e4503c0d1510100080c0d20242003001085401d80e80074290581044034142c40d502c3e030766040d5000e0311039035000c51102c0706410004a00d0401c56801540106581d9043c80440541c0f0b2041c4010750281c0440043d04000a000150200300d903144020503c0c1c40080030b8a41d0b012544440c9005a466103401c481d000b8000702c100002c0010000d01541c0100441c00e2055481d03140c12402583d911510100420028000c1140c2041a5030182034238040c1d5801a8840c40c14030b055580c0d13801c2c44501d010340f07144003170038100840310f888850300c2242d001d01c54010114850604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198030332 1250 198029082 198029093
    0x305030a0207022b060f02031e13060c0f11010501120305031005060d0c120608030f07061404030e100c0b0c07050a0b0f06190501091a19030c0207120c03 67
    0x1203034141d03048001d207943d031001c1e03049200c81344200c00b02c6051011044072150400314100c515103020155010b1041041c4100321264422061508025024100c5aa0744520540c0107000c03206000038221401e01445820487d0400250b4410b022550b1b64141c07240024400103090350070a00c603400c81040326905980100e032060780110361186510000b00d10036652358000c90002d41c020303c0001741e8503a07500410007466a0202040e0010444404240045410030b11303404d44030320031580c072041c0101c40010f48001b04002134001c14801d0106030000000761606080240c412800d16a10501c40d0f924000c1c03c3c120076004003e02c0701c0c0381c7c0d0401c130400440d40d980c41150700b0a0f80221025105442404081d81c006040003008a00c2101c0402c00c404c801c2c10454288084400700c90182e9500300c60401d01803205136030021035842211652500344083c100c03171070540c0050744245103186c002d003007580799012030490705a080341c0c108000a80c00c48841507aa49001401c10303624410003080080f000da000c001055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198031582 1250 198030332 198030337
    0x601080d020d0206010612020a0314040b1b0909060108060109090504111003020a0807050901020f0a0807050601060206010e0a05101509080c0604060e06030a0b0a12020a1203050a0311130b180a030305030a02 90
    0x180f842c1000211004820200c0c0d00bd030104036001c440c219403980170000f036590301c0080032443c17100c2c1d010030b103003040410b10020341070000003000e1504001404002410300e070b2059a01c4001001003c000b0002400c3c01d05000c0e184900480020303001c2d12480c0c0c50110f00521a01c2202d007035042603501c09116844141c4111026880b14002d18110710649103582184001840030500c41d42c4280040c0d50340e00f8041c50101c1c107000c0168040030645d0810001009104481401e659001222803400a420b644003104003032070040b6070304a0000000da0707241c030003041600300c00f200050b920014120b17100d40c3c2c1d01c0000c015644c411805070000040003540c081c001400c00c04c01840c0c204085080200781e1542020104903038585c50b03070000c0c84402641c841d040035402d004154801501e080c2000344642d0b24903480141c103d00c2244e070000205507a56021008000c07203c401d41d60361002c032030b5003003600581e5080100c40c83e400c08031004161040f03a082c1c081180c41c22800d05022250305440702401c59850342400300094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198032832 1250 198031582 198031597
    0x907230909151f1e050d0c09030f060902030a06061206060f12170f0a090e0601050f091c02040c03061a07030c03050313020d0b04150e030319020c0601080d020d020601061202 76
    0xc0e009004d603200702c42c0c1c0008a2440b04c1540c6580c1c07959090319045c03040da450128402c081c89003040d0280040b840510f40b203071003160400c8000c1b880307408510101380b1780258140040e040a24205003c1240e803c400141314406008080c1070000944801d00200362100c948254200c02010541d44c41c0056150b003909400074280b401c10604103940200b0501d0280e015050303003c0040c00000050003100e4044240340c2e0041401e2a180e42420ba403190b100e0498030591002c203208100c0c1c011201c51b0701c44400c041c5042d2980c080c10500c40d681c201000600540454003030034241c02142d040074101c9260a000b03862840b5051b0f683e2120720082a00c01703a502d035001615421502e500203540d0400760301c0e42103607401c1207403060211a540349400d0070b201620010031190b002c1c49500300640d43d06802d00000c19250031101c0e07254405880c28041c0300d20802449103004000280c0611000003480c0000824442058030094081d40c21884081c07030200e0b1260070900a100100306620070ba681c5204055001d403084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198034082 1250 198032832 198032837
    0xc01020316081228020406051b01090501111b010209031504140f0d030501140f0f01021f020702010905010f02072102060d060513020a0503060907230909151f 69
    0x8002e0705014020300042c00301c641203800b0b110108030300c5080150700030840c05101c44c601c1c2142010300780003009003113100b048012070020001d82922251101c00b03600281140b0313440b600030040000782c000c855160341c020000711038414030581c00d54091554103000719249050001c016104d070070400c0a50011510028205a038002c40d0300041d003180c44009c104410301003000c02e000b04520000c404008040d6401600b0001910b1204100c2c01540d80350200d20142803002120b18201d245d500c00c1c0102c0c6858800558009000d038007262a80c0103c001da4018071003103000303a0740e00c000c05440b039006403641904860000c0c016800f4102c100940d144207442c07403400020111500c66031386030036000146030740c2000901010155a407041000301d40781c44440204003004180040d130802c4640f84000c0c1c0310307010080c0514042c5040d280025411489003400b2541141116021120142c40001c402c800380c0116550f2402104907101107140c9030711000c1d000c40401001040c01c0a0007400c600100040d420347d8950106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198035332 1250 198034082 198034087
    0x501050405060c15090a0506070c02060306121c05041d0f010e10091103070f08010f060806030705220f14150111101a0d0c0614130b04050f030c0102031608 68
    0x22084400c4d00c60745d0081c802c903401880980c0c91410a542414005080ba50500410421081c0162561300a91764026030840390308680319011440c0034100501070001c294440d000d00a0703041800d4024000d40282d848840e80c4000c424508259034030300f90429181200c2d404e40003c01004401851207206071701031500d907040321009a888000400703030744840300500c89402d0040308000e01c01c3c0d40803800c00d698030680c0c075001006500d0b0105131403907852a801200200281000000d500da2010000500106006011080960615158104078a0240d122104160308029002c00403c1c464010400545c3d0a480505881e49400076084041000458464180321a40d00c1801984034240403d900c0b070080002c0106500ada45031a841d0031000f000760741445603000303407420000f003201c01a5607019180a8208044412420705010f4401c0c058400741008180c0041c1003ca441041c10019000302c2d60151228000a49140d00b0140c903000f80e22a40e600690003803011414580404148940c014007804200340f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198036582 1250 198035332 198035353
    0x8070c03060203010b0405091003150902010e060c010e0d020601211505010801020d060902031501032406090504050a0e120f0c0a060c110a05060c071515030510060501050405060c 78
    0x1c1a600264860250000081020406800c00201c12070307211020400301010203082d65607132241800c0e0a034070352030701c640e44075250700440e4061007028884000081559880d200180e19590281c1403c0341152010301644c441000824000a08181070720112409040e0742030b8508080303042c441d07a030311040c0c8002044450700201480144100e50180c0748520016945010384480f4070113849180c0c2c48041d40303501c10000c10000c5074500500c00f0000c1403d19000c1220700c0c0307601080703c52030b452250100d1950940c41c000140e464011008104403002658140159a036010000049a40800703510040d60080b007400d0761502c11b03080003001c9003480310a415040200e00018545070074640740044034680d54403c00c41500780d07001072034000c1c2442600010500c480403036880546510000d00304ea0700f03030480800c20400300b1112084400c941c0202100c01c00952290411241c09a038541c442502d40703010320117000850350300e00d005100513500180c582525051521040c0b08860b03020104003102d50003103000e20b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198037832 1250 198036582 198036593
    0x7030504031b050a020109062111070b1e1513110c0706081e01080d030b0f13091a011d09010e0102040315050f01050901060f021c02100e030f0708070c03 67
    0x294501650040804c03041c90f100240120010350803440501c01034041c0b0640c8080161300200312144168400310702c0c0920030f0300519282c0545880105a04c1c840c004005040750340c804501d4403019028084400c98039000320b55131041001003485034000404480c001d140c2403194112050102c0201022850b1626010410703060200e56048600000c508405001c0107220450b2003102d900180340038010b447d450211b8150b5070310058003500081c5174481e4214030b890340d58034461052003c4040c3c00701310381e000f810b410ba80041c020b0010859080018101d45100300041c480d940e8140e034407109681810300c50b01c00c4c22490915000709070f02155929610403a0603e04207001600040d403065034004c518040c60043c200580f4401003010251540d45001013001c0c0c0d039000c080ea0704482c06804d000700c4070101440101c1c1800d1280c0d0302020032400080c803c0079507942c00110a041c1d010841420859410800d1103640c80b40304005d010a074905090100c2c002080005008044241c031a034841c4901c00c1da6507680 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198039082 1250 198037832 198037877
    0x32a0301060f030f020922060b0d06051008040b0a0e100207080309060a090302030406031802041508010f020c1b011e0305100b070203100209040e060103080316170703050403 76
    0x101c0058401c8004409140d014015000f0070420f1240544c10040756401080c400c031210180c0c184140103811100030141308907403019014101d10410190340d440d0360300c0b01c030740540568420306016080d616038084401b4894009030740500d40c00080c0c0382c3c50761924842400545120100001355014096840c0c4404210344000c0c900309204800003070700d03850040300c01420108014331440c251810440c0060020740e01004550940c0c0b05402e00180d42064444180104240402c000750460b02d480180e5000b0315000785490200d030019802408140340a10542c03003a4007440840d00100d0740130021012030030064801d1103581e0303041898142c0b19491611481c0000f40f0b4504640c0c80400e99a2041c006840f40d010741d10301c085c0a42001407481c28116034086541e0303013220540780c5d00540e4041400d030310682c0e071900001c0c8a40300f0f1400312038181d40c4070709000da4a54000c3e40c004110034413960305140ba050007045021010064464039200740d540d41503068018040080040381004950b024844400b02194503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198040332 1250 198039082 198039089
    0xf0c120a0506030114040b0c0f0d09150501140303040302040b04020c03040f0e0601210b0102160b031e010e010e130c12021201060803091e0409030815040b06032a0301 73
    0x1c07030681004000c0c1802c40c1e40504550500152040401c400705580044598000301c403241000e80e140b041c1c560490040c00f44100300c0c01b070103090106101c01c0c080c1400c40b00044602c800000c00403640da401c01c41d101b200c00122441d805400602c002c2015280c5030340007d08000c405070015140c507510300e101606503405074110812041110070240150049a007295034006005e0034070303061000701c0e040d500ca1084140d488103100503407150380a20320340c1d20070701c6001182d001c00800c10f61202c5e01d0f40302440b041c0c1c1003200d191026800585c0564100381a1001050403120403021855859003464046a8400340c010300f0182440e148a0004002071001030068004142c082110300103034505104000e00700240100b030040320b85c144102800319000100c21602594070072a649209030740c50903540c5600d10100700c2400e03805407405d0048418190420503240c8038015006d0b1184000705001d0400c01140d45191045410010900000d480180d040d0130f030b420715400a59586070204901096242320b1340c000d17003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198041582 1250 198040332 198040351
    0x120c030403030e0a0803010905040317010f0e0930090d110103150f1701150f03140604080a110c0d080c010c020c0d032106090c260f0c12 60
    0x800c01081c5036052040380346049903e0040e0840080c191500380b03940c0010b00032244070703503a00d5020400b0140035000e030803c0104040b011502a42e510aa10100d0b1003c40c80b4031a058150200041c80103280400c080d600301d1014032102c00c2d01c4003505141d49071040000512244c0080c10458060780f84c3e00e4002c005040303072040ca5001081901103000506980a0300d04241401c03e601406101e004d441220345130958060310380c1c8000e2084c00414160241129070103075584101202c0010541d0000318059034103881c003231224a01d4041c120242c080e52503100312005032203003005101c510007040c864584142807802140450f282004c200c0005815185003000442e482140001d11000d0381d1020f0103041d5422006001030100d4481c80d001140710303a506040010304101c01c0308000c000310144501c00392403c4060354010803116803100e2146004005091021001c500502e01031440d5003102d040311018081c505039480966101c0e030080030350716100031300100d0312807400344101c0100304003d8460503c80c2d00400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198042832 1250 198041582 198041587
    0x2a08070f0e18100204050f1f050c030f040f06090803120a0b011403070c030e040c0207050d05031306020a0b01140f01030903091a09190b180d020d05010f0c0f020c060906120c 76
    0x14101f00851942d844518019982203107503051007003840102d403101308080c1c1443c070b907030704180b03035400d415441640d0840b101d0780008034020840d419900142d0b0181c038401d031600142240c84080e2a5542d0041c100c00300103074607240000400203e07180d0002002d440060400c800b95010030540701207541c0044481d076001078654000001815030002c2b10300c0080303d06403420815a800020b0094480209001e003900803000c080900f0304001c1c0c20001c079100304400170416600303d42c03240002901da81c1e662405a0300103006400100b061a80c1d85190300701584006c2001d105101c2800041d8050a0b038401c041e82440708070000051103100e9010001911a80c1c0303125103903105018030400001090061004400c9024060144628a042800c95400e030b60110210300302604c044000843c20188410000d411600ca07020400400074150410148200f640401340201c3e95070070021195201c80e0900e030001a0301c00d60501e022410024010400780344058161032424010780404580104250340205404400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198044082 1250 198042832 198042839
    0x30d0207051005070e130b1215070806091302090a060305060a0606020708060601020c01050c0102040503010f0b03011a01120e010f150320010804120c2a08070f0e18100204 75
    0x443c8140d0358024030300d040040d403100001c00880d081d00301c06103100c0006039507182c480384196500c140d0400c81f11180001c407810000a2050070001e100c0544014010a0a10010034071510b8680c064a125004543c1080c0350301e4003030f8007000013400005e8041d60721640d4400004c00426010311996200e0540c1c11000308259240517002840c00050b54000101600a64240b0180381e90100703a240314003c007440c14545406080309011300a206a9210030350541c80e1401a403840c090720340210400100860080142894140c054003441203800101e5001a12003840b80307a442c440c41e8040400d000b80c58000240103080c8200c048111603540d0f08900328680d1000040040007a8404042c203241048084020411032410003c0d08c00f600c050002090880f840b0100800b0728400e03440d055009404c44602d020b0740c42090402c80342c1b0f81c08034805c0001e40c180220007142d4510b000403428200e80307600541c481580c0c0741c00031098180c180903111403082034288c54400510001001035008190800a006a80d6440d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198045332 1250 198044082 198044113
    0xf010507020d05041a1b0604030f0908030304020a090e010e07080304050405070906081b0f120a0c0c0f020f0a05090109020a18050d2d080304062a0c05030d020705 71
    0x60b1600d0007820004100028403524204091070b810704640b40812644600e428882c400d22400b413940d21803541d102d07410800c800d140c0d0010f4452400f540944034282c080341c40e400c110b916884100d030082e400800c11517007004084490380c004030000b0030030400011030741e40c01421a41400740580c8030500991010400788843d140500c50f03190020441d0510103806480c280000d440120b0040c00421048201d4041d005101e80305c0c001c4594800c3e2804409654004103000c0c41090310040d41d8104429160400716030300c06000e2450140b600f6044803207107049503165820040301490700300300e040c0c0044030224002082e4680b941028060103290401588a0381d106800404200088501500001106508102c0760303c8031084240000d0f04461180b41905222500c1041c1c4d00118041200700c11400300030341c0c00c0c403c440c40a1030087c1c0c42540d06224481c01e81140d110790030f41c80c1c0d00254040f400c5a140b1000c00e8011413061841a21031801c0c1e0741460203258111040b078014800a403000e40001c82c5070b69041c074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198046582 1250 198045332 198045343
    0x9080a111003020403050d08040201020a060c050a0e0604050303161a16020c0f06030403050310080303010b270a0b0304030306050303120a051e010b090102070312170a02040e13140f01050702 83
    0x260b40390440c141491521200c2e5910aa0820441400310501c08901564820300c640301d8800d4100c8414004481018401001503020010b4840000c858200c621420301e0224101c1d400c9620060096050034a1b8402d10b0007199000c09007150040013004000010f0000d014449114410303122413101800105072020341041c155102e0702c2c1c4034800c030810440c41c503030f551002d0303d4004d501072500d0703034980e5106020110f1607130098100c281680301c02f0000203020340a804c01040c0b10700c000d001402c49620074502000d094948100030a90023051a6000d0240d403155901443c0d201c2d020f860003082c041d07a91310200c0c0c00c0d6480071541c103001181341c00405c03034000c0a0f07010300b541045003141403421403580d001c60544524070601500050100000f44030a0903031080220703101450300b00800d101c2c0ca2110000207021000402030380c03c030503420240040c164081c14403d86040352070800300c88901381d950602000c0d00d0144c01100310b0b4913041b4000b5942e0303003540401c201600c8898820000480d8142180c000c0e2404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198047832 1250 198046582 198046609
    0x9010501051c0c060822080c0106060908060103080f2512080906040201110c1909060e04050d0332040c0503030c0a020d140d0215130b040209040309080a11 68
    0x26084442c540c000f500c5000c2c500e00312169464120501d40b100b540542441510045558034820354106030b4050013081d03030040404140110081021513503800742035455011300e105000940d0082c03401040400c664500901072004d0003d0341519140300c0794150b0024100a03041a1642810b040c540c9003048116441110f90344814209220649407000b0340c2640c81c48005c0001341000348554506200101c10400e18041d110010420078103602034010088400c003c030b102c1c031066030b818030340c000034024405c40c0e00f0b034052900180601b99200869901f6805880e0f43c0d11080320080c0a506412004910003c05c5100030302c0c14003548840f0305040c101018000e40c0c3c0c0d00114880d8000700941185598002600140e03164180c8206921241c0c508120100c42c2000031064008d0050b400062101c07a4040b07524600300805440c0581a9100c0c800e031001c1080720710000034000303002e40c030100e03000d031504a9011381e102d0701c6803500740215501e8a86842c00d01ea00000f04950f00c0d1800c0c0104a1246401c41415100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198049082 1250 198047832 198047869
    0x3061505040b072a06020303060f01030606090902030c0912030d06080c3f0708190f0602030901090204063008071205220e0a0507051b01020903060901050105 69
    0x401c0d04180c1000038510643c08001c00340e022a80c6003164450b900310700300c2500b1201d1314070065065079401c40692240d20441d012480f580204904841560003446068180c406075a030704543d2604000c1410001d51001e0030054030001c05000c5816035075142c0b5034504c0c0d5044c40802460f00e0b003841010f400e0a9a0041d0000310460300700c61415010740c6c844032032035a1480540c0c0f65881a01b4660004c1c03820700018402e0380c0703034180c040c0951144030800c0010800c1c1107808a40803100d04032141c0300740c40b88101042d840101040c0c2c0c0e84054001103401e50b005150041041000000c146580342c0c0050100c40b220362104040c241c0150100c0c1c3d100e01e1b41d0b8900022a417241162245166060780c2e459420b101e0310300000d12151400000d5004184690242c03010304a48070480c443d5181c075088642039602c3d5034420300f00c1c103203880b00c00206e01c0300640c0900c41c0104545e03100d40307007003140741510700188243c0b01d014485a0342d402d01c00c5040c203a40c02c021450007901c541c0000202d03541007409021280b2240c0810514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198050332 1250 198049082 198049087
    0xb19050c120f0705090607020109050a1d16020303060405252307080a050f0708030c09120c010f081f0905090606010f050304030806010504090e01050f060f03071205120a03061505 78
    0x222550480100e5149490031200b160b0f84454a08c01aa0902d41c90f410650708000406000f10740d50034240010752850603041c0d600e00703d950700d4240e400c0404258005080043c1c00a0011403028100341e04484d8000078040b0718184800f4007101f25030300500003130160000040b0311030040c51102262241500b038406908103c5490800203454049840c456035807580104040001c8a280e05110030082e80e40d540d511074500f6549041018030035002da04440380d900d10071542810690390080c80007405400300030041c0c44503070603030700c0c181c100b502d58000040210f440f00c1c414a4065182d10540188400a802072403c00101402c007041424903102e00140040c3c140802548020901c0c2d4000e800d40790321903030601d400c2c1d58958401e1f004171014002d03544500d00090800b140564035031010f4020354460400306080501c1582c0e000c0c200300078031609520841c1c054001450034401c0c0d45c59002d0b2071800502640072a500c1c01415000e003a131903408485028000b9603518020311050112001c2c0e00c04080140c40c0590 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198051582 1250 198050332 198050341
    0x30615090e090f03030405031c0b0f1002120c0106080c1008041101050708072118090e0a0507030b07090608040c0e061206010617010b040e040b19050c120f 68
    0x40040e0041c0c001d184656a803100010003000007002103a008103c1c85095980380d04040c039040c0d03640c5e00001c900456884038840c40700040c1282e4400e2003400200201500c00c0c0c640034a040c80300030b010b501462821400380c0340300c030401c09030100010308401c08400d00029a8900e46542d40d4105008410310714450354503050304c480c001c2e5020083e00d0300160080824121044800c005940601c210f1200030160b01c0c0c04600b0344248180512901c034003408281c8030580e100300905085403111001d0038640c00c1a00c114106019001d002e9101c2d804c0d8601c01c0c02101c19182c80c644910345404500d40c0111903d0300e800d0100061260320500e418001c00c0182003030441418541d945076401d800307500a511aaa1001000501c65070302c16919806070641d601c181d80d03803940c49060081001500110060640646900020b4502c4000045400716403500043c07200b0f9803202d41c0c583d80e500328003038410360000d02803a8401010100c1c0f880f030715005060020505544103515051042c8495000f07140c00a210071030000c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198052832 1250 198051582 198051587
    0xa05130f030512030a0b090c04170c030d05090f0a090902030d0e0306040b04081905030a0606090b04051c05030c060103020405070c050a030f09030813061b03020d030b060408030c0607030615 83
    0x5152003c040c221064982e074031903e9000003000d03000f07103a540c4001c0e40b1062000000e02d1b440223000342c071030034900f050114405c268490b9076407443c0f1100c1c64165021303090b10549588240c018194200d401001d5243c030f180c1c1880003d4181c000d503081075520503501c0c000c0c201145020483c440d0140d42c036007084d00d590005c03040001d80301c400080c03000d00000f46440020342040702c0303901140c0e2460340d01104a00700d502170110050031900700310740b055852440c02d8004a4414025130221007252141c0c40b2284c907060403c018011017880060201c24203c0301e400c40e80303001500030310103400751404400040c4110341c5140104001c3d180050804000d02c130b035001c100300c081080440d1041c81160107090a00f4443d803d000c041703030b02041d03590010301054004a10764245500414900c0125600d55540c06101404085d0b400d0540700604002405039004d506400b94490003600280c3c1c80c50740051000781019074401829080d640720024440d03081e0492701c200014640c052007182c01500381102150382968811354003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198054082 1250 198052832 198052843
    0x90f2703090e06010c0f03020d0206010f0e041203090f060b041107081b2a1002060c12130803011d0a020405060904051305010e03040303020601061821080a05130f0305 73
    0xb41400d07180c641000850701d9010b144c550401070f03030002c182902d0085c58180251904424100d00c1e005000b40000003030100f080118420a9510642c6016415283d5a40b6010200e4a50011805240c0c0f00c0300c001001c50f03039a039015403000e4064280440c1c82d0008000704800c4926240000d10890001e10010001c0b40d0010240d031900700011080d80d4203054190711151600c800c048003540f50701030f81c5016205543c5440c819a000b420140c802c03070004c8801010581e2122012104580c2058003400070303c21240d8101440c54000c2c080010404540025480b000c0a41d4030903004200e03000701103140002101580600c6a600404107501141000d04210024078a8450000d00c0c83c810340c1c803000420f030b01e2900c510762240c0c103d40c00070003048a18500307860031b6260b401610095015000700400040c0007801045044e1550a440c4581c500c61401c1220350b640400d20307441c1c4582e0030f0354404154000030f141c041c000c150710560b40d1912504e42c030300054002524a42c0360845c000010704210104002000000d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198055332 1250 198054082 198054089
    0xc030c120207020117100906050609060306010f091505040e070207030c05041505060a090602060907080601060f0309051b03010c021c03020c0f1203040b0f07090b13090f270309 77
    0x15948414500041711291941c003c02c1007505019014400d43d0301c0b2070a40c4504980d9161810302c4440d694000b0810103005554030700e604a0010800907400b50300c01c40150491035614103010850301d88611407800070b0402640200003040002405102c0c22911480781a44110300e8070090a0260079641c80664031744451141a000310303101d80c070042110100341d090202500e0094100360b00c03440000030090951049100c0c3d04050f00800003c10b590200c04600031099505075402400d80340d107402ca0440d1480c0e26030a0803010190340c1c014071000140c084c00202c0d40d9004400c143c0940604900c1014216000b140c012802e42d03111001a0205030803114400381e0310a00c5040050301e07145410030042c2042c02d0296110068003405640c00c2e0300c81402c80180d406035001d0a0345403520f541d020302c400e1207800161a450301003802200c0c20440804540010b05049124a4030b0460031fa56034901141500e685d00c82d0313604015180c1c44480180d4420075074103c401c500076522907144a030f258174060600c030910301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198056582 1250 198055332 198055367
    0x41206091a040f120302090301180204150305061506090603090c01020f07060819060308070f0b060f13050601050c0f0f15010b03010909030e090f100b030105100804020d14030304060c030c 82
    0x50b13200c0e801070103981920340c038141c050000d0110b0000500348124200700c00c2800c0f0710562410072a241003418590300d0700192a80440100ae1a80700d204d042017031044000003086d84040e0800030060303192200809103000e85881401403403011912400a402c00c5210341c9050020f501c03a440800c000c541c0054466000011001454184816644004058016604082c044440000e0898104051040040ea01074040c1610550944820041040c6c07025014010f543c084d052020014081d03019030f0009401400c1414103a25045800d40503a0038001101000c41c410f4105501d4000011400c5c41383e8580302c211500198095810880d000c5114001130140c0700c005031344e913800b1001700340c010000c4d450501c50040201c410b031b02d0095190081d9031000c4440364409500301da0000360b6582c542050700e040c1c5500400030350001c100040b0458a0a400900690740482c0b004207680c08120040048030344c04466901840d900d25103400c05130159041880d00000f0503103083d80e01504a54080102e128800c19071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198057832 1250 198056582 198056603
    0x7021c020d031109031f0b030309310606050705011b1707030207050102040f05030f0d020601090b030c04090302150702150f09151f0f29041206091a040f 67
    0xb4900b00c03110f4058110220742611880c46c403500400d91504a0f0010f50351440c0302444110018002d01d0340360b0281c0d01d44190003080388031040c120700c4404040019811588207803608140c821a005100303999259114030f0200340c000541c00e040c45403c1c0581040b200a095003030003c0910094018040d1802c5101d20f070401005001164078039100750110b4142c560014025901d460311080e0400700d403051841780d24031a02c20100c03200341c0341e81c01140c030007000100307a0040c00490303207040070040c06040b01d0840e81c2d5050058901c1c41305256180c1c480d2900c114002d44c0141070b2085400462840319502a0111055600c01583c5015004d80081c2c000d42c8000c031404650038984886000c00d107045255500c202250042d8000c00c202c004201001120311811440c040340c0d480d50b2100800c1d0703401101e000c0d8240000010742c2c0e0195901148018809031510004810301d0595128485c048006540200700c595039101d1000d8400d00898090040c02d14040c1010080541030503528902041c0b940302000b8010201d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198059082 1250 198057832 198057851
    0xd030b180c071416060c030917030705030c0322030f0615050d0b241c0c030c060e0306100806041202070503151605090a0e0a02070204020f0307021c020d03 68
    0x503402d440e40305a00c20035022140d00400e031202c3c0c0b02d80012240d51542c608031940000d001c0e11541c5604115074040d02c032500f6050a1440b0190380034911414812680b000700058000544c0420043c02d84003440d45c05945c941d4085002550b041d0b40443c44240e030321050b01c4083c8081a0004c2c000d50640d903125200050148071340c00400030081c041c0d804141c1c480d0341440b1034400d204503d42d000307114000200302040c0c2075010111481c21000201000e9401100503005050054184007020b40400d000d07a461141c3c40b60703030360750b0300b00b4080641e04000d000903644008001c450904005140e0000c40c0c603039090700f905c1d08014140e543d50000910281550040c01e55800e070f414002e0201c14081d20022f4143d0303154850705e407055034030b0300300584100309544e86071003250380f04034800c03c142c1c0d040d060003c1c05194030624028203418684009401c81c840d840d42048400016555807000b09a400703030402c0341d942c41e464902806820803450481d00b591800c004164511000e9010900d034050a009082c0015140307203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198060332 1250 198059082 198059101
    0x408041a03060a05030708250e09010b2e110106090c020313090204120303020d0e101e0501030809010c0c05040606110607020d1b061107030903050d140409050a09050a030801080d030b18 81
    0x3965028412794003d00003400541e1106404c081580302055074481e001d1401d02c07030726a100902c109061786009020400b12100369202d40415217980c1c0c0301d1000031814544481092003114000800500580d20000e0307200c000e610b40980c11002042c130840d085040c140340845101c00c4540b083e00040406600042c000071080c065403180303c01d030120b682124099010b0482c10750003885400d041040300800d902084c07501a600e4014207041ea41e10033100d03130600000c9001566442c480b0002214105d0340400d010400c0c0d20743d40300703610062110b6a80d007420201d243c0021410302501134519002c641000c0500c083c46508102a40c020f01c00071082240078100c1030510700020300d40c00b9080d1403110ba000801e0401d05621588020580b4018000d032418016141c40540ea0361040b0143c0203003000040c0300801016150740e004e1503100410302c00108003480c195035542d080a500200c00c9003ca00020010b1111a40030800641141e01c071741000c0001180c1800000c511154212401c80303e0003407a00000ca0701078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198061582 1250 198060332 198060403
    0x201230409240303260112020904021206040b07080903090f01050f0c06040c081501030b06040c030b03030a08040b0702010c020c060f120108010f140610080408041a03060a05030708 79
    0x82c9140340100410341c603403400801d914100090745060b000700c005412140c210f654141412a44584c100c0c210b907204a034240100c1c0440140180e80c440e00d5403141031242074080c0300d414401d0344100882c1d03650303150041007d080d8150180072182164010701010803103880300f580b41400800300342081500d4124000d500300181c864802031840758040d0030180410017050075107080a590300f900945180c1c2a0280c0070000c074030024070002d0b0100360000e000c501641490340c0445041080f0b491f002c9a51388a03070300402e14662200398641c000624603800c11003070001540c08aa00000503100900011014420080d5a45a4a40303240d108940018414102c04001c5007150103499907080c00315030325a507800b07000d802040410007550030b02d401c00b2101090030003100002441000010400c88112030545821146694010402c0716002c004010210f40200d00d90b4141c400e00c81098442583e901d44007061040029203540440d0203a400403005100c001000b0400c0c00b00192207040b80801c01100000c4e00d60300340c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198062832 1250 198061582 198061631
    0x403142b0204090e1e010506030a111503130309090c0f05180a080a0c08060106120f0e1e0705060304080a080c041208072303030c0702012106030201230409 68
    0x914180e0113002d82e0b80302180310392000408190201c05408120041d60980304112081a8550480c0b242000024030302102c070a092034020b01020480c480c0c03104c5407011580107131144405003100c1b10903001015400b030880c001504075541c0c14015603000202c09401b050342e039962402440f2003c64019241844a0000c0a1000f8000c1020540a6562135044d0301c50303c180c40d0030f0720f5039200c244002c2410580090710314100d035600e07a070301c02c1d6001c1402d042c030b03005100c00c443d41000541c031450310034280740d01006004005000042184007051083e03d107149410f0540d8841401110f080c0100f00128805400340c888249050400107000c4d039944500707110300d02c119040000c540320301000c04000d024190b0050046035100d144c010030780b8110840768078070f0024407201003096a441007000030821050030010b422860700c103041100c40044c004078112a900008104a0a21540c0760404c2081d50790101c02c80f6075400a400e50702610324107203803020761584618015000c000c5e450728401da0360240c22000500c980c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198064082 1250 198062832 198062849
    0x305120903030d1d1e030901030b120a2f1309020a030f05010f0506060702131802090406050601140316180503060a15090e0712020103110c03030403142b0204 69
    0x135a001902c10644020321101100d560302c240e0260b0b0034a10444013090700400c502c2c100860401b49060011400741200700011900158100201c50501d1810456032081d244545103044d82c0e0310080d000340c0c035034402003050001100c4080800850503181e070300e400f01c00c040c0b1f15500072030361003400d0001c50181c5045600c000c00100307144444405000040d40104002c01c071448050109446082c100100e83c060a00003a620880b40840c0112040390f07940464404030340f01070314807942030141c3c0008a0084040700d094603866210004c02c402c1d5a40410902089540555010f056081417240c415825502d504070905210380c00c0740f110075100302e42100c90010b000060484204c1d01d4440d42c40005003c02504001c0c04015100000c210300307406005030b4200340901c000070604545080c4e55a41511503144050b414141d55089a20b64655440b0003049000410300c011552801c061070010071441c0104c030000d8845100340801500520001c100700c143e411807880c034917402451100741c00000c4c070955011008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198065332 1250 198064082 198064091
    0x70c050a0909020f040504080901031a030d1809023c0705010b01171303140708071a0105040b0d080304052503140111031308070b010303050409050a060305120903030d 73
    0x1205007454100390718807071099408448925107202480f00303503141540d009200050911144807507503c40d50052195441d403000d0603428400c03400c0031034189084c420761800002c203180064020000c20840e072000405c50190218500043c4040070160044252603030880040d620000c5250001000c00b01d20ba02b1000444c2503548500d170703140c0076000301502e41c3c40c14086601500b0b4517411410122401c0e12070000c0b030201c107440300c0c030b140e90032141c065003034004c407100045c02d00c4050301141941001d410031601c1000e40c0740c456080ea4074a1311450f00141d11503417281d0304280700c0e0b0b4500c1d25070b4035400d84034988c0643c41d90784030748451800300d01b0710144010845411815020540803000c08840b0002120f0046c20901e0b80c58240000c190700340c40c21044007010061040000c9001a0401c001105e24a0b00803000d441c245803640c1c0d14110800f00a0341b0a50001d10040317002d00000c1d80511443e601302e41104e80c02c00400c1e2650741c2d0b06440340050605800c001c18080b0760310701caa45003402202c1c800701c4034400420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198066582 1250 198065332 198065339
    0x10030f08070213020c010b0111100c14040303020f0f0a080a2f0304050f010201090804030210050409020c0d0f020307030e01030f11030a050114031515040626010f060506030c070c050a 80
    0x200070b401045e0340181c1c2d50f0800200b001e42e94080e0101c402000d03041c0c400390400102801a0001400b05109200c0c2000310301596046218008009031002d13502c030341d0107010000c6e250b00c0a20b14256403101d95000f29005081600c0003c0c1c022811038401ea04a8105901507100200c0003911680c0030071088c45200c40040d280301b1440901000420959001b06c9440e12400c0b108030049089401c2c802c0028407080c000c10050003d8a4100c2003001c555480b850240e203003070345842c1d0503000da0308203601c0c140d1203034043d5810b4180300c0c2d0403920b41030313a40312039100440c1414241c3d140242841d00c580d0816040c107544442c3c0308200c1c038854010058094010407640d40d2030402c034040000412003485403494070108000089414a008512096402e101c943c1e946d0003600d82c1650074086400c40181c42e039003c1e40e2030400144c10454000b281030700789030041170708185200092115080d1551040092006d600e000ba050010780d0741c030420740340c10050b43c48003541c6851080c0b6007504040d04a80240e03500c030301240e0000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198067832 1250 198066582 198066619
    0x40606080609010603020604030809032d06070507030f0f1214010503160806010b03090114041a010b0c030f030c040b03010803030a0e070b0f0304030c060e0f010509030310030f080702 80
    0x880c0c5200080707a400359204188a03088039404e020007540120200000c00c007050000004e041d017144004c00f40c1d110314090300792034101040c81c4401c20860200c3c00100c20080c40003809900d5102e64941080703440c0c105942d0f001020082d0840c0800180490450603100381e611501003a211001070a00070480515080c900f040403207001d1041a10034410038802c0b20b41c0410004214085485c4400184846d1342090f108218079040144078190130b658030000f0307003a000d01c40724015000e14010311059403031030214400c056032030340140c002c4070501301c0401c43c1c174000d04000000c49509482c0c5543c0d29482e0344940c154010544940e42c011905524040000f20303450001000450240d070309000104116424514115255455481080400c2d407041c84140c0c140301e110001554401d120f4034150b0011601f42d903544040350184200560140d12845071002c42e01400d10bd095004040d1800460443c5803044e010f000e030341520700000b00640d01e25020142004400c0c41925107a95009048107050100304800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198069082 1250 198067832 198067841
    0x160b0c0403060f180b040305070807150b0103050603070512070e04030305100f05030d0c02012d0e0307081c020307080c0d1b030e09090304090207080304260427050406 73
    0xa0742e51a02d0245440040162031041396051414031032292075501e031136212000104d100030019410301c1010011180041c1c03410000b80794940c03040034134451200500d01400304031400f203005541030500d00000d018880d0340001e2b07170f85c0c2159402c6074211208200c0b6a14541400416402045a040e090041c08105500354002500c01e0411002041c03242d6500d9800c1d030f9640c07040b80300e10780e0550004014040c905200e104014034003030060504401c801c02030100c0d881030342ca142c0e0351a41c441a40740010b440150388250700703015695045004000c018280030945480c0ca04270060342880c40c07001406003107098002d02c00d4400303464000171101c1d29821032408054039446c140d007004000600250222003420506010070780d4139038040c1e0300c0701e0560f0f00000c14801500c00103000340b24288024400080d100b001c42c0014050a440340c40215142e081c00d1070004d908884c0445c120f00741c02d045600400e01a079002c01590122020404900505607824030700550b04014508500c125034100002c2100b0300095400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198070332 1250 198069082 198069089
    0x9180803130204090b07081303090b09060405060d0c2c040207030311030f0f0c070b0a09050f0709090b060411030a020a0e04110703120c0c02120f061008060603070e0408160b0c04 78
    0xc47c5142d03942c8102c000c01c841070b00c0744001070118010700420b1140c81c00642c041c0950343c07000b604540c07900740c990300010340f00d0b040341e000c2840a50b11000d0751000c00364880a0000f100b80c60034840b240c5015042004080b000d0000b4002c1d025550104201c4c0030715100740c1080011101e091034090f80c0e828a82c1600c40d1000f070482d40030a1000c01000403032000144941180c2e0110740140320303803c49845940c6400041d0041c05825100d6105050090300c40034400c1c410f03880282150500065454144d1820100c0b40000070401845141f4100c01c40c1e07a003520340400c0720703441440c03100300595903581410256481c001e410310940e0803924042100c20032054503401040100d00075221902c1011804c0801ca095807a520008000103040b001e0640c014140491014001c00b0724038141d03114401e00c4001a850407500710b42c440007030001c81c101004042820701402d600302d0030039005411aa400e1012803c419103010300024661480000c0581c2c81400c28541c801c28258445e400004500b003502c034030001500a0300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198071582 1250 198070332 198070337
    0x60d0f0216030813080306122517160524190e240d0609140106090905040506010b0304110310270c030221010c030f0609180803130204090b07 62
    0x100410004460840300300135859001110501e181d8a000501518002c402c084507002e20501c2d00790040f03400d021182c000c282013004204d03220035280602540143c15141560756013500005d49a80503580081c803d40c0039100d05035055042d0200000010081102c6226070341c0ca00070b0041104d0140d40301213441e0602420151740c6640310018100c0402c0f40c4010003070421505280c54500500340e80500d44058941600c40d40000a039407503440e2000d40559501450040e84012500300500000b50031000990280110303040421503450107079102660b5a606020300344c0040d4011000038100103200605528101001d0f099505102000c1c2000001c2c018040301940b494000d040c007001c104014158000701d15800c69001e180c082c0c0b958007031100004100507051a02c0010215810941509014404600040d40d400042c030014100381d0404440c15600521115410004010100c071080351800000b02d0304846402e640327495403080c0941840c50003070000e4015040c040034405005e1451403180c440c00356078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198072832 1250 198071582 198071597
    0x1b070309090c031401030b070315030c030506180d08040f05030a0e09011401120203040501150b090307090524030c03010c0309020301060b040620011d06180606060405060d0f021603 79
    0x2d042d001d86001d24107006504414200400c04202c941030b81c5600700c11541400208401d943d900440141103e810a0b0307103199140320200200729041202c647d00009220440c01d00e0791801d0849511103540100701001c02410001003010701049116034228540e100e0100ca0b581d0031004806003008908644807841086c0990001601c0c00950404100110b816174410b0702d001c2e0403034848002900041c0040e02e2541d6540480c034200182503807103001801c0d40d801810b4880c0048410140b1301483c5802c1190910f040800303000c008900748158041c90b03ca064a0306074031612a10101380b402d010f81d09800d83c158244400c4224140d0592300020b0402d000b50001d004091301c400128100c0e129511443c0005503030440840e500480d0b00c611f82c5900c0d480a000801c2242c1c1d42c1c004c07406601d0780c1c1d802a65254115009200d41c1c00c0650b80b107080c440e08107402030300030703840e10f030f80081e5180c055072049074055030002480044404a81e800341507007000700740085444100c0e91400c40c0504205450460201303054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198074082 1250 198072832 198072851
    0x150f0a0c020102091804060b04020f0d0507020a0b04082214030c04020c0312190515031603030e13020c1002041a0324060903010519060605030408030403081b07030909 73
    0x10f00803207045070f101620080803103903900d120b40b89849008105940c00ca9940c60340c1030003542c9038001000c0201e420308c4016119100c802003101107460141c02007055601c40d13402940040d4000c00c00350b5019400c980300f1902c03a1842e103000d0102d4070449010003201004c10740007048220f10a090b81d90080410790489110001141c103102c200d01c07503080d5044180d8003d02c4811462a1107a401c158410710040a11004208988108042e2103085d1811031014607481560320b10340c20200000700040c0c0400d81c070005450b1450b00c000e004100e021548500038900c01e064a81c640f50203404490100601008592030712415090400c0207401c240590a8007202c00032071402011140c0d800d490203810400d050091700c08a00d405026425503450070f03550000c0045c0302c41c0c1440e80d000e100d1184580f01a0105060200d00f8001000c22076005800510900c2800c1c0306100128a04c1c0080c0c992242d07046c1000b4943d9114140041c201080059031a02c0788100051038000309a4449000305c121386614201f4880741d0780307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198075332 1250 198074082 198074087
    0x20715050103030201052d060d0c03080708030712290102031303120f0203120114150d0608070510020a080a090b030a15050409210e0d05030315062802150f0a0c 70
    0x12031f075441c003201c4d0302c0d800103d06207142485000c40d0003841102140388155690b5205003203500100e40503030300c5500c04020416001e41140321201c0b0742039004800c01900c0d040c2004912000d0501d91b440c0b5514914141a0402c2d9000700b0031600c0280300c003402c1a800617500d29100060100d6001d40700d00151100c10040c0c2c4290001041d61545100320f054010300ea030904075910200204d0184442c0c0c060b5000c80a00f80d4946200c1c0104604814044c012031010304164001380380c21902e910403406440c2c1c01c2400c0364071990100e4060042d0ba404004169245244a400c441c204502d03049403d07140030000910060305020390040102d03801005c00321628a540e801080b040701d0340360f5000740c042c0720580c0e85021002200141c401006a090408691440410020a1041031505811a03040c3e00c000280101107030300103c0c3c2c00700c841d0102c0c0c8017440c0000c0040c541440410204c6100341185e109040d004006009201400d0710700510070546690780b4001d403104100c00c0003619003080e842c0c07611403900d0035a032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198076582 1250 198075332 198075391
    0x705010f020c1e030d020d0903031d030703030209130501060203070c08210d1d0114060d0c0314010b1009150c05120904060807030f0b010b07020a03030302071505010303020105 77
    0x2800c44001c0e144003c9041007120010418001caa0314502040246020480d91172020309040c0c0b107a0301700040e500300c8070314004d4101c0e01402c18001ca140c44100c8a00d4428100204691030030b80c0c140380242e2038100710300119502e10b05a014011003a4140070001c50030503400009410a079000e4805462015503404446455102c24914840701e00900d800050712500b94000414284512200c0050800d499005103680f0302d20040714154165103a0140b04240a0310071040c9030400812206501203c10a070707103800541185200003090082d403500440c0081000307500c0301d12100c0000c0d04035003001e440d501c40109005001d000b0344030340c01c5056030000a558030540ca6403641070351010003082c5240300014040e01da030300300340a01a40251200700104030b4507000d01c05c4130000c51056024a804207541e10b031000c90070405070482c5400d120203000701380142e41c03501da039041126094180140e50381400c2c10030b1a403c05024001240c12414003000104060741507110034851fa00d0b0107011380d10000081d1860344ca15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198077832 1250 198076582 198076597
    0x50601020d080603100501080601090e030405030319020f061f06031a191703030711030a0e06030406240603050112030507060b0d05070b0306091501020303130321020705010f02 77
    0x181e111610034407a450044040c290051001070854840980c0002d001c030a0715400d030003444a640254004020000e803d000f0101ca00f01c41030041c40c102410705010a036240a03801a01c41c050202c00080b521060003131024103001321516081d9001480c1c00c1000c0b1846c01062020751140c03003902c04000603003d1180c0b0078030800c15401c00c902031700340801c1d60400036110389001c010b02404040e0100020780c0d440c01010369000da405030024503203034a06542c001d460040c2151611220750000c004032059964001d50160030402700f101d91a40340e8413103080107002011038036424142d403404140c047c0d421010030304a03481222110759061040d0b80e210030446ca5000d001c21001030105a040c0003070742c0000d0b44d42d04200a40000908040d4090b0441d403521403900c03041e0f0703100320a5068000144186404c0614400798061140091180802ca201000039942d100003017901c100c04e56a29080000c02d48180c590684003901da042d91045020308002400080d480103c04540c1036103000c00341d148108160003a00e020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198079082 1250 198077832 198077837
    0x90c0108070e2b03020a021801050d061a0a06020c0f0102030a120b1c0305030711030a050301031b09020a05040509060d080301270c2109080906070c0513050613050601 73
    0x21052030900c2110f841c080d42c41c44032011034038298000c10a0258080b9902070080d80104802c00142c0180000b105c20b10906180f4040004014040f98454540d101d242c158040e1000440200041d140c0300d1510b58000c0142c2d214042540000b000b55001414000414040740c0c4010414002c4005a80e2031094003444008220001071040e00041141d001d501075410141040c070f0340180da801080301141c41507004070049100841484000c9621021500c201f01c07900000318034010581c08041c00c1800144070040600195801c0499170044400d80c050051201d070005641790f02d070514024100e50401e010b50341c0100c0750000000e549140c08460b005806811056a5185034200f1110412501315440c00c0102440b234402e4045059040e8411142004d400e82c1c2c840c1c80b101d06210001e4601c0010f805000030030760400c000341010500d40d80803202c066030102e90655540340140703812100010750340d01042e441040c40402611804803500154840d0070115074010180c1c0d0011500d00c1120002c0d00c66500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198080332 1250 198079082 198079097
    0x150a0b0a0f150306060f030e1002030f102321060f15040515100516050d11011e0510030c030c090506100504090203060a150c02040b030106121b1d090c010807 69
    0x42c0c085c000e80c42018103003e00c0c8c00381c40c00c184440302c0d40c005a03803054800d410714949103020070200d80a0200c0300409400c3d21003040c03040c480907401540391541240720980c401c1802a425051040200c50030030007000c6c250040d01d4a518101368400c00c3d000007240c4003c0b8020244a8440f10351802d4801c6500c2111002101d5201d40085428090400a501c248a0a101c1e0800c4103592015903000c0c40381c01241b09400914082c003040c40001c0c10420401440419a03040c41e0b00500d242ea10020200602005900002002d0740d030b900b206102c98190307034409003602101f100080300b8804040c1d250800c0e0b40b6014011700081d202e140038045840c605847c0980003c0c028442401341c200f10390011500000c00138801c8803420703181c2013030603442100b4549510200d130b810b11403141141020b010b08280d080085000300181e529120b4100949503c4641c010f0002c0301c1400660601001050060054035400e0840681c2c412181c218078405142641d00f0302480c8203445801d1030310361190100074030580d456581d04a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198081582 1250 198080332 198080357
    0x40603051b270c0a021608010219050a080402042703080f0f07080c2b02070506010509011d060d05010603030804030e06031b07050c030303070e010809010509150a0b0a0f15030606 78
    0xf005900820300b42411401800c50300c030f102501e4000408040e0540c00e00050380c5050402440100c0e0244050300c400380b12041c80b43c008883d400000d65907011350143e0340480d1a0300c030704111541c074000c00c0030342050202c007180500c2d0a00d03a1152002e841010b03405403041403501d403c01507540c150412039600001500003000288050700510140081e1421244190001d0303610035400c155000c488480c1407074150303006c94803906000080092034014401540c21a105505102c03070034100412004074016040049404a0110f071503021320391540750f1300107008100e00d540381d1500a00102040d076041d00000e240c00003068561410380110380c0110100203c18407841240c00c0480c7c0160420501030320b080c0520000d00005440a000851184030180d0b0740b040c1280044002508918001c0d00c5001160701d05410050700000001e4a54003c0c1c002c0d0301c9411084d502c03460840b01502044259503000414454001409014040c818041c0c1d445015025180018170301c0480455000e40320b6000003a08428100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198082832 1250 198081582 198081601
    0xa1101020a410c21031e190903050909130201080c0a050d0b1f0306080708070e010306240308090111010b0906090c1b0607110a1a06040603051b27 64
    0x340204103000d41a5465100c1310504003984030400500e492401038000200217550102e101094403613504000d0140300b50a010320148681c101a50100b1003030f81d91494103606043c020380554802c800020400e01c0760b450040d140c0080740201d4202207001c1040301c000700303075201c0f60042a43c44150b00d5650700f60505a0460b440c7d000b6001c006440c1c0c2e00081c810310156003415003e41e601d81d144c1c0140d00d01141642c94524060714146840d4003440168100410a00c40c250141c41d1290459800007070104a44014284004039221306082e8001040701540c0000100314004002d0314950000740c890b003400c00a400c02181c240e0320609002540420741d84006016442c00c542e0590f002450b038501682488000b040304d1811038035141611074158000810440c031107510000502c00c08105101900c2e509089580301155030450300c501c048a60134400c0003e0507030302d442e0320010007035800104596526001c0301000b60f042c008240c142c0d0242e030504034000010400c1c0c840004881d9025403081c4801d50362010030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198084082 1250 198082832 198082837
    0x4031106180303160c0b0403051f060510080405010b0d0b070c03120e06091905190204020f04030602090406050f030706080405070806040b0a2007080a1101020a41 71
    0x11440701910881c1c0591903078400700050540401c140c0a0341940203080d00303100311070b98003503800704585800410042c40080e50104210340c1c5100121030050038400b00d010304030081d0601e5001282c0040580f01202581c6510404050023540944000c01c2000b00c410180240c11900c51800b4000351145004200364911502a00140c14000e10780008409809920a07040d282c035010f90f24421b9024078140070701c802c401d1003000d28140f200c01d060301d130202544c0d44098a40022034032030f6035290b040000c2c4209540f02c94040300c00c5595200d07080d56896469207050310003500401402c1d07020750328001f004112810629016902001c00a000340805882c12604868811008104a405000d450b80c0050250b40401049025038443c50b0b05654501c2c117148941d0071280c0040b0020304c003030781918071410100d03107080444694a4200501c0d41d40c03480010f0f020703104117801c10b10350342c1658400100341900d40c2d885000150072140d841c00b10300007820143c0c120310034101180080500300c41d545054056000c4600c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198085332 1250 198084082 198084097
    0xa0f02010f060b0405130510061b0501050103080c061501020c0d080c0f0105010509090303010302151b06010611070504150b1605030a1e031a06030a02160c14030304031106 75
    0x204840c0d1244214500b900c195502c101c01c89200494240410300e03151000e040f401081c0742042050b481c02c502e00100e0101d05100f0701042c0300184585041100c01c03481c0000250b50001e0080c41203581da45001912a4889071a441d6a07024000100d20141103108011380d40c07401c141c0c0201481d40c0300d4070400110784054142110301c14810000c0c01c0d42e00f1000c0c000301c04100120400012190b140030180003900c0da0041041c02c564000700010300050361412a1444c44d405400441d0341c540c0d43e0070300403406c04112920f2812503846202c1c00080c0b40c5078441c40003981807141d03400342c51001d0307a41c40500090f030305842c554180360600303900f05000c0c00c0052400341c407242c1a84000390120310f2040e1036017401c540c00030404c0c0780042d0032408050f151020a005004244140c1d280402240f18240310a00045403c5290a4462100040440c0c074020341501900c10038903040c4400e00c4c64030300b1840c28101460280c4589010100840710f01c6a044c0b4000c81a501229003090740c4104030400304040008540c071401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198086582 1250 198085332 198085337
    0x5040b1c0b0907030609080c191e080906070c062c10170a02040603050f0421030e070807050a08010e03180a09180506060324060a031a0a1107080a0f 65
    0x3c80001c080740c41c0e40101501d1902072041c6035a2403108500e07103070500c80809003440758a42041041c0380012840c0303942c8a0540c103141c0314000c0e072054910f008031441c0300e020301440c0d02c000041186002d203c00034044508450040e00e03801000143c4080c80254203222081c21707940101110115445400c00d0310340600c03101440d15040c624802204480c1c4190b200641d82083e100390302203802d11005804d40b00302030304010003000d400114a0300e50b5132400003007680e5249003c2d0b042070312852a0654042e400a54400c04c6182c155650103444401495403a913003441210304c500c00b060000180c800f010b05c075009001d450007015501c0d0001c200c0c0e11041f01e104d00412140c004e42c030150001a41e04141c410343c1002c00030180d2150086406c2d0030114580320780038040f00d200781c100101d070021030042c003040100d00c1d401040409146036109070001b900c5c11a280d1000d0218840c801549021440000c10309206112a000c01c002040c400308580340030f030142d5a00206884820410cea0803035001d070030000341810452 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198087832 1250 198086582 198086593
    0x50d0e0a0503040807060e031f0c0306090203012c0108060403051303120f0e04051014030109050604060903080a0509070b1b0f1e060f0408030c160b0105040b1c0b09 72
    0x141d03241e520307650190384100d800ea085084140030260b0703c0400990406802c07001860061900c0d1283d0f81200c6040040c030014a030b440d9116001035000350041002400549803c640f03d41c4e43d03a18190f80c0c0503040e00c9940916105c001003201002028000314140c603640d00007003613685e98a035820782e116030050101040c034003081840040014042400d103203e2115940d100321080c3c41c4004090120800644103e1045051104001e40a194012860121070240c5010a40c03100e04c000401e0041811900140c01c9018900c2000f007440226081b60741258840d80e10f44005a40c0c0b16800c00450b81e060328204001c0d00a5071041100702402c4010381010210317600b000c1301c144105d65800b89455402d0305041d526802060540c0e1200c20425540c000c00f9000078003820603854152561511428020700062003040040081032071aa1490142c61064000e03940007504801c450030030401c120070034440c0340e200310304000c0d1407141f50a000500c641c241c0182c10002c3d4100350155030f8100c2898004050308600d2154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198089082 1250 198087832 198087853
    0xb0702090606160f031e08152103070c05100503040305070c1d0604050703060b07061503120e0a0f050108070809010b060721020a081206041503210e01050d0e 69
    0x240780e440100c0912482c001d000d02010b5280c09001040e0070001100a86039115008846c107070040d11180d80801028410201281c8600004041c041484081e0b4510f9066603010351781f41100100900446001d40f00c0c2203003480d690030070050983c102d5061400000e000f07201103030029004001070411544107001c0d0301c00e0a030303d407241d035900070b038846007100c80e0403280d01c080c440340c0d0500b40300e0307150007100d1841c007488428100703c00c1c1c20f2240f154080c001c1c50705548030345001d6422010b251481c050f550080c0c1010000150980091211507209607540c4504050f00001074400e2052100c10100c43c1e041e11000410b655000080e11440f000808281c0655240c40e91002c156072024000d01300180b03e07402d0b20001507468214886000400303a201001d5501244418001c60000e02c15910302070000d00c0d6042141e611000418044d050a810f041d25608024101000b0003010b221507140500281d04640740104032028111451030003441c019010410422445622402e1600000214526002151025a80c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198090332 1250 198089082 198089107
    0x304090c0912051b03031e0705010204080313031205070231020d020a171023030106030c060809010b0901090b220b01080702031911160803031b03010b0702090606 71
    0x14100c42202c0a4005114403d040704c4c403000080c00d8200140c000314200b00104680d98002880c004943c506080082070318820081d0035011200a000c40c801620340b10104400100c103402e10a00044800c0c940030710754085068884c60076190100c1d00100300108083c4190700c0c2c245607170242c010700450070500d03c0340307101501c0e9070703000410419412520060340e038456110001d180d42d80950503400000c050302c0c280710342d0100f4000312005a642d004880c9030311411800101300c1660400c0f001725015424181e0000500804038200803c848858480c0c02007559201c0080e422200460b2103160312000010061003080f2590344a00c01542018110340d4030700383c0d00f110a0400348041460001082d0b1030342c4c80942c113564404496600205140000c0d030400d06c1031440e040c191020341030880200031078102d00001d6910200000798543c1c21070b40c0041e012039201d10449031241d00484404800603500e85048242e601164126030494482d00c01e42810450141d08012503904060102c40c0e0080051102510194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198091582 1250 198090332 198090359
    0x60f0c090909160806010e010b0307020708061f06050306030d05091c0615050d110607061d0f0105130f060b0d080d0204091107020306040b0c040b180a0b04080304090c09 74
    0x180b40d20014100c050f00e8500140d41000729800c406103a0f04080c0c0104402642d940c00c407815502c4070b540303042e01c9980b2039008900e8800b040e80038141c2c502c100c809024900c2c9148411481c0c1480c10440d00e003c650b1180c81c282c0e400c1c40180c036040e4140e401104c100e0880b42c81000603000c107220041030400301c90000c00b20442c146c4407400081e42c00550b00c1d180000c820100c00ca1041c0108000e0300c408064440b42e8580001c03107841841d1a0b4042c050029408040001c2548002c1580001e1140c03a00c290100250751661400340c0c2541c8441ea41c030b4400821070400fa40845401919400755640c0000f4415580703840c05050303a00e014540181038125040001064240940500c3e10f22400042c1c440785400e2164040d2035100c03007607009052041200c1c0d0f0150f1804580298080e401802410301500c0f09881400b41d441a0391048540c1c01f008908500c0d400c0d02c020b041101423408549666041e42c8032001c98040e44602c1c030405c5410742c0108402c00022460380c00c0200d11040c03c0c100904119501c0116400b100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198092832 1250 198091582 198091591
    0x201120c030605040c0804050604200d060504050c0316050415210c090b0105030402042a0c02040b0a0e1f0503070f150809030405120a060204080606010f0c05060f0c0909 74
    0x2070322900c0c00c0c441c83c1850312417051303402540d183c01111803c0a450b120385462000d4405001f808805103030094414690072600d801d4280600b80206010560811a000701001c0d0740480f43c038092030a0849070f616000901150000007076008a10851900c0104402050038500e44480c0d04882c51000404500627050403026080303100b90010b40c80c408d85800d06003003182c1e4002a004a19000c0388a51990340f00060725403242c1e040e00e00145288400c030460010303452030740001c040805404040c10034668801190740203a8802c0d20140080340d03020080046030304240c01281c0914803000d0019840d46240902c5504000054489030704058035200407a007800a240c01003403000b81c50080c00c000480310880c4140d80c0a01d180750100f25402c11105180c2c0324862481141d10880c942c2e0805400801c040c020540516400311003150742d40d40d0f80000d10b454000c11118035000c641d61040103030080e40604100b24516610001425403a81c600c0c419000d42c000140c00d80711080014008240940c03100d03040103004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198094082 1250 198092832 198092837
    0xd0f090f0308090d020d3e01060608150402070f05030f0301030c080d020c0108060609090f040501060b0a0912080d05070206090c04020403171b10020c010b010503090c010c0201120c 79
    0x90390304002d0200307a80035005042a038040f00c02c4042c3c442e408901107520042c2440c281c9201c0041141e0040e84010346158103c02c2d8404420f19420202403440a00c40411014002d009660740c1c0c0c0000d45400380110b4400440e21403e07100001c4a05e0a03034010700129204104c0350448600c1a12a00c3c5140c100880c07031030500000000500034003042e805184003e00101c402840100042c58009441d0700421010a0610180d4400b1560036a5000d0a803004031300040d00501c1c40c5e14200340604e16040040c2c400b6551035107440c10102d40744100b2170440c0c880407900d40318110b01910340903a69460310b60118042d601d009082c000c40700c04041703500415000c2c180c00d81c010a03603414044200d03420080481022849580f04220401c0010180e512004400b21805d004a40300c80303051805441110041090034840d0060641100d402d141ca0341c05807001141c00c90081008282650045d41d061206403110b0225900c0101e5001d61588600d020854092061400180301e03950030000c0704c183c2d905522110013 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198095332 1250 198094082 198094103
    0xd0e03060f0618010b0a1e051611030102070c09060515040b130902030f06040b0a1a09060d0e0615010c020f0f0102010906051006020c0307060f0c03020c060f03040b09011103010b0d0f09 81
    0x100c4030340c0b250541c49820b1f1000c85140f2248400c40c000b400d140320b50000d015140541800c1e48040c0311115520084001d40a0001e55482c0c40c1c5141106480c40396000f04252030b03140c21008582d60404056501d2a001107074203c0d45810b0402c10710200c0c640000404400740b80711002c000c101c140c118005103000e95a010030640310b604080d410401502c901c0c8031300758058002520200500060356100d036950480044d0386030b0303a4654100208060744160f5640e0012a410600542451800028400d20600031012208c00a221a10044480c4140031034042d51040502203005000c1c504000b65500140707050000096465050f65021300752002168160840000c0d140b08009a540600074007000010440c09451541d04045019201600f0500890200b146056040c0c04050080100000c004001842d02c0e072507000c2419051450360044500311000c80c40b1a01040c03c103034050094108122140c15902c2c1582e0a08407440b00ca0707048280c02044e129160001c40b611506240b02e6801740c0d501034245801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198096582 1250 198095332 198095347
    0x60f18070f090e010e12090d020a0302151b0601031518020a08010c030c0314151305010e180a0c050415030b0406050103120807020a021c05030c0f0d0e03060f0618010b 73
    0x2800c43e1005c85658006402110807003010b020440115071085200f00e03a0f40300000207900126208440680000b500500100d18800d2a480b04c880070b819400c5144d041d07880d0018801112946440080c84010240c03481103802a0384036206821001081031040780a13601c02c1060b07000a10403060750380c00180180d54030f40c0344100c13266250060000002c40703403c0c2846089548000e0000300c02c0e000701390000c281e9540e99208510342d40c0b40041e02901c141001c060041d561075400c6d003103841c8410744100c00c00080c110503070603180f00003080e001426504510249402c0e4079120a000c041d00381d15441034840e8641900c048005544a298580214059a00000d1560652811844041e00400743c401400305030000c2060f15075000407805111681034601030344030809682a0b050399010034070700804a01002c074240020f03490004401d64003080c6402210b07102d034600c84c030542e01e2005688050b60581c200c0400100031041007100380d178125102a040c1d540041c000201c0d160101d078280c200040c000030010345007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198097832 1250 198096582 198096611
    0x3020103061a03010b0f07080715060f083409270c06050c1c030b030c0a08030a030915060b040e060604050a06081f0b040512060f18070f09 61
    0x803405066403103001070401600d00b060300b480e4041482003620003a0006034120350000d583d402d5a40740b5500c80c0d0655192403062500700d014204c1c15100020b0303d8030300703000000c0280d0f603d1503610451340a040507001d0059414207072803442000d020752601c0f40c2c01c46640c0545090400e0a11401803243c2c0a00080c0f440c40c40c40c4c0c007040d03001c2e80a54260503908000324a00801c2002101344111021418016541c651a03241c941c1840d015048407500c1d080c1d01e15040507c20740603080f080880a0071000d40700f0700c0340503808020034542c250090b02c7d41980b043c045138000a0003540400e111500900c020100c400d00140310406030344668108000b8542e010400700640641032640b1500302c802201c111b03083c40d00f05008640746503401d124610800c2007130300c0400c5c0002c00d00c8000d9407015440341d4105a91940710610007040b03521038401c0a01030724504440303000150012a4680c01070700340c402400c10544443c024950380c813400c172150700024052500f0024006048603d500700a0444200c089980205843c00d0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198099082 1250 198097832 198097841
    0x12070e01091109060703020a0602070b0a230109090c122105120708130c03140d02010b0d0b0402031216061109090106050c1f0203040c170a02130b060a0903020103 71
    0x1c06480c02c00c801c0c07414411100055511802c1c080c1d40040c2c40b101a410201e00d40036210001a002c00d1000030048180700c540d288440c41040a41020f108242d44030006074000300040c014a01c01c071400c10b0052100d031456420100520b40a840714400380da0725035040c210042e071010411542f0400c45020200718800341d2110303501000590400d0350509849a882c008801d00040609082240303890014040d204c22840c0c40103200d410044d48a4004e46a144c0b5042c03492072821190319034404c000710720f4216441406402c081020161405003a411b8503070f18140b00d03000c042c00c00c0341d140c01011081034110104001070480311190316800b9541e250141040001c5401c04016011034140c1000351081a0b2a40340503141154510320308555640810b655560800c00b803e100d40c0d140070078801c090303031100e445500030358059030080202030100365039071a20f400c0d0013540e0308000e5580c0d0440d8690001503c3c0560822054040740300010038080c40e003900085469002142090100380920414429564540304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198100332 1250 198099082 198099089
    0x20132191d010203101d0a0b04110712080112210219030903120804051b1302040806011404020a020a0308060402120c07030f0e0a1e030b070914060306010509090901090212070e01 78
    0x820f11082006c641a207140e415000384408091600c540300c060068a0343d51020102208060140d602c400081c0382c4500e0b0312000a8002c00018181800420010151385490307131080c2d481404446100165031503a8402e0080c03111407419030061800c260f02c503e0320300c006040003034840e03a12458010b0031840c059450f08204405081040740410402c000104001003071907084c07050308005800300b40c607000000d4a12001c3c0c0582041030b4000b007030000303ca62000030968107941c0ea40c018108444000803c0c0000c0740128105000140e00146102000c2805030070441d801003405003015150600c503021140d50a5400c2d5014182e500e000103076002815030003401c3c4000380441b032800034540708a1400082480c80076000b29242441192140c541c0e620701b14401c08002c65010039143c0e4245031001018080c401c051090b106405403090b01401c90b840c00c982100c0c81800140c442c00d091000e290305001460000400c100300540d0b0310320300702d00940d036200060745e85190030700010400c4c11309001f4040d05000040c0d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 198101582 1250 198100332 198100349
    0x806090607021507180302040c1205060d0c060f12050411010f0305010e0c0d1d01151a030106030504020d0c090f0e010513080a02070f06020132191d01020310 69
    0x4410004901c1c10990000a5840c0081d05244500740b446145d0500385d04c001d61051404910460b141e030044030140221142d10030402160f42e94600b030146e81d5654240040c00100d2005003401001e02a24448100304954500401000e00c3da2000c04110740b000d440c04c0d50441100707000c1401d42d60740109101c031b000105140600c00c5e03500d00b03002900201009440c40002c000003144cc041a042998001e05440250015200e800303c42003210328000c2104035081d11078001c50072400316004180c410300007210409071052034079513840d01404800038000900101e0780402d0002e2004041108845204040c0075441000500b81a5031802e50044440107044040540d0402c400c0000b1140304e15081598030741c01101d00c5039200c94000301242010f04582110010000780c0c000842c0242d8154443e190100408106110600000780380d403a014140310441407000040030001317146010130301d0580e20a42401d110103c5c4000c034a13803031140c6038848104092032981d40402040f0f4004a03101d6990018205038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 198102832 1250 198101582 198101593
    0xa1202090c090103090203012c0303090d05031b1206010e2d06070b01030b0604060e0105030d121503030c0b0a11070303023403110304060507060b040f0501080609060702 74
    0x9601280c800e12004058081d030100100c1e0030440369000f500584070f1154000e000b000604041200b024001e640075141410344001c000302001045c0c03001044a0040244c04018800d042101c40c0860f41584010402103041c0d8a0000054401041c00f01404507040d90700d000700d01c18036180000401c40c40c00121540e114a101c2c1205180d00311507892951181030000240c104001a0303900411700c01c1c0f0030a00001d0882581d400000244100300e01080d00410046405224040e80e0380318030b00c460002809032a6064011403011406980070340c8481050840004020607400040c460b420a02d03060f0f40c2c41a00803c0080b80700c2020440c104202c1076100605140400c07003040c0004007030105025203000201813585c0007500e4100c0710210407001c00c41c0d2800d403400d180f194081c09150040041c0c51101180424070401800100c05004001e9070191007180c4d440c14208911034503000f002c0c0600c007050310342245c2e0f40c810f09007405100c4c1c02018041c02d1701400502c03860174030321501d91a00c88014a07900031504070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 198104082 1250 198102832 198102869
    0x6090606010912080d0b12060108010b06040f170109150f0e0105041e05030c10140603060402010e04091110020a140106180b0301180b0709060905060409020a0507061103060a 76
    0x344103c0c1000990400d4442d511000c48890640092901c03000140d440001d4032500c803541c050000c3c0300c6040e64207110003400401911024004940968011071481e07032001c00040c404010101c0001500f113202074000f0540c181c440d01e83d05484804940220921030b19000008061245401840c81c5580c0c080000c1010303140030307241c04529980d4003215500100740c25040800780f080030015184000000016203600c240007a946038010101406030b81c24100d006030008499250202d151407040381c041e12080f0812503c582000011b1066050440d801c8521520003010f58603200107418000b6915001880f6001c0c90342402400d1544407400085144e0506005022503e195400c07121440c6802c54040303994001d0b04002809000340c1d40b00d01605410b100c1030300b4248600040140d0182c1c90a1700c87e0b5070350742e0b11400120791400e2503001342074100d84200000c00c00d8070210b500802c540540d62a186007004080d40e0307090f094402403034012504801c00b00c1400010710304041d80e00010200001a0350b00d0340d28 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 198105332 1250 198104082 198104099
    0x1605011508210a05070c06020307030905041e0b030a0b04080a0206010f0b0d0c05070f0c0302090c0a0c1b0f08060406050708280f0f020301090e010c022a060a02060906060109 76
    0x51120992081e04404583d40301c03200e00607400e68103982c0d44010f294804a481d030070025074a40012070309400007912403c00060608291240314a16044188000a00b02154400300b0282490300c040c15010720455000d040486d016100c9980618840d000f4140e0707800c10000b000f403522006030010201c0b01c0401404224412400c022900d10a680c00c1000c01d0a00f00f400e41503c65000ba0400940240c402b00d80340b1040080302034016040c1c900c01c89202401c0c0d111003840c0d440a0080c4071660021510114480707020030b491701a120348154281480301030007900c0f9000080c01840545c8082c14076407240080c4001c10909000c3d031644010a443c0075039140c030b001c9840041c0580703000880f0300b440055003020040b12846070052141c0d02540c2a09000103403502c0044d0f00294000d200305401546400a02c0306e4040041c000e03082c0030072030b5074000d120010319042c010100b2903207000c0c0c3c0704404c50400408101a140ca5010744980c41c4541c02410340c503d4400c40c003c0c2001d900a00080c100310990405014404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 198106582 1250 198105332 198105373
    0x50303090d030b0117100b030c090a06050a020307060203060a03050d082409011502010605060f090901081203010b0a0e0306040809040e0c030717010603060912120605030c01030c051605011508 84
    0x3058a0010b0380652544694014940401e4001640f01d1500204001e0401d9041d2700074602804142c44203400301d80e661400701c829020b959105030045c0c004202d008046039181d0060350300200000d002401581c0d80390303105813030000301e09000c001154000081000b4041e61580c4640c3d01c204561540000d907a080c000203000d05814020700c1f6541e00a982c2e0b01d420035200354014005030070b000d040b15984112950780c003c1d280e0804000107201e01010700010401ea04013141c0d181916091180160031642130825000881d001010607000300510000f91268564040064600442c00740d036400e07a60340b0351513042c00709440003074801c800345a112121541c5180c90015140007115001085503034104ce41640c224054016a48068035080c1044005400e002c588695202041801c1d1030b030110708800409800180c038518810103605800c1011482100c1d4000e401002e0402c0b400d04d030151400b887c81e403555134440e9080c5010303100d607036403601d000703040c80807404034000900307000001031400c4030400a003160f401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 198107832 1250 198106582 198106607
    0xe0a1205070510030b040501031104290d050a0503040b0315100f080603070323070806010b041e121a061801031407150e010e0d051c11010207050303090d030b01 70
    0x8615104082650602c250710611700c4a20052090029585d82d04110005140031451140700300c1c90410354404c8142c0a161480329010107041801880c4180000c102d070400fa4690140c840780a0555030000089040c0000c10203005685070356030712400d050f40c1150544220120780d902824264010390364081e0040800c40c0102c03018a0f0064660351641302182c10001154802050803113014540c80340e403c40c140c18500c3d9480140101c50049584542c100d40d02e403002c5c030400d80c0780f003000c0005203d410301700c1c40390a4150b07070040d00044825944a00c03030001c0040b1311600399203090a0b50b0a1205c3c01210b1001c09400c0181201d100c140e103000c2c6c0c0f118000000040c4002070201c0103101104000a0703042c80201d005190071302119003102c179004030141c03114814080690002d1420740101e9a0303454244410081c1e40c0d0000010207242000c12007400300802d00ca0701d4401440103840c4400016002400180f49480c4030784095900c0c0d040039240b103440c014074556400281810503480c0c0d40c02d07990194510045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 198109082 1250 198107832 198107839
    0x3030304060515040204031119030210030906151d07030b130513050f0a06060509010b070803070c120908060a0b060a0c082122080306150405040c0e0a12050705 70
    0x454039070f42080d005200310030829640290000c6400401c0c070000311a02d0f189181c040d5046180a4040e03c0c4c1d580001505020080d4440d10b00c0300d100c0c150354802d0b070240041e24811003000802c0f8200311030b50203070f110065004003211402c0c1545440007060b0820b800f60803400b60f0500303002c004c14000000c0c12948105948070b42403592000050380b11310038500381d600c445070002c003580c08601d22001e809445400b8000c05541c41410080c0004843c00d256490138100c8880344041420b0a0490765481110b5101400200030007043c05142008200c0e0b601c001d10282c04281c0f1600c00d51454062541d0a10000401810382e5034605642c040d19529000e0884500c0742e25840c00900d4201685017949890203003c1164801401c003030303d80300c03c3c4c03500782001c2401650a00f038003030300c0d41c16001036000040c0304200d001080800e041c004104141400a84055040611000300c0d00741b6440702c0115045460740c43d14440003488645d003411329070400f1003011000d44240300803e00c11042586441b540c410f094803c4600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 198110332 1250 198109082 198109091
    0xa021e07152901120c030e0f06011a0c16080102030109060e06030c0402030c2b1d0a1101020a0b09060601080601020318130f05070e010f020703030801051302040806010608011406030103020303030406 87
    0x1461380b1400400d80060020101040600301c910380c010010f0200750307518000703071207296050b0003d0340000131094100c644110080c1c0010406e520480c0c01a0050700810740300d031081014000d1440c1c0c00141e070304050520980010703180e61400300001c0980380207030301199064070240c0c280841031302c01182010584000741c50141e900d80350a43c901499208902d4042ca1b00c015613642030608840c815100311062888440c180301600c10340030303403200c1c41c2101503405050382e111a10f09400585035050320b0401d01414010340300200721503120f00216080450ba10600c0cce4111030208281d544e000880103420103428401107040443c52083c602d501c001c94a0803e03c01c110800540c007130002c503a041100c4c0540d880c60144000c0c2040c0c013000d441c0660381042c0d540402c5a0051004c405840021080700703c0c2d4256072403994607480c02091007510305020f80e040000c0e075002c2001143c10f42040100b43d0003407035181d07a1103842d9271403c48070208580040d076500d4841c0604000400c0565400030035170b500310750001e10008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 198111582 1250 198110332 198110411
    0x1020a060908120a0c02120a050702040506030316030201020318030a080f19180203070e100e0c130e0f07050a050405120c03010f1d0105010e0106080a021e0715 70
    0x900b42d010700c4100c48000c070f12500070000d106540d5044624948021703001c481c03410b4500d002420a1340202211f030310000360148005005441c15401c45a00018040d05891820400300c0c000008034204010a0b00540c0d000000d0094848100e0035601c0c030000500c02842c248009004018000b08010309085000012100481c2c0c0a440e062940030190a010300100020140c0c110314186a0304643d000340d121b8041c40382d00084d10810443d01c548503040c922401e1102500f8400c5a4200d4400a021007010710414006400d00c044404a041d0250100e424048042e18181c911030414260081c1182d04010b02485424074154010703003920141e910890300200b081170081d150303503c0c068441100551560034410410740b0300595602107038401c41d000c86551400c05d048203100d4241c0b003080c4901d501000c20b5034010015944910500b035000340307891501510708180d60382060101e00d007030f000c0700e078400c0b0001030781c0342c104400488610000480300405010031741814202407400c40c480406009a4444444a40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 198112832 1250 198111582 198111593
    0x6011419031128030b070f080c0a12090b09010501150e060a0c020303071b080f010b10030b1c050705011101090507031209030501050a02130608011a18031b03010b0f01020a0609 77
    0xdaa42e844030007428002c5596401c11703c1c41c80600380d4003113010440c1c1c60740301c1220346d21501c02140302e0545242c040e4078041d90b103d42161116440b0042061480e52080d00300c000030ba01c44032242c000e14541c0f001003107550400c80c00043c600c03056007902044c0728407001e0350751b016129441580c8142d01503040c41007080d1440d00109085110b03d410050214010806a8502001003a070f0313103090b01c107810100d445111405e40313264200c40c030f0964002c0d0300500f0101081500740c4240c010703429803000500740d00e05401c0003c10220305074040c080200c415401204081c081c030350344000030f2904a12610001e2220390099260f5a403644581d01002d087d00300040041d83c2e165018070040380c020755018000f0040c61401c15032540003504048044142c41c404118000f80c0f245c86a03917202c5c140c9032160310001c02040202c000140640c44010071141c0c0407a0754a400029650034005401188030030b070301c80c4400e0303100e0000301400c45407610b400a10950001d4100b4005d42d038005410a001a031010001500116600b0103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 198114082 1250 198112832 198112879
    0x10e04060218130c02070501020c0a031106040807080604031d0d030c0305160b1006050a140304050a02090f07030f11040308070c030f0f05060a020a080a0207060e060114190311 77
    0x40b0f400548030541102400034991101d400040c0e294240d8444944070801203850343e8031001d00d1b035031040d4440c81c144003050b03d484205200c0c0c103005200610b40380d076498200381000368135801111260002d404100601d500f00340c002d8a55500440744c0340e00b250b11000040d61035801150060200504202d0300c200701030282c0308907901c020003101c800546001a1400c0c0500040484144040c224916000940e01d8001c0341075400c1c403103c940f1152170340c0c4807420481380702da00300030700030b4840d071244800c0c440140e01c0d90024036000e200140707502441490102806000ea400000b0940801442c040c8041d050102c83e0080c1d82c281c0c1c0c0d00084c001d55606003400c01c00041034142c1c10190101d02018104410044061383c602155403190f03050b0380d5541e17900c0f164002280191007200c00030840c0500060a08a0346500924040f0300c40c00e00051947d0300e88152a143c07000c260441d14110345030081e00159450b0192501387c1c448600350000303440c0c0b0b08658a40d26000500c0c2c0d1824010181681d0120500910001c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 198115332 1250 198114082 198114127
    0x3050705070506091f0c02120d0306080f280b0a05150d15020901050f0408060f0f010501140901020a050d03020a0e04020403020a0b070213020d0f050601021606081f0b07051203010e040602 82
    0x3d07008400c03420f20309527450f4550b1082c60030200c3d1400500040003d80030030b410041c0c1c0c500c2c2000d0001c0c02682c1c0300c23840707000032040c200b501108040c0c0c082500040c00c51b1080c0380214128980060a803405420740704c80e0340c442060862240500740b0111000903624840700000882010015840360701c81c4005a0795030107002c060b1903154070040f0740480d10100002d48148920710320300381c00c2c0c1d541d00c582e40a54900042030180c82e0001e03542d44649424208040d00030291124103204450800f91240c0320941440d25010902c000a0340008503890305a510030700300d01e6030f107400711403c41c0780034a16400690b03c0102d41c07140102c4118041118401d558406003216210310502805541e21005001c1420017403502e030b1031a18060746001c01007009544002003032030980c105011240c40407424004144c4074840300501c203103020700b0440b030101084541c2d10320030002402103040244c3c8401140c541282443e4a5100da038042070428030040007440b032090f003d82c1c1c22a4001ea001a960604011400e0940c4901003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 198116582 1250 198115332 198115339
    0x1060203070c350c0a06050f16080c030c0a0c051002060610020a14034504020405121615120b010525170f0904020c010902090403050705070506091f0c02 67
    0x44000c0c10004030719042d01d0082211006491529080306840c0e500070200c0ca42d0605000388050120b05890070149c54490f07000f061041c1c01c112001c20602d00d10b60004040740015008051400204050009805c028200413114516003d01d1040c00940e1101c0042c00e00d0700c03e0044110608203640240000740c203480e0002c0c1884d1007002c0a80c069680c3c0d602840031103417440340d04000200b01141c41402c840241c080040240c20003d8011034808002c04400022036100c2d600b00000100c1d0360700c254070b07100000900d1019000106030302c08441841201031384420328405220001641099020006103010032a54900140d030030121001242c260003944601c07050000301e4212070758400d030f00245034103030340e442400e070303c46c0c40490a03211602900541c005240c4128007071140801d03d1510ba00504042070758600000303900c6410740c00090265109590a030003007600055100705122060198802a201c1a100d86181c401120045000c51084801c80c038890710300b0f42c114054061050085a04542d00107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 198117832 1250 198116582 198116669
    0x13030305180f1c090320041409071e030302060c1b060c18030106061d040b060a0809060f0c04060c140d0504181a0d1a0405060f01060203070c 62
    0x40448a940d50540c1001e4080c801010015803480f602c107051100a0b6036100300440340c103c4000b8090b401315192800c080398050b032900c006101212010460324850405a0010640c5a1800080304c404280c6640540f8060070700d03c00510200b500095019040220103001584d226a0030043e000a41d2400f04107801c00d0044070288100d00c51807401a104060006418551908442c1e040600b00d80310341c4103400100e4100900100e41240ca583c01c0c40300c080c406071001c80c540c07020000242e0180c3c01030000704c021031034203814459020001c00000b50b0204200031114654100f41d481002540120f01c51036080020342c10400c0108410400c0d89a050001c910444d1040486c0134005000d41c2c000d402004203004103d001d0302250800d82c0204a0541e40300390b8032114080d00c00b4103100940015401c181c41100800c0f0084444400d0200c0b40d5200d2401071028024a060011a00341e183c001a8042000c560041c0045004a865043c48004480280403006500207441d5400007010507200641e0b030280214 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 198119082 1250 198117832 198117853
    0x40b010905030307020f121b090a0e0d0f0504030c1e05030a03021203152205070504271e0203010504050f190b01180b070606051903060e0304090e010903030f051303030518 75
    0x160188040c1c0b03040482c1c09c00035035940c43c200710701281c03c8444081c000354014844045000e001720340c2541001071900c2c4c5103107415260780b220b041c170714860f034403001441c0038105104a0941104001d4005000c04401401400c3d4003903c000f5580c0604050040c0d0340c6034004040b4107850425600c402281030090444603a58080154140b406440148058256810080001d20310740c82002190103a0b020303002d264442620324140c412849900910382c401c8103558400210191316960552041c00c049143e000d070740c03076040c1002c0c081031b80c2d8041c1402d000c0ca042131041c008000345010481c00045400340d0005460601c0f180102d5522203211140341201520040c0400c00011550040c80468000c00080c021160b864050041e900c5400e070304c81102d04c002107018000601c1e6604030220072104030b0110780c1059103030080c00084524081100c4c25603036460b0318081c00c16415000e40320302c0154000003001a46007c042101c840c0f424050000c080603642d40004003500c4a0812140036004840100caa04004c2c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 198120332 1250 198119082 198119113
    0x4060e010605031905060d0b040f0812070e060301060806060c0106320d0201050703201b130b01090b0a020304091803020f030a021506040f0e0c040b010905030307020f12 74
    0xf0545401321034865102031141d51420300c2c010b0301d000b1400645012990581d40c0c80e807080a50014008a80c0042d00004840110784c0c0300d00a403541c2030700843c8803591414240d001030003019075405054019481480100300311600030b001507038002020340345a0780e144c850000290040c003140e00111000e420150300d100580d1550001020610822001c11415070b8104040020b81c1d80c0c4418000c0c000b900420030900080d2007a0359192480150b034450086201c81a554181446481808100400f01024290205142141103c1c0d10710125113010440c24101f031000810a031890300505038000c1000403d440c1007842001194000c00259008100f040e05c02c803182210fa4942c000e041d0014800c00c50710500501d004000c503007800b1aa84c004143d4110b8400000d1a5010002d140c242c0c42651462a14450190f42c0652440c501401c40034001200c401000c1000b05e52081c043d560400103580300602c041c0d1000812106001c0d0111000c1038540402c10028404248003407114400f406030b402e0085d0310300c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 198121582 1250 198120332 198120337
    0x30b130c0306050301090b0c220806040204141902340203060603030a0c1e050f150a0c0e1309020d0503090a0b0f030403080423100608011808030604060e010605 70
    0x4910340c0e42071202e9580c41c41014282d560600700039001d0600f83c80031914034108000203003000c0501800c2154500c81560440c3c85041c004d610540c4d054010108020440c5070a00c80d10010b24402441c8450504241000700f020448540ca5028000d40c0040d18503101c1000c0c26120310565070080706401d162011b0b0854072400100311400b00d0107489a20042441c2c0d180101c256803031f00107079607903880c61024140c9070f100003a44010141e5160701066011200403480900802600c0031110b40242102c03142450010f00e48080100301c2c01c4c0c1a49040015002980e115100c182000811510301403100601000c403c01040c0105000358030118030720000040001c04000b80c40307040340880390040225584c18981025211304003c0c480358040030400500004e00902c01e00d90080d0058022004031070102124103120400c10202404903800031859081c045100d00610010b4110308000784440031450f141c6c00011a82c449d401006500b02100003555074a42d64060401050080c1da030001d2560341c3c0c0300203003159 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 198122832 1250 198121582 198121601
    0x3080f072c030d0e090c0f04050406080322050a0e090f03160b070c0803010b0a0207050301111e070c03080f0c010213080105060d050706031806050a0b01120603031e030b13 75
    0x3d00505030094015809503079900d50101000e8040b941c65910803640140c10b5002801782e00101c0310074440407645413118881c11010380050f40096030340e0f6038160412207541d03100c800c00ca0001c082e16a000c0c811920341c0c4d11140b00b00c0740d40e41c0344190715468180946003000c8243c80c0f22010342c4004144e240350444890048004140506200d10b5151200c0404603501c0f41ea004010b0403c5104000401800080d01c0040c2a8172205105444115885a0009081d541e100340002519000403600316004820782c8001c100080184642c5442d204090f80e510340310f8540352101820321300b40821550780500049080310000301006000f150384041c5000354480340869030286c8000d96103064005466803d1802080b60580c1d005030041150b40d1410307100310060301031107143e894182c64000004001403a41d01440380110812308001c10443c803880001407064410714a03002501d400e043d0204040f80d0414400e584d01d1501580324211513140c1c0c1c0c0c055014100090707000307400c401d4000b000c640d283c1d0035074800c1095 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 198124082 1250 198122832 198122839
    0xc0f0b07080a0507090b070f051b0a09051b031003050d0207060f020d0e060d0b0607140607080f130c030203030304120f0203040b220e0a02120a060303080f072c 70
    0x107807580b0010500300d81c0d04441d000c0101d821020244101c00c07080002e403511030b00c120b51b1105a031500c0e030307225070612a82d60300a613800b14040381c0c411014a0090140d501502e2100f4080103d4a0704000c4c15031448000b60040e10703400d0707002001c900183c46100f41c000185401008035144e404d5803e100950361740ca2849800c0c0000c0041031402e10003803001c030b8a51603140e510303603403044042c41c0e410800c080e940c4004034488059940310400010740d25030001828485003c3c1030f0821400203496803c5041c010700410400030018a0020080150981c40005130040c4484200e400c1e005990b01c1c000b802c0010603080a58944404800c00007001401508000300d5205aa2000c03000c1042a006a80c1c0f0b00a50050100c803160900c00c8580300c00c09002240d44424080803004603590b51140d044912240944024488940000721a04d0007010003410a801c4100170700208440c1c2d04c0c54600030140c2802810304004000150b022074030b8588580b14002d0145c4602c101082500a0749481562640350f800c1e00d10300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 198125332 1250 198124082 198124097
    0x40906021204120e0f01080a0507120e0309090c0324061c020702310b0f0d0305030a0c090b040501030f11041707050301060308040b1b0102120105180601020d0509010c0f0b07 76
    0x3d803d1100c0141710b0f501d011b841d00307c80c60f03e0f42181c000140800511490400500c0562091081128003030744000c500a40050740ea905155418001c401d64001c21000c0d106104106011031004880c80ca00542d03c0072402c6200b0684003c0c000030074510909909080f00c00c0c0316045d0004c00a020f6009140c584c1c400c4410f044400300e50301140800c112148860540380c10300b02ca070325503403105a800074120014014440149081e5960010300701070007484054001076404810401c040300b0512440c031030f2528030300704158210701d0070b0f134140720912542c0134050405480340400010032030241c00849512082860f22615a80c40310032240c001550558030001c203108280000400d410306106590036290460002d9140034240020000d150303015100c00c6004001d250030114a602d001e1010b0020841d001000e02015450001008aa42d0500c02841c20300078024062100c0307aa00020b0380050645181845900e5158107401038840050140c80035000038121a00c1d60100b05414003064407880f0300707444095 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 198126582 1250 198125332 198125357
    0xf0d2916020c01081305010b06030c03160801120314070204111317030318070f060e150c07031b091401030204050c1801140c100903020d0e0f04090602120412 69
    0xb42c0e100c00d06000940854851008a9481040e40794030707045140c0200008220101e050000c03e100d50710440380301441ea5800300c28009031000701d901f4014144203600d050751055043c8680321000039243d010050a204036010200011030303400c002c0c4c034186e5800901c100030015101200c48201d038000b00f00650b03214036150000c05e04100c554072000815110300f004504640d10a003600c1544913110860780d01501c1a40400104200200d401e40054502c5070350f2a240c441c2c0c440305100b0324001175001c00095140030700c000a100f0800084050031207410041d01c1000540e010641e0086641c69003000e82c50504126400c0f1701c60001030580d50480b8403d0301c0030002c5540b143c21010f0700b0301410381d1140007041002403211040d8812071a1143d036841078548039282100200105160101d1452046c86460711400880c007815018414901740072180d041081d0b1440c004030014905407140361246115a559116203c14805168141c81c00044d400004043c2d606180c280480b180508002010001c1d0103000d0a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 198127832 1250 198126582 198126587
    0xe010b091b0714010902060c07060318080a080619090203090606010e06030103060504030e0405011511240a0605030a03050d0b060a05030a09020102010f180201120203060f0d2916 78
    0x3044650300e10716629041c400960740d03540e141e4010074021900c56488a4022015a0700c5000a015034034500009011451403d8000f5069560010300e80d00840c41c040303044800b1030100012186500094640754483d642c2c6c090004000d800c132003000e403485000c010404100c10040c4e500650244030590102d500c00e9980f803004654640307802c40c010750841303c00d000420009000b0b8001c5a08207102c0d0030407a100e40c20381808241111800d074048207158070300e2021390300c525800c80c00c2000e01d000b008015140621900308100c103842c0200d404520441121400200d90070095445403014110003030a580340340c0c8403810b0041503500f0070004505601e00d4500b000c0403528011703046520005407078031080d04590b90452008014010001c0c180e066540350021040000100c0c420312004130203104105034032480724000180b130303401000a0108258410410300446582e03a07034103030300c404034116944001b00b0010700e89590802604100c0042002c1d02c1c030320390203038803c01403c003501c558010f541c0070701d02c104110801c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 198129082 1250 198127832 198127861
    0x30a0908070f060804051f020405041b051602030f030f0307090f080705060a1b0602040929060705150106051b190303150b070809090702060103050705010503190e010b09 74
    0x1c1a0b4285000d01040100600030501c0c40d83c0a40076500b40c0d40c0728554103c0c900324404101a406011a034009000e002c01d10b020302c0b0f1140151080d0010000703241c940d0801410b00e10410300f00910140c0b800400004540c0d0030072141c000d1710903080690f0740300c03003000503d200f4640054880310003148180101180c00340d1564450000c40e1039810040190a14100520075503602c5a201c2d201080248804c188544620b80394546015108690041c0ea85280610840440315280d003010b940d20122000b01c40182c2034400c400403280811140c0700d598a04901d0310300d1a0a10a2900401d000410400068907a400501604c40420141148520540c0c00e0700c03225118081c03a048401d103880390050300404240310764451030700e059076100a050715a8580e4178644044c0c01c00c4504403041c000000307842c0200d040031521180c1162081c0010402941951344d265101e42580c016076041000100000381c0c03000d0180c064401c800119001007000401c11400395000c1d1442035080f5001d00000f8000c01d480420310800b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 198130332 1250 198129082 198129089
    0x4061404030f0e0a03050102130311061c0f02091008010501140f12150604031b0b040608180a0b04120207230d0602040e1e010902090f0f0301110c030a090807 69
    0x840d6500e03075498500c20380f02c0d1404000c1d250f402114002012001600034401482041c4440d004c1110043c603619080a0441103400420b006501c240f050010f000103c501c401d100025038080030500e0000c0e2507080c0e000340201550756a00402c00600695029082494141039480a036103800d048661f0748070500142c42480c041e2110070030100004031040b54540e4002e50090f180d00c0d207445001210600269050f000f5030820303903101103a2804942002402c1c00030400030051441703001d04007480d089001e04040350042001c4015040d500301405980802e00c50543c0c6264010041d40c0c1034100f600302109140940c3c40d101c4058071885002042260a280c20713058202c3e100d1984c2c2c204120014140b0800002030f4070122462902804003194407100c5180c8940b01c0c0111541444440301132480101c07001030103074001d00b400d51040000704a0354640e20b40c0c80003010340641f0710700300c09084100880d00404400804064650010030a9002050701000602e15650380d66208100562a1400780e0f450781020720 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 198131582 1250 198130332 198130337
    0xe071e0504020f12040b15220b0a1802181207050105070c050603010f090c02010e0712050703080d090c06080c0409180506040b150306090309040e0f011b1704170d0b0402120406140403 80
    0x10306107010842241c209c0d90b110710313016211048003607076400100400e81808060040254022450361a04090a079640503103000840e00c010701c101407444001d4541820f40144e6040107400681d01090200d1400c2c1d01005100c0030701495503943e540c05490405000c5c074061000203905203029803404900c14051800c5070501100a810300c0c1d4501590120305018444003206c45014402d0000041804000906008541644c1c04110b84456140420000304250040030030b010004061092528558090f2800c0c2d44107000001006d82c600340c000452402c0c600c0c0002e08038460b210030041007080c9014164021450031076402000c40d08101056102d90301103544105aa100780100501c1749080d40124a40341298001e0f12807840e881500b0500799201084905a911580903402c4141070b44140c0d04007442400d940a9204c505042d40c40b070b014014244002c0400b02000304140745000c0c0d1540c0001c8140c40020421950f40503121800d604038001144c0c280c03155440e00d0391604914961541d1640700340d40c0355 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 198132832 1250 198131582 198131629
    0xe0a05040b03010b040e06010312050301060206060d080f0a02150903120606070f02100206060a0e090303130519060f05090307030f050c070e0403030e071e0504020f12040b15 76
    0x8061000a08407061500e82c15900c030006040c864035980704604104582002400c260b6040d07003081181084200c03504410040200010072015a002c00c0350b40d003144003143c0c2203101d004a0301f80290a4003030340255401c190400104034000c1600001c403d12541b0010107021003a03501c4103201d5442740980e20700d41103807120000004140746032004c01007100c0d902c210300403040c3c2402600401c05030b40c001c400640c003580c0300005010780c0e440c252a01000600d0701c0104840c144c034081e15881d44070b000140420350780c010f4240d82501084001d10410b030351903698003010020000503092000190082c108a000c81e24600720100e80c01220100840354a070350107072181f0360315140c160012140c0c1da1024034611140d003c0c004c0d02255000140f40307964000da020f560013140c2c1240e0310110b030f030400605074054000c45095840c02000c81e403081d084102180c2c0b0440d00181c80340c400d07412003501c600c40c0c0356005d21000300840400041210048080b80603040d00007042510807140018000006d460755030303094480c17508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 198134082 1250 198132832 198132839
    0x1051909090203071206081f0902060d05010f03061a01090b0d09050f0a0c0e01030302030a1d04090b040201030c021506010507111f1202040f030f0614070801050111030f040603051305030f040302040b010e0a 90
    0x6a000702780c00034030140c441c5280070b2048103c001224020b030882c1035062001c0504000b8005a4014640941f001c50120310826003006c0020b8040b40240c81a00e0520380081030000070840302c0ea001000540e004000c1e0f40f0614540c01d60308e91610202002112203d154010110346400070140680c1030741c0e4950000c0d880d20300300b41004d48403103980007025054140084840501915140605041640b1401c8000a9402d0600c0054203a8941c464040115404442045081c0c0410386103650400c500382045561650181400b00418a8492181d134021070502d44030450421001107500140c4402e075108401c002c1e9255114050740708510450622400684060010841451490303051038402d40001840034144613002d82c0d9050f08440c03440104020400410065070800c40c4d1001c05603104c80510710301500c00ca400b030528000c500419040565650014004001f005403054145400c003048a4035403900e11806102c6900c40c3c0400c03809a814158414101c2d400344e0348103584020002c0642095904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 198135332 1250 198134082 198134143
    0x200f0c01030b0d0c0303030519051306050601030b03010510051009080c130e150f070203040303080c0306030f03041517040515060a0906170c010e0105190909020307120608 75
    0xa81041d143d80116114900800554141c0b5620000c42c480d03100452146442046000341e5102120118038507403c000410800545080c0c1403070b901e603800900083c0644540c401240104513040e591074040d031030001401084062103034500101c950407141c010108420b858200c50340229072081ea01c180e4403400c003920441c0b828000784600007024500000781400d18901c5607280031030040600217407480c0364050000d00c54401038060b40c494558002103240a1440d50020a1401d008082c0d118440c00413012900d10780e07050184039000710003e011a52120780380c101400d6443c3d42c4291040208500c20240c08030701c0b80c0000c42e64031442c0c2140142040e168020740707685403904010300143c3d101c15114004210061144100b8028203500f8494461015002245902d00304044d03112605101a00030131084581e40310b4200c42101450018480d82a401c0460541d00905290054603c0034004030800011540c4039846e484070030300f400c6080c040643e0b114511074646120341c50780820740d00108240e01c185407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 198136582 1250 198135332 198135341
    0xd09021203070c440c011803030309210f0323040b0702011401080c040b04110f070c083304050d1107170129241306200f0c0103 56
    0x141840c2008613140602e8407082e004010455099050320300e95000070b081c3c4100114030003000c00f8205481841f803d07440d800d0f6008064800181056168441c030402c011441450300e89800f0011224081d00c0c940d0f120140c014944d15404000080c5042000140a24142c2002c00a00840000310503035864039250004410070082124041d9074075600708408051600c41124001c5c4000310107840188201400c200503940c440d00300303505c1113041845403c4c44c0b003031a204495824010200050742e40724203190401880180740d000400394020048175030902c0148840198800484000c3c2104e4281d55078852031203650140c2d0007800a50103051010340d2640215081250740204c0c500301c1c3c540c1035136400404c0c042224412076064594440c0d5111500380d046c00c0c4c812407418081540344c4164030b12100407072a82d135500c0d420841542124410b07400301d4442c00c405c0741c2e2040420241011210345800d0054108a002407442030700f901402c15405d004d81021821482951458001c1c2070750b2081840118042c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 198137832 1250 198136582 198136619
    0x50306060a0c02030607110d0215130213050406020d050901020c0d050c0a02120d030b06160204050a0209190503190206030f04020a080303091015060804030c080f0d09021203070c 78
    0x10095180a60250303031304000c140e00c40c0d05240d0ba582c04030440e038001d44d13061851002180c0d056502001410300b40b804505203480c0c0c80b404038401040f00d00c410b80006601c4d9911400001d840c1490041130000340012070b0018040386081010900c10707501c03060800c600302c0c89034403500c03151a00058044216039100b04010518020f803407007250210f1425030001040741d2851280b850305540404602d441558041c05041c0b4144412207100c4e003805100300d0039542c090300c41c17040203205907504c0c1e0001d003615040d513054802250001e044012118154000c03c0d00452007030081038481e20800c0c100306441d4103105d516010090f4050442810b5071645201d0344e40003400500101c1c1e000803090004640d184040020790f120701070f4040240342507000b0000c0c400458805d0b003403c040c1511208005e01c10944c00030542c5030895407524100300440c4081c10400390310301600c00a5580000002003010b2800c090b904100365a0b8000c82e1071000c154590038000f5502d10407a503006001d107845032800c010104034407101e080b21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 198139082 1250 198137832 198137837
    0x20423030c04050405011112101205070902030c0f03010617010f051c0c120308010f0509041703130c060306080601090203090607050a11030307030c021e0303060d03170a051b0a050306060a 82
    0xa000c110000c07641107800c901c41000341d1405d140e04111809100c8006038008002e0542d40c1c0b01580078ada140c40d5240d0010380519500e55400101086070b508080342119002010b1000e041d85950311340f0383c01000d10800c45161400b100d012000400c0c8140c080310181c0450344c009060b20405200c0450745246155151016103103185001c400091100e0490082000c1d10310079524801e241d0b040006900c03643c01a9080503016400250421000800d0708910310a070000c00d242041c0c80c1c2e660100002e80b44451000d00516801c049000051003030b030184c0000044d01c1e5050255925070b0f0701c410f40c440c204d00081303c0104041c0c0c4554003041c0070720701038401440d1914880c40d106c1039810040c041b0030702c1e50748150703034840000340d540c06100900d81e030500c000c80e4804c50b00c07141d204900c40d00da45026943d00001d0b000510901e006511001050700550329010f00c41006a8460074501c0d0164804d00200005c40e19640018400900042c20001c400200c030300281d0540c450a00350740b5482c09100301900003007100f909 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 198140332 1250 198139082 198139091
    0x9020402090612010302030f1b0f042c1e030702150f07080403020f0306060a03170d15140303071505060f04090c08010e070602120906040e0a020423030c0405040501 72
    0x10300c0e2200d5004040d01c40c003140020f0030310352440c0f040c5446c6c4a02c40300305015540100414000072024003d51800342081241d07c05031020503040001e004091000244511040380c0f841c0403000c0741c1e80102c80e4504100c100c01e07a444500003554030f803042003005601021079001040840700601e00100078054030360016000c41d0038602038501d044490b521a020903500b41030049802c20440c46c080c101400c0040d0150060b01141c205000802d40c641031501004051400551490100030003040984203800800181400001783d14203154008403101d005003286082c070301c0450130403401d0000840340c1c09a4003201c41001d54011b1541d1030020300c0090711459000e02d00341c49208180d6180e004500b2814020101520503a180006440c01c580041c00c061216030001c0380104046030700400d81d00000701d41d440c052070703607407021400040291285800c0484400100c20510540210903800740040e11650403150210061443c03801012480d400c0030301c0e9059000608595242c1026003040741c0080c0724900105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 198141582 1250 198140332 198140347
    0x315050a0204180207210e040507021903270b0a0503190f050708070305010f0303110c03010e0d020f03040f060e12030d02360d0f1e020301150b03010909020402 70
    0x1043c04106000d4100158003c141941806032142d56100b140d480c956031071101c0c0d1104a0302900b011541000c0030b12555442c3c002803041802401300d04d00e001a1100b00c0f6524034154600034000c00503107412100149200b444445001200300525000c0e200d80502c500d0410403d03070002c440f2544000d1120f102c071988441c103c00300700098012058001603440c408141807402480c010f01c0c10703e00078041c8003094104001040103100c00d101000550340c25141500800b880184458a44110718030f09580540c0f901f104a1400c80000c1591140171140d0303420b440c036200c0c4c0543ea4595134081da00420860001030b8104100c0c4034041c6030f104043ea000681400c0786ca4003004203090468001d8941401565000614172080f174026500460398112640e071107881c0c1c040141c0b40c0f481042680302c400c0780034041c1d0000c0d98051082c3c1000303100700150301130491003500344602c50404017400c900008a01030b40c02c0c80c0c8807401c00940082c40e80c00b030781e1441c031203582180e1a01d06e0100280c6102c080503a0025400c22401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 198142832 1250 198141582 198141599
    0x31502180d2a0603050601030c0509060f04030c030c0602060702030712030e0a0506071d18040b1e04030905130c0e191e08480d030201090501150315050a0204 69
    0x1031960500021910300302d46010302c058169a802090341741010b141801d280107150700201620a00700d415030300142c40b55100700154180e4070854001800c40380d4114800401c21030300c4c4203044d081c2c501c0d55007954482e45078080c099a0302d00070140020040c48002d048858418400c1c0e104c003138003284280444452100584406003070503025117040c00012181080200344194030a41886140000d0fa0709a0288041685034103401d08040d0009021040110116020b00c101c6a0003000c0380004074200400ea09003884d002d0300b0142e441c4502d5010b0141c0c511036401b25a13540c03058070105c00c0103455031414820070004105684000c042411300d52a810100442c0056400700e000c0c0940d0743c603007214500607041c51040d515011180740c00840000c482d010b0404d01101024514403e0074000c000341c480e5002c1302a40680c0240000c06840d0008814051032080c1030341500180d600b00d004000811204480305a42e1122021900000d0720f5540402c0b18105100000d1303001c02c1d84070107a60801401c09440304e505 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 198144082 1250 198142832 198142883
    0x6090b1611120c01030c0212042d060908060106030e0307060e2a1807051b120708070b09030307090b0f0706151707061202070302120a09031502180d 65
    0x16502c4a5110b9540d5200d2940c062140c45200c0403a4001091140c02c4036801e9001d40c46580102e2181c4084520b072001c109038400f80c040c0306606421003038254235842d460020164a0f9503c680841441050000151075000b4440d03100525403440145107450500e07120103010746500354511b1441d21503481d0340503090240e055200602000703600c1c9421281c403032100300010b0200d090903403084d802011040c00345064000f42240c00c00250000d0021003012500c0301d403420b150b20240c0400c0210b00001c0c195007085030060040c450320740700310b00c0d10070035440e0500ca003581c85c0812a04c141c04184070100500132440140302400c525007a0920303242c503007212943d03014183e41a42c000e86c011131002c010240400c00c10389a495901c4072a00300101952031405c0c200400c820320407461040c03219030000702202070510030301a20000041c40d010580c5c0d29481d4a0f402804c007040b500c8162124a0700b52030003d040702c04c074022034a55098079000e40410307994240c200541c0310b1105034229040c400d505a80301061018014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 198145332 1250 198144082 198144109
    0x8040203072403050a05130215071209230306130c050303161202010c02060f040609200a060306080c15040314100c08040b0103150605210706090b1611 66
    0x148490703078403202c0401606941d4080e10041541c1e040100b00088107001d9030706001c03269011150711124500c0c01a000400d4070030b403000904a60704203d002d0001580082c0b08604031110002c886801e090780303009a4800448c844510341d45a000000440c1c1880791401a100d0384c0b5000d9021148c0255859000034030b11b41c820100e125001d00860380e00000d10100c00125808820a80000d110051503400000e40380d41e07004104e0084035800c2070125040c052168007201c00a07600c90200e500e80310904401481c840145658648a85a18040820050b00c00d0240700c046a480c0e00040c41242068030070803068841407501c05481e10030611000011408082070100d0311201000544241c0d1501c12909050303c518113600c50600a04600b44000100b0510b00d550440f5085001e030075a5500d080c00e0f14001e0400d550103240c0c071000710703100c4070301521403000310100d800320711001c5903580e580d01c020983d144140c0d40f258503403c013400c1c0303c0300c5940c0c1d80d1050721001030351107803460404460150001941d5214481c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 198146582 1250 198145332 198145379
    0xa0909020c150c0408100507050909040303090b1602190f0206040b0424120e0f010c0509030609010506090106050702060405090f0a060b030c07060b1504080f070b070804060804020307 80
    0x100c2411800301d01d440c065000160f21100500d041c0c2020310a90f540c2500c00b2040001a80c2c0300d0000f03024911800c16140346070310090030f0040b141010304004028086580c0b06581c00782641c804074002a41c0112a4802c030009500600340c0b906448650400203000c0d01d2050302d181c2400080400180c0c1c4040c000c0c00074014404015403224140b080e2200340e001c0c5d0840740c10303a01c2002410f1030100d13504011b140761040001c410104e0003d0484258504051100300903a01540c00c0c0421101d509030040041e1181841c00d030101d603025501d2407445820b03158269400f0350800c540c100140a80c80c450401001c4160010b800545401e90350004512984400c071461315144204034144003004483c2e0040c1001041c601c0c010302d042d8104203000203a2407050740c4006020658404a0f1903030368880420380980d04424100311070312155699401d9489a8004050226600036600e01160000200003a200b509803c00c42e000c0c200343c2000015502c04801400c02d80e4907115031000054038501c000d800141072243d08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 198147832 1250 198146582 198146593
    0x6090305030906070c21030b03060a0e0111030f010312050c030a2006040215090a030f060b1219060507110a0303020903010b090f040210050c01021305012a080a0909020c 74
    0x14084034200240504441d04020000c3c0d000404180551200446c51240c1741d041040c252540c4c400f5002030444298591b050300804080014048403640321101010444000340549100341c1c964400d02d00c81119224031124051006001040f40002ca40140d001036080880c40d140109201c0e0380345400c130241c6480021fa85404450881000649070300d0100c40780300c0202501d08241c1c0c0081e42c000a081030a9100e09004141e14006664908040009541010310310190501038101640036055007840180603c415240c0708400c02b000041081c02c1c0700302c40c03000402c9174507290b40305000b9007005490b0808000b01100e5660040000b0300a000b0300e00d10a490040e50740c0c0020b01414251058030a41c0e6209117000e40c00c00010300100040c03035038000c0e4100c03030070032807210b101c3d0b0b05407424061841c10302d001e9840401c9034850302d8240403c0c40e060741d0003621074152001580d20350700076003242002030a1900e14190582e0b000500c43e503001d04025640d50804544007a1124880e40490300990508441503000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 198149082 1250 198147832 198147841
    0x130b0a0b0a0806100605090415090b0f031b0409020402070506070f0906020f06130503040308070c03020310051504050907080f0303100501090b160201020321150303161b030609030503 80
    0x109012070060115074050001c074600032031480c0c50507a0034440d003418080005900d140316505c6501140c0d038941e0501401c8291500c80000400070140ca01c01940644041c00241c80b9620300000c40c0c0181d1444600c40c3d03235101244405100251101500c01c9801ca03400340f0082e00012421b100d2203201d080b0075903d081104006490003041d42c0401ea021605641044105403100440840c481c0d0340800c5489541c64560b405241851952159600140c4003500100d5950200083c03c00c1000460b4001c41c03c44280004044400040711005d903240d8154500200b0a8181c904007038000e294401c44078001c0d121502ea440b003959041c050b003056141ca0640000041094400100a0180103407034203113813001c0304c2c0f82041e00c3c001c40e41c800c0c0c004400c40c0200810389002168400c2046400c2514542111000303030400010817800d082051302c81d00064030b14034814190a04000007a201000c50402e603400d204d81c481e4841584400c0085442c3d084020301c0c1502101042460042440f414481c0c0c0c0d616030303032740742 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 198150332 1250 198149082 198149089
    0x120103060c081f0317040b040e0a0f0c1d490209011a0d020d0c021b090a1509020f040303020f0a030504060e0303090a080c03010c0801030209040b130b0a0b 68
    0x41c0207007041c41d80d0f08021040710a500304482c000742a00c0e8490401c29280c21104a404000c0c000d5a102d1030310f80d00001004295480101d5400b802590041c006200d0010180814002c1d20b80100791040012101d517035240c02400518000079800f070001c0c0140e8000d50140c95030f2041800e500003050b01741001c80c00d20341d482e0820707801441d00c1c3c00503a030000300207016680e0008a18001c18814413080c9130f140303102c044a600b40d6504841e0b5101c000441151f803003100c042c4200150107001403a100bd40911000740d00e400c00e6102d512081d5010040c082c003d0380d81c1b048900e0300180700f280c00407001e07034105920224000801d44011f05110084c414165240c0746149802482d2841040d0b0040307003074002c40c1000000170740040c20380b42a1001418100021544c10020a00d1030080c034007030302d6010080100c00540f944001c9405d482d1101e0239170007405818480740c0705450f03c407400c0c0b02c025004a00840028013050080412540240003039644808000d030b56102d0851081007074450506056440141a00350324 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 198151582 1250 198150332 198150347
    0xa1a0301020702060316053c031303120902130204050f060c030304120309081b06061005070f031419030606080402060d050907080f0601050301060602161202010302120103060c 77
    0x108600961601c040c503030115803640030107481070925240b44044020454041c0c800d56410401244014454203490340300814108042c600b111070024240340110001c003102000c50380b01d1400c00e01d420800c2c02c545e66084a003000130491401c080c6564088060050b41c9020501d1088803c81c80050b849505160800c1010302c0c4a850a501c542c10400c18142e40e00c0001c010390f544290803580c0c0580008120f1030640140c003800900404180001410705004420100040c04481d044812105265140c1e01800a42c4800c0d1814601140c1c0c148040d0000805244040940303501c249000c000080c206444011a40c0082e00c034401d00c903212001c04070000740d05119201c0104002d02d46604941041e40218007288140c0b0f608000072074a82d40041c401f0135040010750001d00461302258104000c02580c6a00c60400b070140d07078801d50130032100090b0075100003006141210301039417120601d0b2500e05c62014048510101300c0c180b64003480b841d034403c240301803d1070085010703080215100141701801807504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 198152832 1250 198151582 198151631
    0x1506080d030902130c0804060f0b040c171005030a2010110606030102041206090c0e090304060216030201140c011512031206080d120b030604050a1203020307020d21050a 74
    0x146082241c411051b44a06026080b0b0341101c0c00080c446803114103580500301a28900350040c1c201546803104a50015500d4003004080360343d130001c1c2d1640901c10910404900c1866450ba00a203c0d00c404030f20080210342d400b000030b4140300019a0100c010075130140c8134078030704004210340e01040d29452405024240e44510110000c503d480d05000b260b0000510840010f85443d0b0340d0358000d810824040f81c403001404207070510308030902d0308080e003642d82d51090103030600500a02d05011040154000d028055035416100c54840e12000421b40125400c5240c5c5518950b488030100e2802c0d507005009a4080d0440c0a0403070707000e03042402c02030205c104c04594000718a142000400c0412004560741e40403c0c164688041c4a4001c041c0c68006001216040c40d07050081c0d000340800c000c40020400c480600c11030712949920354089041c1d00700d02046490b000541c2003510342d41c4016110b01c44001c509861003d1002200680180e08411694100e58611906555a9001e10360f02c2161f40810b04d030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 198154082 1250 198152832 198152869
    0x20f1b0604031106190f0b030709021c05040b0f071407030201150b13030b0702070e010b0301060e0126100909050c030f030906070803060a120803060f090708041506080d030902 77
    0x608000f800c2c4640c109031480ca018010744d0300c103d0716031b1070703d0207400003841c2503002001c0756881e0380c4896003c0300940c000c1881c0c50990007000c0321000105814000c4611550304507410306556070f6124038900a0541c010701000400100c4040d405040780d48002900c9114002c0d030002442c00c03a40c245502c90140241c0100030b07456814024036000303490119260055950100c0050701548406034240e01d4003035142c10100542400c00004103500d0794000103581210b00c81d0303640810240e0101d0040d62501d8403280480702101c080030a40011601e180000d90f00070360b00070711901c9540e41d00c50b60002200c0e80d280c0104e9050b04070b254405074929040002601900d00c0d100a14502040c41000906510524600801a4601100060803650758604120041080d119203545506091510001c6c691003140e41901c2409042c0540405060001c050340c4190f04070786580b41e0715107031a00c2d500c080500c00006c40f6219a10f030355022602c02400d21204031150380b146c42c0850300300194070420480440d0030095044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 198155332 1250 198154082 198154093
    0xc080f03180a05091305031309021c06060c0609020d140102130501090503030a0e03010e010e070837050a0510060f0503060403090b07050f060717101503020f1b06040311 74
    0x40d0b1340c0d15007401d500f0280380e94030010240a01d24000d800c40c010340007010980602c0400008105426400500a00342000d24031180c40703e034021400c08403000303409818002041c0c5030314000041c0b6142e0014a02c140024100c05048182c0e42d0351103400e01c0e03141030b1000b05075004902e00c44030503650309564001d0502420b02c0d20300a41040c0c04a5600c0c00b488000b801006041506c01810703440a60011100354890002031010380120000d0541d0b80030b05211b0f8034003d00c81c0246552907500707040e5424040745800319201c46001d0641c41c54030440044c1e14001c2e078107030042201354000140c04101c800c1140c000b0840c0843c9032403504c00400d02c1070220340e000314084d800680400000940c8841c031041030b5240d004190b82c40700004d09105180c2690081003501d113108990a00002030b420240c02d400056240549408a41d070740d2030083d982e110940304111a80310702803200c0300300c64081d4000d803c154035030604e51400c0118229015001c1c070315503030f540a80f0b038211109200a040e8003402c08040c14030320034014030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 198156582 1250 198155332 198155339
    0x150406021b0609190f020a03030203070b07112a0405011401030f05040506060d21080a0b0102030c0a11060705070e01171c0503100b0315010210110708070c080f03180a 73
    0x44d107522000b031952881c0043e1600ca403042100001c0b2960781a41c000c1d100c0456030f0b80f41e25010356a1303440789200340c400e40049800995981d2280b01d0009003455040d01a03d05000038a00c210031000c2d10040000340c500001c10b0342c10217603c4a09c542402424650980e0005803c0d0340000741c04c590b04004582c005034145810800441c000203034032a041902607a0810a542039410100941d01c00c2800842e0402e508580c20250700782e21a08a03030086102190030400c0315810300c0166a40d10581d4054091608080020380200700305c00382a11800c1405400d441ca0324480fa500c540c1800c80c290450075030b0410500041c8a4011150344000b8081400001031404c645401e094101e45664a041c5a0070010000300142480c1d40c095801c5004181c030303000480d00d030308240a550302d40c18040c402d128018070848501b202460043d005000d03207034094070116490701c0402e4036451030f01d42c0820b2050303441a0841c1c0e00040c442c0400c10500040b03030340202c003031038413000c1e0110f409000b00039181800d4400d0b1107000090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 198157832 1250 198156582 198156601
    0x1050a1116032001050909061507030306031b03150b060d1e051003020603280e0a02010e0102061006030b06070b01030b150d020105091e040501060c060e1b12150406021b06 75
    0x30391307a0382007c8440d640e032551400001022940241184028007401041e403d0815405401580580c0d10480d40c801200204690280f0896190b200141582030f40781040c02d034094903588240d002c5440540f05a140c07210780a0a50103542141801c0301c0f20ba105180d8141100c207840c803455030454001d0320640203a514540000e41c0e00d000103880c14900d805806000850042c44488440f0b240c00c05030700610500c0c00342c0b104252142c40d400410790100d4403038540100704e0741c03011981e94130031001e59545070356980c2019003c40007481c0b4400c9858020030208a10b00105400780e0140703008600c2a940030440c0e10b0300d00080c402c41e0911103499070190108001c4440141e1300082503510441c0c0660f9011081c040d220b41c0d82c407c02e61505021074201d0729007000800c01c0b0f5030210788181041e0040d0000d020320700c0741031a01e5684621302845020721140e042444801850001e00c0d07207010b41da80c64211041c40482c0341115034550303000c0e0340458a940c3d000800708400500185412440e1400344040d2640c0d14158010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 198159082 1250 198157832 198157837
    0x20318060316050307020106241b02010816020a0602130f0b09060409052512110705070605090d05030d0c0e04021306080c120112050f0d02030901050a111603200105 72
    0xb003800740000400042e18144c0300758030100040c12118030300386242c0600c07400b40ca04000c402c009000020036640d031918441d0200055000c51690680d545010382d0f651281c802c451001484003082140a901c881c3c4001c2511070001c2c02220b911086403540c00e61034081e544c611850301e0341c01074050000c144801407081d0345450035207085511a000116040e50740503403086000608924125032000740e49104019164070030b40e6284142485441007002c04000c20110380b65014010b4010100d45c800e07142440250321071000b81c448000007030200903039055079540700b60449e00b000f04540c03401c6940c0c0c1024029164407220301c50100c8400e40742145086480b007079034400036000b07001c1d40051000003c0801c0845035060116500e90405035041c00039561100f144d6a220720001070b0607200d6101da03c003501010320000c40c07003200b12166500294a4000c0d220019070309504007034200c1d0700b44410114100e030b0040c4c083c0315084040b4161001d000b0540d04520705a420364400c01c800000440e010f0002d1b15099820908 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 198160332 1250 198159082 198159121
    0x30b0a0b150309161208090103060b0a08010303020601050f0f04020a05070f060b031501061d0f030708060a150602150a0f050115140313020616061103010f0b0a0e0907090e070203180603 81
    0x80306da6039000f01800582c042c0000744d00c070581145000034001500d41d0b01c842214142c1c0d20917401d6400c103903030b902d04000e21b030a0881e41082e0310900a50610506141a60040072620040d0a01c5030410b100303511485092a807006043c1e40341134860341d103281580390510414407006d80b0801882c07805d506100d001050f034a102064540c180000c84403548155a40c0d91680310242c40040407240e001e900d0700481a00d4460545401402c20304141d0005c9544410041040503035290364020015103002445c2086124809000701c50495541d50203074900000700d0048a003c0c08240d0f240c24484034515100601d40d01d005103801d1141402401030190504c14110703240021a011074001d40c94200c0c0b00c40b07014500d28842401803030246068002d00010140c0d5014504a80a40d00401c1b4595a00e0090140d01d200355034044002171080001b03038083e440d0201c0b0300c94210340607141103070000303483c1e552601c082c510541c0c441000d43c3c0b003c40e03c1c0c1c191040040510110b504165100d41c02c6041040680ba4030180204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 198161582 1250 198160332 198160343
    0x251704030908010515010801051e010c381e01060509060f031003050f0307030509040f021c02090f041418150109090201030b06090109030b0a0b1503091612 68
    0x218050510405211010b485004020001401c2045410410414044900b80881d030860000240d52a0038000640a030110300c4d41c3d240312105100c0116018192a0350807240c0f841c0c044128246484503048041e1001c001c01008a6400050101d8520344000144030142d9080030741e031075002c05161b2640c0705044404030705050341c981c0c0140f80040e415003d00320200d42d4509010007004841210303d981001128000c2d0b054402c929013802080303031030384a61070300507010a02c10810704420f030400d035020406184005800504000f1803a501d40401440d05a00c0d40140307401040b001d07c1440c0c003000750031400504403800c10a620b2440c540404100e030050150348004e8103080c080072080d10500c40800c2c1041b021842c001d0640e141d840e240c005001612003030380001d1070704450090034100b40040b6464604161505840a4990381d00d0a00e00a4000c1c01c8914168554844d2082c6840700005c0b041419074440741c80f52a1324005503035a162088150f202020040b056070200100180d1102c0200103e0300300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 198162832 1250 198161582 198161627
    0xc091419021b061512030c0c060f04091406010809070303020604080f090a0f0801050c0c031e09062d040e0c0903070f0306090b0114030d030515060304050625 69
    0x2d04104082600401d01c0c0d100703901500c8100072400e5008500854210b00c1220032090315a48049000c0e03483c007800c44071005541c001034090900d460850003600300f248640c2d51a5180c5a2204501d40641b802e01855006001c0301400744a030079a0881c03a00340c0d12140001c0240015031551310020740c4e911000d4005000828001030a0021500700d5048540309000900030707002c044d81c1c1e000b003940c462030f642c0b241301e800b0752a00300840c80b03100c800412188070541e01d800542c2040c0031007000d030360402160140444c803210b041005c91142e440714030140000303540c610400055140c0c0e104021080010300a62000600410070080c86044e03084819103410001581e2826100c0709184e010910700355458000000030402d80c0030000402610707400c5285001c0c030481d4800b8442e42e0303039640c1c1c00492001e103005070f0341034000843c811401d03031281d80070b60f070300c4684010070000c3c6200110200350f050348191400d50b840e4002c84e0070000c4001d0040032882c01c035500c2400906108005da0f100400080f075014005c1c6118010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 198164082 1250 198162832 198162847
    0x180609150a0221071e0b0108060103110117070e0406090e0c0f10021510080105040b150406050105040909080915130e0c040b0c100c020606041d03250f0c09141902 71
    0x817080c4220080c1e88410804860350b10f9446903560f5590034030085420b4801d09540201652190040c000302000c2d891881c00580c0741c0c40340c1030b40c0b9042d43c140c1c3c4076005135440000141075240c80c0200c044606114025100d407401610a00010f1612000d00a0098003401103c4401c2c55000a0003210600207841000716616402001c10f0184031a82c4002070310f43c2881c00703100c1807084141003603000b00821454020f0050a140038442600d40607c100790100b00280810814403c213038202e551030138880c81203a03280c08504c20018a000e0344182c08a0b01c02034000c14500c280000300082e0501070140020110040e290542041603940b241c0d000c1c1440740540410fa1090846081014030380c3c101e4070040c2032008001407032000b581d0314012201107109504040340a0300740c030110805803c039a61010040c51502c01026030891410340c00600b018002c403c11080f10012075442d07046000b203036214080103211145450b040701d00b40c4e000002c181002002000900c010420910201400b0111007031004d82c84106 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 198165332 1250 198164082 198164123
    0x203041a0c030c2e0c090302090601050903071706071d190506030717060a05011b020d080706060e0a050c071403130803040e09010908180609150a022107 67
    0x70300361070641a2203611080451103428251401d1516281c2d4030a070465404401100706450301c000401c00811b40324a410300150400e1440701c0c0d840b8a0605215281002e07032401b10346030400d80d5101644006104034801c2c0c0314030f410b1140640141c864608511250310808410045e0410b10000c68400d0103000d100300d00311100130111000901c0000c044036164070b007158000d07000310403210303502c0c544035080d800180d0035240c00542d00d400c1da803041c0e40710703403846c013a4404001e1414507050003a6480514031440d00300007002c02c40140365042c8641c102290040c503042c00c41030491009080c03083e905051808000c0046c40c1030084d00c200982241140091000000c90641103102c1c003d544a071403408440041040303640000104111b51800552100c1a03860650203800c81c0c0d00410001e125060400034021010072104200702d144000600c071606e8140d0f814001a90480500f01c5071082c114040b0300015866014840b005010180c5440e01d50a040210107041d00c900c268074004119503603c000c0c4028442 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 198166582 1250 198165332 198165337
    0x140307090f06050307021005092d01020a180501080112060c090918170a050306130f02030a051e07020d1803020409080301150c080906070203010f15150203041a0c03 72
    0x8100c1d00319844035100e00c0000d005a00c2201c452005d0311030410b0244c401a5944540c40c42a0f002902034011007a220390101c10340c103204800c1320020314800940c030340c6924080c40209160a4103484819008515401c1503121f1103035070b4002810b10040400400410015000b981c04141d80200c000601c4000400c0503218661642c2204c101c403807500165064080e42c022284420500884400c600c540e070307442c0c4030030071441600070340e60004a041c03011440310f042507035012040d0101000e020907907040c025140310032600300715040150301c2c1e140e1050180e417104045481c29500751010a03007031240303040e0360701070b40c2c80740c80c1d070750350400c000980c1384401d2500d1400780154040c0d6030062051010350280e00701b0a016420130300940040340040d9a09584c400d00030051a403c072540800740e41e04241100042040301d402241c41680c05549901064904030094415000c0c914200c0c684a4119406c00c0314103143d40085600d903030150340c0100814000d000c606280f40581200c0f802030726965010042126080d070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 198167832 1250 198166582 198166589
    0x9050d0510050906180313060302092205040605070c02090412090e040609030921020105091507060e0c040213090c090302060a02030a021002070b070c020a12110f0301060614030709 79
    0x582c902420f00000c04001300d1414050385a82580d01804000011100d40740c2c8600d204802220282010400102d40260060301c0c450038010b1000707070403030000f041030125a514203540009259452080101300f100600c102078029019281c88600c192081d40858107110300a070010f41345100c0780d12100704030703403052040201610468100181d5400c1c40c0c0b402e000a4083ca40048012841818012503414000d8088120304d0100b1078403030709503111a0300103441d140c0c04001c030150010004a603100500032100010000144102000564850920f480c0d604110a14807180e101b540100a0405d500400400ca48281c41041d600015210b03407400059807100d00035031000350410804589010500d8020014040ca00003640964001010050070042203202d007400003029050751001040c0e209205501e0b0a0744144050b080c82e02c402c1e01c0b4148503078071400142c0c1c1210000881600201941445a291303a9903070820790090090600340480a0501015181840072180300400041d400620542116004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 198169082 1250 198167832 198167863
    0xf03050606070f0606050a140f0f03211306020c01020d03180605130f0b0a0b010903150e01151404061202031c0e04050123032d0703120305010e0f0709050d05 69
    0x21990fa1500480c05c80480606601c1101504274455580c101406c05214922000340901007840880c400280085040c400016402d1014004c000c0c80e0b184c0c100d0000040c00c400d80052980d4900c840009152940030010802014100082015000d940010300c5001e1070307114101081c5a90340c0f224030101c41c0308520b40903120501400c00c0d1410f0141f058090b5006901c4c1c20303800e1081c030603413900640b0800620300c0020004003003218043c2040540b5444205072030700c3d010000c2440e50000300b11001001503900000500006004150301d18a054400c0c90010422001c150024a089400091b00c4005620054103501080c00020305560b204084018042c00020b004100c5941c561302c541c0718810b501020000300c4200c02c500c05480b841c002408848940058030035100d005c400c01280d030300c034400205100f105c03441078003008000208c0d080140e111610700d0b550001030541c5401c050010901015000d8000d5400321014032004030b50150840b410703a0410303541e511480d1030502d0315616200582c11107400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 198170332 1250 198169082 198169099
    0xf0b1b0109030c02030f0a02130c0c0506040311010b09040c06032403080a080112020904030311090a0801050f010b0c0c210f070312020c030714010c1a04030f03050606070f060605 78
    0x205500040d5448201d40264100c84144000001281c1e1b10070381050080e42c49240b46842c0000503d850300702ba20310740b4031407400c1e840141d0b00d941d506103004004c0d10101c0c0030520000c2d502545a40034451590800012034107003040c4d0401d0b459018202c0d145000714000c00d525a0140b002d801c40a0a50110201c0d000080403a0a542c90609090940101c200200014080d81c0001a104800b00403802403580081c800b0003070345c45a680903001007044501035488100140311000382a41c0791002500181a420300100e070b1450300d0142c42090030816000100007460074040203924080000d800079140f207040d640702c0300e070214044101040c0e0088071444000707845101307280190050f0100701482100c0c071811010090034075110050741ca80d0821907030303603415911101c0d0030040c109a1182c0d0080028040c10b0403040a006510340210041503025442413401c018028042015444000c0d4800b40340940f40c00c00460501000260680c4241304001d070010180c0600380c0300b4401070b984504024040240001c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 198171582 1250 198170332 198170351
    0x607120302040b0d0f050703050408030f09071a0301140603010e010b0d02070c030602090109061b0b0618091605090408040504020304050115060c02090a060e040f0503040305070e09010c090f0b1b01 86
    0xc014005c00000100018202404682c0c140e020340150350049501c5038049085503104003c44422500043c500842d41c420014000796074409503060302d0512449a0310283d0365818441c04034051640700f00c095000e07a20400041010701c10741c44440e0305689002d00e01c0c0390b0701c1720090109000781c002c011024081d00c001d0f0b0740010810003968010181284283c0307400c80c0703c1d0380d00d8a0546210340024100c101050a00c40c0c1040001da1080d07501d944218000d2165039117070090b0200b0401180104c910030f41d0360340300701000d040000120241200810049034503038410b103042c0e41c85030b015000e54810f243c0210340100204041020039081030f0511031000d2800d001040d590100149800b83c000002c0c0c0c048c034000d4000c583c103160140610420b80b041c0680811658070780c1d0b65600031403043d02805817081d010074030010000460500030350300140784003010b2903040d08003501281c0c00c40740514056414040501010130414034002c40841c00c4680c0c4034181621400b9024031400c3c40c0e030030b051000005502c0c0201c00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 198172832 1250 198171582 198171607
    0x106050319060b01090311130216080a121104060807020a0f060c030e0a021f1413032001020c09100b030901050121051f180b0609060f0607120302040b 66
    0x80c1807a40a0007041c0301e258401d40c0151200d0381980000741030101c40d40c6160229040407144036050605070700e0700502e083c18505200c000c84001c88030803182d40b10002408540503a20030a41c10020800d0b00007040381c3c80e0030004c46103440c0300e0f500c80c0d0300c203110b041c01c0080c40e5180240800c043c0c0a0b0402014440800c1515000c8007d107a0342e0350b8040448d240c800c140c50003000c000b0360611710641c0074040d100d102c88004100f205600549060404001828007d0255406100040c3c2480808104559019411854074001481011720210b80b003900620001c045c0e0ba030b0015184440c140151400d072640d8813200c0d9295108070464005c848059000010702c00b0a000542c0214102d83d07407542a542c031904031540b00c1003403208030000900306910a9800344008500030034403a8455504820010300b000848418100e8040c501009450f28444d213002c0142d030707046c011403042e4000d004851b0100403510400010300140500000500a000034540100e030b42c6000c0d0b812600a804840b0320141c07a40d400c880304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 198174082 1250 198172832 198172873
    0x9080604151506020601140307050a08010c0e0609030319030f090321110d0222080a0c052d0423100f14060703020c0402030a09140c0306041401060503 66
    0x498149524021654000014070074810066800d9507002d0b2a150346081ca00060307d41c3e000030001e5140c040e44c0c400084e181da5241c0388900038414080003250314400550054410404540c2890080d8004c014881507940c01200b10744018074200c0c02e1a0040e500d0346000c6004040144050350001d1520452509060f082070031000b000c401d96005890140c4034500b141c0c25101600c17444406008107100c1413441c81f131036402400b0307601c20158004a1040c190f140c0c0070b00000e001c3d80821080e42041030a402844551005440a014285c420f41c100e6014551450460041029404080c8034401c520100c20755035504680641c0c0c10030700003e080c0b031091024002c1d508030300b5500060b064025020000d101040b0010401c01c54a0310004882c8212240007800f440c3c0e40400c80032803c50113681c03080d02c015a2180702460141c080f0010016660540785000d0b68003144595602e8042d07405042e280c0030a80c0d001410560141d488101904000030500c00750f4090030183d004981d15000d8404490385280449a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 198175332 1250 198174082 198174113
    0x10906090614060702010c081c0c1211040501180509040507080607090f03020f1801081b0301020723031c14060103201e0708130f0f090b0109080604 65
    0xc2044050790301e428000301103140c400790701e8000005000e00400342d07000b4042c0828a9005058407450310f460041c1e82031900d00c000341c2c1e81410740d99402c2845403e03580060303003007902003103110104040c00036100104c0c1507025078803c0a04001044090b45505000d0b1440a0001c241c09040a0200d00703251030120b4441040c0e001e03032590341c441e4200140900b0300c50045001220032462005141c1e50464081c400354640b141451908012410321101001c164403d15500900c2100040c0c14003150303151002502e04007001005110340e00501600780444c02c110140c84e5000c03645482c0080034481a01d819040d030190300309102001c4508491102100d03600d400603440c000030944040c01c96a100c100540489010300140015103c0c3c004c02c40c40c0404403040103010040c0649ca1010041024032a40c1f0110390001f00102c0350313914080b40a150020000300c1410103800115258015a803c0118500582e03489105032070b081e980725500c2e820164026100355010308001d0041d039446291604000b078060000c0030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 198176582 1250 198175332 198175349
    0xb12030408010c03590d09050607050312070903140a03090e09060f07180602070302040509060708160c020604091401090204050f0118080307030228030903020103020d1103010906 78
    0x141c2141d4950061224034080791070456131445080958225403003902028612828030808098812041c00e500d0350611808107017490080010765000e41d8020101e91050303000b14001c40d01405030340c000a001006481045140c15003d007546d42d580c2904503565240f0743c0c009040c0c0d200d09030160b02d400c6070218071008c40303601035111109855940d14940000820459070709086802180208d414202d440c0140d6401c110340b45011510300d40b00e9541c441444409510a42c050b0b40103407020021410b0501460b513100300074502401280c0350030030300500f55820003040c2c200122442031700c0240d443d0040718442038140e00034141e26121070325241c00200030404442100f2071031203144000544c03840d4500803a415154040c20300400d07800356400556148540d050b06031504481d03030801050450f000c0001d4583e10740690b0003461440700c3c54a01e17503205110144000800e101d0f6100010101c1d4003c2c030550101d940c207203001039072202a000b8020081040b00c0001d07032202000400040d070203000350001401c1d152881c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 198177832 1250 198176582 198176591
    0xc05030915040807050f0f01051b0102030a02090909150103030f112a12030412060609090803160804030e010f110105010807050a050603241c08040317030405100b12030408010c03 78
    0x400410540700703c0089416800451101c080900e94070a82c0500032b0400c0d4804841d03400007034400c070182a07070411901d00c0d002c25808640480d071440c201d010660070044c0300000e010b004a030301403000b500d804140005801c0c885014030406500344148038103400c0403030900036200700c0200302c48801f0743c406011041c80d2500c8082012682d5514112281c441e4100b103240045191034a0001500d14444040c0802c0d40c05a50316800000e101c0c400d0b0141e2000f00707103d281003658910304410070307001c620600b801034002c22002004000000c0d030003103d00800342c08242002c014005051204407040c04040800f240c09509020001503410000100001034a0003242c1d1040c0003a01d0743d042c481d10b404120b138a003070f0340310362408030903401a00000e180c441e001014200840144071100507590301d886072501181c070003400240400c00d00401c44c0380312030103010b4441c10500c0c504041c2c03691580c0d9a924a1100d544980d941041503040e038488180211100030314050300e4440e81c4c0ca4800b075000b0080080b00030042400c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 198179082 1250 198177832 198177839
    0xc030c1e03120a0c0c060e0307020a12240906150e0c0c060103063b010f050103051e0c13150f03080d0e03040918020a170703030c05030915040807 64
    0x4015900c500840302d51100180d0b4500a400e000307440522140360034481000888000310340a8000c0702d085217580001142e40b9011807050203051f50300381d489001c250301100c1542c1c00299110003c4c00c80140b101c0c000280068001e03082000403d618000203084502e00900004025103000460049034200000c0008545d201103c141280c450032034481103542107880103100043c0385031702c44090f0841850304041e498041016074032550400042c40d01d402d40e40d41071140d012560900440d540701104080c18021545969661550ba201081c12410f8014804e400351a07a500b04000c09000420014108418108180904002402000c0d043c20101d00000004141c14001c403c1d84411a9488a8080e01d05050038921600520026203080c0090008100008594a5078082e02e880c1014090708480c01060a10400001c01421f500402e040d00d8007280c00300c000c2d04042100c5080b01d816080800e0b50520a1400e41d003148104030344c107a4044500d840340170400440340041d1055505200864030070648 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198180332 1250 198179082 198179143
    0x20307121803060c0e1903022202160c05030d051c2d0b03070b0f180303031e0609060a090c0c0206210714030403030f0e010c08160c050c040e030c030c 66
    0x940c580202c00c4071805580c10401400d09043c1004805190600d852990031a5881075052f64025240c40034060800180031003440380760740c0108010601100202140302400c2c1c8041c01a02a92040030304520424501b4111200c0c96080400303101308207260400080c0408007a100b580000200c1c03142011300d00b000c00380c1282400a01e41080e960f074050034500704810138804104075032010001d110011031541c240d0605450400145014224840c44071101002910340207084990040950780b0a280301d1040c4070072034542507411000e82d0102c040c003040600050350143c80d0401d4403c0c00070740050000860101048031540000b0f00801a5100e08845464020b0200ca031801003294140c08200c0400c00300340000d004e5808050b000004d0980800c03424118601c040c2101c002c0c60800c00420415800c2103800c0040094000b004600c0b420300f1090105542c9805d9a100c1d040e012140c00355550b01d09110030141c2c1003050f038442030282d07000c4954400308200340c180c035501410010503182070710703950640140e40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198181582 1250 198180332 198180349
    0xf1e0111030105040c1b0c090c05090f01050a02010b0a0e0609010f03080306090a06030b040302011505010309110f040b060d020d1a03060609041104020a1701050102070303020307121803060c0e 84
    0x1030440551800c0d40d0034201000003c11903500d40c6424880500030404141c01d0020142c14001c0c00f80c848002200e1a1110135810340709010301150410a0802c0451800e58450b00c04a0850b4000c0ca0217035140c44450106070300602028203561b902907051313840026144450480148962403d0301c00310320303690343c9d0425a80f8400c1c40e0701000307282c4101800040c0081c1485140181d1084000d0800b048041d5a40c0314650041c406640c1900140d444256410300380c0036102401d00101400c0c81d08018074402511038a0180000034001803140c0c03060031146d44c00c1c0e5103d81000000c0c4000412461340d030350f019401d940003548100c0084001d58204005098404000b8070f00341e00c91600030307000d81070300d5440c20304001e11101300a01c111480c1c0c110f1840c80055407520f101600b01312107540c45250015811710070341840800c1c140d01a0b030465120395000d00009074080151941c3c1c80d80504500c0b04000607540544580d60580710184240c114150008184601904172000d00034280d1104091410013100344007110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198182832 1250 198181582 198181601
    0xc1f0c060f1e1104121103150117010e0d0c170c031306090803030f04020f0d15060501031b0207030803070905130207150e0607051c06060206010612090c05060a0c050f1e01 75
    0xc02e1703210030328000706842802d50680071340005d094601d9045024504241c1d9070084e0003842c04050b071403170b80c2c00710103209100d00b0944d488440d00a05a01d091414020718095100e90010101001509410034444110061324680d24000064903250b181c0408100440e00c420300c20383d0005400b451000803101e40100441c0d005000c915403c02c95541d941c1c0178486c3c0008241031450300000100e0218010802c03da1030008a11010308020035514a4100014143d48481c030301c2c1c0314030203030845950746129000254070003107a620106842c2c89540e1900184c0b00e5000d190300080e0000c0d0381d55000c0208042c2c40d03008086c40d603ca0040550064241c0c1c000380c04480b403c2041060540c08074000c0b54020307000302c02800031000c500446600001402d610741003a030f142e5520040150744042d0040c001c4c1c82c2c00503007524042182d40b2003040300c44c1d0103880d5180912540c0c800c0070701903840040d420580a201d61700d1070070b1094015044070141d500c0003600b00d541d1240710500d03414030340ca40740d54410f2498040c040c94000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198184082 1250 198182832 198182849
    0x106020604022209110a050414060d020307080609031e070302071e0b070f020909030f160c03120f020c010f09031101091205010e0c1f0c060f1e1104 65
    0x20754442c0e090100c1d00414002d2440c0c00c400300c030f220b142460810b0149020961141d10581080018141486038040c81c60300802d02c030b20708154600d035034078a81400659000c1000c88603c80c032190140040f0741014190341040901d405902d04105800304000000c000f80c8109000c404c03240044000240c03c180600e40b4010010303003100b1400c00c40c45a80c00f001c8010068442d141403e810754890404070f041d03202e48130454003c1012030030b901c02d616121205651085030b03900914980078441c000f828880c07080315011098a4030136200c100511040410510246030f0128880784c030400d8400018080e1100d03011400010701c20906202402d5100300180d43d40c4d0600d41d11b030440464210b5660b0030640d1100600c05041000112002450b448000c82085005014000005121143e16850b0781130082c0c9115107070150744403000e00400c008004500c041406428504041c800d0b0283c85d020b0094004070940b013001c2070500441c1c03c0f020301c0c1c00010384007400b100d01041101d030880e00710544440c01903115040d1b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198185332 1250 198184082 198184093
    0x130902090a0507120603060912020a02010c0f03020a060207050a0b0c131a0c03071209140a0e04031403010602012a210b0607060203150d1e0606080708060603060f010602 74
    0xa000c01c0341e070005a0085858200b000b01c903507065500604071041307540155209038607075240c071040c0703c5101d491070190391680c405002d442c10b1135000030300308401071480200701010480c02242410710a02c940c0c4196035101000795520307503403400c00070f40d02c1240e0103055a11000f040085405050000221f0341050180942450914640741000c040d40300a8840b83c1c5110780304009600101c04103000514a41703100e000701182e2041d8124004000c0c1141d0380004803200c503400500440755a451136641d0440b03c9040d0074196542d0380346011909056035070390300e40711400c0220002c0342c00c1d901034200c0307401c0940000b5003011070444040c1c24102c465800006c800881d4520404e00500755850102c1814007541d500082015600d05000c1420b651020100380e0b080b55000c01800004c00940403a18884601203c141c124181d10342c545d404a540408000411866188a074004020260b00208028641803080e140601c0d0b40d640d0180e25104210344646c82030203280c0c002a51001008140350507100369a00511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198186582 1250 198185332 198185341
    0x809010e1513020d0804091d03070201090306020c2406030d02060618130f03020705011e090915080f01020307021507021207020d0b0a0605040c020c01050306060d060f08010b13090209 80
    0x2501c00500c0d0b4000e98200d41d41141150228100c000180300901c100c00300050b0340d0224400b80303400c002d504920301800c4c0c0c008100c02000360b80d02034480d40949400c99801a50784c582c2022103840d00c50b02000708a602c00d21120000303c2401200340462003140c050303043d10543c08402008130f0b01c03500301b2141d903a80036080c1c0d0081f03000440c0507e4002c2d0302c00019040b40f1004400d90b110204192607218080f001079200c1c0d074050003a541d01c403a89031000c0c07a0034409500b0242e8032150181c40b001890103400320955484824218540c5c01c0500174009151540c01d4034030103030054400501035401255050b001d03105003003944030401800c1c403010380f080901b60702070246c1a070900582802c0f540000d42c140d13480320406100d140441c0c04004882c0c00781e80031090005025151009000568440303000310815500022080005640c001d400c4980c05034003102c036140da0b402c805880e000105040d4012101a900c2c0b06000720ba410015841a050014102c516410068205082c2e9068030095040203412440c00c60114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198187832 1250 198186582 198186601
    0x21009032001090803040507030c0f05060a030c14130302090601050403121d21060106051309050a0204030819090e060a0605030414010507020a0c0b0906040b21070809010e15 76
    0xc5400032101e800101d54909151540e16040c0c1003900e081e1401d800c8000b040003002500c150380f4009055644440003428600340005107240603a41c10041410780792842c00e4130f01ea125080521034510401d9065407902600300c8031110345440c900003280a0072581010418642c010002d89003100c0c4e0003c0c46141c125105d41d4100c854109103c081404520400445000f82e035031400704000d0601c4298988000c0103400c18820f2800206a0103e0240b01c420000c4420303c402040840c401e0782c00580e0f0100316038803000340b0f4000a22550b4000340c950724000c42d10301c146400301c7c2c0e01e80b1499a160307910008002e4403480c0f1540419401d403805035000168030303030421041d4020405964030134012039030b0582c9a800d2088072802d560044494034010380011414204000811065101428120300003505080902c80422030381c2c0310302d0203902484080807030351b01c0340100356402c020b250415034040e2407114108040050110b00040d01c801c9859400c0c000b004000000028020303506036041015070b02e032516645840c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198189082 1250 198187832 198187877
    0x30f0702060d02040e040602072108060f06070c06020f07140a1404090507080c1c0209040b0903130608011805060d0b0a0e06011206050105031920130b0102100903 71
    0x400301903c0e02440b0000c0d241100300782c1107120b03600860004d40d1380d80440c980b01d5800c0c1203070403294181001007403030591007981c01075606038004025104032502c0e10000340014028061220000c0100702d0111001c01c7d0590701240e80c10100414004451205072110398502c0810141c0350195042a60700c2d03800c1003001e042c03410340a008440a0b000240e0040381d902d40c94103000090304440082c0e0b20409440c0307200d0421040301d209460802c001150207039031560014224a401030409030045400300081417080c1c60600844141644016001021a5895001514262092203406100301400c02444e9580906005443c850b0000410900711008039a5072042245d5001c0d19a540c400d40c0c80d40e0129032702c3c0341080864040c1030411804a001402490540b06544058104a00a130803540c07001610b0a0300181e2000d11303da00c4082c0f4200002c07a1a11980381c1c42e0004011580b206550181c100c1c0e6886560000500c40700a07400d81c0c6040d04d005403403a06492091000900041e04007085102009a2105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198190332 1250 198189082 198189097
    0xf09093301030b0d060603110f03030301030605040302160e0f06060301270b030304030503070605011203020a0f03031401140405010806010b0904020903030d0914011b080a020a0c0203060108030a11030f070206 91
    0x40003d5460f050030f0120b002601d040000301d54842d0345a10501c14000800d404640c241003c80300303522100400c0e000300380c0b21701041c40002c007040e07241e04c041001c01d4000c0c0841d0f43c1c01605911000c00c03080d514034041a0b61442512100945d0403414046582c506104040740e0507035600824041c0b12003031030223031003010110800101000c82e5840300fa040c1d495606000810046000e80008c54581c08039082c00400c03280e0680c008200b1703246a00c140030010b900840d042000321f8024030f01c240784207501d050640283c401102301c0801a4007120020a006618101d0300c3d24108041e2802c000c983c0e00c540300f242c1d468100f0300602071040c00070700603400640307015002440500009000c0d80d0a11841c0036000091b03d950801c1201c28461980348168842d409200d81005130000e4400c40a000a08040140c00e40d079020b00100103042c1c0000788114aa8001c81098285aa0140880b1015a03403030701115240d403c10007102d03001884191612520120000917034251780c40403034030740740303449aa0f90070841240d202030f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198191582 1250 198190332 198190337
    0x1a090619080c031c0e100309020d0b15030607020c0609030f010e01050106120212041509170a090608010f052211070b1e011403010605060f09093301 65
    0x4080c081501418002402840028406070555000b01810560404014501241d00c828400b01180e803282c4152110442915500140400b40008802800982130080e401a40c59400c2500304030000c101d0034840d14000c1003011101403280c00301915107005403080d400503030080580071200d03e040d40050a0360f0800504488518000c125030342c1c25100c04040860740d44e50b6820040150a4110100151070010a00d0846c5844c0412011408052010340086e1410780d038400c1c242e99800141d40304202444d08040905107500c91500b5242c01640f00c00c03000c20000e144100002001d5000b1146036068466207460301141c142428144250056103031903040010780250f19400c4080250710810100f45003803200140e4565943c1002c10b43c101d00030382907902d800e20807110300035901c511003420b074191990900d200013000a04000203025011582250f0b5001d5400100301c00152401030040c04000710a07600002d03240d540689603c1424064a2030002c152030f540079205960040c07001c10b10f00c042050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198192832 1250 198191582 198191599
    0x30203090a0609050f0c060a05030106030902060904050a1a18060603250e01020d2c04060902040906030b16050d0207051501060203030a050f1005010c0f0f0b15041a0906 74
    0x361900701c00c0c3c0340c1e078034810f07503498001c0410321020000a104031202d03850700b40c41e85490f166020200800d1444140719810400d079454804030210341d2050200d03280d18100900501550402d031741c46034020850010341d04010202c1d8000300c00c85082603041c010441d03000240359451980ca11040c0a1a44d00003410703654460f1101071034540c01201c50b100f00c000004c0d6652040452202e0a001928000314031860a00b330020311694071040304009030364440c00c14144c01000016004070300105016101c10342040c180d00d400414003045601c8e0650040c022039002e00c01680e8540c81e02c1098491700b80943d800c400001d0410040c08690a296400400e08507216100704c90702c50800714002044850283c101c900140c20000034030602000e18003400b60040360a281d2040142440038008048140300d00c205414040428090303000d0060a019101100d5000300840e080c0c0c1e82c15240824065800f110b4100020340d019481c0301c401c1c03e1511403c0100700c200040b242d10400c4140800501450003070141303901c00c104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198194082 1250 198192832 198192853
    0xb0f2a0919180b18011e0e09010f060e09030306090c0408010501031101020d0f02030919090501030609031b1106030a0902040c050a1b0c030303051003050322050d0c0603020309 77
    0x584038954000c0c810790442040c030001c9080408261110705070a03610503c8188044e034031192104100604484181c0b040c205100c03a00c508082000b0035030360084d0907816140c1d0402101d00f1040d0040100300c1e01c603900811403d5103508080085078000d407030380e00d61980705100148480c1088020280c00440f0611124107003544c410a81d400d42d14260170444180005203000320f2556010004000c039a5000c2c1407002c0441c040241c000d40e28000c21045910030416060700c45500001c0e8114000903007251003050056603101e0401501030180000e04500107444c6130b01d034030910410000b94500040e48840c0e400c12448104082180e1a0409040c40c41541d903944050700042c0e0341d078400d054558202d40c0b24551240110100503204101d0a00e002101a5801082200003000080842c0950707070b0504001499464034a0026003400f40d540000701940310000781c1301e8000c02d10340b2141e90031144015190010644660500203803888400d0014140e049910003404000c4c0242c0295500010305011078007090f04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198195332 1250 198194082 198194119
    0x2d08040218010612060503030a0804060b01120905030301031b0b031906090c090e010603140a0207060e06090a0b1005030307060b0126090c0f0108040308060a09090b0f2a09 75
    0x800c1c3d10481c0418a45a04560f080d031990044800801046010f1814410340c224060311180e00107000500040d580c00d441ca415a006144a4a10702c0c40c0344000c015010841c0390184d03580d0b00a00040d80e00012848110040000090b489070a035440b600013141940c445c146c0c42c01945072941610301801d521050041007001d40392050805a006a41e21246201d2411007100c82021040c1c001d001054100341580c840103500d4016140c100c41e0408006a640100d410302000900f03598141d83c48500500b414040c204000003941c02419020720b450208035121040100e00600c4944203590b059041840004003298280e881551501018104a10285d8500c1400b0150700d8490483c0014209404244030032003c080114034100c22058402000842c0c48100181001c07000400007000c2202040004480d910f41440ea2070003403140d40c1c030a00c0720090700e00e4000c3c2d00460031a40200402180c000141020000796804030984a10700100b003000640d504049000c0d900c80440c44d0f40000798031160340140803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198196582 1250 198195332 198195379
    0x200301110c0606040e0d020c0d2105030910050631020316080108071208030703020f030406050402030f06010303050406050a1e081603050408090f030a06060906062d080402 75
    0x20500e0700a8405803070490104011a4482c01000b50300340c1c4500e501c0d52615800080d22003032110212000120002146002c80030011120f40c98100c4001110500040c00e42140c0038500071308100007950f0ac101c000d003000f1011100304551140d17010005d05d100041144101c02410b104408a0000d100715200b003400d41402d0380c1c000e4a050301c0010703119000b4086503911941380d501410113200909905440e08042c0510700544010107480c00b200000421386160182c2e0440300d04001c0256a03c0d00ca00e89070400e80000c0001b181e050b8080d01981c0504007403480007040f13030b606a0f689600c60904141c2041e0044071280c2108106034244402c0c0300e14110140564208403005900c00c0e95103000c1460058030564003120202d80c10020b06040c2410304c0001455001a01c1111605540c1c40c400c03200d05400182c40c0080e1000d0140072140b4090b400300d003005e450b0304000700b582c0345600d42c01e503a4103410019518a41003903201b0110041c0032820844554441c1022039003140c00180841403054160f440801040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198197832 1250 198196582 198196597
    0x4050304092a080a2d150f1202130219050c011401090c14130522050a09030905061c2f0c0c0105090907120e010603061d03040320030111 60
    0x50707861003001014240340c0030b4144103210b6510420440014110702014030b54000c000d005d07a9a8a03180340382d6a55031616000c1004041401c1000440d540e141036940aa500d840010307401480c4040480701010803600840b030007d054541c440d40c4142c0c80000403500340e04005104000d0f5500d880140300b90306040320b18540609940f1500041b101d103000300190038504101c071503118249007400041c28440703a086104048400131f541c01082d4035104006520302000407550400342c1803420060003003d440d59805100454800e40380c001400c0c2d196020040180101903007007605907007400f2019845000c0c0d401000d0052640a0314100c080b24440510b0415030281c5542c540d103030781c04941c0c20800a001c0186071b03448071080c20a1442d008890012075030420b0010030190602c00c1d68141048008810707481810765650b007000801800f1740701c0c545000541301d00f4000030070007440201c000c8e07004a4044119001c50358421703440b070507502c42d81d02c101034018400c45c039aa40c9550f031000c518052107207040042218 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198199082 1250 198197832 198197837
    0xe0309060a0206061003060e0c130506030a0c0f090b0904090c030506041209050f0117100902040803040810020313020907140721080106120902030a12020105040309090504050304092a 80
    0x1c0f0304d400740501c2462801071401108041c00c00c8030811914913154802074124850100f05030f602c0c480703509203180b00c21196109a4000b5000001c200510411346e02c201c947c0e6003030b0b54900040c201072043c01c9820500038005c3c0b01010700100304c8582c0c545000c0c0d00581880388103440e80c1e0039150392501c1d80d50415000321b500703a404281200a4948850f80101002e002c0c0104440030444002c142000030a00c800d039150031141501140081050300d01c0da03a803a5402000c1c0304205540c0c0369100c0d4403003030b103a4119200b03071a100e01c00d180f4400c107840d045000792441419400b03e511507844558080048803c40580740f00144550000c88140c0d200f08540200840c0b80100f0f02c04040c0408411401d00d0f00c94100c0003d010031503400c00500c10b040e841401c47d00311622004010900b0b409074000030f414031078400c40050005c03907025034000010f5010740286204a000e0740712a884030380d036007414500307440040320018680d410400080c40b812211764021200b547d01c0000c400501060305030b05403640c40350016000d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198200332 1250 198199082 198199093
    0x603070804050709050f07050703022b02011508030d020a0c1a06010e01020d0807080606040504090b0a0b010906020c01080703060902030a0603050c01181a0f040b0705120702010c02040e0309060a02 86
    0x140802080300f00700074500d24004000e81c1c6060100340d295014054194410084c000480b00103051080040d02c0740700000243e03019100e082400e07000c4020601185a102550a050100000498041c20071302164600c0010f0740c58a5403540311b1354001c1d8810702c00101802048404140814000100104039502010340d0940d2820140f00151100d2011900641103500602c115441d01e64010022504210f460400e140507495910002c1d410340500c0d00403130703085032814040380b051252010042e406902c0d620030400500c91034400448164030b46006035409a405440c3e130401c25441203100c60783c0301c5a82e140004860b03032503a070b0000581e48180e40c0380c0240c0d625064240107010082c03103c04914002400d02403401c1d402444580c20780d0070284540d01d000c80909510022008040b012601c8140000201c10b0b80c2e55101d20106030b090300302c41025100791003482c040c2c2a4210071b9204441a0356016181c81d44810200c5d820000640102a0340080754001849015182e0311140d0180404d002d054002e0300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198201438 1106 198200332 198200341
    0x1170907090e01060f060507170c0c150c01111312060902032d0102070b060402031306020301121104020403030f08090c090103030f170609070c030e06030708 69
    0x1121800c02c00310762203851065025000341d50b076140403e945503407942c0c1c044404e0701074103500404041c1001c0c40d081c2a00b205034007a28428000b14115103884c1d001001007001c040c505501b4008142000c83d005980c03200c280901496403040f90415428040501c0f22011813075040d00c910b02070180c1301c040600c24001d183c1c00c0348401d1600907048170040f1003244140300084284800b1440b030207541010740d2040b540306000302c0d0285034004c002840c4a4940c0c10400c4002d40c405000600c600d41980840e200003011400694000c040703040700d1b000020154103001d5490394180e4800c51250340304100510000ba003020048032884020300c0d0418440c3d51380d45a0625080859140c69441804800000205940000007802c03050181e41e481d02030039240c0c44d5041c0303103480540790311f41d100d90191b00080da01c0d40300b1141e00b1001070007403508602e68080100880d4490340182c5941000502060402 = true := by decide +kernel

theorem cover : BRFrame.Cov 198021582 198201438 := by
  have h0 := BRFrame.cov_init 198021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198021582 ≤ n) (h2 : n < 198201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
