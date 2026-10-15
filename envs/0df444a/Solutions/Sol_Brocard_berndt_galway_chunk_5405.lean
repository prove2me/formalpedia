-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:45:50.123624+00:00
-- url     : https://prove2.me/submissions/85769963-f1d0-4497-bff3-325baafad1e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971942446 ≤ n < 972122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971943696 1250 971942446 971942507
    0x108100b0c030a09060c0c0519170f060f040302150a021c1505040e1c0e1e01080c121f0504020406051c06030206030411040f05040503030a0f1b 63
    0x64011501c10045a8004038070410b150303600c084000c0050101d070914400e254250303101c08141528a0084600440d2a8980e04c02d00308981c1d0b0361040248190303038094a9008042c0c035890303200c00690114200c1c038407440e00410140d156204416025507410340051600f1003082200c0401ca160090501d012150300740068503060024599443c0c12000c06031000808228030361b4003402d0042150492070099140c1810070b1b00407a1300203a55019410000c54100f110803039030340c0440703800801040c000c0c1c000c070344403083d5540b9244c0c0006185d040b07030090300c0d1000d480e071701c510100c85940aa00400c8074071001c0000402d1030300804059486070001c0d0380e1041500592244049400c1e6072056218400041d40081c205000704034154001805440d00c000030301100e0320750b80008880d408064406010341e1034544003d00300b070366142e0140411200081c0300b4403076490641001074a9070422600e0701c445508003501c0c1c02c690391071845032600340c007809519000800b54a4104640408403d0100148807a0540303101740d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971944946 1250 971943696 971943719
    0x3080a1508060a0c0221031f0b0a080a050705040e06010e030d18050a0501020c1302090409030903050609011b0c02130f2c03070816060905010e0f0c030606010810 71
    0xc0d01c681c5004081c01d0514800110480b4610952002190040703022001152448510400742c0000104102d441b82c884034038180c89441d0001c000503a80d5200701d40041c15080c80310113082d800c10301da1982100740e607802c00c4c6001035400844a50740000c1c020072080c0b049818124a10f034000c141071401c2845645e440001c240350503640c489031008100d1804100c1d0300315200261b410060801600d04542103840c1c000040e41d20926000e03042c1c0f02d081d00440c400b05624480d81503a501c203000a100344118440d07400c026081d660301d4001030356107002d03140001d214030105005658a04c017103840d43d1991403241c85402c1300e042d100040101d0707000e081a250300301c0101d814040c90540204648000500b02c8145c15820b400e01d90582da040440380940204401d540c0000c0f007503900541c0c0080744280ea90140b4150034001c4048980b00408070f6181c007506c00140001544140c81c0c1841c418202c681200d51241e0355070303454165140d00d03a0b03d58042c0001801c1540b0901e00540c000a20f60039203c2019241c2c000c5d60003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971946196 1250 971944946 971944949
    0x140406050a0b01110607081812120f041709040e030408060609060a08030418060509071206080313141f0c0b1b03130318031b0509011203080a15 63
    0x14410345450920106020301d01c10354001603401d007010740d110b01e11020041e031503400082200052144090006204100c001d0018000030b03045015150051a010b02100c4a600903070071182034100c0d10380006108034034a000890045800020811400d40d07102d400300d8107031744400659074210352503000d6184942d408001a0000c1e25514001d00070520b044410b00c442020000c0036284205030031072040107a6000407080724180e55003001c114003040c2070f680c5040007a0000f0f6001d01e07040001003041000c2c503648002c41c0600540c465009100d0141d4940a2554074000c1860a0301003280c0c80008020914020511054001c4090000c0c4443c0025440028041004459410115001d2080c200c00c102d83d280c681ca9011809407480d102c146004008821140002040021480b0b5040c00c24000e05020302c20540d490080c40c40082c818948901c1c2400000140203006c401c081e911110109403840c00c3c15140341a41c001c0e5072443c0c52442ea9440c00c649090015001942d1182c0e01d40324292480c128440c0b110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971947446 1250 971946196 971946203
    0x7051204151d06060102010c1b1b0306021b0f0d20030316020c0d030c0b060a08010c090911070209061314042907020d0f03060801020c151b03010e07031404 68
    0x1402d8840903403218104203006240f01c0c11645005101081c5036000803004c14015191030184041d88030358581000e425241181f1031184584040740001001182e400910a601d070b00c62103440c1100200d1845a943c0541001000d0b5070341108120b210201d1040e005d4082c01e06445952614804007140306a0840cad0040c0da244401402010801400d280c0412450303140103000c1c1c0b9865514042c40c2c400501a00714040000d001d00386190200f607180ea1200b072840c0c041e10400e0f0082240c1d104043d0701030140842c82c407a07000881d003086c50b0901d89100c158191484a070300038081d401540e9900c003c001c843e00d2501800440c1d90790703420b4ad50341340800c4400d215200310b100f003640f406140301a0100103004c250501e031a000d40c80d54207040200741580032564595206d00d43c105176540302001a4142c015040b150041a5a50303c0492510704510340000c501002c4500302d540281c40d615044402a4468550404040820700400041003085180c199103940140320f40750006001c03a191407444030506040c1c8080d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971948696 1250 971947446 971947481
    0xa022b0c03060902180c07080306010e030706200a0503091005040b040f091a0a1806050301051314030c121c0906090c08010606080c0a020109020616051002030705120415 74
    0x40f070031130910000a40700303101c2c0d891042d6224502100c580c1d10900c2041c000400ba0040400030404030b034010345c1c6603100c4d00d0004050360314446d21000010034090f02c3d1200d03801c0c440c0001040308190680460440051368008014514210307840b41406112990b01e5080e1080000070080040d02c560450080c00142c000642250300061030031802e1011707201c0703403c1d00d100895964440000700c2d9480003a0034088406c00f5584044403150a007110004007426444980c065007407404010410310000e071803030710030381c8294460340d07649100b44045540c034024020400b030310303034031480801c40c55a5501000c1c01d8100712005402410342d01c400b08100644007000812200682c03075128a804020365688031101800c90f0000070040c3c5490802d00410801700541040641c000000717100705403a01c00e40201c18031035000b40c00d0b681d03103008804140307624a0026030305641c00c0c0500e02014900303005a000700c0f0300030502c40d030300d41d41456181d4070f21009020001e042260403000540000044601c140503100407226110f000c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971949946 1250 971948696 971948711
    0x1707030f06140a060e04020f06040b0c03090316060207060c0f0c060c12030e0a021507060207050a1505070f11150703090b060d08040315020423120a022b0c0306 70
    0x1120b0754500040d00f00700c02d45003005410f0003108a002600b0f90701c207404540101450945001160709446143c01c03902941c00e0000da0800040c10000090541c84001d400b1100080200301407a030841e0101d004010050304980400c205052040e00c1840c050b1b030140d2051103075161ba07a6150844409940d1001d00403c40d01d07503185060140100030002000050b05040c071a0000c005242502c5280d441c100a01c02c030b0a400c9100701581c40902540d40c45540b1503400c42da2803a490030000c1c1d4851000c0341c100d43c114800e0305c0781b40d50350b59035018582c0961480c2d01c407822040c50b2200c06441d40201c90300c140030103200e0390b007201c003805c1e840a001c14020744a039240002c43c5000c905000b05180c4004010341d005021905540c00050303c040110f03402c03603400030541642211500c0340200a40b103182e210303001c40360a600551482c4417106602168450041790b1b0300080d0342521106a4440f0781d42c05010758004404080c406488400b10102c04202c003440414150020302590b0345607014400d0780086e540990f65620 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971951196 1250 971949946 971949971
    0x10e03040303091e0f0b07080d050c0322030c06020c0307061a031006080d2d08101413020d09020315090111040b09010c0809040f0519090c1707030f06 66
    0x180e0003004c41c425818621903070401d400000c0306100c030310030704140000000350002404011001e88249100540f4144894107205201140941041c0c0d1a40c031211062000e03d01e26406a1001000003507040c5c9502400400e140c8494009401010941c1081e0100708101000281a84103d25000100b00c4c1c0400c50011a03400340352034000102c40112030342c0d00e0003605120f0701000144100650035a450030fa10006215900e2188080700c2c2e61880f03040607444e100005c0c203680c011144a118030a110044140150390321203000401407181103a540210021200c0c440c01002c41d0010558034030440408112004540c1c0030902c0c044202c02c01ca050ba808603c14001100d400380200f8131890400e0725064103150400b503011242d4450b07000b009040c0601d04044208200181080c2c0d008002c000b40200400d908807000305024010032070b455290001d00c05100400c00c1414450190040c0c0c200d00005005030a1004546440101c81d01c82c01d024400c14000200080010310350004441c854200450024800d41b13 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971952446 1250 971951196 971951219
    0x50907032c07030b07050403080c1b1f120e031b0618030409020c070906060e04060501021f091a070c03020601050108040b0a0b0118151d0f12010e0304030309 69
    0x41d150840c1e2400a41400054800191042c01c1e81d41005107102da070b40b41c031001600c2d9445254002451218003054150440202258020b0038850522090400b05124020172403a8206c05481520007030800c0240e000052203803c0340018180404400139204018502241ca150410400408107131aa8160515490f80511000c3d402c030300d40041010b03144403d05030f4240c40380182d0083c5010b4550104160000c078404025200041400c20410000d06486183c01000c40e0710038044180594200b42d000078440d440061316801400c068001e1b0704000604106800c050300e98003800b0781d0852600f20403807040c84401c25075240100e940e80c07511001c0100d02e14001c0d04160050780264141712504042001061107403802d19440100c0d002c0026411100400580d80446071104911440724810700100d1410101200c4030190003041e200c0345200c81e5482d004260050f440a0103d0300f00e04444400c0720703035007014142111590a883c1c00402d5100440e111686590000c2c0d01c10b4000444201080101d5900c0d00e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971953696 1250 971952446 971952491
    0x50a091b05030406200a02060f0f13080d060906051005070203060606030717040320070503030d0903050d1e0507030b030604200613142e0905090703 65
    0x10409006915424141804810815a03280240800040040d0411001d0b5210032201d207401d6100031041d502d462684025904564021005842010049001e00c00f910112601c20444c1c10742034191a41d880e1580040044488000c8407926000c3c088d880485840740200c102070320080f400003840901c1c02081001038003c0808200620a0800801d40980c4000c94581c4d40118140c514541d030381c9401d4411204003188541030944a014070301408101070340500d4210118a101005002008600280c3c03901ca00240c4203041d4183c0c42000000d01d400c0503500001c14030703806030408908080503d030710070099403011196514003c0e91020fa184980c5035503c00e00c2c0e04444031303140801c2000500404a503841e20050005014801c101c50040040800e00c40280f80069000e044951901955140525074200601440144501c9969611510700781001419900181003d0840940810305060b03080121202c41210802150440210340c545500c41c440313018040980d40001e0304010410032083d0034060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971954946 1250 971953696 971953709
    0x30c0a14030c03040b060f031005090f010c090312090807150305070305071d04022109120c072706140906012124030b09061003030f0c0c1707050a 64
    0x601c1803000c180c0e02903054a922a502c500070318200c0d200d03400020525107120001d0799040c4160041c690510a003500b042d4010034400d01101e090181c2681014261105101c801000a4032250100007091000181d601030a80d030b420181c200548038001e4504140150300b19104103000545000300b035030b40c140310f8513600c500750b0300d8108058200200000d040070745d050302000000302034440007031035a40c1d03d41c11074010040c0e407000b46134050003d45512400007021204030390640204501d0042c404504001c03585500081d401400c00342d8200001030303e51425a0048885288184084a102105510800d000350228069040054240f041000200c0e0070040c1000d04104005041d0741c0c18081220b00c40842240b60f03203020800203407050704072490402c1038842c2c5c40030040b04c010000074800a8401c003400340b0080d006a03481941c3c0c910101030501d20900c00103002800c0c1000703000c60b280c8074491801046101300b070400091503440d49000b002d056440b0800c41d80e6000a0340802040c94240c002800a049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971956196 1250 971954946 971954987
    0x100918020a05040303030f0e031b0c030a11091005060301060908100b010f05072415060305060609040c0c121d0d080702040510120303020301091d1b060c0102030c0a 72
    0x424200003015401213101c01001d042c0c0b00e10302c2007a5030201d50006000e111311401100d849011280507842444503480711042203018000624025060104480e265140c200480070030000c50740e0306114050100411074040500341e4900414160f50b114001c1d0b00804c040d03554911080e0402840300d041004c0e6814000c10303146000a030151030303600302d004c88011303585034144580c8a2000c0d00b001c80c0300801a10306404d9170b21142651040303a400650005014182440300d107542c1719242d00c001d4003154403c1c1c80d41d40e03124005100500306440c00c1e8000740d40d0b1075032510705030310546410f40d21002c544108004107404292600c8840c038544041d10800c10744008c080303410a54007146a11344403114490f00c0c0c0082c1c029511440000c140004141c0c4400080030a40c04125414006040080c000c0d0001c0c00b5090696042505040d03001c2000502400e003802000050201c0200301e41c448440c40300c070b4681840d007159080c006986004028800303184034517008545a0340c0c418110900926081784240d0007071a407030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971957446 1250 971956196 971956207
    0x3140a090c05090910060f0611030a09030b07090305031911031303110409080c030304120822052401140607030f1209060608010b0f0a0b1c02040510091802 68
    0x3520391464000321103060b1001c10054075010111402d180b810301490305c01904010300042d0b0801c0d07400d5140704640c5241d0701c1203029840d0003015900da1189000d400006880d529061001ca503545800300c2d001080f80c1041950741e40d0365545c4a007035400c562119082c030403001000d9144a0b4100503000261912140610300e4404d4101c40080b450842c0e000c0640903000b1442142c070b03c0e4545502400205070400307040342e00e810051880556070381c411102210b2094143c149401914000c48a4071f015241100b07420451910904801866001d0800c0a862900c0380c0d042032001d200000a040d6440c01d021480300c2c10710340c100440711250221220b80b56004034010001840803a600911358200e214640c54102c016201aa00c0725002c4d2620b11400f501c1c0300d240c5000060140c50562065440c2c45040d15440c018081c140104000300c401442100301e5003404020201c11140500c0510040610050005007000d89030000b10344010095034031400030a078141c4003800410300807410700701c180300304140135440c19 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971958696 1250 971957446 971957453
    0x406110a020a031d0315090c0405060a180908160203070e160804150525030c05090d02130608010519020414060c0a06050c041707080a080306190603140a09 68
    0x201c24042e0301504104039600c0c00792110406030031840d0741c1e50000b02181d120140350109041000c00c155084001c80c031800d21200010b05041c010139209101c01440da2680302e140080c410f036010f9821100c1c15500b0b680c2c0450720000355001000e0700c0c059100548040d007000091042c9440c0c405150418880452080c080120002000c02100134007451445d2884040e1150300d002c1c11188008014401503500f0300081108141c0c03040b0040542018886030700710101d0f240407040c0c0440e400c0301e00d194002802045070f1603c074204203406c8005144098200321603000190001c0c0b086451641026025035116010301c4510700d001c8104000988000c0011480d16140010856075154102405402084046110050940c0c00c0c0120864150000344c184098501200740c030115501ca40900d4169021403c5000c0c4441ca0019a00003912040001032490072200e4442000e80c5c0c200501e029802070f0300c0c0300c848001961600d03d100041000d5180800c0304070149201c40c0005400034861000645846414000b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971959946 1250 971958696 971958703
    0x106090605010c150c05191206272f070308010b0f0a081e040309030506090115090504110d1101080606030603100b031c170c030702030d020c0c0d0602030406110a02 72
    0x71002d01900025114a80750002d8074580071f180c1e0242c41c17280c1a0070504030090703040b10080a829006180401500f034407400000e15200c40010094800701e45140e141d4200107260344950402c0c440108a05c11800801c102c40026643d2841050141880411810100754000c08003d0250180440303541c1000d044030052200d9015001d00e40041041a0000c281c0c400e90002c80340131a0302e140031004090b8034060501078110002c500c000ca8040c07140038001400520180b25011841031143d2058500b0b038500b1081101600029205482c07800c4042d0300322074540d071071207031646043c0e01c640e07102c04038030521381c00240907000c00916690190030108104190f07541e01280442654011071000607412001d400884c1c034001c1060101c0800e007200c1092448002e422020800e84410341c050b610300030b962409101c2120380425100100582e00034006600842d004c1c1e0007500b400c1c2c50300700840b51040c103d17100140e1030742c0c0446c07001d4402d1580001400b081c401030b405000301715003091000e2407900030010300017541c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971961196 1250 971959946 971959973
    0xe030f041d010b07060c0504051c0b0a0203060a0306051008031c0606020109020607240204170c0315010b07140d110f06010f091a030f0d1b08030c030702031b0106090605010c 76
    0x140c5d0ba48400e40444640140140c60161401500286001c2140034061800c0b60344c4940503228005034400290303a5050a008481c4190b00c09810401590b1079562568080d0001404003021502c0e8a00040f8940a003080078015121429101031600a81c012030941103a609400c29401c590522207100d0160319010304803507a5039400912221206080c500d810100910310410307076002800000d00059800020318aa40e41600020940e50841c017001d007010b0f955901c84560300c0f101c034110300040002001c01400303450800e0140840014044011b280d143c1003800054103600131811030520394801c2c0008022021000d5400c2c801400030354146805040240803601c0b501004684903c0d02d081a03e90b07292103a804458090225070b59411900c0b582502d83c90012500c00014081c03805030710011380c00a401c004425004481240381d600c40f540b020032181d200822042c198482000140e035504000c102c5800b030360380d624000141550804d6441310955840d54000c504100781000e044001c43c942d9041d250 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971962446 1250 971961196 971961203
    0x7090e09160b09120a050d03060e15010e13061d1311060901091a0918040309090b0607050d0c0b090705031b040b0d0f020a0501300e030f041d010b07 65
    0x5803100351110001309241e203145030701081c501072501a1000c01c007000407291801c01c40f41d1001e009250f200c031640790107018121061640e09070304ea0f00c5505954090f0020150300440a80b00400e04404a518582a941180c1c0040c0c41e1010107071400031100706002915411031600e40280e10320304865210940081d02811200e03100302800100075a8a1b80202902002003241845c0384020701c2d0214027100c4641c008149550180e18016064030541c07003000c0030244120f40c10784803014514240000e00d0020450003001d503800074420071071000802e00c100004007a9031159520041d05642e140782031706e881500546035660070303401b14500f40566500071400c049100c140784800461144040c000a000d4582c141480d40c0083e40c9502940134402d40c468540d5031540203a944826040c0c0c2d4000444030903903649508a86090155a14030b081181c4038484c01d01c1d00f107101c001082ca800c10104d03141c11603010024111980714002410001010455a031500250311a01e03100b00b190300d8850440704a100700d94008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971963696 1250 971962446 971962469
    0x509010308091305090d181e090c090e041b03080c030d0b0303030126030d110307110a0f02010804050a05010501060530130c0e011206050609060121020c0607090e0916 73
    0x5400600860b540c1d00040c10030b4a0000f00b03041e10380f0723000080d40100340241e02e100c40c02c01000000d0035026240c05c01c1110303a1080c16a019696580b94020104000d100c040068054500000007181040780600710355841100a550780b4140c2110f1407080b03d801e2110540250418401045480620500e0040303224404980c03103104000b06004904520a0a403958a414540310701f95030503031000750155201d02c00940b105c103a20344800105550b62850104020a807161040e840f00040d40f041d040c0e950014440c3d01143c0440025a40d080e09440b001d80140340002c00c00f1501207078070301190020f4900001807419102c030380c4403140c00d1072840402c001d04a074003000c034802c0c90713408002d10003212200400340a91f031030f180d6584410140f01207001c2000b0030b0782d02c2410440852118030f410b00c255409001c0c140c4601ca41161160380000440c402c1c60114480b0075070920480c1d814400900c4958402c1c03000e9503071002d03840d04000c0680e5000c03c0103807100100740d004403284c0100c046036103802010b07580c50328680d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971964946 1250 971963696 971963717
    0x20124060e010c2a0801110a0e13050406051e090d111504030207091103092509050f1b0f0f1605030c0109380408040509010308091305090d 61
    0x6071501503110300020030903151208808403410113141c0811002c4a2002a081c01035916590746007039030488441800070101c10411020990b000d00e030f100c0c024400203400c00c01115030100550003120300441d406d9075000d0300c41d01000701c4140b045c3c80c80101148000070070304141c104419400d40e2443c51452010a000c0301d00003c89001e2020445840c0041c018030a130601864a45030083d2240418440c00b080c181c2880d000540303501d81e07142528400c030a444010700700001e16441181e84000c1e650b00140320f070290904041101003003405164403618480c0640c0340b107070811050514034282da4038030042c0885004d000b51a94101c0c6101203801212003101c105072640b042d186140030301c40c10610010941c0c0302c000303100c3e0207122040d04040445070040203101d202444850206c8100400003c9518442c1081f050203401e1400c80241c0980003070152402a040c65141e2021070340c1c0600c2a0030035184014085500e01705850f10b030046210710407aa050612041c107021074039503581d5010f84601c800b80441141d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971966196 1250 971964946 971964949
    0x314030a0e030d0608060c04080d0c3e0604030213020f090405040f11091b0d1803020f0c0414220203010c0507020405090a0203030418060312050901020124060e 70
    0x4481c070340048010789a9800b2051220300c0100814820608140100c170300240c07071206900169411211450301420050a100d001143c102c1414142200c2c003080c41d64008d440041d09000c2260008000c0c464042d420450b40740d0000c800e0715007490248500020041440140c8a2501a44003040030000c050f80b6000c01c8900c070149401180860b9030000d00c5c0a0070003051240300f500070400e1a0151000148810740e240c144aa00c1e10100c42c01ca015845e1000e0300c0c840c1c12a0b010080946030380120380010522181d00400c41100c00060f03040e401031b84004030304520801c041c4048847100a017154200882c400200d49a18072900c01008208a100c0003001528101501d01840e580a94000c00030085100c801002900d150441c0001703a001d2840d01c400a441004009070381c440054004004505103860949080090408500c01412158071054008005807401c1e080040708412915201c1d182d46160000a085544803428000c4401c03c03a00110300c0400f40b80c1307100b001d440817464680300c90b5a0090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971967446 1250 971966196 971966201
    0x181b0a090204060e2403040c031e030516050307211d0d030f020f060a23061305180f0105010311031609150b07051606020d020d03090c0302090414010c0c0314030a 71
    0x81741c07254501c0001000200b249102001d8142d81c80341614174000100c40c0600f06034801c00350b20040114808020442907045548202000c140c0300b80122888d200503540c03040384170600c40700f000c05030401c40388070001d00641010088041040e002506280e640702d80001a015180b01c0e90b002e000e018a00f01401c000324402c2c42518862007034542291050306244000038020400b82074100e90b00d5a40c0304510000880081000340140740c000d040105a240c0802304c8070003440b02800040d036644034601104e031780100a01483c900f2003040b9000144561450510042c02d40401c1096031184d0001034041703400c1009840301c20140e5141c0000022001e00c00500030758141007541045c075041401242c86820001c00254a6030541d01c2030034049101940c5032070a0f03076135400d07c0341c0c07030300140c1c202040b0015010306c02d50000001074061043c10350060f6582c0c0100b1902c003800d40e001e0700d031007100c00d030324828401e82402035113407490842ca0b081a02003030a440c0202401080f0b2240c0c5a10030001021451502d00ea4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971968696 1250 971967446 971967499
    0x912240c0f0310050f150306190e04050a0506061c060e100f0e0c060901140c150c1e041a0c0a120f2601030209181b0a090204060e 57
    0x4035080e940b814030b124001200503da00c9a00c1c46108483c10b00040350400b8468201c04581210f5001e00355140d00b0204a1280c442c0c0a01c0d6082240394107001030740f0304445045d1400b50b40101c024000680c0f050400b14288100109050700503003002003100301d402001b418219100e90402d00020b0920250580103082400f1036a034124114184100c1e600150001d500021500807444110340c05030341790700d084c000c00c1d00900305030a0115101c0501e406411000170000c3c0080000c03102601c18801000c030b8003014140054500c00084203000c5540500c10168403035051222601e0621182828074101180ea00044401e070107044070f0201003070f04d4a215400f04800d020450b402a4400319041d4a040c0041200d8107182d00c080015503130352000140d00110704180401070480341a1030303207507a0940c1c0034811f820340b000e400721110300020b030402d8039500d000340b0840c100d0203100d40c4102d035a20700410402201400781d4126124603441040200030254021200020b010b005640b05090b900c00e905420039041c2c1ca0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971969946 1250 971968696 971968717
    0x70b031609050916030f0513170405030a08030103110409080f0903120304030201020a02060c043c140f09060d0618050319031d0d20070b0912240c 64
    0x181e00138808012541c00c040e41c840040c44d60300b005500b4100910005030340098804100181c5507071000d03008148022460310000503403071091483c155560003c68a444c1018905407004030000c0010b00800c40190f2200a05140484003481340178095160900188115140100880c2002a0704441038409005a400e00e591203100d451b1a89801d08019010b5407010042d0401402541d0010b8404d0a2880586081e9044000c0082c80121040310f901c2120015102640408219010340c0302640380c600300400181491207018240d003980d910a0080c5440e9040c0013a114084003010040c0702d44500040c80100c54001c540400d4420302d5458900c07802e001c80b20090480c0c00300142d0b80f4007010b460354121076489e205980802048400c0c4007074120703200c11041e403000c039604119024075032544640042044008107002d8003000c40388200d400352500741c00d0b9106030207411010481c9082d6260100d25254400c02d401c003d090a40440c548a054080c100008007800301c003c407010591042241d03050f0b8284004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971971196 1250 971969946 971969959
    0x1a01120b0d020a090c03150311010f030e01021603180b0f03040809130b010915021f0213060c0b060409050a0f0807080a030b0901060302040b09120a050a1a0603070b03160905 76
    0x460380f40d0080980051510385c40803d0400942e45000a031030b544e100122a0450300c0495030070400c000448514484035007180030192a403800c500401020720040c4414000a4503400481d009850080e100e002d80380704900d000b0b54000700400007402c000e4201c5405c80002c0900c180d0320ba0701c0f071800b80e03600d00441001e07c1d0403042c00713030506401c0784165001645254098880000980e0b90f14640c403000440c2140e568010b810150300f200344400505c686c007140015840c070240c204030075607102c046020405d43c05031000901c49083c0301d06100c1c00e01e51141e00800184c4041c4010002c58846950b40c3c41e4100000300742c104c450510000f840300c0300003550705c80e5a0280e9a80e030355411000c001405802000c2e680d51169440000014a00d80603108640865032505002d034203000c0f008041107903d55800c500380310140035017102c6d0030001d1014002c01d000e03d48502410015000c10984003c1c064100400c3c003806980441b50a111940d201c806883d406629030340950384c6281202d0301103801f0407459110681084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971972446 1250 971971196 971971199
    0x50912220e04080d050c04120b0604060506131e03050319020a0b31110d080708040933090b01110d030608161d100312050d1a01120b0d020a 61
    0x2000c0401080e922010060502c031716203510b03400d4070b03840c4075501c51400c44011040400001504d55244981d000c00000c00006065030342d040403418990110748408518817203048107012072608481e0300c101c03418070414820003441c110b03a180c1e580c900c40c1180c40c070001c0e143c044040441a10811018644c2603103c5044070300350400c0c00b116014031049505030b100c0c1e2000660450309803050740703044440b100d402440b0400da401c81c4205001c00d0a42d059001d9a03c214100082e4010440120041004013041840020040314000c201d00343da00c0c581c000c0f400f101d00081072494505480c0d110103030543c3e4005900040242d05400183d505601e480c0080105006910580060a405600080489081e082580c00b00e24401d050f0480d0b0341e14602894a92000c5003260034a210700030002154021310040628220b2034594441042006484041c14006000020f070383c0303402c8205014840454014441500e482d518040c0003906440c3c02622003100d042c0d80f01c50203c486c1d41c4190400b82c526401800304032402c3e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971973696 1250 971972446 971972453
    0x6200d02010219030b130e0f0a1103070803030702030307031806180b0705130b030406180b0403140301080c13020f040b072913080d0e0d0201050912220e04 68
    0xd402031101c0b0f102c0c540030000c07000c80c0c2500034040d9000c1c2c1100288019804040082480002c02550004101da0711440d0606a4148410001002d0381c0d0702030607405000400030002c0500c3c02c40c2d2604a807076140c0003801480940c039000030603282c101c5180c1c01d0104980007060348001d654001014064030403802c00c010720242086240400c100c860007058104016596000b0035151403080c011f800964003d8030b4010440030b1040000741d03800038131404002c90000c200e42400c1181c050f40c50400c1e01c50044044c00e000806810400d810903443c101c2d00114111740c5052400d81d104e8105039051405010b4074081c4080002950f41120102c1c00041106525540c0f07038800381c102504050381c112000b4480783e00c008400e0382d4160103243c500e00d080b070070541640d80c0d035244200c191036424800c1f90b0b1804107001040d2841414022600028a030200410400c1c4119000034291030000d048420349170402c8450a001c458010115000c000c0c04201c0101c0d1070550366800104c00c0b034a64400a0604801c0c0c0601081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971974946 1250 971973696 971973701
    0x414010b07120306081b0f040207050d1d010f030e1c1706030a02150a0e030303040b220b28060f030c17032b05041b0e060a06200d0201 59
    0x900707005480c81102a1100c003401e4041314083e016203082075100142d08507034032980c0c140350314102c840546000003100407200031800340d800912044610b600300c01250629164025a42080030000c45c85101c5d01510600018040707001d0b0b00050782c10961581c3c400c3e81d04030020060100c01c8520101c80c40c20424280f04003d0a5200b81404c141d10080306401190aa1034002501901550020030b46441d100c01a01207088a51103d0803543c14411034018005141d80c05001852050340030300c044110a252201d4007441070f007088001d03c030f0400d07206000b91003c50b0040a50300e500c204019154a1181d119400200200c5120821803100504280001c40c03040305580b046000c0324030a13101520415200d01304010444000200010b13607900610000d051075000b01c03500d1014a06030401010031402c005041426194111030569000503041c162501f0781500303034070000040014a041d400b050074902c00140c0c0140c1c452243c0000c020050040f24083c1d40940c84242d0001998012101480c0095001070b02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971976196 1250 971974946 971974957
    0xa06050702010e0a0c09021c06092c0607053601091a030606091c1a18060a02090109121103010507091415040803040605250515060414010b 61
    0x154285880301280e6040000c0c5050400e5012601074002401c10003040025000080030140c9088454070348c9915140724419040070700191040422003421501c2010001c6000d4034458042d90b04424034410000c80116585070004c0480c50020f586110f0300107031820340c3d1008407081e40c44211030706004111181c9007240703000c007000c2a207078102c0d020350702c51069920b01c190b1111440c06080810004801d03280120003000351010040c030740444800350915502d9002c0362040c0840c0c0300c20000d0305c0740c054001052190381d0702400c410184110b442a103000a911040003410782c019280d0085001c581aa0081c4082d1010f0b0510702e00b002c07038890407418004a08000100100d00030351802021030304041c40f55108001b070340c0032100d0414041c0120002e0049a0714850b42c281d030903100c2400045a20075080c00200300502e4030f50344240d1692680500342c1c00110340f01021480f8824405c1d1072900140e00071402e5202c0a0b0f454154403501c2e5900008035010b010014419003079546480008145020300b00080d11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971977446 1250 971976196 971976211
    0x609060c0109060b09130b07021f0c081614030406180c140d0c030308060a0b04090b0a140117190609020c0c01020f0c270a0207021e0a030b090309030a0605 68
    0x104c28800f091000b60203003034514118001c4103940c42030100c2c4400240303541080652048481c00d4120390301d00075511000506000d143c5071a44e450041169006506580222480076940c10211040101400c0d2200c0b04030701c1550101e0120011b000d000e1580c1c07100648541c40d0b07806240c0c2c24002d2400c3c1503211b0300d038014046142007070940001c507410f2101c003605078140d01c00038084100d030550310f040e649421700501166000414140110313407070807518080d00c003c2038000c1000c10348060440c1040060085500036410410f41654103803885daa0201c1c1207140b42c414a0700d0300f0303000d03244c03050024907010350900030803c424100580002c00d110181c3c003d08100b5441030580700b468800700c004a842e20f685400c0c60010754480a6088082e1030491455100145404071040d4846454501c1c0c04010b08215014101c00b540400c00c2429400e020f1414104501c0703150120191f0010000020088401c1d4000078085161a4002882da45801c01c100c41642e000141107035040451031820001400b4100c40c4003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971978696 1250 971977446 971977451
    0x21003060f0e1012051009030224090331030b0402130507020d12140f0105090108070b1e0706051915050616030e0925140909060609060c010906 63
    0x14440035800082e500482400307034405002850002e0380f81c0740703031450902a80c0e54002d005a00311000d040380b05002141e403003500a0600d0341c1c52180d292041c0c007081c20a02e010303001500108040b80e0740201c2204c007883c40c01404040e141d92070007056030000c0c0074807150350f0700e034121004007205202c040100da0348910b02c216a40007560b40f541048505807501030b502400542d004a8500c0e18803806660403443d00350b00ca41c0c2c00501c90f220f440031031030000030584e1040d044040c3c0d4001031005090110140380500a480d00405070545400901d01e101d105038800d4100e1203244184ea01042e4811304110b5907003640001007840340c0e04045c1320310b000c0009640f50209000b40390544000000078455203a400b1a84000e1246081151060700f0040312010100708a0410410180540203035a82c001038030b004070590058940003084982c000030f04032803d44a1030041c08418001d0101c1010198201ca0038000d00391101d11454441d200802e03003500841034102d6001c4004252031064072015800404242d010300400e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971979946 1250 971978696 971978699
    0xf030309010f0b18042301021b0f0105011211012c21190510050405030a02070801090206071b09020d0b130b09060d0312020307030204031a0c03160507021003060f 71
    0x104140740500d00040c503400c40b1364800040c081740c2c400d0f002e40710400c600c2110420050316180c40600f2170344411405030701034400a55440044200708890444803100320000c000e2541010300c1a86a40c41e036000c01480704c20a542c3c3c0d0341103a4403481c11201414446044401c5003d4000802c01d4103417203c1040e10300606410815030001003003207820500c034581ca40082c0070080d641d4041620308903100e083c242d032244120600a0814001c610070584524020030144d5101d4060a100905000c3c075607210002a0781850764000259941034104ca420a6010343c01c2d491450302720001c4295800e640d40015111403020401e08500d55443c0c0121844900c1110850403070000c4e21406012034068001c0940c0115819000070300c103040100040c50314601130b0404c058031400070b14000381030341d10403141c1500007500405c040041003464600304403c2e12501402a41034542010308448074000240440711482500e469070034054002c00441d150aa00039040f005448c03403000001d0f000d030050f8411241103500c082c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971981196 1250 971979946 971979949
    0x3150412030c050a030c02030f0c0c0910260a060e0705010201230a02280e0a0902120402010e010c0506040615050105041202040209040f090c060206060d020904140f030309010f0b 78
    0x2e22004001180c030b0705030512440000c00c4004200702e5a0300001e51000300103040800380410040c044481e02c0400604400550400744a0750f00c0e0042c1c180069450804070a205442001c07101581c0000e601040b146403110307440181d40740101c8418080d014a117092044156481c0104881081d103000b0380081c485c80300310403004c915641c07001740404441401d010100725894490380081031400003540c0c18117410b000c1034245401c40034680e6901000320341040c10900303050404030007400003007010840441c100b402c40080c0000400000788020304012403001880000c0e070007040c1030720b0707a59000b100b1a019441c091820078010007002e01c802c0f8407600031510000e00c0350311a6046400b61802058480e81807001c42d42400087c2d002480c1075a031060302c90090310b20001061165505843c000c0b201d03101d03110328103440a800c01c00003404181c0249000d0500b400540c4480700100c4e0481e520002807018100303500084d600301948080c034007465000c004144148248150003510400e0b85011080025242c03160 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971982446 1250 971981196 971981201
    0x90618050c09130b0a20040303021905210c07050d08220e0a0207031103031b0c01020f031807060905091f090618050a05040c050d0302010207020315041203 68
    0x60003005070780001085042410041052038010041c2d00c2c103014641c0305665202060b82040300d0132003407565100040980b6034081e0100340445044030b2021413400b03045890003511020101010403110300e620b004107080290801000b0081d100350150300c2141280d40482c00d6130380c0d211500000e907030f1140100110741c0e40f5141d000440d800354407000c000e24020350004c41d14915445400328072035000341001d00040003401001810700c01c1908850042c1d80302c8140c640680000c002c07002e0b0248030350041c01005091080210301201c0c8442900070b843d1228010650b01d03002e441040c21038031a030680402444040100b4202c4040004820015100c990fa203612085401601500c6826440030062001c1450105483d503124003008005104082c0503840300640400e0b222150b00c08031700306241d289400000342043c402c02e60001c813074181c00d12540c00c0035180c65a900d221405034910600b0300001c0700080600035811203411079030242c15a440100c803844d104182440c00c4600307588204415000302c540314482d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971983696 1250 971982446 971982491
    0x906110a020c01080415050f091005071d04020409020a050909070804030203090603061c03020d02010c03090c0306230f16020a0506160504170102040824060409060f0509010906 77
    0x20740c014400030540c200111510034020300150381d010001c48002d50038000c907000b003601c103100c0f5491192031414801081c44c81d01f00c2e91426103d8072460b04040c001426841400c11120307041070f07c601d0b503802c075915001800334820380d0301008002e8030003d9580c0307140e07401101801030200110703081c01c05541c0d5104295039146089400a0042c1c01c00c2000e42864504040034581009010b8802001490110311070241d0700300c0c0c21401c0d405a0301c41600000c107542d090003500b40030500c616003404562043d90781d070b03011030000d030000800c2d5948170500782d160700007110040c0d000d040b41800b9244003400c201e1015018002d0a4a90509800d805403005204e6400041c40b1012564000f0040006603100468010030304100c46112080100c10880014014070f1509154001e00c2c07120001030740d4524000f6035910700388103079510b18003030f80029141c0e41c000350031001010b03070001068802240f8403540b468090010b245001c22601900d10300401d10040c404158402404144503020412012060030301409800a16 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971984946 1250 971983696 971983717
    0x1030b03070b0901030207061d010e06011406031306110307090603060501090b12042a080106081c030218060a030903020c0118031410051303020c0d0812040212010609090611 76
    0x1000983c06552083e070080050900840000a000c4d80801020f038415040040c046000da44070b41c4030038200101844110300510302d490401c05000c902801040250000515000c64041500404000d10003203400c071644000a0490f40c40d968507014038080c1c039204250248200203468140d000c5895400b5002d0700054814862502d8240101d1628040b07081200401c21141e2000010f02c071950120341421220410b03001e91034441c0d07043d080c071013400e08482043c1d1110b1202d5200684007513021512446500301590240307405661040c80005880c4d00151a48442d504008000351390b44841e83d050380a408010b10960a803500807001400449010304140380000828180207800c000040c071b1001016400d44801d070030340c1c01074118104030780b04031075040f82d03d07846011009140c002059030600240e640b60310219a074142401841d110314102c3e024080101203400c1c8490702140035507a44810341034480501c000203200458444041c40003a24201c80304568036410085040100750501c0c0035030310010701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971986196 1250 971984946 971984969
    0x5100306140712271103031605062d07031506120c0e010f0509030106030611130801020f030a1a09010303051305030703020609040504080f07080316020606010e060a090e0f0601030b0307 81
    0xc45014044d401c0641c002c045038070345030b0b200b007040080d00d0500251051106d503918201c01d05120303003031450800700003c01203504246a0400e01c1c09250121070042d001125013084800755542d900006d500500c40c00341d0340c0000300340b1060005040e07a800b40c42c02003400540d990501454402050541781c0100a0050341c0c0031503102c1c0210142e051085001c0c1c20f00003001030001c140d403a076a443c3c400c1103500b981e104c4140c0100000d5130001d03c440f940103c000414612008501d0907103c0203040c04113000c00b0740110105030315001c43c040380118000342e042c01d1403c000e05030002541e488ca0090046d6020030140441c681a89034001002e01c1d02003148000c82e50050201e514000c01d0f0400c00c030013040b0040003107880309001e1080025000801000d40016485aa244c0366a0305002400366210f102842c40341045500030000c002c0503990143c0441680801620805c1e100c0d20710000560340510b86070440410580d642003001014118099524010102a01d0400440b1b68604c280740e100d07200c60007003508609 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971987446 1250 971986196 971986241
    0x3040b04061407020718111602090106020607320a0305010905010f050a14120a121701291611181b0d021b1e0c01090905100306140712 59
    0x724407206c1900204484440040d02c4550260082c030103800034000c02903030085d503240722401c41c18001130f4907024000c3c9000400c41441c000350700030700d0548092009030b9042d9602d4180700060341109880b800c11041466020b40350141540000d005001c24815441c4260800f0000504e013803c604013a015614064225000c1904005800040700c8080a4041c0c000082e850304251140d0103004581d4514411400030729100482d6000804928240702811b1403a90100300410140302c8941003410910f040c0c2807500482d24410381c00b2030075070040303600003d400e8aa00c4010800c0090582c0d00b86881c100484008010b80760840240490341821110700300002900226002c0f41c041e06030251075044680c1c0d10140c87c150020740056240d0341d0a0351075a505a100d000d6030080d02e813300b640441903000007030081c185055040e0000f45904882e02c9108142951400404c8000d140744404501942d04184207100c1b11481e130981007001d0108403120b0f0001250350502000c2e0341e010340034a00710194208540610304d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971988696 1250 971987446 971987459
    0x120601030b0d03180b0418060b0a0e0d0309093603050921010c0909050603010b0604060509010908060103081b03030708010315290a0503060c1204050f010203040b040614070207 77
    0x80c0782c1160800d160000e8041300007041c4680744010800342800c0000b204841c0e81c82031190781580c4583d0040002080148000032105510103001480078204941c2d0b0b64900d0a14242030b1000b06541c3c01c41b52400303042400810201004441103c2c9642c01c8036400c0502c050811600310401000c441d0003000603400700705591840c41c00e0451456080312641041600c183d810707031690b003107400c05c118030008a990f207401000039040610407258803580940090110301c4007000054194850780c00f512003401004924922664415141d00014100750400c8a40a58681c1090070583c0c000300b0003800c4003002d0981c810b2003400084140c902400e180d440e0030701664250380d600e810745000c14084403038a0717035102824200c002c1403206120b450361026002c0c05034102ca10003030281030b8009070801c40c002d50006051000c60030710101160f4100703548400030032842d11286001c5d4184a040c4420503000e60001c0244024806690702c6540120f11400e02008110350010180c0240745c01120002d015810030103081248 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971989946 1250 971988696 971988707
    0x80304080c0d0b1b0409142d01061805040212010503060c0c0a170c0a0c06080108160e1513021309060b030a1d0a03110d110706051804060605120601030b0d03 69
    0xd005050304c05041540302c09110301110304c14000d103581820403009100054030208182c501000c0300c0c209001c0e540c40d14800140280406105120070080005030b9043c40c4041d1919680107000000e101350f546034502c85600300802000c0c01118461302403107006c50007518403c03044036541e041c114082d00e07610465440746140030b080c6550000c1070040410010940030b03070500061004078466a4110b608a0030300b6402003802ca4140c211a1055121003121020007241c0c1c049002111460f90180f00c0325603482194808081c48101d20503002600001d40d50001c611a4025040c02d5045450128449581e5106030060394180e1107031049448080001c82d001028507041031011885030700c4074070000c030000c4050600d002c02141c4203800080340c000880c0041c0710148a00d000d2005549032810b00b000c41081525105c005a11880c400c0c4500011409003045000c0c45010451030010001c2141c02c0d503da03400f92155000401002c511250b10700040c407558042e100d02c256040019040c2040f112199a0a551 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971991196 1250 971989946 971989981
    0xb0403031104150306150909051005030304060809010c0207030c090914030c07090513171e12190e0c0d0218130210030b01051e13080304080c0d0b 64
    0x105a1201d444129482000c07000b0030041c031400749002e0b00741d1040340008007142d055030003500d60140303294582c0880301d51003c0a03d0076100c1d60782001a1f9512529030301c4100510301d901440d014000403600007000c1d60007440c2c0902c940880f500038050040381c40c03000c82e1255024080241003d8501301d062201401c69480081164480d401c07000c0b18543c040c500602c0c64010607415115948080303c1880b40c4120340c05526000000c0300301d0807901d036200c1d680c0d030300013121150900300d840c1e84041483c02d400032074035200200d4140c1042100782d03511252030448106250403034420f8500f0700c00320b42065550410b88600c54561000030003521520800d10200540d580184105031303072003d5401c04800645e4484042c083c0501c44481150b03142518520500031941c0e140c02189007814034041c1d16485c1030343c000e81100c40c1d900381400785010100101341500703000d0051001c240f0105030504004901054004000c10075110014119500c2c2c035010001c0000d4041e82250003844000c2030004a0300140601e6015130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971992446 1250 971991196 971991203
    0x20c0a060c1a2244030c0d06030f030f020f1b010302070506090109060b1503060906010306210606080c1e01020106080a03170f2203030e0a0f12020105090a0b04 70
    0x10351200d4043c00504031408889000d5520085110340010030f00c90340d201990000d4941900c2e080b0203504189401c0f5048025914071051400010008041e48091012140d074681017890420507941c42e810300281600d50700d05c2c21008075260100102810b400015412224902c00000380801e026015581c0b511032021041030b03041c036400744107000c0080e1040c0001d41c07103104080000121160903007804000e480822000c10301801c51240d18900d00300d640400c80ea8003e03020754100b90780380c681d00c0048000b48029880105100410950fa403401c1c0d0100ba55100d010f0b00a68040c80b03c1030721020702e0741d03c0d2070b4413481455001600340840c200c0f0340760003805080d0070310050000040d01c0740c0d00d40601e42441255401200001c401402c41841044482c080d550001c030400da9940e40740c545060010803a80c165040c468000d000c0080000402d4865001074804070001d90a0b688403c0440c80c08203807810034461f04880c514070400003200050b10520a861040b00b1200090103c800c00341c441d007605940250094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971993696 1250 971992446 971992471
    0xc03180309131e020703020304060503060a03140c03060603070518041403160614040206030f0933011a0328060b0901020d030b0625020d03020c0a060c1a 67
    0x2080d51424070800102c0c01003100468144100f001c1c0c041007031101c02e000c4840e40d1044c081d00c1c010950000941f4260b8041d414801e03540e8442600003106a00c16a20083c03404022600802c4445008035409018800990032225181c603480308060312440e07680035041d040368044c10110142d12090290a400ca40650040018808082415030460b031003540001688042603110004010451090082c81c4920481040da40c1c20075900060251001410312040c0c041110040f510581040c06815000301400d41c0c080300c4c0e029000e104e461240803080101d84058008400007856482102c2035409031114190030b51b1950f50754641320355a003909021001c030120300021b00d40d80440e68030711031100074089a811564550139050002450040d20102c03180c201802c189803184940c48502c2a61200c00d500322841c9031581d0048110681013507129030281d071029000034464141034001c01c075410001c01c10380781348a01e1070322004142e45041c00110001d003c10034003402c541107040903480c2e0640009005415 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971994946 1250 971993696 971993707
    0x19060902060d050f01060206101502241008010203060a051512010e0a0606051306030b040908030f0f2503020318100f1b02070915030f1103150c031803 66
    0x1068582c1c100504a04005035910180406031040514041c0103117658070080096160007001031074481000e100d8007807602454544100340c0c40c020b000d025000c00e4610590310310000b000c0214043d06001341c0d052404661042004680c900041c02201d114050280c20712406070325000c244454002146480d08590f502400701c942d04c51181604903001300540004200182001181c0008980c2a13500040620008000ca030340141c0365049090115200e504000407800303032107000300b0003406035900010f01d031070000800c2200c81003001d02c03224050707400000c41e40810354912103000d116280e00c040a040740d4030754622503038045109400030369202203441c4003044500300341c4001528081010482040061b2240004203030300b061441043c003110001e00710b0301004a24040041d40314211030080080c45621074410884031621200400015a40042d0007032401d2228100a29800d20a8080b00e1003400342c244403000e5645446647c0b8061001300387c9a82c81d5884004000c003c00804000c014400d0206020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971996196 1250 971994946 971994949
    0x2030f2104050a1106030103021c0804170a051501051804260a0e0916050d1d0312060603012102010903060c020a03140301030b160c0503040303210e19060902 69
    0x36a805184110024102c0e5502460030219005130301c50744600508081c001003003d6580ca151013003501510441030103508030a41006440b034816038012048451070122500342c0c800000910511150081b07040c0d801a0b085880300042c1e422082c450298042c0382c4012841c410350340c4040c2660070030b02c100c45031f104404120000b4070b0411b0034200c4d0420b22442c040395103032400d5001001094000801c1314600d400e45800000c072140e90440f13007000c070100300001c0751041d002d0300380303601282c0e08100803040801415490241b281c0c1d82d41c0041420440300d01d00601160007400d001c0d05a078140c5071942c10b030104882c01c001c840184044990005c0c0d0400554040000106243e03100d540041203184d40078108102e02070402a1200c04103404280da8490100700400104141c000c80c50b0f04031a05022140c110840101d08480050300c0403c0036005020010b000000c146d0004600e4840f180011008407210001000640c1280d0200c03130052901d42240c0940804241da0200b2042c1c003074443c5400007811080c030b80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971997446 1250 971996196 971996257
    0x1b02030106090c030f0603030f031a04090f150b01080402131b091502060c071e0812010e15030a02040f110c062a0919050402120f01120302030f 63
    0x1c0c04542c4480e920106043e002c1e52600603a206160107120511405207140d030001c0181410101801c10155200c10aa003610240480d401915500500910002c400c5007040c041c1176800381401c4600102400110044907c0c2e802000c3c0e040005845028140e0750b142c0074858010702c0c807110613000d50354a40c051242c89811042e280800348a0f40e56414405040440b500c22102d0191a41c500303540c890400c01100410001c1140d2050fa0310216220004075403020780943c0b101504802812890045a148007034154000c400c2e04032910400c00c081d00e41c035954036000100944000c2160190014001100541440e8014044200031000e0001d82a20010300075091508040f540c40025002501440080e40f031520b0400440c2000562603010000711a1204040b4030420000c43c1c094040b500212400c9000c0004000c0140405041555184040320201d4040d43c001c803960b2918030b04150000c90a007940d00c0b100c07504294103800031490404682140319082c0c026403100d890705800c10200104000864 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971998696 1250 971997446 971997449
    0x5070c0905161101150b070c05090906040b240415090c03020c0708030301120605070e090a0b0405091f02030a09020a080f010614131d1c020f030304080301061b02030106 74
    0x3000c801d081040b410381c01040010760030290320352681098400343c0412007802d41d039002c039955800706039502c003454030f00655181400d50207594891000020014045408140c892144d803260f101400c05a8928483e940c0c01426084202c0b200800130102010f14140780d8400f0040200c40a80d0004030b60307942a0050585180040d603100103078001c113451aa24600b08803c4000d452a1801b950842d0304100d44040815403050001d02410388980200c1c00f01405004038540304400544034a17070a15000b140500030b002d2000c05940154a000002850301c80c1c003003615a4400c01d1403440084490704000e45501030b40024084242c102c0d5600f08030f800603a05e0800790401085240d014085010b40d001b4400e0854541e0741c801403500400114403103107655810104013003022070030000120f2182b084091102c10541d25120181c503c0786000b1098114410b0040d014118140e500f20707000601d102c1d20594036800b0070340c0e0081601d1000d0006100440c052101c403a0f907003212000c44018102207400107800d450a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971999946 1250 971998696 971998711
    0x3030c0f03300501171906020d0f0b030d021b010f0207051027060f03050403260a06080f0303150d050304060f030614012f030304060f0513050d05070c0905 68
    0x44440212110900f030089030b004020408801542c05100202c160715a003000080e04642e030161080a802c0041c15415207000c210004020001d284856003108000c02070f00d0003080c4240704110410701200c0c400038429262a243c84036054554020900543e0105200000402580282803020820751517101351024550899590f594168160100315801d100601050132103100d5007107820320178640c0200d68900070f10304914000a242d52103040407076070b81d4484080303a03c14480c00c03c401e40d4181c41c101e541d1070280c000745400b00885c0344d45558580d612803140c0d1507050035800500000d058811001e1222f030404502502c0aa018826661100d04580c029000f10010505102c074200c250780e451f104203030250502204003001c1700c00c140c1c000790802031203204144608000310000c01c90402221068298041400e0440c1d89a0400d4549500602585034002512a11301000180901c40708000030f079400e0f401001a20382401c1480c01280c2941c0052001d0f01c6404601c9400030380360489100d4544103010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972001196 1250 971999946 972000017
    0x1201021614060705040501080c040e090a060e191e140615010e030a151503080702030613081e090d03030e1011040e06030709060e011e03030c0f03 64
    0x200345000e604081072074400000303aa2200c010490704642140486080da0400d0805542996650821030120320685d0130003808084500b040c440b04041c0064207030300e9988113810902c090034010050603034a25002030314181505c1701200c0500803910856408002ea050840f80c2082803800d5240c04081e18030914498885e0b510003c02c105125401d0000045090000d103060751080c030740b1000185e602c0b0400c0c0d4000d8580650503c0c0e041f500c0c503c41d4000300300750610645034010650b0320f081444003a00680800da00a000d41400611710341c10300c40b40c070714030f0070342c0550503d0130000d81c03903d4020565a00542d41003200c0041005001e00d90b00d180701656540d200f5940440c503030303000f802c0b124207160050000b01c00c16810041c50311403d170391520550302a100c440f14000801d50f074034800a45003440552200c0100c1d0702d07080c000f140900e100100710307059401c0b20303290104c400303100a2540c900c09098880640022032120b184400101d4100c140b44500d0300a2401c20340340c1d44084502854590300c14400843c016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972002446 1250 972001196 972001237
    0x3150405070501030911010806011701060201140906011d090102070b0411130c020d0c02010e041103310f030e0415060e0d0b070e1201020a0c0c12150b120102 69
    0x401080741a024000030300c0c0a21103042243e46505094000b194600c2c107001d8040001060350348101403a00d003082c00904100003075607613280c0c003a00a00e1415803003030410200c0c00c00075008520000304241210401581b0300e2004600034001c0020f602d02400340d040c603540800610000c1030000c404240164042c120404000401000704800049040340b180d24107030a104486030800d8001c560580340e40c0341c4d4104090f040c102480120790141c5000459540304c0d00d04030344802c0450200c170103140708182c2c803c0d220301a02c20010120b115100208070041010035102c4151000440040442e40814880c1c2090420001d41c0c1c0d0000e000c0d245021040442c0800800c8200801ba5016030130300c0340e00345c0980b0011000c88007900d4503440302c1030061002080c8005d01400c64403646030034003400081501c03a80215120421201d0081000040440039281e10b12910b0000c11104200e12203410a580c3c0804000300f41c403c0809081e025200314201541c5c8562062503400b900305081c00108200e0010450120303c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972003696 1250 972002446 972002453
    0x80a03021e010c080c030604090609110a0b0301121101050c0d181d0a02160c0e06010e0a08060f0a0b04150f0b130b0c1c020307060e0f2a031504 63
    0x118000c070008012070303041c1040c41481c42c0c0c2004141d900004111100d680d20390380e100105001c1c240c1c815000b44134901c2d00d441c0e041030020070356085280420468090310816a22800405640820f0041c005812030002603840060b092030341c051150300c13043c10301d2814084142c1589003840d9407400c60f1008601941e40018004c94241d40c6a000343c50403210030780380c0010f2203202c100d44100040c40310402950010700707034000881c5480303001c031780b41da000100a01090715000b40784039406098585034040748041408249602d0311400f881d0035a28824004c2c0860390f6500038509003c131001e807410710f08564401c114012a142d501074150206201c1d10310305400703461300403041c40ca00c0aa5008510303514040c000010b4004c44945440200d81c00142900d0301c400c04d140e180e81c101645a04884401c5000340e518444490300440641714842c00340301d0810103211985681c1e078480228440c010a107820002c01c0f104001040c8550025a0b207a84441103440c00c0c6182c04a89490140b08144d15001c0c000b000700001c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972004946 1250 972003696 972003733
    0x90712050a110406110703021914011d040b0d0b09030c06060a0b0f0304110d061d0a050c01050a0309050106091d01180b04080c01060e100f050a1509080a0302 69
    0x30041074541040101180d1031038030301e01d000c1e501030f840402928221604d081c4400700946006107800504000c081c0c0c40400c0b02c2641c3c81494401c04801410420f1403542c198010315004001c00020740900081038081030400000703203d02181c00d5484664042408046508a4103052184515900440e61074908040780e03407506000618140c401c1ca038101060186414a0094a42c4140341d20609034883d2103d190500400050388400d5401500e018802d1040c0241508808004500210410b4a80032200080c43c2c4501048801501d564415a8031103000e5210300002c140d41b007941e20340001c4888850f650315094604c16400f00e0042c41e00c80c00f14801406d07181103181030400251008010f800060f07007510301da46203010743c0584480a848005410300c0340311340c01c884100d51140c0c000c10007a601e40825240a2109032100a8400e030359050102d48999070031050070a8039001440f03101070600e0138080780640340180c0c60500c10032085c0300001035442c608100030039003584681c029100f10789602c50304020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972006196 1250 972004946 972004951
    0x609082206030e030f0d0b0307090f0c0e01030b090105090a021216080c19030507030e0d020703151404020f120d0e010f05040b3a0501050901141804050a0209071205 72
    0x150804c000d0000b45c0500b0380125515031507810300c085607082c0d1420001e07027040216800a20020f041000e0148202d4040c0c1c171242080c402902ca1980084000c0011400c50701c01e011402d41240c1c683c401400185060f10300207074040c04880c2d01510700002030040c1c80411400396400d110319000e001c80d9003002600001200d6102e0754840035203081c650a0a190004c180031400c400c424966a8004103d000c0c1c0319401c06a4403ca05000b2100c0c00100044000e640f0041444196150170045090b1140f401090041841c2820042d00c209000d4617107408001100692800c425840a44420352140102040c4200b60030641107840d01440344a40500251002a01000e10b4040001c108402d009070140d20044d10402441110900302c1c80c1d41d00e50b03210700700504c1c1001e5950142c1032103c001000c2c8000c1e82005041e03c405481d170304481d036a40e5011681100b4501c20a07548200c4c1000d80009030402601c2c1650321900071821200008410740100d44520007e03100310b000189091912000300c1080d0003402e8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972007446 1250 972006196 972006221
    0xc030203040c12020307030605040b18031e030a1503050d030506013f020f0406030e010c02071703040f030b0a1802030c120102090303031e0702030703050304060908220603 75
    0x6285281a554150001e103890050f80c0701e00024005050035501c0821111000d580c0c4454100400e0070141096015080200c2d40b1603000c9803000150b07203440e680441920000b807840900c03044c48600c40a41c010064200401548085a0340c40031480b10710701542a9100460242e4068201070100d098000c0030381b080100424103101d050700a62420f020f8502109407041c00303000e00e456200d520f0b080d03120f081c06031074140b00d070000f400815000150301e00900200104c4c1c4203510100281c118903080c0300c0c03e0301e506187d501c003d1380105108000140350050f0250341d0300010801da071714250311620103030240c00d00c03170300181c818a45102c01c10401e4a05403040c42130307503103503a4603480ea10101c540c000fa07613460179000060b000328007409001c5101c0b5000d4050340c500840080560b500da150800b134a88070110000d451110003004c12010440c4030380040211145e182e019610b403407569480d41c5070103014000449040707401d09400c2005044c2d0080042c50b100c0e10404d004483d096003894450001c060f62090340268 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972008696 1250 972007446 972007451
    0x18090706110c0d020402091002070f0905010308030601081f080a060b09041101030c110106030f0302010c0f020c010e0d061e0e0304050d0b061f030501230303070b041e0c090c03 77
    0x84141c0d1000180a1890705048401400211141c408180a40600300406410032501803420310401d4002c60001c0c151041c010070000c807295609554415500d080c4800780007220100040340340c95114401c12030780241d83e40341c081404000d144094010344150ba0020229801854402003080003c2c090141c44400c1120b19200d2818503440d643d90149101000b0703414540c0e1004038000e4680038004010400015074000c1211617540d04010a03030703103074a25046006501e800d55454401c1d004a4080c0c3c4205482e13801040e10000c071200558244041240c2c0940c8001085040750005031903001d9620020303c0d030490380440c0301c03000c5081000e450100300c1e280c00c95001400144081d440d0002d0b1000a6904400051507544607003011840300d203906a83c0055560285a01e16204d41d019040b03541200c004240005003030b0f8220700d001001c3e29003800080c0c1d0542082142c0c1022581080c40b20350824061b100403400b001c2c1d50b08281e580c4003c4594212102416904100800c07030382032155014602c0c0c6400e05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972009946 1250 972008696 972008717
    0x21060f0605270f0a0602011a0103020301060c15060306021602120309030307030503060a050a080d0e0a0b0318010e03220e0705070f03111b0906150406050f0918090706 73
    0x152664002140044814180c1c2c2c81000302075990304100303100070400079000040e060744901c4005d01034900c460185a00700c40c24180181c407540b0174800c803412074513955204c0c0da0b800740c507644110851010041071407105844502c00b00108407580b0041100007400c03800c107002c8203154818012f5603104c0340d40c48002030f0024031042c200c030348022045030364059040c0340059983d91201d000401036a60ba0b0080b680080c5810000314040314001480c0d0ba446c002520703000031079907011080002c490034a00a03c1e808000900c041b9600149402240448400490012032140346d1001c00600e1604910902400000551031040c0840c0d0300c0a4448081c1543c0781d00340110b85030060002d01640b05001d00104095508030114061500c644d13060105c08174440c054840f907400607030300501d411a182841d20320881c442c4011592624040400341c0300d0310402d4200a0030b013403900c841650990018002c403a40c20700100001d00442d5a00c60300c3d041d81c41c0b5290b0905880d4102403e00511704a01a00a60180800c80c441c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972011196 1250 972009946 972009967
    0x6010809070506071b0305060f0f04020f0d02040b15031e060d11010207080303190f050f0406020d0b0306010b041508040305042108070b070305070f0507110121060f0605 74
    0x40c1d01d42581d0040d1145a0f903082d4a01c0c1c01502c01c01c051645403444000414080100580850142e0003029402407464485d01c601008480e151801d0790025070045c41002010010308201c40e50706040c41c001400002e0840c1c0540101d403580041c460350140000e40002000010014030600c52105820307103564641a2910300040307140c3c89001413002c3d01c111414a20306400c0d80c400c11810003c2d240c8481982d460341822110121078410f14144003c0c00b5081050701e488092807449020310a012120700300c4941e40b11034071f600c0000d601030409801642d80b285002c05139903c042252a0003800c0c1d20920707964a92800c18401c4070705048450074800c0110b0001400003082e030142c00c1c0c8040e42c5000301540d01b8a0307051015030700642c80c0000010426035010801c8001d002e51088014882d401584003446299101c1d03104550b42c4840820301004274200703104075004111280400040b0390b006041400d249000010341808410303401c10324040c1c840d240d0800703020b42444100301400038142030802505001c45400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972012446 1250 972011196 972011203
    0xe15031c090308130815040c150c060e01110403030e120d0804030305090c04090807170a05160503070516090b0a050604090f1e0f050c041412011b0807020606010809 72
    0xb00242082101041e0f1a80390341301000690010078240c02102c1c80080d1000d01c1e02c07030b1108216000d44180050304c00001d10820b4404140b03460401e540c0e64050040c02942d141001401c54500c0501517640e100d004103170019a003001440654000e44175483c00c44020b00030482692515114840250455814510890341000c44650000c0d814140803c00e0398a111406140020104400794840d0500040c04140520840288059805602c1c3d00c8100b002c0440c01080512a04014900141040107480441c0d0011140764459510540c140d07881d14941d45c480606d4007000441600d500c40d00400c0420060520740700b6903107001820384000c1e1005203458009003807400b4902c00c4070b16040d160720b400c1c4103c90300780d03010700ca5950002c88000d5a00c40400503000003804040407035010381f40341c030300400c40d80c4071004140c508984200031150703001c40301c0009000583c00801d0511034a5920303441d09082c1280000300c0070503c0f48041d40d80e10f100d0b141c650300081c0750201c06859070b8188a80300050090030003010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972013696 1250 972012446 972012449
    0x20703060627090f0f0501022502120105062101020f28030b09040b0403031407210e0a06180804090c0909020313060c050424020c030f0d0e04060e15031c09 68
    0x50701c200031000d450030302c070380688151403044035907894103c0800c26278900813540007581402965160455039074070460703508a8400360383c99503000c8c001140030f210718540e8181d88107008100034009401c107003107003060442c19045202c58240c2d078001c4a080458402c2c120368030090780245442c0600180c45e420010420303460003e4008be00301c42c0b8000c006003e0500a8002280307040700c808a00040d071509610041802801150070901ca00c40001115120038040c020484200b00c0c8034086c01d04e46031701e03940d0a0010201c002c1c400e207880c0c0f00900c405000c9000c0720301030b00090448090201e01440f410200400070781c15070b0003025039544103005008411108012003401240d02100002d00362401103003d031124000c0b5801403801d010b0911880303007551101840d03010b281c44250200d8144000d80820140c0f14441c5041c4c0113500d601111204a643e4810481c400500304080d00010703240340c03940e56980450781c04039401d06005c4000c004010140c01d00308004002140501c00080440701d07402070013800b15045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972014946 1250 972013696 972013703
    0xa031104060c02210d030e21040e090f0708010e06010e13260a1106070503070f0e010306030f05012c031c0b06070c0807270507020703060627090f 64
    0x3130840303c0041a880c1c3d042c4481544804c00300d980d030304640031380100070b044c1c1d40034030320364601030080c081c403090915848003081c6402001c040d40c18941030442d0030092000c01440c030140ea00c5690400750704010f0511049010341040c10001c1001c001d05010030b41f4105c3c0c103901c540800c200340303420082c0380b481c102008810b260344009010b036089060110b1310904ca007131a80700106090001042082603401c2520320b9460030b46803081d034071b43d81d41703000080d6004e00044070307041d0200e03011035801c0c04414858040200104070504000680315200d4907a50113010f1000310803a400d03075480c4501050441d10542c50f240080b85010320203450b2007070ba080140c60303010300407100005840b103c5e000c010b10861a00080e0310030782d014196645170038007810010fa82c85281c0c82050421300840002048084050b10250b40c03205100199640181500351814000c000040c601c008501a11a0110001e403407406140300900d40f12039030024903280c4d1128405443c28110141c01c40b58640300c00072002030303107a180c04c00100340c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972016196 1250 972014946 972014959
    0x1e0503061e150a030603020316050d030c06180614060a06090b0924030105121c1d030d081005060c10050c04091b030c050c070302060c10110a031104060c02 68
    0x51078020641c8600401500084150003080080c0c005616038800c0c1704a81c0214100d4101c490080849201c02500f40035450b040104907a2040110380144e0009a00034803c0c100011510701c06085a8012403051104403101a1a1440a102507103000c50564001d0303021034142c1c0029103800400b404550781d505c03400950380030110700c64601c0e949010040490074460b07140000c05c194402c10b00d20040e882401841e10840745000e2403035490200040c43c009a0350b0040310100007884190082d40c007466012403800c9a5840740180ea007268a00b03002c250100b2441e911461020b0074440385041800085401450003400140401c1040d42c1c000106010030b641450000075943e1148a4404d2492050740c000b03001c1a41881c000920400078107644800064107036608100c86101031904907054401c010580e2056070000b0820300141c980701006200d140d83c51004c9402c4150349101802c00c1e1407412401d003200d1040840c40140064060241c120200a4961424900b6007804809440708507040307406406410b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972017446 1250 972016196 972016249
    0x5181f110c0a050d080f2404090206120709120b18030702030f0304080d170a05250804110414150607020a1211060406020d0503060303040e071e050306 66
    0x40050044824522414090b03a5030714500d03042c190b0b501c810500d401c03000903000c5800a0552000700450740c1c050380a950070b81580190900d2903c1c0140d0440350440d501968440700c0c41c00603641c030402001031140f41c4101030514601180090240403103030b444050500d070740035051030000300e483c0700940d0b00101d04c80140d01c058000a0209246020b00c4200940507c1013554084147c2400405801161007410450303078a03501031102100c4420b402d001040c2000305c08008522094000d0b001181e0112058080c1842e42a00720340f007a0302c81c104c0d102c0100216121b0800d0209009812901c00030682d02070350b007803100c106003c2600d0980b1031b000f45415441c0b20420714100d07855440030202d4803c21303001030420f50907945402c0b0341c082d02c1c1c5560004403030030794200303030b5004040c203010301501c048400f182c0292041c07496900781614243e0004105580c940000c000104401c11200135003409058941d96015983c900560b04425044040181100380042841000340c01e81d5180d280120800c41303c003580d600c01c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972018696 1250 972017446 972017471
    0x30305150a0305031806130311031f020403050618151305101b09060e040b04140406020301060810080c060a170a020a091202060d05270105181f 63
    0x59400c9a46650000e08048000300780f19000000d440441950401c40340a81c0141042003034607c10a0f8a01d903200800742c500304089029800c401c0002d42014054420040811a2040203140c1d4400040708071a0b0104041c01030040c00c0281a9201d180b100c1500072410104501e46d50304d07681c06d071800e07082138400300c001407a82d480c0d5280030800a52003000c5038040386c0b030b1207051406003145d405a2040c80800c2d143c50902136104208100444040c1d07140c002ca0030401d00c0500028080c09082030350090345404440e0806185148000d01c560300802e0016100d504002004000340c0f4090072018030368034424001e00110301301040612040e203048400303582e200742e4802e083c0c13a001e19400361050400302140130401e0380940c1d50001c028504096940c0c1ca8079a448d0a00c400e403400d880385000c0e40212040c841520480b8080d809590440c44002c0b500030303801e03581e5510010402c40c110065810b65160b805000c4c0c14561443d03441110014000503291100c98440d42100b03040000508811058440c0301c01d0251 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972019946 1250 972018696 972018721
    0x1a1504090b01021c030c110a0c090509072103030b060414010804170a020c010801060c0c18150305071406040b0d0c11010c02030c0709061203030c1b0609150b030a030305 74
    0x30aa250011040131a00440301400505021400801060184010380080c0d540031a640103183d83c030900e012841d5080207124001020000d04a040d140304910022a6902d15044180c41050035030f250050a903241d480c008065070b20208481d400b80e1303010f10050144144500401004407020300e8007404961b500d0410490307600791440c2452010200285820000c0d43c085410404100c0a888410199a039280c0c00c0b501072080714001f40c5240c20103501801000450f070351604c3c1c2d5220000003c41e0f44d00d00e1500d0500201103607801201c03a031707110344402c00000564502100c25810308031490341c10545400b0300748101380b01e042c4000c0c0d01d45503183d40000806000ea1001c2a0081d0040700030030201e507030300102070b507690301014803c4600d2240a40c0040c81c1081805610160780b65549d5103420500f01d035030150081c041800d40c0105210020b810401040810a6000300542c020701c0003103030075091400c000c262400c201c81200512030a00d2001046601e0001c0c50200b1690b16140001c4c550b9601c00c0c441c0b10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972021196 1250 972019946 972019963
    0x181d0304050d111804050115080606010203220e0903031602070e0604021605031c050a06080c010c032703060b120601180f0e010510060903050a02060d0b0409061a1504090b0102 77
    0x15440609003480140001507200e072505051076800788e00c206d611b80703254954a800c1180d0560048e80b08210015501c640500083d0800070104407000105448446000c55860110390200d640d42c804000c01910b070062840e91114032055001912440d81040c0280c008040d00404d142d028540001d20540c1c11102544000c40040c0c000c400c0c0e90b1201c40603101d580f141000003180e642407031700346000304401c4403181c81088112484600103240301441c54005407000311059900780e06001d18485a1a000f860358124590440082d80312403100d60b08605d45041140c1c0540d400c607009040080c1c404e0110030001480c1c6041d40c803222551841d581440491101908194402c50940c0d400e04084144403041500441d000d0520000e100b60a540c6961048134011042d1201908a0707121420704009414008000c4c11180304060002c071740002040007240585038901070450f4442d42e1520709041d003600d0000c0f07a0000c1c2800711200b0705050b0b007400380440940914010f404005940f202c0500341d580c001c000148 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972022446 1250 972021196 972021229
    0x9040c020105070f05090303121312080601080106050a020d180305010207050109020a05030d05030f1005031902041b09032003060703050609010b030103030c1b181d0304050d11 77
    0x4204900400024041c0206550380c0022900c42100340f206103015070180d81d58200064021820082d52661503000c2c0303138000d898030017040d0441e80e0030b5020501c800c60041384621280c03078080f1f8500f040c000040008405078880c204016092105030000c56010810a0000c4190318008031a24840c00d09003406240540c0028225840050700c0c1c01045019080450482c0c02140c1002c941561a014180c81e400c1101c3d1160006608000240345880c90400702d0350800c001158076141d503a203030390102e850a0500c602564a281c1803121000c21450140203a0807011403c0316510402039600c800a0645000c50000130644072a5400e914545ca020044607010600f0040440b00070f03003480c3e00050b00618050307450030b0142800d1400400c4039048102200e040700c1d03141da1460041d01c1c0e41e03164181094280369810404072812131001940600003840c409034141c00c01c00c0041c80071011034001070f070603961104909294000344001c00442d0b03035821001c603601780c201082880307005d10b00700050400d0320580c0c0ca86 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972023696 1250 972022446 972022451
    0x20f03101a0a3014060906060f0109272a08040807060b04061a2101030b06010f05090616061505060d150504020a0201090b130b0a020a02030904 63
    0x103241050a401c071403281c0107008070303a0803410700003400d00c0b050002d580107070b07494040c100d816824000c40381d80c8001c1c04010440405070100ea49566000a800303102d8109a015a000d41d060003600345080c0251a040304046601e0070700302052400180441100b4401c8005134020307442116200b42c841c0c03411300450501e01804002c0c0e03a00b0020300803803c03041e00451081c451130300b0780b4240c81580101c599500854011a40605200060381d0f264081c14458a52640094868000144048165441407000f0200c040c0c0252241c0c15013140807600c00e40103450a000d0f0190400400c00310f1304050186420503000c1ca082c1e00145291034003950213200307502d0502c0c1c00c80800a52448180d0780044032500c0540b1038201402040c01c1408204100c002d6401265446041001800c40c1c11042d9807100300301d0090201d0003040f0036516000502227800c61450480581d449030340a004001c00809200d80c0400c045020324000d55451300c0e120305000d002800440019400181c07445500e0003041a28130f03040c0300034003d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972024946 1250 972023696 972023713
    0x914041e29040309091a04110705060702010506120601053a030f11031e09150409020d05060a0b0a120e0d120c0504080a0b040309030f050303150f06070f020f03 70
    0x1440c4000008407001d900044c0700c0c02c004550b00d0194000c15000c2c007480703041000391014500c1000010300540c00c2d040600a8104580c7c00015800e10035180714060300c0e00002814a01710061100d609000e45441516400440060046559500140515001d2030580d620b070403550000c40d8445035051100c2e0b214011420740143d0415130303c0642c06001d5620350351441ca006e00c5200d43d007a03982c01281c040c9807400f40c0305040d40540035100c5002c3e101c0d030070380109051030b0024510201003050f44503800c010201a00041d44442c0180c5900030303142c110354180c4103648074510b031204441c0b090040807a14410407074285401c400520036a001030203024420010b440004104803c098243c0c41c050f030020410a04004000b4512070040e801e4a0440d1307120700c00740903c20030607503890280444c000c00c101d082c8808403002101083c0784201c1034200501ca1300040da40c038104404a159840c80320f0880620640711050340200544680781070310340c0c0582c08448a40c5100b46032000030502514034240e950035114480c40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972026196 1250 972024946 972025013
    0x120302040f080a020135041b14040b011106010b0f09041802040e0d0c26030126061320041104091508150703020c12040914041e 56
    0x6900681a00c01d8a0700d40d02e80e00c400c48850740308111080429192221410101c03134041c0f0f4451100c1d40140305029511070008c102c410400c00001c260403200c484098040c0084040c02d01c1d1107850350210003420040007003600356102c0b41e078039541402018110440032988000012940c0280c40c3c44410041050020788420b2442410784401d045040e442135083c405184c0603a000401d0b00c50300846180c0e103000540e02c9035110040209030104800d07803503400000983e5480044070b800b440c040c0411741004000c15800715800c13900801e03441c0007000380303821034070500c25041ca88141c8010b089a12940035043c460540f5040200c3d100710322030440d0440c2c03c1c05a411907080b4100000d02c103480d4078010410081c070500940300074110403805010750303a80c812034104114410140c03c4991101703461070058601030031190054180700091104840e04135020405000e00c07141c03401904082ca43e4034459174000d18240e10780d80351540ca03a02c18038401070303090401c01c400c4c449a41c00403411009083c80c24602007407400ca = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972027446 1250 972026196 972026203
    0xa1703060103050a090209070e1c1a0106080106081b0c0a0b0105180f0a0b0a03050316380c1201150e030f0a02040c050d05070f1b020904120302040f08 66
    0x480841c0082d1800f00011401070444c414900180d0300075001052a81c2c031600140c500d607030040307074541c0e00140c20048100d6425807038004c440c00078855034400c040b07100350013010040300c2410307080780050102e2a40103004031a07000000d554407410141c81030044010461401156100d40000840305001d006044000e000c103101403241280c0d02640c040319201c1410386d13448080f47d0b080d1303039020311800004003142a1000c5904260040c0c140100210381440d83d0340e50709403561f8442094031500301c80b02d460031000d22081038029400240c0704004145802c0b008850800c0c0108400924031180d08804045151000e541e400d079108000c04518810303203561203950047c43c503000c40c9600300018112414522041c107000c42e44042a0009030f004100d036181d5079007044050072007070506404020003401000c4507140315006035809400c25441d0f000380b0141d108401002141c82c0220268400d1441288400585400e5840f6a0280c1c10032844514100c41c00c000301c01900c1140d10011074070744459004a10b1280c0403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972028696 1250 972027446 972027451
    0x3030f0f1e09080306060d060e0414060708011415160807050c010201020a21110a080f0609130803150303310f09020c1c03060305122a0a1703 62
    0x521a020146407002401c00958240c0900184160b60a00115020b4200310f00504031310740382500d000c20400c1d01c8007480002014100c42c00e40d90705901010300c507003050062045c03070f80101d403900d4514881c0d8100307400a034002040f4107120340501d022040c1250806180020390300010342c513a44502000e9001d0a02c0d803000d8100d10700a0b1614003611200100d030b503005100304c038408566501c840d18098500d1659180d401ea1001603020a43c0d1100d4101260607050802801c20450380d869140d002d0402e80811100582c004101d24002d502c41003c0c0076021055407010590540e10056265aa90701ca1094078462554644520380610001c2211900c543d0400c40000c4402015107841c1502038080307035014038803071480c400c1404084c01c0e0740c001c0c0554000da40080c83c68031031a20460b000d4102c148044e0031003c881c00191000650741c1c0034144100501031000030708414030076000c6801d10305440024141d060420741140c050302d0b025401e58020001c02c4c040710000700d0f08000424920402030704245040d6208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972029946 1250 972028696 972028721
    0x2010c0204110703022a1203040305070b070b06030d080c160b010902192a05010209091005040606021516021501090b012c040c0e120a230d0c03030f0f 66
    0x80603401071034a840003000042104501b04040030a81c1c14009102c0c01a10030700d0f291555000030003000c004103508100120082c103000304550380d80c40c0f090600b003844030070240c48203111350403000f005003030b0075402500d50380c104107009081a40d41035240b4001c140c00c2c0356108000d123091612000044d8003002c2e54080c02c40300c42d800b0410050b40c40c2011080703480c0310781043c0700c16680c014850b003080b1030a000810005114420800185007a16841c00201640c4003107a000d0000c3e01500c5080c804c0b41018007844008007114001070450411080c0c03039054014000300103480840b0410104159680300f0003050119030a00c103107010540d41c4400c000c1d40606102188076000c00c65284440b075080c91702e0140c210300440344400c101082500f8104000280500c40084020400030301c05960350f50303036040c1c1130760510784550008140a018030b241000481190101c0c1ca40302c00c0e1141c070150001c00d404a8908502d54062034500d000703628030300c0c1c15401000c01c607990f034520901e01000c0311111851513002d0a4181c0c0c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972031196 1250 972029946 972029953
    0x607270b071b03080415030b1f020c1905190b0a0905030c090f0a1a03190606141309021507060903020f011a01180803032a0307090e0402010c020411070302 68
    0x108004607602c111140700040114a00300800c10040705481289a080184c51401244a491a80000f920405c400030400b4281d004620091455601001810303014001034550464003159041c02c41201200752044601400030581c0116142c280ca00440e00581a00d081050700e8080c0b51a00030030141c00c1c0d0050703901074407550145c0c030342900d4064100d03485409c0000c1e00e844155582e03402d41c0c014124420340035840740e071701c1513900003166828405100d00780c00b00410030301004584e04180060700c545a0003000080744143c01104980c990b0550560000000c0b1404601001300d4170228941102c0c4054150780e055000c510501000340e04e03040b4520547c040d50854006c050a0207c0c142299100d2011564105140c0c68009255001c0e0b4114080310001c00400e400c0641d5400380039085600c111148c0e21200d070b0910801c801e5001600b0f00c8a41000700340040e500354680000040c28209060040301c0500307001400160031a88101d2000800340c1c0c0c0603105003d00500d482100d1141d80184008801500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972032446 1250 972031196 972031223
    0x4031b1505073203210a050907150c0606032001020d05091909050405030c19050c04110c0a050615030102031e06010903140303190209030607270b07 65
    0x348074105981445400820744180d81c0c0942d440750003402c01e020104000c00c2c0b200c0a0354049103600b803000d07282124480b00740604645206030a0006124001c2043e40c410785403105001e641200020701c5816144890807002c42c207030510f2001e4071050003c01e001040e0382e09180010040114000b225250184850700b000303000d625020069890b098618031440c0003072414007104159180404241c1c0c0d84078500c50310364407455110080801540c404981c143c9040d8400501104010005c000d0b51261512003a90b500c91070030140d503a50b840781c80798180f5901c2a620b81c01c100701c401004001712808440705c80126403080300240b611a480d05000c4800502681400000c3c00242c2010f0003164410500c10015107841c44550781c01104d1440c001d01014108011140b0100000304d01c00d0403000300c42000c00096450f85804040c40741c80c107071b11000c3e540d070507401404140e025440000301c458200710b55052800b20300c040301da0301c0840b08040c0c6610301401c0b0145000000d04041d00c90090007c24003514132101402e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972033696 1250 972032446 972032489
    0x9020d0b1012020f07050a0804050117010e0f27010606030c05250516061d04110d0e1f05190902090114010512090c100e0607060e0304031b 61
    0x81c05200449000c00c00c0a50200402c4560350700802c1d090720f0041c01c0130b040040c1601d40c0b51501d100c44004440100300090300707005640c0c00104940d109030711408500c03e20340c1800c0e0402c42540b405481d02c0350201e0010085103000320f100c01e00440c101d00c103c02d60b501004051400a010308014400c800c046460302050032140c511801c212044107005085420250b007449008040001c0005400da41d280500a0809009401198a000184000c5d9180040100300800211611070b0070300c1c0c510311861811201e40e54215488064540da40484900020068404040242080449036603422800118060010100050741c00240110300d40c50443c23040403080851003003150040755001e03510140002c01000705e01c44c1c0c0050040700d00d41c10324206051014003101c0b01e03000002568030f1301c110b41100c0900381c0e460500315019102048a4038107400601801e20100740b06104e102c0029052070b03116100c2c10300d03d0038100101c2c0c005540c0700d0500c0d2100b403820300c01c008808010380203a009160b080d404040d5075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972034946 1250 972033696 972033709
    0x1407122001030e0a0f150213170114041112010c0f09050a0b0922020d020403060c080622060f08010603020a060305040c052b061506021c030e03040f09020d0b 69
    0x910043e00c00522080070952944005031038501411250b4500c82091269099494009440348483c4141603145a03070402c03440862821700f000b0200120b030b14028805104250992165402c660001c080701c05403c5400c02041840405100c0e4076000d6082c60071000740c20740d0181c00c0d0350103541c182d03a0b40c180e00d40e01c07941009040b000c1840740321980c0300c0611940400d450565041c541e240314240c0780d0000030504130240d000342d0b0803646446000d181d01140402c14010315000b4550366481c5494901031501e084000682808103224050780000d50034105214001c500e40d102102405000d03a424009513903c080041c086c0000b40001c034019402c034400010b89601900421340120323031003188640c0c40c41c100400e02038102241e000020308003034254692052a640034058041c1103000c1d00c07000ca01c1d003480c40e00d08441078546502c0a411540711701954400804040d48500b45d000702842c0101e100d04e4411201407450003146c2015540c00e50410380040d00d1001c583c0101030301000400306011091014040001c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972036196 1250 972034946 972034961
    0x19121b140c01020712061e090f02130506091614030406061d0106050a0e0406050612040c0b0c060c0904060e0c0a0f0509060d090c09060303090302030601150c140712200103 75
    0x61074420030004000600c9641143c40031400c0b00030181d140c04020070104048d910b805509071a1810500802d03001e50030151601424075850110034051030602c007020032002c0400500c101c1301d00e22520b0850341150300c06c000c3c4101080030481840e0b10b0303003001d081940050507203115083d2007065001a103503030292001c40c46412106a030b01e0345401c110032050242e800740380214020f40c0c082d61742d90020820780d072403401501d4080316090000700c0b04d190600d0601542010f94101c0c84040d00c051004000c901d20000e092507202c2204508241c40c0c140c01c101040207041241c020300380b40c240740c5040204600039403024085100d01940e41412f800c1c0ca005068030103100f00d80e0119000700d810085203148080a400000c00d091043c40e0a4882070355403030307208044803202c0e0400c400040c0c10043c104198a03080002501422507a1a00d0040c4070064030f014014804d10003004081402e05047c031900b0100a1040f0801001c0301400280030b40c10a140c040440d0020320024a030310304040b86442070715407080c460001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972037446 1250 972036196 972036209
    0x2019030e03120c190e0a050a0f05040908090909030d0506100801060503100807060c0203100509061308131710050702032b020d0c090819121b140c010207 67
    0x40c90b0154161281000c0740000b426000c81181c2004802c050041d90300e5941c816150f25540c04118511020400a4000b81c80e4821446595010340c20710000c0707040f1915008072003040f030b00001c812003180b40201081c020101d4465018a08200300040f40c040400105902c081c901010016a590841003103800005400f580e80084c05c3d8800610045002d01d005580000c1e140171503001441e6160311481c81c10255810440c0000c034032180c40e40440c1010800400c100007071010a21451605440050351140002d0103000c5000121031540240001d00084911200c144484081060340b0b500b8200003c40000c3c42d00b00040c0f0828a622a00c1c4100c0d10415010350561b038041c0d0705d44119180b11600103d40e0550380c5c103000064092811040d0301e14401840c0c101c18221010900d4058803801800001083d884050341350401100c10840c181036811600e211684151440b0120310b030300e04200c405140c2201c124003d6001402c0110600848940760380402c0703201c6048907940c660060049032216454071a12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972038696 1250 972037446 972037453
    0x100203040512070f060f1a03010905190804090509011e0b0901030b06060c06091c090e010902070f150b040f2903010b0a0e10050f060a080601032019030e 67
    0xc0c160100d00d0001010700a02945094044d4030b990b8848004694100700b01400395a42d60740c02090881c1030071800a44c0034001c8000704040c80c0251101c40d00c50b03000f040902102d00400b64a04100081c01054401500c041c000410040c5402020340e402040c090300c58020158468406402c4078406015400c507005d03001c3d0005039213910310340d65500e64040c0504002d5101c03005001d042d0302c041040001d2403044000c0001807190585420f84210070a000060f03d804001c10a0300902c003090f201144141110b40f9200010f80e941d0301c038101071402c1140d140c0000d010400c1100060034406242e0003c0300700315000c40d41000484407010150013228805051504084c645040e440c0c55441f161001c180102c2001e000071450140e500300041c1642000d0f0003840c0c8840d075100c14048494001c03107698020344410f842e00c1801504010004000d40a4007007070008000004000070700d940d100780c00c030361f848001142900d601d1a00031070701070b00705070040f01d143c40411180c02c100c400504d00c01e0041a0802c007075800036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972039946 1250 972038696 972038713
    0x601080c09032e02072d05120309011b0c060f061203050c0a170a020706080601091203090e090309040b030102030403050306061621030c0c0203060a020a030e120c1002030405 76
    0x58030300200103e48554074040300c2d907403a041d04114001081c0b503c1c45959003e036600c4400c0240c9660801034046001901941c4095400141000071503521043c0d040342c00c55101d13540c00385443d0140500950440b840d280048846200c250041070440400f48590000d00c188180c1e00f1140b0101c0d0060311400d54015a950703245d0022078007c00003403c12284110035a2034010450315541000c6100c150041205d0000054207004154144480030180c5018645a60181800c200003010103085004000d134140e03882111004041c010031582c401001146040b200c00c0c07400d040303803076225080b185041e401282000c1d150700d4036240c184212480389500d500c0300c0d811519448148038060300400300902483c05066034032030204203800c01807186100284541603502d080040c0007000d40e00e010309071601380710744840e840d001039a000c12101e90200041c5401070315000b042100710082d10394103195505900a1101000c7d2a800402c02480551813820880700d1460b01c0007503400403440115000b0348a500880217 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972041196 1250 972039946 972039973
    0xe09092802090106090303080a180210111213060816050f0f030a1512031e09050d0804150f05041509030605090c030c01020313090b0d0b040b0601080c0903 68
    0x2954148000404032098055140e404212500d2003a0400d00c00300d04080700410405502c81742e103690029843c80c0c1449521452002842d07010f0059000a108150500c3d00c1c6072054402c601c908403c603139036021a034090f1500e80110065900010b41c003003040818080100e50070b4000c460090299551403c0d800c10002c05000480d0385400c00820104660004c000e810212101070000c0c0d40900c90b018000121146a085100724234003140e44600281c00848081c0400700e0741080da042e240c8800c0003c20002c00c4109501260200860b400c0300e54405858016070050099920203041a078140c0d400250383d60784407500a650607031541030700c540040d1003044140b1401142240d0981c1e00c00c1582440e000880c2c60743c1e154001e840007200e10380500d9114035031030000e42c9420031001e00b030450300380055850020185500003d00286000f1a68519210451036015450388801d00700704c00d8010304c400802d400c040c0350070806a40c00351001c17800250074001041e2010740d01011902040801030041c40030704070808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972042446 1250 972041196 972041233
    0x30807031104060816031508030301090b091603050604020d09080d140423070e0124050a09090b24070b0709180c1103130602100e1e011e0c0e0909 64
    0xa55085c02c05444013520f80006604042c504058014a40610388030360404101c4400c4a4400c01d0507445940c1d42c07414400f4480500030801017030942480c01144075603400011401901c40c0c00007030349100c0d16042544090018076009031004c600c8007603050101c0b42d8808140d28048000342c5028100081007a0321030011942c0b01c0169000300030100907111007594411348182a010241e004515a0150280b2a03144003e1308281406009440c1400740c20301d02c600d500100022003900440c40d070660b8416540207d940c449140d1442829030001c107910b51010300b0b40303222a0380c000800440f0f00030655404100038901406d40b89050b10ba5800010743d5083d15080460040c02c0590074413828004a601100754810b01480140081c0d04030540001400d07260180081c0381401045220b035500b8905489215504400b044662100000b40c0c0c0c18001800f070001110300504a0f00078840c4482d904901c803a4081c8469046084a403603d0344a510b50800c10000303100c0b0301c080880d2700d4002070300308240c1c00084802c102c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972043696 1250 972042446 972042481
    0x304150516020d0c0501111519060e0705070b13020607060f150602060910110409050402060f13050114070218070c080d0f05130f080307110a0308070311040608 70
    0xa0841c4580d800d110380100315040301d42c2200342c0790007400703250a10203035800c5003e101000c1040d40c010107100c0407030101904400030251915011600c0b2800401c2e224003075821071070280507803a0000c540360410b00009426684010402c0f9403010703072600080c0e254004c010580109070780180ca03c5151800945e1814010400c04201d85007603540e03503000300b40ca410514600d0003e404c15800078800c0d402d01070300b02e505d480301408071140d0090412503180000c40c00001580c1c01c503003402c01c01203100d403030342c0c030000e00f2034000d00e80280c0b100306003c40c18006c0c9410101140c01100d41c00e07200c002d1448011500141d0902c141d0a000e500103515400d80e110003800640c40076400106854440301d282d002d96101d1740c0962240100d02050303510742480500c04102486115000f00407000b04510b80003050780c41c64001010450090034082c804000100c545006541c641c00700f0301502d055035500411032401402c1d4030710a0710000002842c00c92000220300444085600707507010340d01d904000d541c520b1310403565540c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972044946 1250 972043696 972043717
    0x70603020d02161101030f0e100c0e1f090f060c020d08160602030f0907060804030e0d0206070803100f0506090631080c06030f13110901062003041505 66
    0x200700120b55a1600d250f000a050310844482c0c2d01841c01000060658090303100c400880c0e132600c19400c0351101e0010b5016910b0801c1c50001c00c00780d40218060300c02282e8070000303d030007200c1c245c83d0483c402c0304d00074031044407903813900d41001042c1c864002403a0741000d8041d20000c6030200040c0700c00b500d448108003181d2031042c50b02514203401500200300506038001d084076800e4000c07091109200d00641c0f602d500035484030041c40c11526100004090141c00380c13010341804201c0f0f83c00c0f412502c6440b13071440529000750980d580c400302d61a149407154011941d020541022010100f42980031150306c0e0102d07500140005c0c02e0450b402e0421080e45d11014035a280700503001c035480e940a0480c8039440c0340e45004025400224034084049080003056900703107206003400c1040000340c041c00071740f0940040141c010b4101c0d0351868900001c5045000e03079030b503a0010408000084461740100e0003890b800384180281c40c85001c0c0d08155a50f40a107008007103c00400d801c118075980d202d8009045102e44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972046196 1250 972044946 972044951
    0x20d051309090228321e0612040506090d0e0f04020d0f090b07050313031b020a080105010609170601050906062709070c20150c010c03060b0c070603020d 67
    0x10812080c50203400ba8510001c1541310703c080165003c20b081c020302002c049041c0e240c80604480d41d02072036550034007549202d0340c4814825150341c09030080384000c0f040050916503843c0300c2c84880c902c2030142103808880070320504000529151001c02c0d5890485290346070700c03207140b442d5400c00c4546054030406070341181d400d1100c41034440c13283c0036101c2201c2442c200040c480c891828591980f40b002004070b000c1c028100180140d1100015518070299014640304080c82c0c030001e41000800810400a5440f0746191000b26003410706501042c122a06600c400a4455581c000d000c1038000c06940c0751042e80000e00104281d0501e200e20642c0424010301c11072902425007841101c031641200d01e203541c0e45a003454076109080800c00c65402050314100b03100d0b201c200f40d464046d03001d404c0c1c201c00104400d040a281082d19440ca40312055190002d007141c480c42d5000c078190080c180b0035100c0000904103000047c1c000d001104845410b00c4032006030030018103103141900a1750181c0014140c03e903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972047446 1250 972046196 972046219
    0xc0a0c1e0312120908040515040612050408121e011a07060c0c050a051c0c2103020c032d0f030a02180603040305030601031b050a200607020d020d0513090902 69
    0x44148104484c2d00e02c500e1a440c0c036036040505125000c0800440c900590f03104000038840c842d08107411100c800c04ca090081006e40e103a00d00340002d4001c012400042c001c8000900110544144c02c4403440c0f8009220540145c0e03135421005461162890307505c103400010449000458101e42201001e42040d0810400071103141c0e4482c1e1034030b000094142c8698110841e5a030240280c7c21002001e41420326191084035101c0d240d040c102070b1840c4d1014101011039172410040e9000c2d40540e8050510102500d8449003031500301d881400000d400c03c6601d11503200580301150915040d50345080600c12900d06568542070560300030341c0308003480340e084003076410050070380d0780d80c0300c01944154401d94550f40c81741841c0e4005401d035850b000c403070070110304100e400c4840c84d0307032240641d00055654589900e0081e0100d2540384040241080100c441c0500f4041049081c0c0000d9440035141c0355a08460045660f00380403030313103406041c20759010003002a804200c1260343d07030130020416000411190850 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972048696 1250 972047446 972047477
    0x1403030c0703020c09010605190c0212070302180c07030f0c0512090907030603210306051003060e07090303020c0105030603030d05100f080a1707080403080c0a0c1e0312 74
    0x19002115084250040010000105981030000c004042d100b580d0051403075040150240440c0101d01201d041c0e02c0042c0549454140702ea1038440b0301a0300544010502d040801049031a0f00250000f47d015555012022412001840360140f2400c011042c7e60b0500105680403202c2880c01505542000f28821380310000c0380040c400e03081d070400041c40d410390310544803050201001c001440007060514014040004c04d03007480380710b11486408401e8100150a90740d090f00202803e40009402203400c080d05204240c2591000341552003145081c82c2c260344680703082b03c80c000306000050060300103291107076055005d50003840d00007100405903420720700030102d50011650225090401d404a490040140c3d031700104948010b020320201411501c0300c281c40d4000c12090404500242c010300082090a010020041d540559407003102582e549900e021100c1d502c41c00d459003075600e130b00030311400140c8103680007003002d0b0440b0210380c86801500d0340c1c8421000b5280e4a03900d1040c032070b52005c0200c0c0d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972049946 1250 972048696 972048703
    0x402120a0506090642062701020c190e04030324030201090801021809040c0b37120f0b030114040c0605310b030403081501030b0f04020714 61
    0x5503e86001001c10b071074210000d8081c4480040003003104c14848200001c0d5031540e1201107010500134452441d90800940814558851488081c1200d075040c540008601c0401240b1070a80100b40d00310b0306203015200c00c01182c1c41302601c5400107007112035820850030040700001640300e8000d08000400302c0c621000c0c05000c40240035110307100300c2c240c0c00074011980c0110542019200c03501c02142072584501000b217800ea003080341c0d140306030040c0c0c00040411118469540c05400800801030312030403544804000e001da05061500380192001034071783d10040c581e490080541c402c1e1b0760490040c1e0010b07001001856004441c806c0644c85210203051501c007406a40e1200c0085a00750400d4030306400c00c5401d4031110f4000c1403c1000400000c0a02d081c00032102c030301d00d07145c402c0d0b01c60100d10407000f615035110664000844080048200001c0c95042054036104001c01000c0d41c0190f071001004504a480807a003095204d45010859805c40c209036001d001c070640325104400303100c000c0210052a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972051196 1250 972049946 972049951
    0x1e012f0706050907170607090b0a02100b1906050a03180c0b1c110d050604020c1c110d09180608030406030902040e030d1b180504020d14040507080120030402120a0506 73
    0x805d94001030034040c0e2160700c1010440100f503041440790a02e11302ca42c2c000d4560720300c2030000c410151500d18500b8255921211040000f01e5202e1074404030380d40c0c0e0300203805508074445e04008070380b03040076a1403400b0b034a40403a00d900741e00051100c8214144031042c1820380040c40b10074801600040300321441207080c483e4488100714120115240e0501c61101016180020712080c0100e005014001c3c00560001307148105100c401c5000e880d14003640021a18618065040030192080196200e0545c4d0086240419154032414885400000c0c00c0700100b40c500310700c502ca60660080004001030b921a61001c013407180b00030000304118810100c4545540c00032900c1403109603a07802a0111103103691a111001c41a0382449800c020411000b480d0320001031003228062034001501c84041d112943c010b9848070382040c04c46041d0304082c10042d560384140d0280c10400d600e4480710203d0b415413444da505070720340c40302c0030303203103155915800d010720b450107122410001d1003000c4d000780004809125162 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972052446 1250 972051196 972051239
    0x1060e280f0f1416090f030b1810140702011509020306060c0a0b0601170702100903260916081c0e0d0305090312030105180403021e012f0706050907 65
    0x70450034a0410103200b075040d1300d403500c00c0c03042c1c0100030426004100c42040440350030103103045469403010f448002c01d80301141c4111403405a034580503c001d40c4d82d0320030081091250308204040d070355500c05a007200c800e0a0b088120381c094090402c50640f203600103503030100c0041c04c6d081c10301c017a51504900d845003859084404416030f804016041d6840103160041000b801400503803818400800394440041303040e021610344d215500d070404d06000756020820100400382e5800d41f41403642c140f00c0c03000303003d480001440c095101103403051407204040170140d5803a41c01a04010090542401a400c090300420051010f0643ca040c01592800c482c03031010342c000d840c1d2a90310820481014140b01940c10440000d45c818401030000e0f0300c90b460300c400e5803500c02c01d2001480d1541d042c180d00d085000d00d202c01c03104640c0c0702a910b00a1040d003002040b801540304249136100b4038032032074500000a18080c0050740081c02120301085140d000345401c0324520099800b20360711902e6000e035a000c140302d2403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972053696 1250 972052446 972052481
    0x619020c150a0918230714040617040212061f060c121b0b070203070308060406031212110f1b061b0d110a0201060e280f0f 54
    0x451440c208242014005520400301d1450641110000b415088440c0511201c0b1012210300350348801c0e560b4085581c0c107100003601400502030b800020131075842100c9040000740949031203540c0c481040300340c0b410344640791180100180c01c1030303070200d9040c1c005100b40da001c1d4154440c1088500e09101c032a0281c459034040e11680c030200c0c00c00c40c1c00f018076a8848010001d030103450300041500301b00c0c850315030307182403901c0900100300c000c0c00c00c0303145075107800540440100c4040c0700301e07540c00000a00d80c4d03521070344840c1100d680364000c1004a88482c4406462840e80c1a01004128410704110780d5882142500007071098442102c10110f07000707132650001d0017500107160400f45000e00d41c0c0a45c8010100003e143c940341c01090645510b0007480c00041c6d501d070103d031408c146411600030178510941c402d4141d031500c80c1600c00030302802e11481920240c0b07248102082012204045200c070201300002c02504807002458210000e08040e8840c0071050390300c85d10a0281e81044c000c44150341000240c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972054946 1250 972053696 972053713
    0x602040906050a15080604020304020d050d050a0e040e0a0f0201200604170307020a020f0a0506030a0f0501060c0b0601082701060e01060903170c0a0c0f0306050109020903060f0402061902 82
    0x43c0481c4a103103400ca013074a44d040c5400641265030250001d9408034043d1030242c1c69482d1440483c0b12a20107100c000d06138015440201c1859511001601e240c020310b940c1c0fa076403901804140011203400c048510761981110480038085144025511030b20f0b8410f1600004101002c113282d951000e869150b9240b5820101c1072005015000200540301000408058a58185140040c2d950fa0a14038002e005000201c00c0e41c0c5c150381c83e4851308005100162803250390f0f203041c0a00200130010b40c82c004031340f40d140400100d0b9062103080c0041040c0e5100c1001d941c551110780c015a9070f480010001c0c5690f03e5a448d440e030180c5007000c1c1e4000e050040c9130020070310904040d41c201c00300d0416002a000c105901904102040c800c9244111554000025079030b00d9240d100c1290802601c6403024100603000da400040b00d5240f000c1340001c0324040c94080140340d03212100d01050780b16143c040c0b541a40f1203008035214400b02501150800e200504552a040030b070848402c610342035058031000740c0c0103240d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972056196 1250 972054946 972054949
    0xe070320150c0114090a1203060b0a02070911040f12050a02060d1a0312040303140c07080708070b090618040920040b30030d060f1e0503100207030507060204090605 72
    0x1d00003480c22010044c100d51400c1441c03240d65a03076031712000d0031058105940f0740c1e0043c000da0100c0080c0150544981d62250b03030001c080c0d5580e40ca480b80c0c2a86600e8880c0500120380f1781820789050320115100c10b0720591421034404002c000c01c2806490902610f07510000594481000b00b0000700155004281c17542002d2180f8400e07255091507a0291700410003042142004000b224181d0750301d420481d14028030081c0703075200740c0200b50044241d8491082d011030307101c43c0000c0102c1125202c40441c1c011584500d401c25141c013428030351503003241c028808950510202d04d16602650f00240c000201d0110f15215250051104041200c0d0a411a0345680302d0307040c41c1c082c02905800580340c0528480520321304070b441c40403e030250a6102a5150509c040b40401d108480c0001203c61003441800d448001e10740288139039116407181d5100105413450903001f490035020072a240203001e0110344e1280c0b0155030282d0710800c0e0481c2006001c0180400040851001e440940160000014190300303060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972057446 1250 972056196 972056201
    0x20918041e030210020c010b1005190906020d0f02010e0124080a020f100908060109150501080411012609030706061208070f110628030e070320150c01 66
    0xc15407159040070880390001c40d80001e2400d140548205005076207020000e41d0600400c03224682541c00b2180d14040b5200540c0800545450300d5030322064100c0490041c41540c02c0c4000d4850b000145e0848401e81d00e9150207524113100e4105503000108200d025042003d0843d180d000386200e4032292000c40d07895061803c42c4a0f0050040d510051840f842d80780c0000d60641411490244a1500811102201ca00c10b00009000b013403208111100c5584510394100078189003100c5030b28180d800000000d8641c4581440d900480d0019000b00d1002c034540d004440356034401d5a641d121041c413500c207629843e03240060034407602d5410051500d603481458100c05584e07503039100c041d444494950b00b4001c20351907004c07503003420ba00103140a403650503443c14144c44c40c02949400d40c422400f01d41e51001813400e240349500e0040309250340b4506c4014000c241c08840122600c0c141035800510b0920019010b00002d0b000c200c00000544460794010002480d90301c0250b12203014a00081510394039802d090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972058696 1250 972057446 972057473
    0x180703050a1506200f0f010b09060405010b07120207050a0308071505100e0411040509060f0711031b1002040308070c0605040302100516210e0a061b050102091804 71
    0x1030b611a4005032510f040200800a04100300b00702080c802c500015141040254051488101003501d41251144034200d001f4a503143c40e5a010300000000104145040d1050034180c9844000d40c030b00f009403e48803070548404035069542584601840418180d5800000400561159991560380c030000e2a0580f49440d0709060240345e50309103c180110380780c850703481030240e03500c0320300320b80c80e941c2c030381c03c01c41445124030400542007032600c0c051000008000c6441481028201965000d503142c041080302c180001c8080e8007a1908181320310341404100a000c124141560070031990607000f6006600100d90165004580300710002445008000c150f9043ca0300401c06414034500303040c84c68001ca1050040c2181c1c0000700724000941e8584a0f040088602200c6d800048494000c4c038005040c0091801d225400c1d00482c0713116a042503207140c0700765080181e07030055544005814001e85100750300d80c03104104550342e5409201507140390311030302e111762409603408040304841d0405040003081001071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972059946 1250 972058696 972058721
    0x2060f03150901121a0f16020109060507030608190305160201090b19090f0f092304110312093a0309090c02010207030e1e150901080f070c0809180703050a 68
    0x24100700040d201b45e503025030754030110f14410790b1000030041c0000c07070042600c282c0007000603250000b880340b9254581d2040c4180c0e07181c5412541c50346410603070310781054900311000300040c03070070005040994030801000030202d106040c24132441c1c0e00d400303001c0500d030054a008422143d0b031210003c0b00580c05044900280782d000800c2490034104001a070211215010b505aa99144c0340b0880c1070821100e207213130703030207142a40c030030401d0400b464106200b2071101c1e00d05100c0e105198110070020407050071a210303120010800000540c9948004803c510002d45140340d5600001d801140c2e00032a11143c40118465650224002e05041481c1c080340d85c40020001160310500c001c40000c1e0304059048000103040343c4c041c0c07041001d00d0301451850412041107410560701d80c0c02d941d4149600c4040d043d9480240c03180c0010782e40e10440c0e41c0d00010111a03a00003d0071500004010030f03440e50050038141c1000e0a1035812103800300740c0905807074041d11b00000003a075a4080043c018240d110b02d2551455 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972061196 1250 972059946 972059993
    0x140c09040302030306010c080c0109060f050703020a080a0f060806090c01080106170403120b1e040c0c05210714061807152613060506030a02060f0315090112 69
    0x4140d01c00941d2400002d10300e90501c40091503034410f00100409035240c50769010000d004a0100b494800003070900d412010904070305000100d00414001d000b03039230180d80582da5041075681c0d03155200c40544903540014204940d901c1021920603000e000040c4134806803c010031080a0740700c001400028168000410030074401d000302c1c1066040c000700ca4102d500740c90000401000c40155900030203074902e1003a8016881511100c0100115a00c151801d50856040003518200d800540710440c951340c00503d541c1060705001c004086406642c1501000ea20740c0504052f42e42c1d8468070b80410103c800f03110340e0301c10401c0124840032041d43c821841200b2015211052030180c1c89103400d0016001e0800f803103102906514915541c114071480421034000402c15810009580340740460340000c00d50b205810640052403d05000510440e820340c06002c030b45c0380c2a00c4c0c0d0100b5295800c0980f100200c1760a008082940350303542024140644840c1200402640107454400c8034100e030141c850b0103452 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972062446 1250 972061196 972061201
    0x6091a04060f0f020c03060a0905010b090402010e3c04182102030f04140306010803040f0e040f0c03030206090f06010509070e03070905070c021203090919090f140c09 73
    0x940c0b00030701c10119401424020030f00c45410340140d082603200085141c06224010801c00d041c00c0d160084040280a040200084a030140a0100200c01114040d000c150000b1040038503007440103028041140390b080c106071001b050104040610a51880c01042400c10154408146001d2044007801c1c2d0010291842400182c0da99601c02c0201c440303100c440303042051001400078020302c12140d40728400c45c55540e40300c0e102c011102c00002040c00181c000e200d444000b24810400004035001d07030360920b2000280f0b80ca03240051000600042045030380741c2e001c1524000041b601050300c00958401d4000e00028a004176443c4e20300300c0f9070f05141c5403a80c083c000400064482d1403486412450382c0c0f410b00e40040c1d922001c00e280044070741c0191182d84c0392004200c035255100000d056614800c0310044409094840d6003a81d038020805c42645c000b48503808100041e512400e903294010b00d14601040700e04482c0c42e40c15110300744090039540c10311041c001d03290f511000c1c400380c000400c04807030006290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972063696 1250 972062446 972062459
    0xe0606090f1002010e0f06010311030727240e0714070b06012a05070603020304081b1c120e2e090c062309060a030216060606091a04 58
    0x3a0400d1540750040b1504030b94490318510139080041c04681c0340c0101c5104c0c5030076055055940509200c1550904c03404503803a10b6500d004201d0ba81110b6042d01c4000c02101d00b01c48a001d50256903007a00c86080d81c8200102c00c40c100e1030712a150b244802580c01a40515081180d09601707401001c0c24200080c96084007010385462041d900754a410454082065503034000503a84144441c4803c0c038405003412074a1030346e010a00c8480b41a0b8418000e442c94650364660a4060340400e07200244a00d106100c503e41c0d003007880c04020080d0444000720313101401542c2c1100583c0c00c80b000d2190004200400c0041d130840b15000350100240d0302001045446601c07940d508044030f0f20302071000720003000500d5114a04468110754031460b0061081d900b201c0d51004050f08100b840504822401203540492007810015015210143e50140107549440100103044000b50300030703410340d103004020101c11008111140b08a0000c0e10b10344c1c0741c004406003000c20203103038124800509401c0d0041041300b070000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972064946 1250 972063696 972063709
    0x3030f180b0a11070b1b0c01080c0304030e030a060507090e1308070227010b0c150103170702120d08190905070315021c0f0e07030b010e19020301030c0e060609 70
    0x2207402e240b030440c000340c2401041c6400d00210f40d000d40000310000c1088007410768450405804d4000803030448075100700f8000156903002c4105c6219400b0a010300018000c07a020308911014054002c0c10b450a1841c142c1d21081120404c1e11010300040a4800c207200500c620121389030425101d15a41811181c40d90f103d2070716100e2070714028043c18450750300d40989060304001c04002400f4025112071580c445c801094250011618103000b48200c07100c1070f807100d841e010181d05880d040a400c418215a10a01207460b90000d80c0c00c0fa0041a00d4028040c422828020403103120401d41e80c07490b00b41080e014610f03824601203405003007503190012540000e1000100e110071a544012003103a0f1190407000b9800a024558003138404400c2d030b042e11040441a68414444449171010422001200840311650381300680801048204500700522040c41c01e461250743c00403200322407074802f40c086c049110598000381d0041b82e094154400a0214021007000503134440307415204141045c0c10000094032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972066196 1250 972064946 972064957
    0x1020c0d0806280b130801060b0a0305070e0a050f01020309060301150f020f0c010c06092909030909010b030a09020d0308101d15030f0a0c0911030c0d0506180103030f180b 75
    0x200d40750006048095001c00d03d05d0100404e075040080064907a50441911035078400e00c05180000d10300000500054041ea4808030f006901030f11480c030560401c002e0080c5034584291580c158401031181c001c2c00d54803480118042c100c80b000e201c0300c405807030101a26002c1300d02010b4003950003500c0302c80100340c00000c060b100003100340781c400c1c503916117410500d000340b462080141c0030408021151841201c02c3c0741c00808007003006103418007a92440c0809442c0d000308000c856100709003800401200030f42c4d80c0919007281d41032000242c1480c1ca94000743c14039900b140101e0115a000d02000040342c01008200028044034103047d20a43c60709817041c581e80002010012841d1440048030003c2d202040070607c4484644202d414002160401183c0309200b840351a0425042c80c901c076042e004c40205030f0b405035000c1c04029040c9616419143c02034400285072a4100298040000c146408038002c02e00850080d00c486c11b65207100c034001450183c0302c1c15040d1142e50034000820500c0d0b0074508a45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972067446 1250 972066196 972066209
    0xd0e0d2a030e0904050303090607051c051f0f031104060f051309080d021308010c021f1e0b030c0d120c0c0b0307020f1506091302010201020c0d080628 66
    0x1410461149820b032190b0740810121078005454030100b1040002c004000c5016980726802c40d02c0384d584080d0211a00d10811040b103011005600100c9080c8509401403508074100d1210b2440c610400008214560202d031300c10310708201803001c104148984c000e0106d103030503020780d018071840c2d040c01520360200d40d052040e180142c1808018100d0140700398000b03003410b41d0103052030355250001004400650022201c0c0150148110740005d0f007083c0500ca50314001007180c001e0300c0d002e40e1444098000140e550385000c9043c0c2c449400801031585139522081604030550005040304900c0c0500d454445030618007802040c0c501c6112000c602c160f140044203c0c1c6a2800360140703030243ca020840e41c0256070088034030000210a21010750740114010214904007001c454a9503c0069030050040c0103468441d000a4802c0200f0115030034100300c0c1c1075050040c00050714001da1500100d240002e0740392100b0018030300c1d40c20302c842072034203010510f0103844000c081440035005d07003e000c054803131501ca0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972068696 1250 972067446 972067517
    0x80f0c030f06040f0507021e1b010e030a06020a0306031505090c0906130e07030b1f140406120308160e060f0c0c060307020a0b010b0c0c040b01050405060d0e0d 70
    0x302d10341e440350003402d982a01d0100a015074103081078041e641e0502a00814410754045164840f44007000803104140ba102d014404501540b4100545592038440c60f800d4145c004d5184140104125000614820100742d8000070f01c0383c5141041d01440d10603100a02400342844103100c094080041c2d000350b1002d0072503030304032540c90b56800600750000304024a02071a0401d042080c000c240410880202c0c0d01a80094034180c0d41e100c0070f03001d20710f4011005003a080031202c0900c03c0e142c6210090543e5040908001405c03515890000b4020004582c00c0b40050700302400c00c00c0256607a01040504141401c4c01d0f12011b03d4040020410f008180001e1403103c00420902c5000000f00600301000780b000e4001c50313483c1070403000252a480010000c0e106581e002000040e031012100842d002e8055290103810507014400400c0040c2c21854041c1d030400a060001140320703906d8400030840a210304200091410a0713030404e0307041402c0850680c00b403141b0b00c084406100100c5607541c440b0940e11060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972069946 1250 972068696 972068701
    0x51f15021b1e0109120f0506090a051507090e1f080610050603151507030801061b08030411030102030106020307020a0b04030b010e04050a17091807140f1606050601080f0c030f 77
    0x4889104e0300d03030f0010001d0700205207108213011078410b24112250080081c3c4600c3d03950340303011642c4e51142c054000c0040e84180c0d079100300185600340458101109140c0304e40180d6803840c0e20a4140c00540c2c15513400518181140c0c41c101c0411010401030078070101509003468034803003000024815124180c0100000130004400b40c2ca10054030404010050540607002d01c40100c00e80c0d01d4002d0001240442c010b100042441030088008070321703074a218005540f041b44c65175607400b156000600100ca0f409040c01c1e00c014a0f550a001650282900da4011611005280100b01c80384600b64030951404c1d90400c02400030480d01400513042d03410840d02c020030b035100d0780340007407030a940e40001515007400720054080300b04001d001012248001c450a203070390501080c0300d882e4001c05484140c081019130801d00706d00f2109002611b034a004038030059040c440480c031500d0806c01071403001c0f641682d840082201d103680010f451034216440001c0c1d50f0380380ca402c80612540b44001342021500350f1041c0d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972071196 1250 972069946 972069949
    0x27121b010909050903030106201903030209210d1713020102071a070c0501051c0c0c0c0909061104032006090d1a06040e030d051f15021b1e 61
    0x2144004041101040103d07240009800b038403038100703008a0380000d072040620100d002c0d1804413415015210400382514101a20300c1c42200070440c9030840c01d058092001070041c0d9510862200a1070004000ca0201d80044e000e06081280003007000f000d21003982440d8402e100920866640422490007d00d9403500030700046c0d1610106d60b00c8564007102902d444c030080d0880c038010740344d0640f10b009040f50701900c0e0001541c06002c0d015000742183c0710740704443c41070030090708400604507690921005c110b905480e50a20f00900d5081000035544408442c42000100e00c10760090080408644c0c1c240f40c190790b80c2c40080d620040031108087c038a900c1c50300072583c9003801c80702000d0300244082248015407820114500300040c00300c407c01ca01a00103400c5051501a4081c1081c04038042e5291404590000f0011710001c5c2c085140c44620380c41c86015100c80c0700307100d0301a09464611030001141040000c1c609051211010b00922103804804025214410500d01c000f403c014120304025000c130 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972072446 1250 972071196 972071207
    0x60c1403041a07060f05070f1d040c02030304051b2227020111160b0c01060e0c04030b0112020108070302030a0f021308071403190f0827121b01 63
    0x8000049070350444540040226082000b80b042d1071080c13000740043c00d0081760040444004440846c0414201040300d15168071481d000180710580c0f010145180140c8408207007140c407210854005648004240024840100710001018480700f07050401441e40a000c41c8150600c0b4080e00365401c17607461003544c0210b854200c9184403083c40c07520020079607140184800f0255250040e070102d02d0309209040d5203000030846104004054004100491800f0b07980042c0b648166008200307556075450100d8816005240c20b40036130801140151214110304000385803007010ba00880c0c15498003001d020040c0d0300300100b1036001c00d00e4180103031245c0c5c41c1c61021f80a01148444110031a07c0090890422400c0c00c0701c40098a00c0b40f0121008246c0300c00340c40700150800001c0b43c0e81a40910500c4005100581d6600d08541c41800035150040040c4d80d600c80c41c2d000300c1c84e0400703224607049075820703003501d82d81e517080c0242030844160540740d002e44076541c0c0310f030b10440c0400b1005841c4500302d40f150b40100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972073696 1250 972072446 972072449
    0x604150b162013060f14031911120613020103091406041203060515070b0403050d0612060b031516020f0f03030105090c07120c06091e050606030106060c140304 70
    0x2903000c1001101d0498440801444100c0c0324803030f004012450048007801c1c4a244141c0f111111000b281c030f4144824900e40c8480e1200c0307140e062260012088510b1048201c510b00944600c600608801c4418100101c2600031201003e880e0311035010407080080e41c800da485615020700b07001030719400d2070422a00c403a0364155040220310415091008200d01c0204401c00700c2c001e543d040003682d071210104001640c000101582c4801c0c14040100402d03805140b59070054400e0800910b41001400c158050f6000d940c8000c202c0f42030044210b080c0206405401c40402c003c4000c0c0105030300048000f0400d44024040ca8003401c020300b030030500c05000b00030302c0c110070424001326400702d0004481e0641e290300c240501ca000300305400105042c20a0542940d610542c80305002c10760661f041821512556103580942d50180c4400201011808250010b056401c1200c083da140c120340d41041c5207410f002400d4640280e2516000304a0513601220f41004203a2003429086403086190f2217a2941c043da = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972074946 1250 972073696 972073703
    0x32701020705150109060621061a0903010f02120a0504031202070b1015140c0c0d060f11031311061b0f060a02031509040c24080604150b16 61
    0x68007014820001410155040010703180b8041d603884581c80c82c240e03600d501c11400415010f0035a10307620100c0301d010b41d40b0016002c0c8002541540c40c510600301180010070103008580000f13104119090038000c14a240c0d601d14029407030052698480da8030040014074074602150f8640c0031a00b014414048000c05014801d819500c4030740c282000800d12205942420701195112000103804854801e40303034122020303444180030014554140301d00380e4071840800c2c1d0076000741070a0340e0042d511303011000306290080c01c00162002900c004801101c00c43c40e141081d1107020300030080c1019a85216895180d400401481980c0030b030f10100d01103001300d600b4000280790b15607000d030f00b42c1070000306032402c5070740c0008440051311181031280c228030042d03c050100e4003684070403d11a00b00401003a0b00984030321414903040d9669005801108010b261910ba807255103804246419845511580c020004035400c000321802d609214040e0171451103103120f06a00421141011000d40481c01d11a642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972076196 1250 972074946 972074951
    0x40e040f050c0301240509071e170103030f02010b030a05210d060b0c0d170106030b120d05091215012903040809040c03090b010530032d032701 63
    0x20318010024078126a2030310028900a4a61700044a1030101d81d110300404060300ca80b145252011840d851160300440d0030b60900484d440d5003d6028100800540214003954454018010f11400242074516507915540302c1d91000c030004020520200b0300c552024080403101c1803811307d22440200c2030041d074020704045442c0030000140c0268510003414254581000d40307500c02d90808080c1c403001b80b00d09040c80380910020051007241c0c001e6200c00104000202080d910650120314580790580d40c0c1c0340d0400080c07011614001a0820300d505440ca40041000781000c600012418510360505201d02d007024424641c04882c1035036841520300e08a20340e220703041c1d540d18090400c1881a40016000c50055180200d442c0c24036200744104e0003103030f50004c00750100d640703061b080018424902254800d40024008100d4041e000c04c91190390740000324000d103480324208120b945194030258201e0144c0c40030469a07660700514102141e40c4803201007046072000401c108002c04046e0000c1003242c0d01e40c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972077446 1250 972076196 972076211
    0x30e042c0a05151b0310080a06090308150d0b06010c05070303080103021c0b18010b0307090e06070507080406180902120430081e01030803100b040e040f050c0301 71
    0x440200740740495034050300071507158040b41003001da003000048402c2c2000c0c1c65140b4107800b1220341c0100650b00404d0154a200f4060344486004d8145000140200c1d441e0f5602c0001004154001c00e07296403028054503880440101c600102e4105421000011304c95880e0383c00144075a0b00586240b211150450101d52805440b441c0c040d25420003800207a110740d00c03000c44442d00c407030510750203802c41e680b01a0200d416216071040280c0140114924003080d522051a01442d80b02004460b0003881d800314041280c18011614904148015242404000040000c640450b48000850b81101c44030300c1d1580c0e210142811002045034039401004005000051040b00300b108520303d1400382c0d0141950361041c08034a000880280d038a8082a0300604540d424002d0907802208484c4c1d101c0501d55100c16409a402090900f8000036001124010b0000c414403032a1081d11010740050411a40490310305410301c8112802c500004100600c1c0202480400c004c210003404115a6020041d0003800700c1c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972078696 1250 972077446 972077531
    0x601060503180c01050f03100b0d090b010b07020306280c09060e01030b01120c0908010c020708120c06041203020d0e06011505070c170f2a0409030e04 66
    0x29031042e0b8030001e889110324400c9140c25004100031071001e4058550920307142030740314000f40b10b4000070481c00d0009590000001c10304001c8004011310300315183c0c0050032204520344850250781c10781054028100a0188100603100020269000158610890340501510807400041d1600c58000c4903024100a190940f03a50026180004c2d11601d8482040b140b040400450845a01d40c0302c440c00102d0420701603108015503032060031190110300c0c090880325200d1035183d0a64404136150320041c1d100750400c000b4031005004401000708c03000803c1d0300d000341310541d0781d0341d403040604040e00b0a2900400307022081d000307a04403101c4181d03142d0107000061240b46000d03241c2d1002d00c0741100a068203c640e01d00c8500c83c40441c1d000d143e0048600d42d01c01d041c04681d48100b00d0031949040c0c80c1c4140f048032940d00301d0801c10f80c81a45015014502c800801c40011243c200d0421a0a4002c50a029100001a4000b42244e050300c0c0107031030000d051f074140d1913115400c03104c00d00402070b4060710f00021a01d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972079946 1250 972078696 972078707
    0x31206041404030f08150a0b070501110f0909060f030109060606020c0103020f0f09032a04110903030306042f2701020a0f0501090c0e0f0708010501020d051b060106 72
    0x16280032141040200000d01c4181500902250000c00150611280303921690046135416040f1050010042c000240e80c4081914404182c200b1100c1d10300100e105410000240241c400e03c96210701d01e01e090282c03803a00902c0768050301c0015807251490000180132521004107040381e00d20b0083c020301c000317192401c25a0007130406000314401400f0391062410309500030b000300c54058080c0d400103403a04418a60031002d0741c020043d903680c14020b0f1100b092501c100740f805081107940e06429085403010741d10070002150998401403104a0003400a051143e5012003603aa001c8401d840206410032504c2d03a50f2009070343c001c02c3d610101510300e0798031200b012502c050080c0805400201d401c1c89a001c802c0224050140c0c8540d00580c8201d4118000030103030181041440c1c4164004a038100a03030f500d120040d10550042c140c480807220405c8951203604c0d0800d504540b040c2401d07003a5504080c0000e48075051000d001c000e0190005035050041100d140428116101c441502c9880d41c42c8c850040c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972081196 1250 972079946 972079951
    0xd06090906050109020a02100b0d0204241d041e0b0705091302090307031509120e031c0807030b0a0b040303032301060906111c031b0c02240c0312 64
    0x541510340b2001250f000e0003442241c0065400342c00412042d24007010304800742440d030200d6a0414901e901c1c10005131200e005594130481240301c05502818590300460381884644d0041c150084d1525440d039820010701130090308960808007005041c170036021202c440421081c8010040102c24040102c40d0741d0101c00390080c400100e86503248080340004c0c000680c0292a001945a008104c082001034480c0c0e8820030304245a450101f10041507499100f041802d0821071b001040000203221418034040c8544085403000e00c2c2111103030089010020700d103c1c4000c0412007032580c1e070709001203503540313055056001303280c00343c03d5030b0b61541c03640340081c050304d0329001400b141241e800c0e184107030542050415040e1400d642d200e41d4100c0ca0700c50112030389844d05107008000c1c055000701c0410002001000c141d03543e25a01c1c041680c60045500036100204400810100924600103100503500d4280d4000505015080b2480450b9000100900c5215010100d01307940b00c0020301070141401290003d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972082446 1250 972081196 972081203
    0x9160803090f0901031104020702120f01060e09010504030f0e0d0209130b101a0304110301090b062d0402070c05100c021801030209070c0320150105060a0c03140d060909 74
    0x708080200310500ca00c10300c017800014011600c00e854072084e4140ba0b8094140f50f07000403d050000c0440c451030a0402403c00034491490b51521028420003004130040d43d000281003000b04030038945902c000301a006000156000c11003082984d0426075548200302042c0ca40040c550000341c1003100c1060a9548045011600003901c3d0000444401302518002c04031144d0660145040000116420700c1c2c3d0720007031003120703ea1107100304940552400d00c240040e407880340500c4442800c1c030310108040301d080f1580c880c9104028085503001920a140d00d80d59950083d00c1c05078480c0198580f850000c142c070f803c1a078001003410403d40d0850b511140a40445000ba240c000ca5921054002422b4800901002c3d4022007408040382c6054400c072410315286000341b600040a82030800c0c5188150f614103484400c66116006030055012134254403030042000725107580c41c01000c0c3c10701411414000b00c01070180060f064101d80707426669404c41c0c0c24807101100c1004110786600d41140140312920b41034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972083696 1250 972082446 972082459
    0x503010915050a0603050403030f020d05150406050a03020f211609061505030402030708010509030a110601031e15060f08061014060c010207050a0c0501021501060f05030916080309 79
    0x160159a80715202005a0354090f015828543c1081816000307054040d104400701691902e0542d520030131031014105000ca4280003240030f0511914202e04038820b00c030294401c0746004404c1040740c1d6008001c10440b50305807540410700311f41c240007603c913425a1039030b02501c090428540240c440041004102004044607104040d0b8440000c2c10468880b8000ca540410300c400c00c2d250303500d024030080e5600034401412100c0305611612440c0c05d6480554607020554800701e803030011150400c0d81401305180040061406600d10b8907000b443d441c0580020161210020688043c00700c0485100c5004500c1642441056035550940d804401244226610342c01140c002c9201100680c031b0b054101d0f003c01c29850440e9603450104501d90707015059091310b80d0740c20824603002a5040c060000d03170034060310b24883c1c281d2526001906040000b9030038003240c0422030061007201d80111041e0000b911a10b402d98480c0d886504440c0b5244402c19054a5407068842c0043c04a40000003854403c4098502 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972084946 1250 972083696 972083711
    0x10315050403020705040e1e0304181a0103180506070905090a050f040201120609060306090b060909060c090a05090f18030705030d0e010204180c031404031d01090b0a05030109 77
    0x1a00111403080d100280142c110000820aa103842c1e0001c07040c80103004242c403400c0c0c5540c0400d41034400c2c04161040300b5040031030100040703d40340c1c12401d99000040b1040c0244045c88100c2d4805407124028207051640d9003410356044040c208081c88600d60100845034242070042010b4a01c03c460f10425214a4003880000c510440e0750107030034061806512114402d40b1141d00654034880316803131a11003070750303210000103400350540141002180a0340e80015069898140141245c0c4000c0c030090080f83d11500b030229806000892950212400300d8072500d80c240600003a05007a0154021039100e1607140a0000d8050b410200500500203040061020143c03042c09940300e00030054081d01d96013040c052440c0d8105e03590081080c040b802070005203480d45070340111003076400c200d0408443d950790b00c61202e070071a0942306800344002554410300040c0ba00d90340062580b200304c0641c00c0d012020240f6200140d0207070003a00c02030b152400340c0503152007482e400203007580c10910503c0c1500c2d040804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972086196 1250 972084946 972084983
    0xb04030203101406090a0e0106090209030709020702030607030e01090b0a0f0501080c0f010c140a050d0e180a09020d12030c1d010203120903220305010b040b060d0e010e030301030b0103 81
    0xc02520180c035900c441069520402000300d05030000301118070700c80c0c640b881e64040d24070a09c103000190109010058482c144241454a444d0480d04960a100d10411088000d43d03070000d800f03a4010b91601d40840d941900314112070251070002e10050216440c1c400740311382441075402034205020101020420780ea6186141c503920100c02085d107810502c001c4511840f035208940840041d402010b80d02b552040140072580b80081c02101904d542e04400245048241e002d0341500410004803003802c01034000c41c4122540c504064501d0042c699030b241d51000b10348072040c0716508035804c00d4003071a4040f80384c140500500031048914000035185003864914026012420b844040d040e0700840c2031004026120f11113001c013401184d445e10050103074144004c3d4582d420750200c00c03100700703089500d407440c54441c0c01c1d1401180350301d00c2681001d401c04041c0e143c1c2019620450326284c40420302c03402455840e4010283d001048110303000c004004400e01c14100c0202c0d048034450f1250f403920010302c21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972087446 1250 972086196 972086201
    0xa090320010f030c021507050301062007140409061a030111030103080304060921021b01030903020a1704030605040f1101050c030304111309050607031b08010510180b0403020310 78
    0x340140c0030818149590555901ca640328003258a00c60046400140e504c1512a191020440309134000401c0040103018440e4804c802080c1d6682c80411549051181442240c4644040c000c031004084181610449507031150021a09180c02c03a44c108141e80400c41e0035800c8003c0812854025802d159101d10300300402ca0403a81200e4110f101f0311b0450311141e640c4005002c018600b942c89e852200510080c90700141c01c10003054a40750000c0421355000b00c0c0401500102411442c14907162100300710110341c001c42c03070400c055400b02c4141c500e01403500b01080d843c019604060940c0c0d281000b00000c00c090322400001080c000e58500e41e043c0840740045800c0d100d22803000c12160002e00c0030400240458609100d45d070070041805102030f46c10000301c001c499134214243c0c2c00381d00001c01d20020740d801d4404c0ca22009010080c14256040c80c4001410295040c842d8a01a4559007a0241c00500c41c0894012074240b242e0540711180e41c0e00340c041100e400c40d002c2680700c1d00030310450882c1500c162 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972088696 1250 972087446 972087503
    0x603061403150406020f18041401030b06150d020d0905100507051209100c0810080609120c010b030304080a05101422020627030607080f0405030f0a0903 67
    0x60042ca4684a0300a0301c0c064003001400455078150288150400c048410002d0f04842a1502c006229010210308100540e02c168a40401103a010401800441c40241e04261310006c01c3c3d4288440480d2030001c89030134841d664200b0b030390301d00c081240da01c0c1034441c3d04082400703400755003100c0c0000e0002042c0317811144190340c26400f0070301c10040300c6030b1402068802a440303076111044c2e4040213001004a81030307032240b403100da001508032410040b4011034000d10340060202c08004004516181c22001d41c0d500f440c0001000c007030801710b0044120402500315005509005d41a86d8689603100c448a1b641c045044d4102c1d90b0b409520b003408056036143c0701d0590303400000c9400c5e504985030211020b02088141c0344804103000d1004003813003da15258000c3c6192034410220410300c18010b850443c41d0361004540500c60b800000c00d01294a61103000305030004c00c0c2411010140d10746141041c5176104080954216501c08160030390317402d03006001d0704103ca028010f1100000f14034140f0800b040d41c01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972089946 1250 972088696 972088699
    0x5180409020906061830011a1203040f170610030228030c06030917030c0f0f0706060e070f020a0803041113050a14011e03060c140301091a030a12050d0204030b09060106030614 77
    0xc9003001c102483e00c09c1410605600c1e24054034900350300c501503410b01d43c4081d007000c3c1030720704540c0c00c01d001c041c001c004d039641c8140b080400d000024110f90010308401c4580300e03102c0049134215131202801c0000310510000f140d106c0c610400c6165620707006070241c0340c0c0c0041500c0100c82d0700710112048844404680c07080000781c80e06881c0030b2444001c01c1507a00203041c44003442e4410b2101e28001400c0d41310307003806001c003261007100710301e001000240f40c20a060049403c64010002690000c0d4158042d0798000c3c2c0c2c02015500c01d000284c000c1440c0c440003981650b0910b0402e002e0045a04940d485410440c1500001c0c1101d60303280d8201e07101c1481c07110441c03000016403e0341007000c00ca459100d83c03440790441c0341403078203241d01100080541d00203800c00190150b69401c821564440340b404402c1d641300a40c09000140c6e6a61903003180008144849014468005054406c00342c455044602855109031000820f0030054a41c540c0d80760f0901940002ca8508900411724003800f10110200800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972091196 1250 972089946 972089981
    0xe0702030702240307111b0d140c03030a030f1404020d03120b0612010e1b0403082b1e050903041e05030601060518040902090606183001 60
    0x11140d0900010315801c10071403c6000f0b000280c6505042c881c4000c42c051941135036a640100c1104160605000d09042d55895484000a5444440d21000e88544c503083c3c210721280c2120512151044c201a8400f21541e8903000019604842c40d405a00c035004401040360304201e0404c03000c0000c8035201c41560302a40c0100d882d0b00e00d00010384903181d50940406004004540d070f601102c00304110343c00030720410031000b14080041c40650b10001c03a0551241c0741070004030044c601c5c004015824401da000c00340c03441000107211240b071646042c031045d021354140b1505504501ca103000500070540070407078000300302040c0c980300031508090103014022807050014511707080c540b10126099098507400d05001918506002070184d0b024400c6c1030003450a41c1f2815960322908002600342030b418400184102d00e880d18040158917036550043d44010295200c0f540c850b548000144003160865149030b1010f06032000c1d112124402c030405c0c0615909114800290b595402e40724240e030684406500c1050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972092446 1250 972091196 972091207
    0x30601030206030628081b0301020712050f070c0f03020906040e0705120709020307030c020f07030507030f060b0d03030f0e06090a03050a1403012402061b13230a0e070203 75
    0x80d01c1743d50001086004034480302c500c001aa2060140c504c103a008009a4004281018441a4031005031000010031802145000d04030358900014a100721000000c0000c04181d0318180b660705400c90b1422604042c81c5010340e955515183c440007601d0004034040c194900114080d400c06001d04540e00501030b006c0c0c0095402c0109103d52908560002c0c44070f031187c1100000c40c1516072004601440c907540e4003003030501c100c070340183c0b0300191440d41c01170a0f403000604102145c004039000b815070358042c00e205402e140f5410302d80084d052a90500d40d00c040500080380815030158484080010561420b000320340a8190068841c0c8007200d00d0340300c0d50070086405c4002449400108480f010b6424044031681407154410303544d82090700300494070744a00101c0301c032000d49101780e07107840300a600c020416460b142074941035a0f184d0100c0a0310308000400c81802040030a00b4400140c62030200c880e514100c090f00e4580880320b1301400070b004000501c00440d9060441800b10f114041a800941c61305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972093696 1250 972092446 972092449
    0x9050115110d081801201210031a06060d0c080f01120f0605060d0b01030609021507050d0e040209060715050c0f030c0c070312410f040305011d0c0306010302060306 72
    0x1030349505a402845d56908010308a10024035102ca00f6220720a4903981c4560f00510411056003016115050041910004000003400d64002544400c610519800c554a8090108102e130180c60194000c140c2407001e5150111381c412442e5100c1c134085402c05942c1d0f640c4800d4483d001c00307500d10151034409900a0103010403e1600b00310b4209101800301d400e010f480d9110700080b8803013070b001101c0c895190145034007035142610b0b10220240003148110300d040d10658034540d40c2c41ea030545000600c103640100e40c1c00c9690b5035040d201c9a800180c0f5080d902c0840749403101d01400e40a600300840c0d4a0040898001c44034401a9011440030300d171000d296840d2029410140d030002c044200c4988600103021000800d40381c4418402c044030346900307001d00c0e05441000c6400d00408407200d8070050542c04c0310108845104814003680c1c0340000f1940c0d03001d441006c0c0545103e10707003003c0d10541c2020202440103a038003400c01d9a0441d00c00035030f4007285081c002c02d601d41400b844003a42c490018000310f4940d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972094946 1250 972093696 972093721
    0x31a0615070609020303040308070b101d010e06030c130204050406080f0d0c11040603030c03201c03110315180610050f1605010b030d0801030f0609050709050115110d08 74
    0x181380010100d0303041590320344d5000c1c0240c3c40200100d41e401c01d03840a01c41110078814160018010118105018503c00c585110407104144a0030300c0e943c3c062808034013140c400388002d001c80500985014840c0000e10310315000396009108090085180180005541e41c01040d04420154030300054407211000712800c232000c01802009940e00e00c0c48544410641e942c0e44a1000118401d0302d800e00e0406283c1005404003401c50658031000c5103402c0b81a0b09100b02080d403c90498801000c0643c1e6540c071102207005080c0b15010300e41c0380e027001081c0040d1011103021020700001c02c507201060759600e44083c8440b040281d4019030451031800341c0742112800340015181284803685594100310703510002c1c07940d0312000e0409032856551034446542e142410300881070011006d082080079540742d0f940d00480c0e00b0030343c000600b0040e40d4450885c104841404480000e00340280148034550711200300345070300c4a4948045000c2200c3c03184644411101007001c49880c01c050310350070003c2c0d8600251188 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972096196 1250 972094946 972094961
    0xd200303070819050415020a0c0603090c06030c02010e011409062401120905061e0603070b0904151511010c0314063a0b0a0e030d0b0103060f031a06150706 68
    0x1808024040401c081c03a00810b4120380d44a1b41d8000c206444203421702d252201101d402c100101410048401c002c1480038100001f1a0071030700e0005104101c11204031b005150204681c5841c2d420400c10f100509170001c401c0d4003e003030700400c0e94031a845590f50705280403487c0c16941d040840440d03c1d9030030340d800782c041c1c0c2004121500c0042500f003002c0ea5010b0404004440d184c907240c07106100c0704071440d041d40010754010380c15030040c0710f143d05042d81c8404900412074228483d035101c0ea00002246801c0340b03504010203d07242821425840108040d1640d900d469081580b0761070183c041c561310740710703004024050519003280f2000d51564010702465420300c02c14918000c034041100c0729800100cbc507107c100d8590849256a850010b4900a540d603240900343e24403190501d0004a00c00b20084200c424040300300100040c60b072400e00042e030240100d54000091101283c1d800400d0000f90300300921010214401e045041c0d460743c0c1042a1800303542498000c060b0180015400500ea6038030015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972097446 1250 972096196 972096247
    0x13020105190314060a210f020a060908010506040204060e010813140109031806080105010503040c0b12150103090b0601030e0708070902090a120218070e0d2003030708 73
    0x2890320561085105001c07482801c0d900009a40d000649422050700202d50380142e000c54186040070320340030594102800c0904844c10081c1c5101d4020200600b805551440c603a02504111485a42d81030203003801e400b5204d401c10341d500784000210309190a100703c409035511f80d281d880e100c0002030011103c4c0f40e8000d2416503c3d036a40c1b51002c01140803500c01b4461a0504030002c00c6085c40d618000b0032050448090000100020fc014406560404034250545d1800e2a040341c407aa1a070900460500499218907800301c0e000650102c110351240031103200c2d052200403c80300e204404011012251505009041c20a100000c01c04031741c070a4101100c01c141c82c90403900c0e815294840b2604103225580081d5105500090085c55414241401c02c01480400988240354020380c01184000391024640040802c203080060002406003100101004000c0c1c11840b5854452410110034000801010110944260550301524001046808155201d801281070050408201c2c520312450300520 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972098696 1250 972097446 972097457
    0x30c02010309062a020f030316020313030c0f12231005010e060a080303071d1512250c120c140601061805060a0c1104090b0a0e03030f130201 62
    0x401040c2280103901503404c100140c08103011040b0391602e490700501503207900395044440b0580c4016004000e0700d030310000000c0790513249204444120300b075100e421000c819081044102109100903e1060415900f46040d404413080d1102481001e000e60b00200400d40b42407202084000c10071244081c0c0d580d4010821101400030500d070342829604240c00c1002542c400004101540c034015242000400001024500c1c608026800500070329054009494071000140c130101141c8030301c41c8801685215128460b240c0881c560450303440b00c1d007a00c45040e002001041100310050880c9148881c3c2c5154031000d000d502d56a860300c006124441c112400d00c80d007504080e010450325968bc42d4844501e80183c0825810500050280b0300d10186128101090701000e005549400044840010090811500005482c40c05040420100b400d0315081405d00b15031408114860b12030f01e00402c40450203014558420403010355034081191a080c15480080c08140c803410058030402049006141c034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972099946 1250 972098696 972098711
    0x1512060801020a0c06110a090b54100810080706050d0f050c03040f11062b0b01090b1c1e0507022a04090f060b0307170604030c020103 59
    0x500342282c0180076968042401004c250003000080e00c9504c0d00f030300510101c1801e00007042d90060841c000d40c041c2a00c3c5070000650795000d018040c20740300300f05c0c0329100d806d11410040c0c05c2003103040c841c6001b4901c6840c004401c64550f0758400c500101c5500d00903003c030203011240e040890313040201515100c9038002022000c10000d5040c040c0c43d02501c16525510b40d07550600c0184402c5480b0182080160791804060000701c0341c0c41c40482e03400c01c0d00091180541e00e42418a080d010841c480c0c0742d40d10810000e0b0140c8440c42c03000c28103042c800d14101410800ca01c40380302c181922020040c1500003251082c061001115203c0500300807800351611200848103d1042000c488544214460543d030110340c08a10a40902815622180700d10143c90f002ca000c054100945c42c015007000e518104005065400b9242c81d40a91310440e040410740341030016906042000300703900000c140c000d0080d030001103034a00311100780307106103c80c0100a1a01d1f94454500310b4500640f500b0890406440e84113 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 972101196 1250 972099946 972099959
    0x161211070501020708073c08090306160f0e0d0623010914010b09090412020109170703020c0a120206030a09060e07051f091e030b0702070806010b04151206 68
    0x2504810b0300c549100341e40d400d07450030506204025030451000300c403100326039459100010003460b02402e80207e80d00d69039402901c1c00110500540d9117040e05885108200b20610104a8200b0308840807900e0f40c640380e820001d001c840d201081010190800e0b500030400c4002401544525000701c15104181007000d400804014000c00a9212114460300c3e43d0003030a40b161200c40c860300522121b505646401c5c40d0101082018000400262401030f800c011600414000e400c0040c049910501000940c0511039800603c0d07080060103a0051080b808903a0090400c4650038050314440d078480f484403840d9600308241c84d840148048002503c6040c00d00006149000b08a854480c1d44050f015490802c4180900b000c0080c00102102c500c0190f0005142d421420107029908400e20030040f641e800400e0142c80d141c954001000c070702491b0708100185601064200560340f5a60580d045a6a03860341c142c940d01850089417582404e2800d51003241d4022803e00700113008040000c64030903078844 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 972102446 1250 972101196 972101201
    0x503040e0a0504023a1103120d1a091303200f011a0f04182301050601050708120a0e100b0a1d271009030206161211070501 54
    0xd90110600e42c6401c2408110301c3d1140b41c80d1104050b4008080c0c60144131540d203c1d103081c00030781c071103e80c4003101060824030801328040394030628080c2c00c0f10044454140c2244140d032110362414402840d00740345580b48004201100c0340040c0043c400c442a44810030940f010781a101b100314240800026010220105100359202140103040903103040c000c1840c2d46030940d140c1c480b40c000f00140c000d81c2203200350b80340c030344654140400b5940050301003100c2003087d071a200b801e40040c0c408a41c04c13003801043e03440851a03065803030100000744900d4907002c0054429000d401d100130b01d845010701498010100814499500451101000c1782502e880015103040c0b0404143c0c0c001e0554a0304140122414005104802040d00780212300c040b4440000010b107813003000d0006800708002c58101003011407500e1801c4484a107140c01e545c803c0c090004040c0003090b40703100c100c02500501000a480c2d142c1002c4603551080b240c1c2303808844116551814008109081e1080c0c500ea1081c001000440c000f407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 972103696 1250 972102446 972102451
    0x80907090504152f0a030e01020325050c0a2d050d020115180c051b0a030e0d051b01140f1b03040f0612060b1201061101060e01120503040e 61
    0xc43d8407012107520a0b0400c0b080c0c0d002c00b84280f03c20101d0b81411020620a104502c42e00d40500c1c0615840c0d100007402207024003a00313141502c0540c008000d0081c1d84100c044020310344007560301c10145111004109468501541141d425560040307958000030030404503e4004847c00c800041d190070f946090010554090460b041c1c070075500030039199040355024810f541010800034091408585003d0030a021104603c0c16030310300e25110502c80074000d003d0360640b50320300c4007200340c3c0000c000502241517844100040640004e482000d440d00704d800c12140c0c520103d0f40020103441c0314500601e0300b0421074102c4999070b0401c41c80a03801e036400d80c0307440c01174103844000164055413221503042508002d1303080341c96150311341c0007000704205101c2c0310000070701100e140b4140f000c00041400e05010081c03900d03620845015100040b10b811032408070800c107041e80c00c5503c0c2c04040e60710444045080728214041d50751403145a0740144004c80e010900741d5400c5200310122481e0949844031a100710109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 972104946 1250 972103696 972103703
    0x406090f05150402040b0301090c03021516200103060b12070504170106050306070e0310110f0d0207060f020f09060d090f03181217031302100207180219080907090504 73
    0x1602c09000840c82c2c140586d1007510401c0f0000c0c0075070145c6840309108510240310091027050701c1240e540401601c1c00a840c103002681130040ea0840c1513040006260104454030039807800c10410b801c000750301070311a07441038455022801341002c1658101c1307034464102030030003001e000c01440002a20414444001031480000d80003269983c0b50200303041c58010041c10400c01d201000c0c01c1c41505841c000390401c103210a4500101d00c840004000011038491107120ba9400b010001d82c540052040390003c1200b244212400c01210013580e84c44012070144c0110b80150318403c000c0098071740b50000c0134000c0401e240728000790b001d00301c0d80c0e0000d00c240d022100314049440e03083c40d0b590b080011050180100b90849094160254541e80e440c61b501c4800d05400d162103022001c649840300001d00e0759581070b800781262002c0002e2901c040d54600e90303031007004040c48803407543c01c0d2198020300075a082d108007079030983c80c800b11804051300c0c1c03040001c11802d4603200e401130000f82d2200d14061103010728003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 972106196 1250 972104946 972104983
    0x1090f0b0a09060e0105091501300501060f090302220b090a06060809030c070603050c0702101805031207080f072f06030403090308031816080717060406090f05 70
    0x1421070403103140c61341640050300c54062441040300c034010407201c055100e48246040d02d4500740d0722001d2160041188400da40f00354000c0790102c00c10005902c003034140e404079110700b10103121540007100c006506000c025089600e0900da220306001191034159a580704d40c0b004a14840c02402103940b00700d04480d01440552203450402c842ca0b00645901d0704800c180000d5031030065416003403076a0b840240b00d074200700b540c0c0340c00180d060040b10042e9180c0a600819400d04074242d814024018140040c60001c2c001c4402c3e07000800d490b00084040303101c40140b520a003012002e4485e000c2c550820054076019640c20003000c800a42c1860360f549034002c500b44103003841740d000341c0603045501c2d003c02614000c020400510010035007240c4001d08582e840010143d0b2075071102e400301d8540001c1055502c0300e102e0615026400e802030369000c020344000104441b8855590103100007800031045851100380c11030804140841c01c141c00c0110401d01810300c40c46480d909036500ea00e02542020b10814112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 972107446 1250 972106196 972106199
    0xb06030a060f0f14190302090702012703080c0a03111b0706030204080c0d060f060e090c0102031e070f020d0b06040e0102040b39060f0c1201090f0b0a0906 68
    0x1002d0040380e07000d401c62400e80140030b820300259482205618400301e2240420100007202c1280c2481c0300005150b01815000c036600380808081e01900740f51107401c11040b21458100a0a250b104074003141d00d400d43d03500c805507200c100141c1d09a40c082400081050745866660085410f110003d2405c080a00e4a80c0107850314035505c541083d1094100780c00b09401040700b0424200001500d400380141119034010954039403500030000c00b4040c900e9000f050030a20009228801d9004140c410500d44c41542c0d20b0303500c80001281c807441005c2850300c150426940840000c0349500150081600ca0f109903154243c503a0001000d100c4050307000c40e40364201108110072810309000704031382c50040b10001c4d4141030074044180c1c3d0f207005071580140d048010031081019201c00c269011a542021024042c54295401c00252901c1d82140e10071101c281070710216404181304d408403810040f4a902c03008040e424038105c5030103410b81010000340035403101d10704003c550751f04000e40001c0194400008806 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 972108696 1250 972107446 972107459
    0xc060708130e0c0d0612021518040e010e0105060405161d040609020406020c0109030b01060c0812010f031b0f050909240106030b04090b2206020d2c0c0105030a0b06030a06 75
    0x1100d994001c252104181d0304d541b00142c030b81030410341182c60420601c1c0c1e101c07480044001c002d4900d501e662a400341c1401148040e003a01036225038240c6100310000d1149540305014081910815901d0f6071040e0003070050194040e2090405012030103154581c8600300350039500250995819801120b103c990018080100707640400c400000c000082c00c081905900d19281c0a0008005200320810301505003200b100b0030011100311002d440d90b200b1016115610350320960003444860108449170024401c45186603031810950a00300c4103004400c0c00024202402d1007075403400901101203a10400310780d0104094032080c6c0b4101c115581441e03506d20342c9451001419030f40340c030f05840c2c040e034605500c0d43c010901d40f002aa40c002c00c095078140d200d40c203008103d0904100c3c1c5402038183d5101203241880b0071138540120700c0c1d0111600c0715904030b1440340c1500b810401b0f003103203ca2030380e40041d9101e51039500500103142c0c440035050000417008071090229880d540102c4800309043e0352101e052100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 972109946 1250 972108696 972108701
    0x90a09170c16060e011d0609062107050c100b010c0f03020f0c04200705030f03010303050a080f07020337021005013204110a05070b0106020c060708130e0c0d 69
    0x280014601307403200e60300c0c440002c2c10301005107a12408540e09800c5d8102c15031590b008603524480d024201a07a00e0861404c0504120908000d10003913684c00d5000c210381c10310030720580750245c008070050700c0741072800b01c0c10400600c80101810f040c03020701d1600d0008582805100178880d40641c02070152103541c0b00989007040b141040d014802c4d8a808507504401c03984001c11000004070b20040e40d9600d440b414402e10b180110b4105000d68040000044101a4000080c00c100d8146840751a03a58848c1401d40182c001d080b54400010b0b030040c403451240c55400d8801005d5160340320140c911002101c0550462169a80031200c00340e40400c034126004160b9205d4a03004240e40b1241540002c10741c11255140003034222081c00d001590124610b040e52142c0c4060f003541418642c040d81d81c21035100207421508940e0081c1e600340c8041c800010b20314008a9000e985c42401001d07185010040d07951560940c0003190058070480c802e20340469001d0b600c003c00c40c041c6803424503054450b642c50a10009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 972111196 1250 972109946 972109949
    0xb1003270501020a1e0f0e061b07150504060516111002210a1407060f0501060c031205100902070c051e28170f1b10030b090a09170c16 59
    0x355517101c4407100b5a2250f000c080e020040010b89481c255448400b400140d0501a20141c007241880300d112088021000141c00300844e58401592071358002000015101800750307200300c002040080200300d6141056001f4044901d10810a84410f400d40704049201e000c5141e0051000d40d2015403002400c100300f0604454045414101c140303004510312000304146040e0000041d4888045030850803c030303039504880402070031404100003d41c4d481300014040c4020f0716094011918081190403420310500505100c0d11000c000202c031145030076031050007540451001c0e2054000142c02140560783d80b28100040f124104442c88841840810880381084480803981d000c04041118038100b03194410b00c0085920401d080604520011015810441c461010048901448101500350000d4450030400b9110075141000403a44118080d42200d070b44499841d80108000b0000e2070303440c2c0c10340061129070310649100800c0745084100e02440d0300002e0107000c06400c00180182401d407203900440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 972112446 1250 972111196 972111227
    0x611010905011b1d0d02010f02030d0c092409050906010201020f2709070c110402070f030c17041a1b0601030f2105030403030902150403051605040b1003270501020a 72
    0x11013504407002452030060000004e0520146ca024540c400703000780107444a894281c5010301011040307100c0141268030501401c005400c148101c0080640740c0007040700341440715101e0300e0510342040c0c2002088007004107941c4c110740d001c2145000301c0c0414000b0b00141008560007554003241524124108042d400a041c010300f001c0c400c22000903449554000000c4e04040150b030b030842001c01240103803041010140c55481030b00000c1007010703807011035005002d00600300d4850b02c00b40c1c500100414420b910804404508403400082e04924041c020412a0b41c0c0144034803614000c207403070508002090703109a5440f22080e1980092041e0305445803e0b004444540c034a590314150006006030202a06c05410196210315500454030780050203e00b941c02c2070705e11922569a8504143d82c1d112082c00141500031622000503141880e0040c04a031840c0207000c2c0200c1c1e90780450440c02800701000b009811125440025030030034807090000407d500800015a45000010024102d84d4044103903c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 972113696 1250 972112446 972112487
    0x6040f020c060c0304030309060603050c0f0402040f0302120f0106060216050409121101060b0309030d1503020a030209041e06061d07050f0d06150806030d05030405070611010905011b 80
    0x7103000ca6400318010f0b900402620110f9141e8490742003c070010500180010000f1303160160104c2845000100e00c0c1c076800044880038584440442400203a00481c443c82500c004102028001403400040010340c4410354001c1700d82c599195007900342551030550010300540c1060b04c0010405071040e03103180140c10256410300109285039100c07186d1041c441c4c484000c000700b0400740b1011140a4200c00010309043c0001030300c0e400c1688116072658403024080c00c94610341515180580800e80c00300b0704494008264045082c80d50f0280300307002d1700040007111140702001032000c80842d140e11690003940160390001e54a810120511100891003000c0d5090024074800c1000141c3e01c4411140100c42e00c40082c0e0700d03110394107440f20207045681c00c00595092401985041140e00c090b5592144000710100d9610349084c00c81915284001d076400340694015000510815000b01c0046500328415000010507082948170182111205e106810f1440103082d01d14101d80e50001e0203480156103808503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 972114946 1250 972113696 972113707
    0x140d1502092b23070b0c1606092607060305040503040807060e0a060806090a020a0e09040803060a0e011a09150712022a0d03031401080627030901030e0705060f0306040f02 75
    0x80c0e500d5134944942c00313241400042c0c10504103010320410494910105009003195103d0202610004950117403030300e601034141e03061030100c801920072100c2956920141041c20b0070640114040e100041c82030b074181c8003c110000b15040104090001480391b5500c414010181c8000c00000103102d03448442000303c808c060200b42c1d0b4070403c2d10354010522500041e52004502000d1f54070b0060207a2499001d1034400400090000c0d1000541c4200c0045400040d07250321385d03410391412202030080e401c1d0300d2907a171448102e9000c100b00a03c9802c00c010070700c05011040da40110159400a50b0407114a090b040440080d1601080009a11411081045181d900c0700101480460510400a10400c101140141418080c0c0e0103102150340c412901141c81d0303141d0b01d0981d41c500c0c041e1582008000301800c072450b218001058100d8041c041e101071803600c4048030045015202000c5007502500035503800107a2a915040103142401c1e051900351744034a85201000308035021070009401c1e42d80100130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 972116196 1250 972114946 972115013
    0x1050f03162d08060102010609180510020f041a090406090b09070e361e1b030414010b04150303020c090702030f0a12090c140d1502092b 60
    0x1081c0b40b041065203400362141e99034000403405400c0b298001c0508901e040c0500c0902c04040440e0010103004070308486c091003000e00c0c0d05049125000112556184c2800203114941401c0c154948401c3d041849d0b030b09040e107080014044403969440711500702e90319166150a406c1024003076038840610305000343c482624001040251102c41144681d0504100420302c419803c50701a01c1024031400c000b240624003401010680e510360900302010a8411000804601d0103a42c00c2042c00d113501195825511190707039540b0709140441621400755200c10203151740f615507105048400030507402d1210a03d11b1400c000c0c1c1000c024811040c00f0718204c5041084698000040300c5001c664107011550b5460500c1040728100f01c0100500042410800c0351030500a03403003841c1d01510090740030301c80b11742458400c01c504030b000d251006203070700f44080115440b500c199010300741005018007855480840d0860b00392102d50b0318032025031190b6141c2c60340c405108003407450038403100d1201c82c42c88081000b201c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 972117446 1250 972116196 972116267
    0x70b010e071e0e13200d0204090e07050a1406070f0f0b0a06090b01090302060a1b0c060305010303120504120f0504050d05010501060905090405060a05180102031504050a0b130b01050f0316 82
    0xb4407170815104e00007280c40e024060350341120010010b4100810000d140c4208003525120b0030310606200c1c0356507040124000034100c4040c81442c40c01003030281b80035010707521100801c100d51025542645144884008101c68201c624800c0e296400e00141c040c0c02e0036000021150105001c1341009039400f4140b00503140d14080310802a01400c125400d00e00364001c60400c5140030350010310110000c900080d009030540c0003181640e1007511800d611041c105803d004440040300c001d85100400c45080003454000c84041e071100c01035242c07039403a140d01c0d40045400720b00480001c0318031769503403001080501d52181d0404050403048540c134070b076403d041d00c6051786c0b400040d0030380500995803004a00060b11081e801072584c4070100080d500d915045040303070386201c41d132003840d8061400d200000d491401c0361b2194481c1640020203221040a425072100002c11003414403038184074040004a0f5105240800b6610812411007002800002107500502c50384210040c11b10000c540d40f0101001c4c041907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 972118696 1250 972117446 972117491
    0x31b081b0f13110708030f060f1f0516050708060108071a0a051902060f0106050309030a080c09032e02160803070309021c0302060606070b010e071e0e13 67
    0x4403903550741824401002c400400b0100d192031a82d5000040050402000d2030155120369031021104005584c5e000511002d9083d030304840d13900410030003900440e200100c5003490515660314000f070a00c0042428100c800803031034000e0311187e010303075400c00645104000c510302604000b4040c01c50103240006c00d44c1c105040e0743c160b044294004c1202c001e11845036042c0c91070340515410740122004090406921040107690007022506588008a141c1c0d01620490340a6080c40c0d00a52409103000c0c411651064003500000d45003c0070030211314a40d40400481c240134880141310800303040c03e034800c02d50200d0003030040e1070038030300521500803041803c0c4e400d609120741140716241e803070343d980400314002c06220030001e6008a454074800301691800790765041951080d0201e403850703265103040100354094200d0081480d1805401801140b00c000c01d003030b4209841d801c0c15036130140d01710b40301008103c620090b80d0004299985140303091908460307916006c4503a010402102007210100071003c0700c0d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 972119946 1250 972118696 972118699
    0xc1403030417010b06070609060c020c030c010c060605130c02070608010b070f031b080306010207081902120f010e062d1512010e070305060c040e011e031b081b0f 71
    0x1070140e80320040b00c0030b400600300104010401c0b9901d5415190180091125074002d4401c01d24141036a4030590001614500d4a403005000b00f01455458004559170050520106d03200e60b120400021540c842600c104c540200140020a4103c1728582c002d1411480b64000c1e0104112540100802e11110007214044c40d0000e00344001c01000c0d007002e95200303403041701c1120031800c500602030034807403e070014500442c4244e00381c542140e0345600c0e083d07403490b04043c984942111407842c80014030341404411011001002543e00340220308640310b00311802080c858080da04203108000c0d01c42c04640d03503040c4d40044214200c032000c02d2002c0a04581100070442c110f150303001005000c913a5103101ea0180d9039404d0000a20280700c07a84016600c5540a200840b40c521172032011818040302c5a050b10290750b041004940642e280502c1210390798441c0d02c1c005080b41c50b000e008030202c1d0700c10095031000c1c1a410b000c00c08442c0ba1019280c43e0040080041048100c59440413249a0303804101c180074240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 972121196 1250 972119946 972119969
    0x12120304060203180d021c02030702210a1407060807091503050a1d0a021512070f21050708060a150323070c030305061504031401140c070c14030304 65
    0x3c0307038003180c82c4c9841c14030802c0d2998450004402c0500c1d600250440c0c00040300c07400c983d0858131082059079a801180402584106240702c446040c51804c80c400c842c11812008031080c0410391b0300d40395091401c0100e000d5450b000301c84280f007010340140c2d280e81c114049103441d4440031310308401c800711400b000300100300700350315100821178210603504040104a85c20110848001d943c1c2a2256616060702d0124025a00481007c001d000007000785d4141006440d00070045a441550403030700a1003514088003032055590ba020000b02402016085419107150006264203002d04c1c05400d201c4010810351007810340c58428007003001854440301002c0ca040c103020075980081c584803510901d0290380e4032034a0001c8020040711f968440166000140a900d00700305a840d4002400795025030001644a207510030001000040d54000103140750014001c000690403400b00441c2d07024403001e0b125120b48010108880007480030700521200102541140000c2440020020030380301d000c5c5110310b620581 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 972122302 1106 972121196 972121201
    0xc1f020c01110405061b01140408030106031a03031e07080307170709050108042d06020301090b040213050907170726130b1f1412120304060203 63
    0x88005d042185006a4072901a04480e981d5201400710f46d030390310401d0441c0394402d10403070103207201c4c5d0a8ac59036545004001810341d01c580200c20305103020008210615039002040364016100c84245200301d0000c0010407a2500840102520310310000040040803503100d19a0b001c40e0355101e00041042d2940070048600c02070724003650340800c030710001082c0800c503a01d030082c1c28024203011540740034403030340980d5000154900003210440d4011005100b5001540111190a441034404500b070098207003024058841508c242e0380140740240102e040540305003001103120b1590340d001e040d5405c10440003480101320980342c2e10b0301642400b141d03a240c9101c82c043c030300408000e10070441a40458641640d681e0021f4640c2d00d030491034542e004111180c09803580010031602d264121480c0305502030020035907100c4002d1031a504030400048402c09903006480d0440e03049540144c0300da = true := by decide +kernel

theorem cover : BRFrame.Cov 971942446 972122302 := by
  have h0 := BRFrame.cov_init 971942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971942446 ≤ n) (h2 : n < 972122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
