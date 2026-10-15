-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4642
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:28.734768+00:00
-- url     : https://prove2.me/submissions/a3ee38ac-1230-436d-a514-9fbb25d29657

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 834712230 ≤ n < 834892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 834713480 1250 834712230 834712247
    0x1303030e0901090504021032030f01050108040f080a0c0b04050708060702010209031b0f0a080f0d0311071b0906170c091003030c051218040c03051e0907030203010507 73
    0xc0e118001030000454940e2041c03241a0046130700414500c0f803400c0115082d5aa58422001c040e02c007001030300c0b14071410f001144a018040c1d861340b0525900e1411000040500c0010303000b1a04000c21141000300284036001140900ca40040c0c1540d2134810483c02191f05048812000302000d602105200420400054160a440105040c0d441c2503071008422400c0b8050244000d5040e800030841c00d0511040d0b0104d0352220f040544211000c00304070300410030884c0f036544500001c6d48803124124501c0010f00c01d100540c455444e0900074100c02d206c00c2005070040010250040780802401c078210a40e04000c1d4000b4402200d0911031942d03520104402e580c8903c85c140b0a0313018000c00300c8550701d00901d813148287c11b40c01e020b080786411038030211080d10100d041204c161040290381540030114102034011400c5840340304001c8040101400140d034220300a010a240c09c002c04c0c400c070b08182c001c0f94036100441300803440c5541e039500061840c104056102039010751801d802d0001c4264000c440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 834714730 1250 834713480 834713507
    0x20d02010608010b0a0311040e0a080711030a171803011a0a0e0c25080403140d03200a0c02100507260f0c030c070b09031608060c070503130303 63
    0x8008842e42d44095500ba6102074800c0c580c02030300303140c0510002d512002050f101e600c0c040d00008480d0404580145080040001624400c0c030128003c001c0110307005000032011030079406840701c405c455580c08600b0140180702140c1e85004680010b9800700c211481e500014010000c0c0038ae01100500711260612000300f060180b089a100070981c0c20303000003000d0103056a5640c0300e18003455900c1c400030b145400ca00c003442000800c40c40700040341418014001450048001c840b2060f49240d54a1520010034100f03003d06062080b0003c03296401f8076120034403100081980d83c1c0b0790400808807840c110f04c0400a5000920b40300000040380e200000d080c01c030f803164130801d1030040c030034414841040600c034004c80400010401404280700308005411034080c24801c403418905040d2005090081c6504070400e00000840c8040c500e01d010045442c0b01da017070800044410b400e1010340d80d00c580004042c0c01c8002d900064a07030800c00300700212019118011440b00305651203180041503000101038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 834715980 1250 834714730 834714733
    0x5030403030b031033030206070503040308040308031603290315190b1c02060a0318030c1205310f0e0a15051c0606090204030f0c080a0525090c020d02 66
    0xc2d0317210305082d41c00f0903035000700e4104400b0b0606071440c2c0c00c02c00c050740481d404131900c4c0010b1000100180d03a01c80500040c510480700c3d0307a117a18009600c0310240044003404010982040104910181a04203c0c982e03502c03810460107556803243c010901d44294219002c1401d030907441080102280f020000005541e07401c418032a900c2d03c0b030100480c0c076140c60303024241c159040142000601e4048010010003a0034180070a60b0109150041c2c00c0303c0c0250b0307040d001f058000459104020003030103900000c1031641005400c1c4000c10b02201d00c500070302d04101d4070032f01d600f01426111030100c00382034004100c12000c102000351140c400c2030360600152040e003110b03820003480300d4501c19078403104800d8680190482542885440718001000001a016108036646400203d00c4090a000a0025601508000300455404d182400b0340300c045070300c03407405034010b8401080040d001240c000003101110900b400303c105107420711900700500b54020385030b9500c2c0c449520601c94000c100881018510380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 834717230 1250 834715980 834716021
    0x20102030414030301030b191112090c0406150804110307061115040803071809060803120c0a080103030503040c0f032a050109050433300305030403030b0310 69
    0x140b03807036600d02080c040181202c80c00400104108281c0300b01c407400c2c0000348400302e4440c040c052140341d1a80400c50401e04c801c000700030815500000c204425820305c0540e8200000e62801842e40031031009840040d08000346440072a00f40044a101c0c1c4402c11002000da611255407420064400d01c10614094064091a50a00303001d01d0030784059403180e5000158545103955208089032100c00701c80500252400d594004194101140f0440010b0312040c1e0045584403021031b4081c440400080202040480400c83d01c032026a0189450b4112903060034416100e80b140d1810700c03481740c0d01c1c2d0003000c0303c5140d9900010600c035101100b10700c940928000e036070b205900b040010201d410b841c02507501150182600f041181000e41c401201e82e00c1d581c1c1c019449001c0d61440b0300c0c1481140003d64000c0003890f909201001100008098030a00700307000035161700c5a0b141c211094803a1750009070602001000140c24917000c0d8011004040300141aa030003c40050920303002005450452801d214064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 834718480 1250 834717230 834717263
    0x2040e01120209010b090904060b18070306230f010e0604030b04110f04090c05010f1106011418070f12020f0c0a111801050603100b19030c0305190506040216030201020304 75
    0x108a91003006c0161040c1401ea8030342e100d141c0a080d0982501d5001020034800b10b040304210801c5600554290740c002c034040740780520300301c030310b103001000c400c10f141900c4c01c035035081d554140000d81c100c0c1080c2011504503070310ac800107800707005550001e0040b40002d4108010007200e107580b0400d0350412600701c0038464022040c03004490130014014002501088140031540c001e01264a035103405261419900c82c0c814242400c100003a4071607030008003c000390400300d20f0014114000326140b1f018400b554680040010b08140c0000024ad00b07000003080008080300d003640458040c0010000c0680c8d0b1030313000b46442941c0d50801c60064a0a080b046460801031505101001100081980ea890164281030800410740d00140003040c0e01c855505000071034090a001505600c5214240380040000a400c00343c2542c044071298403c25242c507040200801c001c004480d410007500380c0000e0701d0369906020800034400c02c0400f21441c1404406e0400f0558150001d40c032540c82440c2000a04004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834719730 1250 834718480 834718499
    0xc0609050303071103120d0510050405040c12080f03010605090a08010614191706160e1c060902060f0409140405120a140a0f0e0904031d0402040e0112020901 69
    0x5405016403542041040401285544c4102107001800509a51a01c1e45244075600c03154060400c40711506d440d80104070444a5081d0076000070202910244403d00d09079032803040c0c42090b8000d24078004a031019420a1000020655600300044034040303a0301c3d61078010242c0340b50401c072880ca02c42c00c0a0403001c030b010501030250004030384160312540040d400d5001000402854091a0140c1c5a640c810010b40003128000301e09008251401421036820140d0f00e0501c2207904d10b0108003842a1100442c6a544881d62008440841c003540c480842c1c8891620b440078010a1802960100e0081003112501034028014822240311b26010000c440c03481c400700c08907050440707001e801c2c2d0b0001500402c442948000503d401e01c0a4a020544070302d2000c0c003800daa810007400d54000485094040c40c16a030001251700b00c5030f008503030b00d4029180c1558000e0504a00d40203168a03260340390020758040e20b654042e03d000c0c0280304031080b204e60710349050050400403081d00760700c039003007034000000c00d4481c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834720980 1250 834719730 834719747
    0x3302030612161202011103030705120f01050f060f071202010522080a0c15061e0e15100207170a03030b0a030b01051905040f050403081006021e1e0102070c06 69
    0x114880b101400500d880c61800c2e41d61040321080e814080300301c140303401c000014001540706803d40c0d1032341c607194000c030301e40e072034140000030540b00d0601c6000005000c03560f01c0c0c0003c07800e00101114806e03074403420184501950301404000802c5005d1780d8540d07040950b019005684140d6581002001c1091452005c07004032520030b101a040031070400c20800002c0c4100000d03141e150040c0e83e02c5003a0002440709000b2109664001820000f030743c4410200300074030381e0380c0310000c00c100c01802180d4182300801520303054454040900c2201c154904400e901e0007400914010644199100100200d0710341031601d43d81c10410460000c0e20740400d00c100340c40c01c54406403e8940101000c1c010ba07003001c0a00201854082403e40001c40e40e01d0f0004450b038882c06020f880d8880040c01181c54181845e014002c0c0d00c02610350001000e05807018080d45a0010300c854a0481d18108102040310b4505407a04183e0140000302030b81001003100141300105400a220031407041c1030130307022141c0c1c3c0c4008860104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834722230 1250 834720980 834721003
    0x409150213061124060103060e040b0109050c042301110d0512090303070518010c021e0a06050903191130030a0530090c010905040e03073302030612 65
    0x141102008483e40501031072180d200b40107040010f4a23948400e9a21452001203504417883c283c0c40d0010301c41001c8038010307103412100000f40729050604182c1d80356001d081c0b02c00c0c0c030004540c2035258a5640e070f10616460f00d915002d001522984100c1c0080144690f01c20240840482903510200d803030002e00000300ca12070b086550340c2c1d07800d00184442c101d09000d200800d903410000001014400350b60380f00c0010f02141100e841810003148900c0600084035980d5101809004c02444448402e440104503a0440700c40000340340c100550070b103807200140340780d40d10068101074910b02400143d484446d10040c1181d1760183c80450b00c001c2044c1950301e1140f29400c20000384c040c04401c020b0545036a135525070b880c1c0120b4055600d0052805035401090894409219030710030420110256003061446000c1d00c400e40f0b05200b00c8240c50300d041e690340303d034002c018440e042c03014030301d60814102c1c0707600a41403000041040d507a981030350740c840180d0400e54485203d00c0f510503410b011140002100ca1a20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834723480 1250 834722230 834722263
    0xf1a06370e10020604080f13061116080c0d060f02071103101a01080a0e060a0b10030917031e04061d0303040302100f0e0715020706110c04091502130611 67
    0x290744560b0b4646c103641114203402c903071000920040d2101017068901902a21455561010391030407580c41c2d07880e14113038611030426540f59001c1805032013000f00710544000380944107548580440c1c42c18000400a04420111243c40841e24000300b10660b0300040c6102c1d01241101e034808507801c0c0707090071140e01c011610300c10509100222019401414030b50360002a0003000034440140c00384490910800322540c1311400d039241d031800e0180c074004845502540d1589000c00940c0216590040700180d0182071024026000c0f0010b160342041c1000c040041c500c001404102d0704107483c155002d001c81e4482c12100c0e02c1c1016440b2070840d0300000b6a849a40c140e40149107110210b280e000003481d003102e00600260700c409503044015010880380c00100f03005a0b0009240e00e4059009007000d84540106082000d01142c0c1d0b00c40c00c000203071414150b0011600001e010603030707140140c214881081030100301e41c000325183c0705070f0321040c800900f164000e8484400064000c800d1940b51401c21180d039412 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834724730 1250 834723480 834723493
    0x90f040611210a0509031303020f031204030804080706050702011d1507030822020a0b09030304050406121403131a07060608030d0f1a06370e1002 64
    0x42a1560010045910340714403040c03030503400d54200c1079407118016640c418122120107000100e00544a40c950003100c2e00040d43c100080640c40300d0b00d501d014400a0b02c141c18045103494540d90500007410b8002e4203201055540d0381d43c1c5040e11564006114600c0f15004030800010058000c1c01103c503410790583d540e9080340203541d0541c1039a14920707285c9820922404180c54600c0c81103004010032070190700c030400a4546480b0001407020381004008504000710a031000580b60044c0d1581078500c101035080c1c407140e03644003107880d500441d03104a0307001c0d09001c400140c412001c6880118140524a20180d940100c20701959030303c105d5646103000142030f0000c02816a2040c0d00c010280c00100b2410300d40485038403130100342e441c20382244c50b254000146100c40364190b4800d8064064080505004c180320b00085602d0140f07840e40b4144c0991000503400f500808900406014400c9110300349801c0b9004030078100081c140743c0352100c0403c3e1483c0e41d0360060324002d28400905241d03527004103030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834725980 1250 834724730 834724733
    0xf08070305190501080c04150b070f061107080901080a05011a070203030f030709170c01020307140307150f1a060d0c0215091b120d0e01111f0605090f04 67
    0x8000c000c02c5a00d50038002c200d1015903900500400c0d0084c050500100850071a900c200b20440762240c02c200c010f00084c0c0400c12902c44268140c039070954100340c190310462118100680601540d6640e10707480c410000e554800c000a02c1e001e407200758020f90b14205103503951000102221002e0042c00780d0060b0b02d5044411103040a001004014400f0701528140079141d11070302401c1d0010380c0c080d000b05904000030300095010641502c1541c801d0303002040b01040c90070000c1e44071300c94104081d00407410001c03014581001042107680d01680b14140b40140b01000039110000e21006404d9013a050030a42125502480b01000c000c171040001d000e070b840c008004038094020301c060906034042d80100140700001c500c00c1c6040c0792061003010041c0600a10540e4520094444110031900c6440000010f094283d40005c605090000350709100a80036500401601c1074070407820303256010312880001c0c800c0484158607035104004c802c10103004507601c80c0c0c00c000322110304454522015404100180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834727230 1250 834725980 834725987
    0x16080114040209061305040e031903020a17160801150512150d110a050409031d010509040218120f030703050d0b0d0503070219080705220212090c010f0807 68
    0x61000d10028001407904041e440030410b82d0b00304110101c3c4100395910200700764280360064402c1c40031000051486c1590041441c0c40540042003410b08050f40031941800031400b40c100ca0340a00ea502814042c00d14080c0780104601305401c02103400550381c40d00024403081c400300d81c40842c08107500e4041c1060340031031410a411500403c1c2e860211000310141502c0d803036250780c0c09546030280c250344021081c2e078400e100d4800c40301c0e808103014500c2c0652080200742c0c48084101c018041208940c910914640100c070140213070554640d0141c400140d030940f809800c440b50b0f941c0c41c011703140c21452a04051300300c0c0d12008118504030240d0010403403000013a02c600024040d0611500d0005114550500401c202540c80c0b04126600c3d48002800c40a51920300c00c1c0d0310003480415a124112400d0448039a102c1c280f0b440780500840e240009030b8400108401c0d110107802c140c200864440050341d04d502c11040c0c0903900880e0718010315424403250f51103000d400140f030307000ea100c42801d52134000c82103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834728480 1250 834727230 834727259
    0x1101090b0f13120f050601060e060711030a05010c09030209060d030504030803073518100c0c02090735160e040e010b043602031c090e160801 62
    0x2e100c00c0030402004541200400d03080c681d0f241c01a02c01c546001d5485c90610700d440d0381a0000e00c140500d01c0d000280d03d68808003100ca0f2541e000d02c00103050001480840d20b0300001c0e50005013a9420040d682c21415444160301048a00880301000c06860308000c0c02952094400c001e40003070001c100c2400820f1a15000b950864468589018011420703c01030ba44050b030114580407000e0f84d030301e180e00c0340c680f4910445e400030006003418038a80e0281040c943c0e01c048032810042100c2d101c84070b100d480c5006031804074591750042c040d580c5526040381d004204940303e40007800d030042d021006264080c44100100510b450480d01d80800d42c0740c0801340d00e280c10040c0048020080c1003480350282e500e80e03000b4568002c0580c400443d0000d0f5200400c41903a4141d0405907617401c12028401d880441011012150841c1c004039101d00c00b0301d4000702c1d0a1041e40032202c801c031010202090300c00c1d40e00c04160b5048469013007110625031a901c0100100500c001e03240c1c800582c0d42c0c0e005120307060f48213420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834729730 1250 834728480 834728497
    0x303050c10270f0804060f1403070f1d15040602010608030f180f030a050c0f010e0916030905030c0a03020c041b0f02010f0e0303061e031005060a0515071101090b0f 72
    0xd580607024903078600722117074480d4101500080c1000e09048005e0303042003407031000384c0171492290b045161415004182031413940c204000c008000c030a032102d5010b400d03401408032001410901040e44854070000c2c81d54450310500c0c0042d842c0c500001800c03007010050b51000070480354130500c1e100100070002c43c422500040158000b514003640002c6640401c41e45400c9445140504000714510041000c010b01e0304003614140314080c8002c3c082907035001840c644c4050440103001c4407210f40c0c0d50485c0209940070b0000d04a1100045512840100180030b2214510039800c8410640c00c42c406e11007519900000b252051a8040000800b00e0150094285901d20740c4000614140c5050040c415500701c15520002d5400010038020315007800c03807000001e01c0078000304c03e00e440101d8021a45d280780c800d542420080d65240454107076614030f00c48000600d00108000084258401c4500165224200031074000700301c1f009140c125400740c0d810504480413251070905050020f41e8211566212090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834730980 1250 834729730 834729743
    0x30605040507050d030e0405090715030515060f120c120601030e010f021b240f0709090207060b040f0c020d030b0a050406030b0720060121020a0303050c1027 69
    0x7008102d84c0c6404a140b5440380c0280c1d01c85164010f09001c2c00b0803210003408882aa8004c1139046c1f00c82825032081e0725120b1050310300054141c1d505480c0c0307100b802c40364524135403001c40050780038518007a28002d852503065421071503400f900d80310304114140c803510b911030645003c1000003c030151302a905c0000020410400410038a002d42000e9080341e20205282a8440c03c160244031a20b40421000742c0b001004403015406002c1100d5454088400034504130200303505200050311140700b40880b07c01004490802d54680310540341c4440035148040c642c4d4000c918010a40c0c0c2680c0c5a030282d903500781070300c1d0042e005900c0a201c045003d08001c01c00344e0b0304002060000202902c070f611581d4010340c000c03d0402d0305404e10702402031103629021190503202e01c001d600310343c0321400032170140d045407802c5529134a08007030f002c100140b00d40b10b43e2000e50312812016000050541040042c400c82c0c84000a0311a0b09608415210454101e02d064601c1d0b012141001030501c60903072044d105090150b00d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834732230 1250 834730980 834730993
    0x6090c0108090a021f1d0307030b0702030c06040302061b07020916180326180d2901030501151404110f1c200306090408040f1410180306050405 63
    0x10041101c51441c1c1c5100e02180481740b07040598658895a2061b007400501908060040c8140000b56190a540030140c0300003110030100741e08500030000c030b44059a0750b809685403840e090401a450301012119a0300c180405100001c108031108202e48003039500502803000c3c4d45440240801e50480f000e00f002c144421000c1200e81840040300a10041d40b00d920303022107020203070024510328520481d2030086e01800b80300c0100c881c0c0145540840341003050b2159030b1200719900380100c2c0e0a0312981842c81584269948541403080d41c607005050341d004034004e118070a02d0002e40c2401c41450720914030b149040c3c5402502d80c1c90b01d0f0308031401c03110360039880c1414400c002c7c0e03000348940c3c001100d00400100e4466009031701d9030180924224050012102000919a520140803501c0000d01384ca10507400c9a00040800c440801564040c020003404041e80700c1d01c50440c0c40c0110030030803407a442010001e5843c2a854858050912400f030010422a140385c03455480e4005424050000c80f17490142d00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834733480 1250 834732230 834732233
    0x16080612070315060f0807091e06060f110321040809090108150901090807020405071101150f0e13080a03021c1b0306030b060d03090e09011b0206090c0108090a 70
    0x1040820051070080385043c00c918405898042140c076640d109100036469060100021000400d0750000c407800c2a902203400010700000820080304014403400c2d4918041003c50800d038001000d040706003a0380c5035140036141d5200b4041d81c0b40200d0f10f0f07031110246400d038070301d040b62018103103a030f04548240500c50030014204005000951300760030001c610391012600e180391510300d208142d08074200c81c00811140a15840e108042e00c120100680140d4031480441c0c0d210b4450a009000c90040310000c01000916020002e0000c206110302d000d0015003043c0803d1307801880242c207000b1000c880381d1101210049e41c1c0c21343c440c2c000f120031009040c2e091020598102d024050b54481c05929400010080b524044880015450b4400c0310101454841c042c030014050024030b43d00710b54101d413406510461440e040703403500110b401c09a40c090b42d003c18401c3c50001504480d8101d41c4500d01d05044541a00040740d440300102c8035005180d10103603019070554060f14074241c2290500041d0b03452001c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834734730 1250 834733480 834733483
    0x90c0913080c0a1b0b0a0c081c060308030601141305010806131503030318050d11030d1119170106210515040b0a06050715020c0d1107060816080612 65
    0x600660b0101c00e0000ca01e152401032202c501c0281450950007401c6c01c59913040201001c000510050000d400011314040c103002400303500201444400044c0101600d07403400100fa134009580143c082140180d201d0200341e9000199a00c81d00182024000c00749030200440392018041c0c03000d0b81103040145c2103030030500070780528001c068050301407180c00d502d10310380207084916203c0c40f540518001c1d8000c000007140402e4801d003204003441d142280d117031816445400c61090095101e2990f190075150f428070004280604110349500705030300c0d40480e40000940c1d0015022810415607850000140245802200900300c0070300e01c2e82ca40300d140041e0031081022100305490103c400407030070340c80b10241e26007070280e41080c58050360030283c40c5203410b10241103030107144030003001c0041c0c1082c00349075011a03605a0b996a400c950884440507103545d400380800e40340242071801401414030225406010314a0b0700d0141018404240e11241e005804441c110b90140480d540000301c0b0007007503d400c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834735980 1250 834734730 834734743
    0x30b0d0b01080c09041a041b23030c03060a0c0c020d210302160212010e030f1206010206041a04060615090e0105091003080c0c09011d090c0913080c 65
    0x30030109041954100a041450881c45900a43c401d541030402c0100096403040c03121841e283c0d00502c3c456035129490803074180350b1a1010103811a00e1450700003984a500242950f0010140603003010005c89203090507100d121007405641c0683c04100418070481c101d50080c041c1c810039143c1146460b07001d600059030300d00a45000e54100300e00c11a40b800c0c8000c8540131403480800c9080441c0381c0503084e0701100080c4020800a40300300d468104000307080d0801c1d04407804030090102900e070b072600c410b1b07000242c680000c0900031a001381b610002d84503500001e000d602440d005841182d5030420721000d0004100005d008807001521400d000410198002580341a03064940300c4601c100e040800440c00c40d01c0503803046200f01001d07000d00c800d80b01194080c2d41620380048029694070000481d5071b180400011542d83c015200700d00002d048050740072011a0305010354000c2a41d900c40400441d036800005100c039a02c4080e8001085064040000381c12034a4070500c562800c000b030307110314a400e000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834737230 1250 834735980 834735983
    0xf16030e061c1a030c190308041203090f05060304060b190b0a0e0904111215090d030c03230709031a06121204180e030d0e0d05210403030b0d 62
    0x70008092009401010f002d0011404001a404203140d840c510000307940c0c1c03c04841c140d000e0140f511a1b4107050082504041c00703103800801c2140d5840d540c800321280007000c090240c001980300513001c5a004000d140701d4080300c13070050a1a0541e141e503181e482c01010210300c4144c2c0101121692142803600e01c62200045c0039594a8a0716114180380103005a0310813024944280f03c150204800602d010031507468025042c0d800a000501d18240540f1700001c503901c41302c1c0c800c5c60004000600c04d00041d404035111180c1c0c0c0502c56403841075016800c1d0340d401d0040400c4a4680d4014402450300384140750ba22003003a10305014038650700d44408000c1c00b8a81d05981d41c0f04481e1003040b1150a205036140c0c02110380c1c000500c01249158241030050081e801070011105504006525450035904600b519000050070350b80c0e201c0304100408014984020700d0122809a80102c59a041c05102600d6080c64285900900900b800c3c403440400d100c010002c400f419502c8400c507426844595201d01d049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834738480 1250 834737230 834737257
    0x403030501140303120a0f02070f0809041413200a030b090d020304030201080c07020406030b130b090d05070b0c1315020f0610170a051b04060b0f16030e06 68
    0x794103120700d1407400c00c04580c40740e000364410014981c4020349621101e500401d413840c002480085d00b0500b00281c42744000142c9070115003c20f901c1404004001080600303412541041242110715040303045140c00c07143e101c1052900a82030010885d07910010341d80289600d044954428290001034542e99a5001641d00520503810400c0484041200c20207002441c0011400c4c06d15540c0000c1810600406500300804003203564030440d191500b01c1e070083c551200c2c142010346401c02c4240d11590709048281e0b070740003100000c40d030808004500f25080b040c00fa5a80d03450907110b41c480c04501d61002e07119000c0c100c0c00300310952182c641c2c14502c0000d041041220601d48a5140e0300928000580c4a01d04558008006100c4080c0359185081e044a45903110000c49441c40a0f41038105803440d04090481c0c0074080941c17944d6181c4031803100052200b2242002070a468580c804614025800040150312080001c2001103554441412443d0302c42d1420b4600441002c000c1f4140350007040708060359 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834739730 1250 834738480 834738491
    0xa0606090603030e0a05030309010c0507030b0c09030c01090e011512021b07090212010909050123010602120c0709150b0d050105015711030c0a080c010e060909040303 73
    0x41540c0315001604c50041100d0249440e814080001c0d1248104500907050000713400305401008020f22811005580200440c0c26030300d0841454091a8844414584280980f1501c4d040755030003408004203880b0010080e004903800d1004041c041c00b12184941c0500014110a4841c070b2130301e0008000e000480f00300c15603140c5c64409000d19000058010407003160050200b4900d08000c102a00c1c1107400000d80810b8081035400c00318010240761090303081c1c00c28000d07040301078041040c0c002412608954200c5501980701e0418506600518008111a03044248200902c196070f4000c00355604086034100c56040e621916003105510140040c010b080c1c0b0748004002c15a0041c4000005400b0100b425035500111008205240800304041045121001003035040012890300300365100e4180360440d449041c642802c400340c030100b08402d0300c0392164102003541424281d040e00200d50415008283c650070780c10054a1f0f040240c032807644c215006002849559880003591801540a078030000344 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834740980 1250 834739730 834739733
    0x103050c10140f131509080601060306051c03031803020a0c0b03010605220914061c03020d030509031603081f230409050313060e240703020a0606090603 67
    0x301240c1c0685034001d00034000e05481502c8030800c01c075039100703002d0010780380d680a4102c8815070a24181d00304460b0007581074070b0b000702c00342c10180c01400d071142c0324105c0c1c649aa0700d28080b406c5d0341e001c0c0245500075100b402c1d959040a0000080380c111882410089821409052424503203001000c080d00182e0ac00304460042c40f000780344480290881181592441d81403a001401c20301c01d10110311144108040401e81c00b11765a48404060030003e841030124112a850250400b40103803480744c1700d4040e4405034081c00344440b800e1500c8541c1a0041d0030104200d04082d001040d00408980d1035000410540200b1480c00d1013103403869110303444039521402c011a0418540340307030744c50210820302142c0c014019040c1642410088100c440305803401120080302040143c181050028154030011403805411940c9150100c03d50b03039150380782c1100c0301030102002150101d4941c40301007125100c000070880720740c2000406103980a40122516101c1e40c2e80c918040310000c1d03200711390300c1b981e4040510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834742230 1250 834740980 834740989
    0xf090f0a060f0f06050c0c040e07060806240f04030203010c050703030c0923031e0303040510021801110109020901031b0b07050c21010903051c090f1502040e0103050c 73
    0x1800b0b442c81c00214450410a04002d40c0700c07940182400e010000c50b400840703c2041221625946000e030082c0b0010039002208c9030b49400c1806243d0100b03140d40000395882c10000d680c882c00403113a0480b013104801c040c2c00070700035a200200f100c0d21440f00300710200250320309015404804030265115a903980c05800e0040c05c031815480e035002085248035040120540001c205801c580210284603418090900000e20b0b00100110303111241800072049048150b0120182d4460f03070041080d01c3c4502010b1a40070101d21640440484000c80c0c03c1e1141119403040d10020381e8001b00c2c00001600402640001d00051802da0080307500c002a14240c80d0f00c1180104500b0041c000c00c012103080140a9a8443d22080803078074803801040140070f05a00803201103004140c1b40d403090000c0020942d01e08008100358041c2c02c0c000c1c14844240a4102003031483d1051000c0c5641100c0901245091580e82c0d50b1801603011400145540900c00440c0c1e0415550585009601c00d0009022010550f0b0502 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834743480 1250 834742230 834742241
    0x11040f090507020a11030a0b0f0a051b071101090b070c171b0f1507080d0c0f02340603140c03040203120c15160306050319020105090f090f0a 62
    0x84918100424454103e80010300904069407112030718030310b40c2c60741020902c0c049100c400649144004c40c14024405002c2103240c0c0901c0d0f5105092005940740750a18810500800102403080c2c0b0411540d0b020400ca0315280449490525115940301e0303803000c3c1001540c1110105403001e410105c410858045c0242510342145501009000f20b010b0882a400c05a92042d2180340541520261130700c00b41d40d010141d00e00b00400d41c180c0d9864610f141001201c1d81c010390f845501c4a4603181805000f540135035104c1401007040c0c1e004240041c50380e103140700341c60b0b6144400b100c1101101d100340c01c03007101e10314014090955070790000760006040d403654140750700140c0303010190f06080080c040541c801148200d841c3c400c60518a0741e810100c210685170540b03042c69205101404000e011425500c1c20f08451040b14682d41440a661580200344d00c54511603884a0b400b0700f079004000040d401800170b003804a90040c40d04440322200030103e0b05003a02100c0380584c2403031204c1003000900c040c1c03050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834744730 1250 834743480 834743489
    0xd140106031d06060d080702030106120305030907120c03031112040b0d1d0307022106150108090d0801050d02060408010e0d1b02011b05030904060e010504111e130911040f 75
    0x1c1810b404c040c00400d5100101c01d8025240d40000201e00c019034609400c0310005003d2110300c5084000c06050040c040d8000b0344d0019a28000c00303800143c0c508074001d0721100d094002c510484003030f1442e035095906100f07000c051801805240f00e4105000d0010024200622100d130000740c0c0c811685424800300c03241e629032180c4c1800c00900300011500d0010940d001546c0c103980994480c03245402c0440680e0b000707001001144aa40c0c10800c5d0a28064181c0d901c06000703880340d100d90340f10b1144660700c42c24240480300020b0302e104010896460b20b482e0031681103001400203441c00c1d840309886030958480c3c0026110300d900140360111241e600c80210310602011403007a0070510041da00080c03030b030702d44040c01c0004003401e03580c96801c0c08014000c81d15000c100030f0041041c5a9244a4100c40460074403540f44914501403c540c00c0c03003c450110b0301600d41d01c0c84800440b5000f070394a140941c0041c0d00320100c3c000d010b01c02041030405440f92400108070341c0795440d2104d01c1d210070001ca61700340307800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834745980 1250 834744730 834744733
    0xf140a0213050d11060901021501080a0b07020d0804060b0d140105010806101202010e060408010207060b0103050c0406080103170714010203150a051008280f0605030f10020d140106031d 81
    0x4083d07000c1aa00d90151028080c100c5446513034484810040740f4001c190b00c3d080d10303028010400000c1c104c03000989005094450600c107595584c801406a03141c003034844404010481c8000000c1c0080c036580d03c4402401002080710b8100b01040d11094010070001c0c1c0000443e03950b50005000d544010000c1e1503000c00d42d8641d120302182410130310303d800407644100905100001e01408420340c2c0d070905503006481c0c0ba0000f152900c1581c03d00101030540064954042840c02011550b2055113a0444060341d00d29142c1c07500396460741d40c0e450120b800d10700000c465032005000220008008648040003428003400260b1039082c100303101c1d4030320024101654880d8000304030400c01a100c088100070600f41c40d0900928680c0c3e44d510041d109070b005070201c0e102c0c1843c07a2082400021640c00b0101c4400e40c0042004881c3e101e0b0181075540d083c100090000d1750199441c110040d0380354000b0080005404004500181c15107903405181300c00780c2000740820f841d480380041040c0240c0e03080130321911100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834747230 1250 834745980 834745999
    0x3020312040515090406030602070503090901090501150e03033108060f1609081009060b030106050918070e13050d021204060c0807080a03050f090d080601030f140a021305 75
    0x10003c0c07106000c0d081006404800822a1402035a99506c52070055170810400e548c1c0e2020303450056103a41c004942c86208a045800118503c0918803c1c10b040e83c50151010880c00f8450500750b4003009602080c1ea41880b08000030314262200c00180c00c8a86034030a43d02d0200610310951309207000c442d4100c04520f50041c003c0200c100d9619003503075000b03110109541d008411500e801c07124040b00d9000002503101c0c60740350541d9040c055000400160242e6000c100c044201401c050030b841851050560103034051000c1905450040c0d003a4150500c0101180c80d038036621045101a9401216400f018021a19100040c800d050002400b40d034042c1c030145c01f0509405107100014003a82c06140f041104441401c401c2040c180101c880607600300314a991100c0421000501514040350100134100e007040116a900c0400500d9008105160301d45902a070707654001100180618680a0b440e140c5550307800e0701501c500c0030a5801145118809a50307031b8451840346941c02520303400700d4060000d56 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834748480 1250 834747230 834747239
    0x6050306070c0506150112091407060e0a2105060124081b0c0a0b0a020d062903060a0504050a0f0605012a030e120109021801030803060904081b06010302031204 70
    0x4c14110343c05000003400c0c488080c01c160048a02d903402c91484032585250009000a22880004110380310a01d0381c121801262254021114010811502c0ba00080b6048d0244038920740c0218201e00f084000760404040c901541b1480d14010b02a48658484002e0001c061b6140705107010f40411107e0300d0a01d40c525052040c401d1016040ca07a0603845000340100d28004a4181888911061358000d0030b104040d040c000b40110007507000445040803a4900340000400500c03000382c2441c5d6200240c07a44c0007040304100ca004441c2d000410566104202080104846c0e0b500d01c101c9024000d00c000000d03032181081140c20840b91140c000605025503440c501e41d00014180803460b81c00b00c00698040108603e280c2035500c0c00c480308040b0b9010841c214010b0b80b07040150721070f1051600884050b0781d00c240d0b00c0034a0130345540c21b000c098a038800c09c03c00107601c0c1c02c200ca1b0017904140b0814500345842451a900030340044c00c01c000300b80a41052004000f0340c40c1c1080394020b40741e10a25403a00d0140350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834749730 1250 834748480 834748483
    0x307090b27061002240105100809030406030e1608150c0405030a0f06021201031b0f0e130c0305030d090b0a14070c14190302010f060302030c0f0a0f080106050306070c05 74
    0x1064144a11400c0541c2140f00c0d10920801101d014a005101c10114904000c1103521070f00b405018058590140503c01562254501034001d2244402640c0b400d410048114058200c0651750700751845000250030b112102107404d800101042006856442d070350380c4130b0720b01940d0301400700130701480140f01c2800301d41d4005c0340c0b007004103030701a000c2c400072400e07032400301c0c06402030b0780d0407030004109080000700f030000c41c00e8842c0b010481c243c540000f10791180700c1e4000c4004240900480720500c14005822203d0002200c0d182d40c0c012151060300325a2590368910316401a11301e0102203440c3c80e04d10040000c1c003c8900e82042c0781d01010702c11103412003601041c90f00002c00c18010091040504402d12114007480d201c2c141000b42070303400300c0c12800100c03c488a2446e00460066290008403a0421000d110355410b880d03004000d410751f0801d000c208802c101000f5242a44003080301000a42c243c054a006c4009000e04070000c0b40d228944800c15080030307002440c01043c064404101d00001d0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834750980 1250 834749730 834749809
    0x30109020f041d03040e0115080f070804032d1106060d02041104170d08070804020a0303080a0b061b120f030105310b0a0609180b06090307090b 63
    0x825540096410750007814070140f01902c00103402940000500892159402000c00e81600c204e03d080c0041c1003801017040707070010002c55101030b0070512100821841c52041e0138944e0001c1c003d00d880e2090300da8088001140100303a141811507585100e810001c80750b000040e501e881070305040038003e03501d001004074100c6240d0080080c0f00342c0c1c2e42e49101945403d40c1098074082d0005000e401c400d0000d980b121a035504a035051a0081000c200c0043e6001c0e1241034501d201d2075018100540301465645c0544650030044c028a40d19900d41c082d100322038403a24043c0148502040160440d00740c5014a0360821580b000101e80c014020040c1c0004070400e84101c904599098401e010200c500e1440c6003461444c1080c800c903407000182c140d94480b022034020943c4528112128020b1555502303083e503100c0127a20402c0041401821042d52042031039010000c4010083d1079589840082e42c00030b0300f81781442d0844054a81c0d506410030f501d0a00460300038400209a083e21030400c440e9001d04602c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834752230 1250 834750980 834751009
    0x21010b1201020a320a0c110f01020c090c0c0a0503040e010812042106050a02070219120206030402041b11100c05160203160b0d050f0c030f07050910110c03010902 71
    0x1844420741c0d002043c2030409442030384514254a45d200c000d0418000c080c03d081d03000c2510b00f0500005085c2040c40e01111061408005070000c0201c2080f4078140a509100241008850003083c840c1d80740203c000c2c0440d0f60081d1040f00903603682c0c2d040c58403c100c00d00701a008520103900000d0703500b10300c03800a0b044a0689040d200032064017005132607100030304500240c00501050510080c801c03030703001e075401605a140c0300b254040c68441806140e1600c0304058843c10b40c401108425450150504d400215005400608003084051589000c3e040c10103500040800142242c900d08441034800e00c41541c0c980d048071030034007800498590003032440c002c0d1140d80543d10065000c0c04210343d0200400d541804100003e074a82c1076549ea021030742900001d1010401c14100740001b149080e44001c464030400360040710b1407d584035441283c9207035400410710010b2080810207054286c2d16201240c2c4010405e54500c4440002d1084281c2003164074110310b4041e0b0b05040007c0d0041c2c1d03600903554042d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834753480 1250 834752230 834752267
    0x60c0a0c1b032321031503010f050c1b0601080c10110d050c0705060310170a06020d0c030b0916080a11070b04020922080921010b1201020a 61
    0x404240701c4410342030505900040c00300940d803140e20262161180c039000360200c0e00050b00c0015103c050754060900f90403201550f030380030802c0000c0000b1503050170301505510185c00014018034554000d411114103641c0984608004201418440c0d8942036604186c0221006003801c2e52401c081030341d89034040c4000c1489030940894100b21180f2400c0c42c99604d600356421140c00000904000d04543d0108001400314040c8080102d4241421422a40190920148503071100c1c030f0400010103888208040c80803c1c051030780c2641c046402400641a544040940014118030410002d011240356400c0240038071100c1040110f420740414404400040c98200016103942e0146403c00810840918001021000c524802440a1440103070300c42c5109440d45c81060f110504255250107002003070b08000d91001003644001050740d0301030164904080c04e40705031241e09005140040707030351441407480c0b81c1d5100c14000c540d1402140c2001d8840240b03000714500b000c804400ad103030b2080348668000300e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834754730 1250 834753480 834753503
    0xf1002060f130b070903051b060412030306080a03110d0819051f120b1302060d0903020c130504060606030b010f030515030111190306180506010e030303010b04030203060c0a0c 77
    0xc144289a80b680d15070740002034051a10300000058610300c111b0005036618404c81c0380900002c0040081c6800c5800300034035090a141c500b0340d42c07410500c132006c0d0031010035450b03110018141608004200c44a071194488000b440a806040c900d0111011030300410407031040f060041c090341c0c900029140c180300e44404107140d0f40d001a13030a40f0a020294100c01400084400540d454400c04130802440c03186440c890580caa140d6010f010810016010394040360401c4102d2454606500400c412171090040c3ca2660000f031000845840c810001191031070b44400c208001c2107a144101c00140500d801c0030044040014002000200ca001011303040c0744c0d0b640c011414220303e01100480240d401402484000301c03041d4212095081406007500440a20008050040c001e00923201980c1070405042091890a1050301c060700b006000d150600c095a00a00e0b60b0b41c500340011400380500704c8103180d4403842c5106051414800030003001c0030720700034004000340d0341d486500b1015151b00a02c03844c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834755980 1250 834754730 834754741
    0x907050322151d07050102030318011401062d0519110a060e0616020a06050a1503080301050a0501081e0c0f0403050c090c0a0207170a06020f0304020f1002060f 70
    0x2044104240040d00680d0b0318849000790704070340d0f000f150414000c2c03103070745441800440710700ba91842c480c003511340541c00030710001e8501002104030810804607000007044403480520781002694080c0c2026000507003100b011900311903010070a0946114111031800507190700b07203009005025042c1c02c106000100c1800c90195072103489031003d04290081921484d015624190f8014010301d8828900fa024800000d0790306c0400032580040c0b14826005000103200c40c0ea604401001c00800d0060303c21b82d5810b981080e0542e050b807810185102d00c00c80740e900c0d4142410030201c042c0d154029410807810b0740800c40042a03902a01c02015a034113001d40300c5072103101c0144101d0080d48a00c040454020400005100c8005a00d075910b090944403400c9035210031001074158400c80c050070004d688030100070020207030b80f00c40308551888010140c0c0e250048a0361903034181d80c01041c0c4407800d200d000c418030003035187c01d035042501154101e42011083e421101c0294482c400141007841c0106000c0c001035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834757230 1250 834755980 834756031
    0x14150f01031413021f02060a0906060b1201060801080f120a0c08161104381e0a0f0608010b16020a030501360212010f022709070503 58
    0x1141e801c0d5401d007050301d518024010550000807014240c5c842d84030b450f011024107600b0262071051100b5640505503a075140410300000e0503440508a503c2c603503420300081d14000380806403003c91201d034a450540c0d490888002d00c0c000c4181c0001e5440e40144000504030b21001400c1c0d40c00c3c030b0f4648a80c945074000c610307003520a40382c6404082c02d07055000504039452540320b418052000c1c0b0441803410505465010322045074142901304d0000c0038403203514602d41040c01c0138039046848009007160b13143d4a160200e011441c005404003c1072801020b003000510f4050040006001d1680394002c2c0c452520030011712a040621030030b520010001141d160094a02d04c4411810f0340142c413602440703a9030f2a041d80207204910900140860907550401031482c0b07207080398400701e503050340c00141c070000c0c1d02080703529581c500e2070190070740da91520b03610403845074005401f50103100310f02c2d00003032140000310103500e01c00c00d900c03a8498208030302002171070b542040581e5088564007640200d000280003506 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834758480 1250 834757230 834757241
    0x609060c051005070507050d050708030105090a0905030d02040305190c0b0c030c1c0e0d02061b010b03060a2a050d09080c01050901060f0503150403111011040914150f0103 75
    0x42182e5400d210811200f1074101004040e01441801260303a030003102c210440f06401841c0c40200b21540c07c0004004500c0d24404240d0010700750301000480703180641d9010318551103823201b07900c4550081402c1003401414080307a54584007408a181c2d02e00081c0d5540402d020700c4d809a40290b11010030305800403d0100f054609a14504048601c8030700440c3d80750248000158130400000c4419902c030075682014030001c007040342d0203000541001401841c8807a44a00c856090035199610031240fa4541e030204079180c0504100c0900003500c0340111a60100400d85212060b002c20311003e640c04107e5014048071485440e2800c000385d508594504400380d8450040d4403000c640c01d06040c4222240306520120499043c240c8001003a582d410074191030700000400446443c0b804400103000c00d006003200482054400180c44504141448800454245648500e4040000b050130f208000141c46963b1250904210241851800100003083e50501034070b160701890b402c030550071959000344c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834759730 1250 834758480 834758503
    0x1e0e0703022107080d0c0c05221a041d0c010f050703030519090b09010e07030b01031b0f080c011704020f0d0203070f060c11060403020105030a0225030314100609060c05 74
    0xd448103104150345c0108200741c16401074550003401ea10018451030001a0550404e040c2c80c2044258a401c003070480042c150009d60100442e105c44050b844d6070703941d1241840c0d601c1c1031614120113100d150025442c00d4803401c207482c1800189000302c08000e80003400d0300c40721541440c02203815680d85150303200c00081340f19a02806405c150301403040041d8101b281c0c1c8660110002045000b80c002881a6110300a12001d801d610407840188046000202241010b40106155036a0240c3c3e55801203881c2c1e410303901001d1a40c102c1c0d201c501c00c541e0701229516080b4881d04407400c43d807d0640000d00c130440b641c2c0c400c1e8400c0703400c50001b000715181441890002c00240242c100c03c20303554080a400000d84034021a481e00800d035400b070b1246080c01c240d500341c0750180d4a41d800e5540c1c0000e03082c025480f80c000c100400780c906d00400d12180c02d1034404142c0b140300e958041014040c40d4100400108007a0104010681440741030011301d42c0030010504407541c51410019042c2d1a0811034180380b1030780c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834760980 1250 834759730 834759733
    0xe0c1311120a0e01050708010b0d0b030a020a0f0f0905330a080a030801090507020c0d14061509150310020f0c15010602160f150e03011e0e070302210708 67
    0x4100b060100c99001c40343c0c03102c000740280304d00d50300c0d45d2041b01e050a09028640210300140000c54881a095100802944020382210000c00c141d8002038620b6040781d00c4641031001012040c4818041c00c140000101a4100c040c080e5050030100f030010601c00403400070140c110740050118182c544080b0814044d4098403a102060f2280c5040751078204048068021825590000030311050700d10a0a114103801c0d4007408407004070004004060000c00400e4070000b50000da445102d600500070306010340d1040c40c51041d941212001c0c031020070001400940200d01d5510081503d480108060700c421120080040e69001010200c02141c0502805070156205041c8888410400001414140d032040d800b1143d005429124507031010303065006034032401d00d03030300810002c4a400e0068110780c00b201e030910403d4400c032080030900315182c4841001c0d1a84222414100c0401c40c4d214000c41c0b006078a01600c8e8090840c0c010074401c500c4e800d03100c00d5901c29100c0c540f00c895414001000607102980 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834762230 1250 834760980 834761017
    0x12091101020d02030c0304120c0803040905060a140f060f070506040602030a142208040308030907050f04090f0807020613241706040c0e03030a020703060e0c1311 71
    0x18000401025016018054819030403440320450000054815498000c0003c62801d0304103d40f80d681c0c011080002c48034444000400709081c4002c0c4041d101406811900040c18035040c0100b00b07051541e03a00c00c100c8a82e200301c07800b0130b50f201c03031424402c00c100560792640c0e00d11001e401e0080510500d40050b2007401484c00384400c21041e07800840c01001c00482c01e01c0b4042810710041000e000664680d40745a580303030000c03504086d140042c003418a0198540b1405d00380e0300d45509410341c1c42224994681d802c201700601070b5140c0107010441d400d4098408004c1001c0f65a80c0484083d82c050001d402c1120210307070681150b8850081b10322400c400850311083c80c0d80c841c400c2c1d0180c100d20b10080c3c0b08d45110850081c1c850310a510001c04030114181c103480c00c0e1a20f0052000a042c030307118040c00c010751203000d0211528100000c00386026250f0081a00901d18142a8100ca41c0c111821030705400140040000e81d6a403600c2c070b46003103070447d4001002c41c1954901d4031144607990207403520040e80c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834763480 1250 834762230 834762233
    0x2707120f02030109051b0a080702100c1808061b03101520030a0e09060f0a0b04090e0102130b0c070807060e1e3007030506040510091707031209 63
    0x1074024504039801e42d0001e01040d220141103441c00143c855a5034940107080c04240d050a100386184c42c2c0000792401580c41a04286c81d4910036100c8201280b40440d151404a11041c0b03030300640700b0000d00c003c001404541c2001d00d441d1500d01001d06840342c5010020000c50344510030049014000e10f00018010329098500e0380c01b5000d00c030294070b854045045000d13a000040404000c81d12450100c1d511716214010840c200301178024007801c40340e001030f41401c80008a85841e0301b44806401703103c600c103440da86001d0460040e40c50345d282c61050303a4010311411075502860003280c01520703560f006481d100c3d100414214581411580119002c0c810b1800c0000c2040e040f4000108854050b10402d141c450748030b82d640c0d5010f420b5450380750402401000400018012440592a43d03166041c00000c00601d4002c1450300758941c02c29501341d00306c80240400c00c038040011900e0159201750901c511038241d140c440208003003041c10b08003000c1c002002000c142c032418140c2005c146020040001381c009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834764730 1250 834763480 834763511
    0x106060906020712030806150919140d0b040206070203120a0c060606030c090e1b0c15160f050307050c011d010c050403110607060b030a110f270712 65
    0xe201d104050701441201003520b1110700100c0c403540b5050384580c4515200c03c418401d040341200301030001000184640000342c0d440504110541c2031150480725058104130704405160f4101c1c00d090711914080d60301e040000d0fa5500d501d0f920035011500143ca5800c1e03400400e090500640c010749a0850004448212079048a800f00181c0d0140f6010400316803504c1e015412140d6010f100360200e0312011040050b814201121584410701e090f2200e15020301c01c03880d00c5150044001c01c00a50058101d0401004170607017482d6200001d1105000c480e00b0208014000da41d1300c11400e002c10600100042050f0f015408440c0c10fa080c02d8000c0168900b803804d4031444186129a1400e29400c1c012807070621071061081e030b81640d400810ba402001545e80801299038411042100d9441d11155500303010b0360b00f0301000b14418041e00e103082a21494108000c800031030400300300d104540c002401c40e80844183d500c602949194846d1110303a0b22000c00984440f10b040a4142c1c1482c180420444100368 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834765980 1250 834764730 834764747
    0x2130c0e09011707170c040515030109150e1212090106050904050a03020d0503060a050433030606090c05090123030c0a03050f06010f050703032405100c0b01120c0503010606 76
    0x141c0421381d0042a100c0926007400a1048010491a803280002d5061840e143c3c1c003c64001c08986500b00061403528003090075a0390210003541c0807144040403014044841c080c0c084698400d07805800b50320390b15500001c0700c0c01890203864110100c2d03000280d94a02c2540004080c020042000b00107190520302180d6030400082d00f200180030340e4940c110030314051002d0341d00414004103da0001ea08140c18000100600d040080da003119100c4500d654000301510381c3d84409001501c1142c40d41036060500c1901c0e480d41c401c600643c6032141e11203c0359444010b48010100034640070008211030640601005003401d10351243c0d2600105016114055000800010030992030600031b50380c4042454010807011111306000c240c44004074030405124100034403006100303083c001405071141c2c4130345440800c0c00010b159801c0143c003007800980381c50141c95543c46080d14210001d9252a070320101e003204103204180c040c210ba1f98200d02008040300025003c0e01d00030b00208030300b50707407802d00411040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834767230 1250 834765980 834766019
    0xc06060e0f04030f0207050108131b06020c031603020109170f1b01030b0418230109030c0b090102070c0b1c0207050304050a1505040b13030807210c02130c0e0901 71
    0x10300c00d01001d41c4c440e0011618104540c416145d0611950f0740120b500c038294940c0e00c0031a034141c04503c464180b0030345404108054603841d070040084807095418036103000b2102003502560305030140f08000503070f071049081040d44c4544079008815491811400e240260402e801c1d021406000900710b4201e40490003203205090036070b0103101d00d010800c240003c071000b41a0034442c03000c4080304c0c10082005424038030348410f5440f1101042c006158000307401c441c20840f00301c1c00100458814002d1200e0038070a944c010181c0c100031894142d80d580c900c4000c40722440385000180001c698501401c140383c20800701400b0302e00c400e550751b9030580b805588a5005004142c030885c0b4001e008143c4051903a01c1c000103c03034070b440b0300c3d241ca400c0c00c00c4100d980d001368905000d140e0310b1403000310000f40c10700040c0ca401c91050040100c0c02c0d12600f844a4030300c00000340c000801500105c1a0701594620140c0060242700710360006180c1403445085a44a191585064106d0300c3c0c407000003140c0542d94828100c44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834768480 1250 834767230 834767237
    0x5060a060906030f0f0305071a09010c0302042303030c1504060c03060b07140703080a0c03020708030f0406030509120301080d030c031b08070c02090c09032b0c06060e0f0403 76
    0xa5140d6400700100c800500001d8000e032020294240090002445502402e029080850501c065540c601e1441301000c4450310302102c03503809105026400340075486200030300d81070a608190070300458104020762036010000c01c803e480c54004040d141882211480340303c43e8140d50302950b80c4071000e260740390b0a075000c548a40c034003072002148a1003846000259000001c5191901d015610340500ca541f141d020802107000360180000003d01c0c000007000c0000e115240d0400c0d5004a007000307420007140e58005a603542040140d0708540e02e8000846098a8050400255544810a82a1404090b54140d84026a000001240349074000800342400715240c2d8003441011440c4070120203440120607524441120780030000f000a0041c1c0780554003e41510b80084654050740018400200c10355403c8000e80e000504000a42803d014640020065600102000e100c9640c00e102c08800d07070b00034008004503d01c0640030440c407030704500c00600c80c40b04401c5a500f4140e0702072038988000d42c0c0803800b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834769730 1250 834768480 834768491
    0xe010c0b160e04050402061c0609050f16080105030c060c010b0301020a030b19030809100201090203061609080c0901031707080d020a0e090405120f21010608061203030c0708090d05060a 81
    0x42e4501401610700c5654050400381c2040005840e03801982c8001054140300d680310000031a1540c01d5216080c420000541098001c0c10511920b81c40340078130000c1e0204008501006000c9a00c00060707085c02c0400603605541d03191140c2440500410307000d9941a419400040c03551486907064110141c0c445040302c030800c4004140c0161000040300c0c1c070005000c0d03d010f0103202040e10f840e0011005041c42ca000100705e4001560000b42807041c100c510b42012292803032180307940790344411020f002c0c21800c0000c080f5089584005495020140f10044c40c50401031030202070100d00e107058070220740d4000c603602d0b21750b62401040d001940041e2006800a1707001c0710307030501c5441c2a141c028003450b004005001049a101550803556100c8000c3d0700303e111080113101041010b00c02c1c1d595280e030001a01000550400340000d1104102601140c4100301420740201e0b205804821250400000d8454940d0352101c1e203800b0000d40035400001c3e6100c04813006250030b000d00412024841d19510008000303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834770980 1250 834769730 834769757
    0x809030406020c06070201030e03030711060106020f1911060309060415020313030c02061327020c03030f060f1002030904050a27021309050703300e010c0b16 69
    0x1a00c0c0203074807a0314016803006030300c01032904000004154003401032501160b01d1881c3d104851465100390b54010004442c0190540085410f002e0030703001d04642d101030f0103280c0da110301641d42c0703003c0040c52801c40f0304c4007040d401c100075001c800c40041c01d03c05040b0301e4803403034041251604c0f0101110107441e0f80d0f90f80b0500c2c6088072080e200702d0340314002485050045900c9a1002c55040101c180d08982010040190184000360070a400700101001c251070041c0804c0f80090f06600800a004551418014032003045595404000da990008a445801980d80e0390a800501c0070310301e01540c5c41c0c000041c00c83c0303007601d1039001c0b0040240e0b080c1036506110548601c40d58000300c6082c100c0020815044465034540d0346034503805031819a00041174002240c0002c90320900315040c0340300c21155a4040d00b400c20030803403002c10010b0855201d03100d100300c240c24150000b00e00c034804001201040b5050500162584c040c5400d000b03000c0e00642d645640e1300c3d003c01c0304a0070309812000440480e0480340c0302c46 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834772230 1250 834770980 834770983
    0x13080601270513120201060902030901060303111219170705031e010506030a1505040f0203100e0c0403030e01021009051609270c15080105150c0a12021603120809 71
    0x28024107046200d4580e85100c0d89413003103900c103080002001c40d501c070030001459100328005140115a07990000804d00c0c51450301a04c2c10403480c5000c812034010200000a45401c071040e80c60800307402c0e0386d0401007800b05008940140b400c1210603800d1449005101d0790b248d10001035482486403049038801c0d44420788131150a04000d1180d1139010004000240360082c6580020403011910101010560f4452001400741c5021071441005158080f0070003294008030345204005040790f21400001c0d00b804960760391144150b00014040c00416081085a80d1082000c29171140d8018000c10001d80c0514141d07441c0c40900004521030107007120301080c5142a0f10401140c02004185c1ca400b1042540480d1800324000405a441681d044000512403850300b01e100000702c2250780c1d00c1d15a40c1018100b00c2d4110076032008080b0040c0601101c06400c4000a04996468010000e000740445a0704200d141504280e0203c1902404480000030041c501e04014000c400903103414480b80d8a80100c2d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834773480 1250 834772230 834772241
    0x80f0105041e020d1409151f060c08070212070e01050f0f091b0a0201141509070c0221060402041a0102060408090a090c02030705010c030c0e061308060127 68
    0x884018104200b610012800c503402481c402c0203144002c290501603020003c40300004546000098120401c1e00fa1201010f2500950050200425140e0080d07840c0141d040003085001d25014015a405400300307110b004010703680f800358010011004000310702243c2d910382c4414452184004040800442c4c83c1c544000070352031140f8041d07c540840c41e1910200003a065001e02100c42c01d6142951020b41c2030107003001081d0038000c503000800c00340a039410303940c0d00352030080c0801016006010310708802d6440c03040c4203412102501d0140d07000381d2180000362074548449100c510b00c614829103031811038004500c0030720441c002c44d802c000480709440480c80030900d51852500603040800018006440700002e07100311a4040c0408540b661154403e4084500c24503000b00036034404640403082050034024070348501080d28051091607020240900028030350700c80d45105090108440c012003a4007004a0000c2072500d08440e02e075607403004134014200b00e4080c03200d03900d0302000c0201044032182c02030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834774730 1250 834773480 834773501
    0x4060b03010e031606180b04080c061302010c080a02100606021b0f0f0d030c4d21071d09150105040203091504030f0315050604120804090903080f010504 67
    0x169080586665175000810071083c9411028100000c2140401c0000303000c14440c51040056560310980130566610703084c4000c24581c00000c0031a24240142d91220803021825808480240c8a040400099090103010301c10001c05928144d000100a40c0c0000c03c8070403601c0804c4c640780624015414446a41e032103540560700310425052011030360030240700d0750213003d0091900f0040000c46907036400201119607280134642020540308492066034030a0703904400c04a68910f1010400910204540507101c018a840744003080b184082c5840c100d5000040f40300c606041d10040c40d240c1e142281c9000544480b441e192402d0000034440740e07400600f4660085000c807229440d60703e003100700b101030b600c000e24910b0030303008001c3c2004419040400c2035005511940701d120600d42c1c910b1009007141d400c000c0100201d2054a41003240b03440d100d046505a4600011454061889007000405440b441e400103075040c1c90074000d4002d04d9071101c485405500c3c4400403006590b681c104000503a03a01c55003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834775980 1250 834774730 834774757
    0x90203070b070c170a0b01170a0b100905160905010512040f03030605060c0d031a09130212030309060106021006080303280f0f060602011e050a1404060b03010e03 71
    0x9041c0700a144440103004407912031020800c07003e480b2503042250000e4600d600c1000d50080d20044d0812500da13400c2805022401c0c1000041c803604030080d030f40c035a0b0100002c0d1040c14a2008290b07070382c2c000004103028052001c014400c605255180140c3c44a41b1072820000031120300011409622a07822111407a00b1a000300506403925105d01c0440072900320210140340c0c1d516000240d07521094040c0c48001080d030054180c3c202c111401038243c80403040407001c100c80f51382c1c2c44a0b8a40d1400c0b440c03604090034000503030303881207540b02141c203a06682e02d50822610000c000c1050f030010005a480c140d98142d400d0b52000c050442d0f8442c19a0454043d981e420381040c00040c400e41b001c14924007501e0090070003c80301000008250040741c1c0e03485000111071b516511303003109400d03d07405188001c00320384c4003c211611484031140116810240484440b50301c407804035502c280706400c0120b90079100c13809981c06040900d09203006011402c1c0e541c1c020350034034407100070300f100102c10750714500000d48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834777230 1250 834775980 834775993
    0xa030504030210020613030813020409030c03030f020f040e09240108070609030c090504020d060c02070f0e132a0608071806140a170a09021203030c07020906042a0f03090203 76
    0x7d0f42a500c02c18010224241e0754565071410016a4a0303014180001d8040e80310540307100c9142c00e004050303501c40300000c280d00d03004003e40b10001e084101114100e600780500c9241c1501d41c2d49029040c0081109010754002c0c41c41c06039002001140e4005040b03402c084221980383d550b0345000d88400b80e0b203100150000b195810704200068071600a80d9000388018100d10110f51255030b0142101c1c15071000e100141e02107001800b220340c4100354180035012072003900009180001010f207000101e4900108a44407065a40381c142084007803134000f4190060000c1203030740d107c800040400008039010000958a41408840410000b0540044d00c4003660380707100101c41a1484110390303020340d0400f81080b4004480e0000b01402c0d81e01c840c0914507110300070400c0b5030640108660300c1c6414068508a40080003800f049070382420455025550503140040603903a0000000c3c000e14120142a010810030012000c5564809404030302d00701894480e01085200c003002141103510040c0000d41562180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834778480 1250 834777230 834777233
    0x9030d0b2709010f0e0706031806020d0b011409030a032102040b0406020f070e060405280509100c05030621100b090115080a0902030f0a030504030210020613 69
    0x540104000540251003555150601c0c0c8981c50254080e0404880d001c0c601c2050000800382801030560032844c00314140a0380e01c19400040c1c42c0d00040c810301080c1070380c402800b014101d004d4940d41240b50418021500c81507140720000c050103200d54028005032035108440c3c0440841011b44c2c4d0b1102001d0014410a40e1300d5806940f21361129070b0315031000c884441a40030010282c00140082e02041c90700c0c035195881e10801070b1620080b001c2d040740700d41005809100c0030350300540b080c0e40800100d402140b142c650070818281c40d103010010b2051444c0340e0079501c034190403d40046014001c0007040701c044c02508000e1030200d44565180301d000400400110710540380210f89401c108404040040e4172900c0e6070a41841c0940c580c42c8400b0303140d00c0b04031104041c984620400e0041088130444421000b40000082258800614a07102295135030b16180564034104995004174502c501260744604050801502c8c68009210803172250142c0e90010030a14804200c840c0152900000f2040c104500d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834779730 1250 834778480 834778507
    0xa14030c07120e0d14160e07180b030c0901090e01050310020c030c1f0c08010b400e090c09180a17031e040c210602030127050903 57
    0x803000034008000f01c01c0200b182c00e80e240d0740c8071300e5214841d0700d229604412081d03440d814903040c41c0b0164020f08883c48200006604000c40a91180e690b207061101c5070585200da10000c249500001c003080004010018000d40c00c074010128908240c80d1104040c0e558031440012030000d005007a0190801094206180b16507001b40102100100940e4280364507001414900003031303481c3c11032910501c1044042c1c8402c40e84101d405904084c40c2512140d0304140384d480261055101d006207481c04a80000206030903241140c0c0306942c811906200040e4090900c01c290380c540c0610903101e11395401040100000051a41c0851000f4082403096500d0000d11154400f4000100e440d6002c0c00d1500d0001861101c001904601002c803015100d080402814a81e40080803500140015202c14000815464006007040340d00120380c0101581024601c0642c0640d0312030010100c0f4004400819102e000003584900b101a80032035410210034030080a06650007500c4c6404a0f4004010301e2224400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834780980 1250 834779730 834779753
    0xd050322090b1504151e170f011d0c0d060608150f03120c100c050310080a0c030b0c0c0a1a060109060e040b0a08060910050c0c1c091a0a14030c07 64
    0x115040c8007949480f91944c0110886000031840d00240d0312138522554442030740241604114072030303450344040d81403994030a4a1140380422070ae07120f030001d001821002c640001c482001c000582d05121480e900e0001618002c01030b103c0b44000c8030040081003030381c100810900300070b980040092000301e503440042403241d40812080581c60040700001543d03908180100d03d040d0b100c0d50340300760b40c80c079048441d8103c1180c00e0300042c641d9081900ca1201052050401000792500050000513070380321108000e8061007640e07021605800351103e01018406124410000743d00d2520a40301c0540e91036004458000d03090044c04089a0706000c0c0031040d040651100600034005040920800e496807007240c94148100c45a51050b80102981c0c0c106180c1e500032190001950401c03503040c04100c15503e5224640c1c2807021101080003c105010a4402e82291009252840040e140900b1504401d6202d80c0a0120030000c5a8880d1030202d495003c00e003260b00ca403075800c421038109650707070fa81c0340701240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834782230 1250 834780980 834781019
    0x170c0f04022209110306280f1205012f0a030f060306050a0e01051302010302070501110f3708060d14010c030f0c0c020d050322090b1504 60
    0x9500740501c4540040340586000c0400c0c407001081a00c0b0b14080300c3c00103849010b000002003410900500c8055140c048454041e061414940202c081c00c501007240e00d82071552007804004480030001070742c1420420700b2a1140e005200a010300540c4a07943d040040d070400c80c1d200c3d48900815003010021015018194030003541c94041a010b91103090319003078a546800c1604c110369500c05100e840042840f440050354008802840700d0b26040390702c41d110fa10040400382c1410f030009000420000c0a52018080c0d1102c2d0b204991140d4500c070710101c0c0380d0015000017407601503d412001c003584404040d06242c10076901083c01503d41c2c08002c031001d15014108981285015905000040400b01d0789026015050000103a01c1410100242a80d4403140e0344440c2900d4260525000e03039000040c440110380550340201d44000c0b038545140340d485a0010848006420300c2142c02c0c10a102c1c8090080701c601901c140184030300d040411505110380c0b04e108403181c00c03c105c104025440741c00152060b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834783480 1250 834782230 834782239
    0x3040501140d0e01020d0b130501060813020604080f0604021003050907093b0d0503012312010212151f140408031c050c0c19021c110109170c0f 63
    0x10300c94501c541c0c26031708001c86c92154035458120300c0f066410032028101c1320010421041c801c1e549032800190845070b002d0070010218100c4000340c025510390004030b600409140042b03c90584000c1c06607520350f5001c0d10100d1040c40ca4401c4199098030a018242c0511205006009400c0c038041201005100000c0044841000f107614250152000081d0b8004e0342515910b2188400c001c244042c280420b61514a00303100d401d000610a0100b07170100c42e45039811400741c018030700140c1340006507040804006c40d58150300000d2110300096043c070704140104404010410a11025000c021b154401340589501180140b490700c803e4502c2005091103041712050003030328103030700ca81341d69045602011140581080d0007202c002a0240e40c070130385501107452076189081060099026403100869030301c900c400c0201021100c190750b50070201001506c440c8034040c1c41400c2d90b1600042c0c00e025001c6550129109400000703060070941e94454a0b02e045c1d40c0a810350085207010406105c51011070650031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834784730 1250 834783480 834783491
    0x90911040e060103290a0213050907090806070305090303040b0a061208190c020102030a0e03030409020c0a05100c090302010324060519050a170402040e01020301151103040501140d 79
    0x100c0d216481040441e01ca400040d00e4a58114184202c40c0f0f2503600d2208591a0310b1220301c040340c005c0420740d903041074008901507500d00c05143d100741e02c0040b81d0403c1c0d500909410a1041e850340085a40e4121102442500e8241c1c3d108030040d01142c804a81100c2d541c1c10410014000540c070684c41640800c0c050b0000552946400404501d001c021004582508000a80b24118004102440d04848492410041064069000075246e001300d081d481d0603c17015511070000e541d010b00540c2c000e000744100071922032042c031401c999901100c010a403043d004900700c1800d00c0350b480c007958130000c602e600c030001c096155900442c0101015491031584c942240d640101d07400b0208140b03c0208007542d100b589a8519a10107101101407400c0b500900104000b03001280c0d0704001014100e903210b10741c11b2940d6445001250180180806400d0154400000496803405421102030b0f000c045a644000004800d1900c503540e01c607034021240400d81e44140c881854807001c0051000c601200d002080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834785980 1250 834784730 834784763
    0xa05160222020903061506090603070201020d0f02090f030d2a12020d1409010f120912030f150f0e1b0304211d060c160e0109060506130909 61
    0x407000710003890545280c0d0002440d190502c0d0811220b81c2040103100e412413002000d0340003c02602c91280c986004800110004403024000e41c159905940510b40038000081c0e00321900000350302c0708003170502c10170030200505800e013000640780e04800941d48480440d90714515205038415070016061011002491104001880d5169840051442c580060012158140020301034004240c24000d520f1401e100000d0643e03808405070081c1c02c0030f401d0101400207458041005000380138005001e181d84d540fa0b01c4141e542c50f910541000c0000c2004104c521403000d00307041200d003680b08810110b6550034042c480904000c0081d03812003646403c0105070b40711801003150540040b82e0544940074083d0700d00c050804840c94001ca014030b546407905454035902d10307000d080c1c1030010945000c1c0a000c510080e903000e080204818400000a00c0e01c0b2072607031000180084942405124660f03418007000150a0400070181c442c1011804600b0503810300700044d44004041815085d110401480d1170802d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834787230 1250 834785980 834786019
    0x611010207060908120c0f030610260a0506030a020a0b0f0405130507020712080d092603240105030403031a0a2c0603120715140103030f050a051602 65
    0x400d0300d1184c4102c50716162801c003065400c01000b00f207a289690f08008240d01e00100b03004a80d07001800f100c694100018140b012502c800004000e1500d0407810f40d10740440d0b024829404e0312490400406100c00e985403c140344d12942c584800941241c0140b8013804250304400207002c1c150b21002038181400d41e10000903600801d06680c0440d55a0f41c2c400b401540d80e41480385901601122101c2070110240e0380d2402900e10418071001c0309282e523060f984040202c0c106046c40345114a038183e04030b0100d1100e44901d26442a14403044208061b0102c5010712075124041003844e5058407514115500ca07102503018016906849000d0080c58140b02d40e140d0f80d000b0421702414429448030b41c0403c45003030b41c01c0c41112030519000c1828121080010383d59000610b001440251504251250f41d9403400b004c00080e00040c0518507410640c3c03c41d61790545420381f5040344e010703907540c25141c240c4140035501340c89032103109000a0301c1044050007281c0c0c2c0c4403480201c0751000e0280c0ca101080b400560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834788480 1250 834787230 834787241
    0xe0d020c1e1c030806180c03070309170904060807030f031d04090c0e1b0d0e0102070213051f080601090b120114010620030a0e0a030f0b042307061101020706 69
    0xb9074840907100865014981d006210320780c070510907a41081d600000800350b00034548010301301e01c0c44c03a00002c0090101c6101c1e4200780151a882071f0b6a0340110050000f140841e0401e14940d40520b192440001d84000d001801000f01c0303400400300b03c050005500d08031a5903042c0c03440b40280115518580c1001d80f19485206403490081c07501610407420003007207901d40030001e440700c2c4c001e809080c03520060224900455103060304604001035442d055042982c06401500000b9511001030070150b900e031038490308850b115124000b004146040254040d904540c814060704026622000c0107102000051307000080141c0c0003480806000310f44c0d10001d0070342d0b010b12208245010a01e00400100360891041c0e07044540300070081040c0207910004036900e0091000090800c065016016082d4030350240450240d504a03c20030b2440d10346003000d14102c1c0068504640940804940c0144c0ca01c4140418403c0b00e0b074a4054110980382c170b07030100c40707043d141c40882006550800c080c00000d000b91150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834789730 1250 834788480 834788509
    0x705160b0108031b160501030f110f0c1509031e1b0106140109231206070f0f0503061c03110d0e040b060f0f130e07020a060e0d020c1e 59
    0xc5075a82e9052207042d40a41e00f00c41ca004d1207900c10913200e0118a400c43c0c00c40182c1340c080c81c0c001020707051420f264000e040f40321850a0860b50001314400006d000c0070040c00807000742001c8554a01c441d4046d0840300500312101c2da000e41060103180c8003007400c072030020000c0c40c0340004a41401c920414800c3c070703a01807040501e616903440c071082020b120100320001e107048090070903110032854140410603129500107070186a030390501d000d000c00e03038907606148072a02071070040340e00c00c2c90f0004002d0041060410a000071441010428803503d1042e01200d2286001810b19402d1031105000c24181140b00c81c4200d00744a82041402c40c0d400042008071180043c540e256035a0034001002d100456186501c07a038004c920070440c1d9100740320044101d8000d802404102a55500c80668103d68001190442c8580d18928001c4c45001680000c050850034010b490811051041070388250742d40c0c0366030307070400b015800c09035900a117480d08a800d507a10480e8a00903000007680c3c00005174400e08800310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834790980 1250 834789730 834789733
    0xc090708011203032d050c0301060c1502130612180c140d06020a031409031206240403110f090403020c0402070c12030c03120b01350f160203040e0705160b0108 70
    0x1322401d005c1a0b03018164020040c10314081c9154108040204803520820380601215481680400040c8190f4102d454039000200400f00d00fa440b2940103007012803104a000105042c0421400c060651045113624560b015400302c080c0c0b854007074a19291010501e5240d4042d0120140030042940350000f89410007440c0e5001440706c08803000c0c101345090141c1654041e13802484036001c0407422090762034002030100e40e9032148441c000000268004440e5000310b0504000c1000070400c045070150814151080b100c00c00c40c9981c903070501c44000b5040b05c015005030702c0008004414103003076004150540c0202091012543c43e41034130100030012860440000300505100024181d12111500b030b9a07901c40400d0008810000009004880415648010800c05074000c00c9460908080b9111104641d80203009403800c280d6050502d8800c0b02c042e82034542d440b85040071180b001c402c95050300d060407110b10030340d01c4e0b980c02103c03d40c200840690f030540038150381001186032074000e0380c0200120790 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834792230 1250 834790980 834791051
    0x18190803091206092812021b0f0d080307091d0403110607081605070b071d0109080a0b060a0302150a020c150d0f06090213080c09070801120303 63
    0x1c01c0c400040500b03940c01032150488070920400020108800d0080c1c82a9180790100762901d0781c1c42c513403032070007100c1c02403032010180418018a03402050711502003c90b00e6540100f00741c24414414802020482d0f42d601100310741e6800c0004074800007441d00305491b40303407001120f42c90307450b12160030041011707000c0c884040d4807c0104240c3c0c85030f2001c0c14064500050040c5040c490b40180c00210081d18541400754011301054030607100d41c0c140d910340390300a001d08a55007051900608000110340e100c403821410301c24074200d10b5008020300002c880b91200181a4000726440d6110742240280c03400e0b501000307521000025070b0b00d040d0301c603480c00503804403584daa09c0007a101071700d8500403072421030060b004640141c10410300007060b102002e069074000b1509203070b02c90301d2600500700d941255035164400f05501758140100c02c503000c1602c4105007180d0a82c2c2c100820000540d40883d8110001a003420041c4240ca40b1400000304c1280300c0e041c0421216028a00d01140c80e4000b240c0354401e12201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834793480 1250 834792230 834792247
    0x2180a06120f0c0b07020d0f020d0b01061709070f12150c0f09090b060f070c0f0821040b1b070305060a050a0b18130201090e0106030203091606020318190803 69
    0x30040070051101041c003a01d003100717990204038010404580a4120900c007402c48013952a800040702a695000040709007660312110301521444407880c0c01d000d03401a050004d8001c060000c0c1010985070110000341300c481c078207000340c071080303159040454003070003841d541d0b06d51006280101030844c1d400e619114688100c1c070000611451003944400300c0c1505040078100e00345c640382c04982001c00c000c034003695641c0890400c8550440940d00211b080e00d20001c3c0042c010f40c01188034081003249525030401c070178240340700b80d1050045002d030615440c02000308041050b00705500c07a2001003070703800f80d0380c44940d0794542a08103102200c4200319951900104140820103100e02c00e200d42003243c0035400041c0b60200144040c000500343c4071407030b110200000035a030196000d0b000900341d45108003070641c0c40303442c02000b941081e210f03040ca82c07140c03503413007050242c109031240e0035541b040d070049d403d0241c01c0500f650928070104006401100c1c005500c281c4e24116000c44001e0700510f4000c1d562441c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834794730 1250 834793480 834793493
    0x522050a0501080f0109080301090c0512010f09230c0a11071e3f02030708010213080a0b0a0510090e07180207030e0409050c030d0c0302150402180a06120f 68
    0x150390100282c5c0d14107412a40041c00410682e0b040d02c0019200040214071002c040d1000e100d0014070400300c503044000002c0b142804065001500d5450f402400f01c0c01609607140d00e00188020071454120160000507084c910f480c01800c45a000c51804418070461084003504025050300101c07078201101c42034a040b002d400d00720b007000b412003008420300b601100021901800139101c01c01c041c0020360a040c40312044e1300e000c2d00c540a0b002400e0ba40000d40e0b9070200340c000d6002c0800032150040c03a030f20000303003e074000c2152003030b154000007140b4450341d4010070100100b07402002903018610100021511880d0340c410b00080049600050906c1428018168040f925914501380550700401102c00003950185007808030840075503021400031000d1410a0800101240254151003166507642d031056000c0926140c4030301a4090f1601d00a0202040091090444d8041d400c00c0c0032600103894000d15000c680d03480030b0003040c0010216190b03100c01c3d4020340b204000391104c105521030f02080c01603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834795980 1250 834794730 834794743
    0x3030e032e0506030313090f0e0d02060703020c01020d05090606010314130f05010b1005130b0301300b070207031b050d0f170f04170d08010522050a050108 68
    0x445440d50a072118010045014101c0c80c0007000c0061600c440c00720f10380b51000c1044c2c400300d0004025014641d51640300280003003e00081c028011420103280019180010078148011070080d400341225940e1803038160041e5000c0000c403455903500b0018a80c400c070b681d2090700c0c02403103e50003031300603818800c00042c00e503000400d0384c0030501ca82100307015000c40c034584007183c06d0703600005d502414001c03424028010541181035580140003c01c952081944c440700409180c0b03030889500d5941c1c4d0b2510509000d6001c2400780345030f103258183d520030381d00710b50490705011082c5840e20180000c0f80da0351101128030303058038030f0741c0903038000c802c03c0c410402c0c0e4000b40c1e5101001c0c22082c12400345007000044061b09000d81c06051501c51001e000140030703129840f00c0e8010b001c203504940d01c19002d10444429030051044c0065500766403250349228101041100d010b43c080d5840508a034200420003100c40b0050b5060b03556000380c00802001ea690a009023841450341c003d0000b42585401d0141e0306000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834797230 1250 834795980 834796003
    0x309080616020d0f0203070c09060302010f090509070302070501020c2e180308040819020a0606090b1e04092004140f150d080705061005040209031c0302120103030e03 73
    0x940d1400c2501510b60001d140c001801c290b14000c0f902200d44202607095100740a0b0251004109410220b44200e031a0001d9080382d1007a0303510341c6124006203044030a500c446c012a548000340c00c2c00300b40150300c02d07006030203014082d500052802c0e18080740c0720701d4092aa00c602005042c007000e028526070703503000013601d95000d100701444a15620180b0840390017011000a041c40715a5010800780f000307500c1990300e0180110240c1241006212010703503161000e9004441403070809a011844505034001c07011903502c09024982407040e29081c0e070f0343c036111455510780c116035910500c10204940700008a40722014540d06000b80c1c90260500050307d08017000d8041c1003108005000c01c0f280c030300c1041540300011000700300b4001121740024624202e020f4001c3c0840e0340104505040c0310740424500d000f4041a090090034655440074441a80510b15445038182c00514000d51070111000c0e16110180480c50014035041034490882c04083e001e070000d50014075003030043c082c282010440c298200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834798480 1250 834797230 834797251
    0x1f030501150e1302120702030306090109110a0f051c060312080108030d0b0109030c030602120a062601180f0308010e1005040b1306140102120f030c1605010903090806 73
    0x40403010b0080c094000100e4000c4052100c0c1e42d0301c5406650603689254080d202940315810314001c002c0d0350340c1081c1c0e0708d00d100e00d05a10000035060a180701d1040000200111141003d00728541951104150f4a1042c14810100308407080c00068084e80c200254a60200054180c03c5083c201e11089000803d4400e200f80d0400502c01c0e4100041503c00659207448041440850980100c0b030341e010544c00103005d15550000401000101d801404880030004024040c50307071a507200005688040c4100001d00e114510031450b5466548a00410b28020800104411300c50f8201510a051040010b0f2000c4010310540810103501c084440e00504244818200d141044405a286007140c2c2c0f007218452603850284042c0c0d621500e00207036154408900401c9011350700e850504445904000d0103005000b90740700c1c4004148944142c0d05200b50050fa1507040d0b66031110304071304d182d001c0c4007082000ca10b050184800140240504541544030b41e59640782e1500e80b0300c0543c03610320701400a1206 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834799730 1250 834798480 834798509
    0xe1f14090a14030903010903030912080c270907030213060c1a04050a060e0f010b0a0b0d050c070501060902090901060c11040513051603170f0a1d1f030501 68
    0x824000180c1107260350b0000032400b1a900380400142c910f1113084403254055007000380d04424540c01da030200c0412801091007140b0101490401c030354000d01203500300804202841850075030312407031105104412254182c0c00c10b9241d000300040c2003180407240100044c4d0002441d00041d80a01d466074001c284034180100c3d00e0106503125a00312100302c0a604e040b5406000050078001d040154a0b1800d400c0322080100402042007507444030541020441b403503007032042103402401c204204800b21010000038504080103404010b018080c0a0402c5944520510170350000c11400e10856000340200301006903648140000d0102c0030700160700c11010301001c4010b00c1d0105401e1a0b41200b0450f0840d40080c9603076404048000710f01305020042c01510030119040420088405c03441c1c103807070046240e01e400c10b14401001415118905114441c03110621103910b01c01e00408807003031403c0440320b4521081d8642c0000c2101c02050000c40c030068440c10b205155410340600c109805000c100218806 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834800980 1250 834799730 834799741
    0x2064c08060702281a04050106050a0e06090604091502070309050a06020d0311130905270714130f020d1104120312060302190e060f10050307030e1f14 66
    0x45441c400300740082c4d655492803891100c0d004140e4400499580107418071284020900e2041240d1000c44040320150329200c00410a89840c0c03003080225804c95100c00290f80c0d45100b03024608902800031504141c40390140b40011b5020102001e020040034170058503051203080040010b05154045800f13a0301e1a0003d01046501144080300341000e42004110303101040380300441841001a00c0c0800b05c1603550220382814940c0140d0700800380714460300c2c2c1c8441400f003610819800d07200320020f1079000080c10400504074038241c55503100002e2402d20711104228120068420100c41c60800070750000c2c54058408541c8115111009080d11460410b13060081c05c0000901c56100a401c1c403503010000d070840340058102901855000d498100240c0c000035107a01a50041d011345c0c165058001d000840a04004502c002d000310000c061040c0000c280b0420f81c1c840d40090200b10406469024006506608015165042084680098001c568010320004984110208182d4040c040d0b0034000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834802230 1250 834800980 834800983
    0x812060d020d02011d150c061b1222210c170d02250510090209060f060c010e0705120a08090f03070305101d06040302064c08060702 58
    0x30309590f082c28560381044203c140c2008840905010552108000845c2c017021000400030300100112003044445541302c00d0800304100b03400d40002c0c0743c10b07441800300d001204111041c02c0c0c0c200007015210b00501e100e0440320041c41c055002c0c16100201c0d04a10324070818600210011480500d141c003c8a60310a6900d42e0f6681c0051000241c201c0c1000c6007081a80c5140c0d030480750b9002d01e030b401641c0344409402010119607c9140b040e00e0900480000c068140414010907481c142c1c001d000c0902565503404115440301e15003401d94202e0f00620400510401c03d100e18890718440600070140d0501d007804101700c05d0040f4181009039004080b08000190201080c1c2c1c0d090101150090124400000800d2030100568030140141c459104c1420b045c26161307004d0000c0d051a8048003004011111042d580c0c0c600559006006a00003800143d603401c07808100784802a03040c038891000301c1c03823120140354800d00540d18172480040860001c6001001c1d012603000700b0825001d0006d602d041003000c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834803480 1250 834802230 834802249
    0xf010203030f0a050907120f11010f0c03231602041805150606191205060109050f09060619111c0801290c0606040605120a02041e05040812060d02 64
    0x619a0316160b03801700342c00d00760601600c0040c00410241800c0600241485100d0315101803041d511920420120541c95100d2f514442d0500441c0d00c0c1c1e295523003501c0c2e03030840380311405a1419114400c1c0e04d04c3d40843d85002d9008045403817031102449600c2d440c90041004032604034010004d001c030940d890394002603011644c0b032128444514402020b035580008110b052141000400d0300140303101501ca1055040102d42c18503040c03c080402080c0c1c0c0d110019910507580b406003030381c0104e540c0b141c02481c1c50600000d81e03204101501c054100821000c161144103107440b07201c00800c000341040d0001c40c004114403030441d0544010440091b01d003500140a080e03040c001e41040c01100c042c90750401d00304046003401401d0282035580d55181c4003000c99240d03d03003514903903c200c0c1840000502ca1405842c0200c80030132070b002a1203070028070703030801c8020711904108010680c04004118000314071032040703e1045000e00d020300d0b0703a0500c0c502540c14118000b001c0354031030102c020407400540c4400e0300d03e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834804730 1250 834803480 834803491
    0x50309010305060f0f090c0f28080105150a1206121a0115120b0d0c031a0103051209192c04050705010e03010209030d050409060b12220f110f010203030f 67
    0x601000d03444a0b07007028081d10510f4901040244000f03a1005410f402e0011a071001c602740540004480404800f15030201d82842402c3d4403d628240e5908940070041c028100441141001d0001c085081340200580305164001e00d50141401d0341034090000c3d040d034144650750382040c1028150b0404a010414102a0800c8001c006020f14010888010750b400000400c4004000341c03850b000500c0e0094282c3d41c0750104540781c0d00c140611f605802c00c00c003803960580b58404007810911070071035581d04172a007041c85281e90102042e5911015031391404d10003805406408003441e50140101c04080300010f81059030040440354800f0071000c0381000c2001019a1824603154a5845240000901a00490103190f42c18003603034006141c4150048024400c6603803084003886440c1d5240030350070080c0a0000142840c5c8540800112004140c00101c08024406d04440400c0003950310342c0b4140c00f041d8541180c003c415145401c1c0030f490512a102e92800302480203502d585840301c601c0d0400b24000c1e00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834805980 1250 834804730 834804739
    0x2030402061c09060f02130603050c0d0516030501050a031214041d070206220822080705031203060105090f040e011406040501090e120a031107050309010305060f0f 72
    0x10404655030324084502d0801d081c0c402403203099180c41c03680014003c0c090b04a40c92454100031216480080c026038554540c07552080c5400c40c0b41000c1640505001001400140010070070380c02032401754401c2a020b88540d03801c201c41c520307100102038102c41041c0c1111380303d61380b40c40081001074001c40048400721013038038010450014807140745044c0d008540000c2c1d50005605130351099840b1220b550740c42000590300b120741d19101c584a440c00c490b4200140c2400c20402102032000c41c50104c010f000e0341e02900001c203001c100030500d01900c0d524507044509290002c1c1d03010056440c0400c004850481e041c111703a807550034650700180aa00c903454805001c1e42c2c200c1061200355685920504040d0003040081c01000014120350380d50342000c4807040d202d1441c0000200f0400c20740d108840401d5040f0000301001d8a440c4c5a07a00190000c4c803441c010151030f0907041101346084d00c09001c43c0ca2107440155205d608440c0050240c9600421040c0949110b132480c214607035030840141c040740015607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834807230 1250 834805980 834805987
    0x303050a1806120609151406070c170708030a0912030c08040603020406110102070206070f080c071203112b050c060f060a080d050304061a0a06030507140c03040902 72
    0x5599a5848030700c00e03011122078540000360190085541418203401c0a01040300340d4960b0481e204442499081e95000601008240000d10354001c180c0180400200b106040004075030b5001c420900f0f0350400b00f03845e0852040720b42d03070702020012100a0300c40840070b0340c2030000f4940024403080003803041e105400c5010502009150081846044c1140c004091941d203944a28001d40a54054401c070300008005000c407000d950410b100b65855030740e0050000b450400e054036250101c0340200015900794030100010314100200700850030003001381c00310645148449080107002c038020641641d0300368100500b42420900043d149034101d6000703181802080700300b070408076100d0003408a035610707503c01d09007408900307500004040e10507a004c6802004490b1600d40c110380f19941060114046202400443c002481c0c2c6c0d00203907000994000170103a811301e00d20000700040c0f000e50100010a55650511064580c0256000c8180c841c01700e09510785224800c0e080d82c0d9225600c90400c103182e003c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834808480 1250 834807230 834807247
    0x408060f04021e0d0f05031e07050c0907110303131101020109170a0309140f0d110d03020d11071208090a0b0604020a021608100c0f0e0f0307050312040302091f030305 73
    0x2080d0003d4998000a4035206511707185040c82c1d59074002c0101c4059031855400101d01000040211040c0c0c40d8418090000c0428100074041c101030081d00074800c0c40076a400b007640e956001c20195109811039100b200c488002c0d4207251a003803214191641c110f904000c0020003003642080b0903205a800d07440d083c2d80e13078043d4450441c018440760000519109000126420300c2c1c03000130b07007a1502500101a25000d120f1800b05445064000c065030900350003403003503080210300940c0a0301e003a0301d40e4400170600125a441044003584001e00498001501c940300c140c48950004010768008555001003c1d0101a6120441041002040325208035000202140700318424001e5005591001c040a14180d0715040703920b03201c825018103410081d1070042d4030789031039101c0c10621001001d261112001c07006054140f100b1300168140e01c0b500f5100b60701c4009082d0b1420012040c204151441154032503045204000340c0e00d0020341940321500310103150000a0090101501c21660301d03041081c2e41c4c0480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834809730 1250 834808480 834808489
    0x1a010c080903150f07020313060c05102d05070207050d1509050a05061012062a2c0102030f1e07140c010908070611030912030408060f04021e 62
    0x10886002d4042c00b407182040000c40c00903105501a100049902940707695144040b681da01441222003460303c544101002124010403840f11424003e02c144c84044072190032441c10744030307004d1040946850390300c1800500030041100514214240405003c1403c0102c4000d60b111068041d0501c140401140403003000740d0101442d0401091f25014415003140e41015030715900b6003030085e00c80b80107410019501310f103102d001405542c18035044121060040e10341c480101004480032402e5407482c49900210361101415282d024615079446000646020811401807002d12600e003030a483d000c01c00419030f03004010342d2104080c50402607120a00340740084a4034840140c42c0040007000501042400241e02c0040e400c021120304946994001c000112140580c0f03105606841c0c00c804420300038a07202e2088010040d0303100081340d08180036800060f507205041158505e95a1002404008c806c2090110f41e51005012030901b003149040c1c0c020403044000c0442c03010404002401c0c0c25001d589 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834810980 1250 834809730 834809737
    0x80601141c0305030702120301080d1b2003010c08010509010b09150a0305040b091f02130e0109140f1005150d0c020604031805030714010e060d020a030501091a010c08 73
    0x8100507901e0444015003009051a070013610904014018454000c040d0040c803c1140c6c1210301040003070000f034694150442da100320440030200c80300610700764074002c150403910a12410a0700486080003d801e40201130031a12940c045030144100f0100400641d550402c4190443c0d0504a0450765541c40c0d6001503c07854010b44840038000c40485e0b0200702550551089201c1d038403032840c040142d2510040d05903101c610481c0c0c40384110096040c15062800703074024003502c044040d400020a52180300d41d2010140903040f808445603500d040b50500000c141d522900916004100216424840741601c04c00804e406080d008440803004503804042010884101e00007101c4208085608004002e4680c3c0041d14182c000440c0703888554810300701441041c4c00c03110014014843d036498002c4081e00c4140e00003246044c010b19400704005512040c004045c021181040169241d25107035014080f904180c011000c082d02c0c000902d54803503d04403450b42c0340d070b00908180c0c1403c0c6840c54036209521 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834812230 1250 834810980 834811009
    0x402030c090403091d0123210c030d030506060304110609042a0816080405010b10020a0510021c020705010914010b0f06191103041a2208060114 63
    0x1003004100506620031400340c181d440032042c890740c01040300301d16400c41c07501f800b8030702082d03010070174080392007805204622048101038078200001314090201d48114890000501858001018000b00b038075003801402040c00183c10200920700f03045011505502000340002c241c80803c00e4140c40c19550b45040e2031507924003c0003402240d6060381c5401103903116005040c400f2146040741c80700039005d501d24910843c1040c1d03003000002806201164407100262003582c1c42d56807200641000d46030000e26180ba640e4640050446803440d01d41035180c03202030304111100900c1484810702241d502951003d4030046540090b03211300741401d1260050403070100013001100541c41c800f440050640050404c424100d40c545a510301045c103200191080039000344120f100f1122803200d09009158072250740c0c0c041130442e8206510f034155080c8054010008071500d410101e40341e03070b21201801c000c07078003a6044400841024500300501e581c4c2c03101809294605140f502c0c032080103440c2c1c3d40300d5000d8803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834813480 1250 834812230 834812239
    0x160f03020909011b05210412050904060305010603081308010608071208090330030f0103020607050a0b100504061e0e06030120090f01090b09090403050d050907080c0a08150402030c 79
    0x303905144018011b64072022000c07244900c0d43d140400346281c0012880d2250760040075190440e00d00c01421541d5500001e03469910a07540c540c0400459800d10680000e14880c461540d92040c3e036070003000700b00105901603409607051083c10f00c0070450200b90b0204a821080411048101c24507000f19030b0b000c1c24001030f400d0705c2441c4e101640c030064a1100c20510318201c5842807469041180c03c001c500c011900140022204070040005007400d030000d00f000707800b402c01d55a00c595155505268001e059a0100d004442c0b0b003400d000310f103000c0c81000000c0c0240d89411078683c02e0303411600b207528030f2403042007503440c01c03100026220384080d00950340031580201200c1c0541c10300900c116454001031109400b40c00520041e0015501a0b03a900d01941c42c1540010b06000c4400100442141c1c003e00032820407030144800300c51658a4001c050040403628050310009081c41c8d402ca250038038a01c0c2c00d62203401c1205003049161300100c0d40f100000c81198400c0d00903590340c00443d10300406c821030150030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834814730 1250 834813480 834813521
    0x1e050610030318051e0d051e011a09070f030b060c0f0607030c0504090c0302040f0e0702010e010b01090501230f0a030c030204060909090318080c03160f0302090901 72
    0x5a000a6000300c050302d10940325804422480c400151a039401c41c0185604030800e0190b1800e1300200300c100071a2103000420540e076003400c030390b0785506206400d51001d60f04204946032181d03142c02800b405080b8160019807144050720040010400040a002c3c0c0040c03044040b9029809880794001c03c00264019204598030b090000c145640c48003a85110102c074080e9002242e0024400e0003220b07000700701c85c0c0d112410541066003403002055698110024540d08000000c0d0001041d4a04402071602c081442c0c064039117484040d00752104031480c1409645841180f04090780c1001914054a10a01c0c205c1c6140c1c0c84410100c1c0411307003a5521986142004c0340d03840f80d40d0f000c1002442120082e03542480000c1100800f0380c1680075038001c1c04046040c042040c081003a87da44031007540ca00901c4c000d10700c000c144500c000c050705150419140c1d070700104604400c038142000401c44c42e0804003041c03445c1c1e6241c100100a141d11074000244220030b0f44000c02ca8216094124134200e02d40c40880130706 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834815980 1250 834814730 834814741
    0x70e01031503081602040f0515062203031218030912030e04020309030c0d0206130809010c1b1401090e0f19020406020c181e06130f05250c1e0506 64
    0x7045844450200e1140b4202a41f00724074041e940a01b0340517650600ca149402c28040080144030b070005050201d180420020502d80724140300f48480c0114000d45510100701d1031a0308010948030500514a031181e800164000040e9105004104075804524a1482e000842c5406c84801555410041d030090010051201c200030100c000c1c416140310000302c542140214000341d0721003100319040c402401c0c4403191030b00440d00309401441c12000500d40707200c80803807640e26161180d5600e01e056920b003120070010f019584043c00581e2104400f4207002102c2031a248010140c250b00070100344d1140c0b2100301080c03031a0007080507680c050166002c10340d00c60791582c40081d641d11800b00c5492041880c2c0790341c2143c8501c0680ca00c5d000307128500901031100e0b86280445a8034401800080c2c124140f07820304080c1c0381140c82640200030300c0100100e05070030300d115442561a0800c03000c85c14014880c1c00f51000507041415008003a0b801401c5800014940078103200030454101d0113407441c002d003000c201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834817230 1250 834815980 834816007
    0x7140f09041d0c01110a03030c0318032007030c05040e0304051309031b050c0d05030c0d02100e24040f0602030103060c02010f1b050903010f290108070e0103150308 72
    0x10102912080b0b402c050003a5004460065100c01e17440d5058000300600c10109200760040c0b0920401810003191545000641e1004582c3c1e285064000802c8018a0391120040307102403000c2201c000020941d45043d40c4600180304418401e89115070782d10614510581000e105907401000700400c0048501c4101c110440500300510b021030006422011180b61018001c41602c00241c015009000140c084c0c3c1c280701412440030750a81e4140b1080c8070003c1d122000700a074105504076035018041000380080030784141d0700414800c0000342c10030421469103644042101c80443d0003403080304020707103e03030425402d02007401b0005031504d0b000000200901c1a242c104c642c0e0365130f46500800c161681c4801410842e941038410114415821a01c40d000b40d01c03400181c00781050090000a1078200501028200c1e03124607400d00819091118002100e41500300d1080800f100303081014a501c0e110381c008010540030400346043c980e4407242c1400540c02c00600c0d40c00b03140d11005141d6038088407640c41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834818480 1250 834817230 834817271
    0xe040b011b11060c1f0c0c060207061410060e0f01050a21020f0702030d090807050409060b0307030606050307080f060f0901181112010b0d03031e050411120607140f0904 74
    0x30b400211000420214000301d4400c035000e600c1c6c2070760341c1c0c1c40606880e51940c2c080d5100e0207003030361041d0b103402ea203041d000c44854109019a4008880055031450808040e12081e408101e051042c10409414003699801c0011901c020300d542c94000c00f1128070425600000644552a20f0030300e201244c000000311440c0018010203008a0072507616010000c6c04407428540390088aa840d0080b40b810019030030660440c0310280d20516011402d045c4440209150904661040c0c03490360f1030f540c0400040c01d041c401c440241c081207001e40103c09031b00003583c4c0d440201506120301c0c003102c0740005020034001c1d8880340100f6256152160081013604000c9810441d086d0304078401e10070032100c2e8004110501c580030901c00b000d85110000d00140e18142c00511040340c00a1040903161480d00e01020f16200e0a4415480345c03401d55860810f100c24084a0b03900d8070100000c1d40e11a00034002160703040400700b0a000701087c00c41d0b80d210380207040c08190b8020343d0030031a00039041031381001a440031103404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834819730 1250 834818480 834818503
    0xf07090914061302060a02100207060207021807080103030f1110140109060609030b3c0609070e0f1f030f0c05031e090319080402010e040b011b11060c 66
    0x40d114015001e846a12404143c400d46907100c2d220b001407005040c0040078052480e6640103440400c180e185145050ba030180e00121345955002441d041140741a92000c0b800c0c030611000d004a51810f40009010303500306000140034840c5126082c82d2032403058500a202c8d04581044e101103101e00c0f5425030251a0100032070350740b4080f01002003218080e9115040c11910107948200b541303861a182c41e5901c1c20064600c0784018183d203109409100030380d0740c3c401580001c0d41e400b150300c0c500001014000001038240c0388691480307402d100714180d01c2038282c400c46804035980b500141200e00003450080c00900c510368815083c4c2c0d0004005605948507031003500040005003c503c190090849961008494201c0a2001040907240b040105102d1a41c4460341c681124603240e00718459481161214440c400000d0a2104110031560300c102e1004401070240c0c1c003440704000103c006010303901c465150399041c000f0103031400b05120095001c0c090603800900513658800021924940721100d045c40e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 834820980 1250 834819730 834819743
    0x1903030f0525030515060403200d0b0a0518010f060503060f160804030c0206180117161b02040905030301081e0a06022b0b0f0a0b0910020f070909 64
    0xe0242c0c0150148158031070041c445124000e0a61003094004110103440402010040d080060081e180d00b00100041c5005c2d855003c0003d0004c09141340490305485254098959114450002138500580340d070040c0c1840c0000c01c1c1ca9a03807541d0449202c084900c808541e60902c0f10b01028150755030312a205407181034007590382c580e0301c905403041021011340b040600003c4120041000612903d0b80390f030440e2103807a03d481d424000381c000410580000d85044040440d031030081303001c3d40c2c10001e030b5441c40180c581440600d00c0d00c0720b607011301e101c0000c007042c4c18081041001107084100d00080b100803940104200600a41070400d0b60f41c039002405566080d225400c002815218034040714019000b038131004100501565503004080d42052030142d062202181100603403629000903902814a41400040d00038000303002c0000b20312011141c81c0c0621004402440f071650544201c0b41d80e070b202596010b07043c02c960307c2c0403481d0001c0c1e4440321a041c028000040380c6608107030040b1915134002c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 834822230 1250 834820980 834820991
    0xc060e0d020d0f08040e19060602190314070203010513050d021b01180815041509020d060b0d1401090c0f050d030c0606120302070504060608040305040e091903030f 72
    0x14416481031004000e03600000e240790500004250402000d0024440e080c090b0809940780c3c882c88044105079410302c0802040d4001c0044404a03114020040885200074821141030003c0360041800c00c110103001c01c0310184010b840c5100280845031201d90150080000d4a020501510201020307941140e42c0d00508a10316900d5100103011805003080c2c600b0301410500c0d290044d220300f20030700185c401c0c84040407000504210244000d1084c03003100d01540300903240078604070fa10884078400100e1480d10340703e1101c0150316140d8003d5413442e401180001c00907181c0001501d071020913503000f001c0304130381ca01c05441010190000b0f01b9162080f0342d080c02030340c2c440340841c4507a441800b9050700661031800e1751020910076942240d0721801001d0000741d85483d10b0000800507803108003500541d02c154800c100500f0300d03210310310040245140041c418201070f640204944694850884a0b904482c04120b15213820302ca400d2540d500c1014141d141c1aa6142c0a00035040c0c1c0155a0f00252900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 834823480 1250 834822230 834822257
    0x50a030803090d170a23090a0b01230105090d0506010308070b01050414040602070c030c0b09010815010926010614030c012a1e03030524010f050d14040c06 68
    0x90030035194400c00c454040100390383d110700c01c0000f00080d450000c14208200d42c1780c400704181c5e00302c030380c01614a01c001d03102400b014144040889c1040e44907107201001c0719060150030750625004030a840e0240303051039a80c01d1000008401c00010100500640100d40000041112190007041e05500c500341e4000c041e0faa03038041104968080300c00c5400054034100180000d5110783c0102005441240c50029a54a030f8480c085203a4083d00650000d55000401480560300040010b5109a0102000460101000c0000e000594502c214141305101c0400c00e0741080c0b44012800c2d10080410082141d01d540345404602c1840c490450f41c0640240c1007490865485105c49030010b103c880e058082c156034100d0260500c03211b503002910144400b84071041407900c201480c40b8000d001b075030080399609002601c81800d0a50300603005401032412914085660461400510404542000c40e11070302c01491140140401e5178100410400200810003000004403c071400c0e1401a03aa50403a01440d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 834824730 1250 834823480 834823487
    0x120f070801020c1b190603020c011a1e012106061724060d050a0504050f1c0f030e01020a0f030b032d070e0705040311181807050a030803090d 62
    0xf0b85440756070702c2d04149492407200074003c0001e0100d030b41c0644050300d660072a8103040e10a40c030681000c40000d400041000385148240218450f8410310030070100394815101c000341c007159880020010031300d480c44002d07034680e0103a02030004103128901c590102c01030607201d0400800c26401030784003140054a80007040e002d204a4903202d03005070740070207200c1050407810505400101c4030301039002e0b004200f4104038115034060a4000c00310120081003d06103480c01e02d06018451300d44080e140e000118110b901c0a0705103450080701003500340084071510b1904101d000e421405040f8210350700000d8442411644001d00141180c260381d02080000144010151140c424000c1c0d0703004aa007040c2200401e000480f07002007008121000c803400583c1da09a1010a0042110001c012600103d0200184840350036603035110682100c8000c0d151a141c00d40003030760600036091090b15080903420003038441d07080200340c01402004002c2000150b691800c0000741c0e0044134920382a004500425510602 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 834825980 1250 834824730 834824737
    0xc06050a0503130602210103210225050409080909072f010608061f06020a12080a0b090c0c1213061b0b040606060f0e0102030301170a02120f07080102 66
    0x45a5507961940d100c0c00000d1954030704034002030b55010390030815030000b084540d8084210b000c09951003182503140d81002850b030a4410005c0c1c4080580044007450703943d010640e00c240304074801c040100c808031100f41c10140407041e04201c3d000303031505800c0814400b0f00b1010301183e5408580100c2199030710f40048a501c1801c418110704081400b1280c42c081409030409078842215030f00006072075a840503030034980203007079030f484810900484162422030b5547d80c11101500050004002040d503d56401440a41010b03c1200b00500c24020584c01d03821900481c15581d4000c1005065041c54024801954442c000c02c4400d481902052015204220140c8600050104000031194584070040d076020342c0c03082000309544080c441c814002034405040d03902907070080c5000038600741416800351000d4881c011000030301c491701c201241603030f0780002224155803085118201e502450b0b400c140c64020341c004002d601c91581c4c0c1c007511880000142c4280103181541c12506680d541d180300c0d508030321 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834827230 1250 834825980 834825997
    0xc0503060f153111040b0304031812020402160c1512061203030c09080d18060e0a0306110c0a050609150106050f0a110f010905010f0e0309040b1206040606030c0605 72
    0xd28600021120000050701d442620340c141d03804141154020425813942d84640c1041940400100c01d00c010305902c201000b80290554134241401c50402e84d02030481505400001d1040c0d400140c0d08900f80b28000ca05035080340d020f443c00440f2511031108540605044101c000091141201d40110201d1030007054200c1c2c00c4d860550441c000140c0b4101c0103860000082c4d82485100e580010f1002c404104008103001c035a03840d00b040e03051000401c105943d90368444c0081140614600d070701030b5120b9400c0411a6800b00e00054032111100c0362205501404603110311500a42010038107200003c281b0030b1054452105417a510411949807100114003801600000341052180081d0651660000c140501c0c05040c0308c1e10411601e07500900e0101d480310b00191594680ca044020070400740070b80441600d4550301407007003c0102c040c05a40703004101c0220b103d2074940c2e2b0a410940c03100328001c020400c0000c241c50740f51a040c102030024142a2100300c500161507140080c10500c03a4050318540c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 834828480 1250 834827230 834827269
    0xf010c1b05041a18090a0c140405011d0712150303030906052a1305060423060a0f0c1b0e040507080d05090d02010207050a06020d030b1e0105070c0503060f15 69
    0x74445404070381c4e4010001000b401301da101d11095140800c42d0200300200420030400e041448035103038010710003039031010381c80ba40500e11040711030000c104540416075444215454503c01e51007001c400240604200c551a248040100d8004018154160070504449004280500080d01c0740030209811000e0b10004140380c00181403041010b14901008041d15034148ad40c0c80401e603107440c0001c1c02680960300c00c1001461070313110419a041100f45480e09850110307401e80c10646400000b07800440995450000c10003c0d940304401c102d503400c0b20700c000d01c05210118003e2503c899003441c1025003541c007513450384907a00001600e00400584404101c600380d03078a5042080a0007448940389100101700e056008490010609403115140311005110940c02030a000c0a01ca4014003141e03030044080e802000036800b2410070510700c004d030560050b028a009907417040142480d49041e04150812a8140140300a101e0084004480075000b60303200310003403075070180007010000d846071900314400e0403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 834829730 1250 834828480 834828499
    0x9010e0a081203040f0203010c0806011d0a06051c110a080a0207021e040e060a02040f08070b041a0c0d0c0c0608040506040611071a040308060303040b04050f010c1b05041a 75
    0x5000b80d040c00741d5002446011020f8040140d82c2c0024251070121803104002400d03181000121360788500f041544d01e10b10a85407500d01060404030320741c0003d6000b00014401c0000e40048072036406052040a0b0152030360400040e242029107000d06e5228a0900001440c44408101d082d0103074403c43d40d040f98010260345452400c5101a07660480041200e50b10a5643c4a4002060014400e0354410110078500580d62400d0880c102e0400f07d19030080c0b0040c0e48114401d10504a52108460a0b620f055200c50148402625008118450101380010f04d00807891481c4036242c02800041c2072611400c01540a9a11068112076044003190040d0456112030301007004121254000c01e0300c2c20340d07180340d0361520545803120080c64203401d0214884182c0e000401003410761003000c00e60007030720450107545002d190040002c0280100d009491141d00d8030003801c43d007070307008480144003183d0102c1c4601d101312400d8040b00c81c0440da441040d0059062035032000381c4440f0100e5585580b00000c0c0905032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 834830980 1250 834829730 834829753
    0x90c0501090608191a37051309020a03120504030b060d0812071b080c1009051b0f090a020d1a030d180b12090d0804030e090907030b0c09010e0a08 64
    0x103444517501039460550b0386130800955031901e4076000c0c00c012220001d1584d488640164081281c6690007005102c01d04010034803860380c840c1d404c0704118003001030100700c4200900000300200c41c26803000304004034010418034125040b1014000f16400ba4032201e80f25502e02051001c9501400002860602c0401ca0f01c0600481564043e070012254640381c11b0180400a021080f980064000e139241d07130b00414042d0b503881c0c00300024850b481c400076007031003079041c0d6940c0c9603500d013102003118035201800d2244481c592940360b141072510000801100c0390b418a940f5200081d4403120141132a01d0406401e2080c8050b005621216488050f0050400b40b5a0040841e500000b50f01070f6004814041000142171840310003502d84a00450242c4246080010b022454101c201c410001400300300d104010200c3c1d0015078180c0300240c1a598003500360b4034400c201c0e0034031450360401002c802c010300a00500c000fa4001802250000380c03609140c0d0340c904410080128101d10449005522011200c1d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 834832230 1250 834830980 834831031
    0x605030405011e0f0b030c0109030b07020a020315060916080a020a02160915060e0d030507020111010606020f0c0901180b150c030702040609050f04061e090c0501090608 74
    0x154814040d0000007040c090300f2500c0202d0180f9924040b40f00c44c1c40c0c01c1408a0404035108841021100300c00510b1611015000a40009180c0c400602524110b1000416031030081c030226503115402029150350b030040c00e214a054030b00c140c40c0c1c107000380c100100081c0d02e900b040054202000080d00d400c0303265076035204404e003e584201191001c600500307091503070190a1b071905e2009890401d0380400e50800c8030124161344801a03125108002000101c44544e0f01d44034034000c0819054a40076030b441c00a4001620405010750980c90707103610700140042c3e07859000c19044440d100c4441a6500e24017034404004504900b8064041c1307280008400902031180c60344a17100206010b40030840c1c1c102201d01d40315858012500030401a000003ca03141186070510819014000c8a401004281090580d0071203103040100300405103681d541c0c000c01c0401e80580d50480e400a1841c0030303c0b412000d482d000300c0045803407280780d002c258805008501c05000e803603594450040d911482c4c6110074a4074800c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 834833480 1250 834832230 834832237
    0x1e0c02010504171b0703050d1e0905040b0a0308030907060905040c02060a180507080304060f0908030909100f08100b03011404030e01090b0406051b1b120705040509060708010806100605 81
    0x4c80c0c2d4000d100302c0e08901081c01000019400752000d031546104444014226402214001c0141d41903c0045c0b00030715044044c2c001543c82c01c0c1c6000800003407004c0400c00556403504013038241c03600402000015900024040c1c291011a92521a07555070b82c0140001c0d41c00340418000541c0000000982149180c5c0c0b0041803100d044150b6008030b507140d00e40900f8030000e0b400050054200060501c006031700559100d0440d03849103440c0a0345442c00088039164081d14480380e01c100c4011010951100c0141c065201a100d02000703d56180d03901d240c105c2c0d860324a1400002d800b4206482421989810f10074030b10841c0380a100075885550f05e070360440344200144c030418107220026001040c103011810140003c0c00407900d41c140d8401413800c0d194018040403208240640c02400000c0c2610b05000154200c2c01d01a12070084115540201c0390805682da0091034005181c4810001c00440000c0c00900441090700e50b1810341e601c40d045241c8403041110a01004c101c560001c01102d44241c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 834834730 1250 834833480 834833497
    0x903020906130c0c0b0c040f030b06010e120307021801030c1703160b010e0901110418020c0d0f1205010305060105100c170306040617060a0e070305011e0c0201050417 73
    0x442d105415611540b8080361801244000000d000c040d2100030071203410012070304003490000950902d4138100103a4520040c5010040032404003401041c10759024003641d02c010b4000400c1545009c040c600795560300c0e000301c030099110b0030002030610103141c19044541d041c2d03030300182e1100e038150030120701540208031000300e43c5480c8810480060848401240405564421007000d609540750820310740c1100401703080050303164034102d80c08400841c10400c50301203403e0144110483c568081c0c0c00b800038010080140d0780b82c00741980601d9030f254080b01e004c00d04106911812447c1e491001503008451090000908503800f003001401103103001c1242040121651422803402d58180d0b03900090002090407607141c980c0d010061001e1440c10b03000e000d01611840322005018007a4801d040e994041c050709a40c240b0340c1d80e000d00d40c510320081c08080061900040248948055000d44001001210b824012501d1a00201c80070700e61060180e40d01641e00f2074800d0716a01490514030318144c0c4105030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 834835980 1250 834834730 834834739
    0x9030712050d05040c090f14041712040503040602120f070308060a030f050a12023408060c04050a090216020114040f0b09090708190c2d1e0903020906 66
    0x64144140070b405441c0c4110f124000d070500c1507203452801019204151f51100f0321600344401c0d0307004014211444c50740650401104214400c80075024842d40c8500c14203030103522040d004000078440000021b100300c9036030b6402c99a02070003000391103600c0c1c001c45039188402e030420411400031074811013000390044002440309081656a0392808806120f1480498050708081002000c0c0070440880440008440c00030307008085d0111020003020752144103900701d002040c240541c2808281d12402d02600d0210119900d034203182000d84003607006031162500c10162040041860800b90090703640032031541c20710100c40f21135a8015107100c0c02080c03060354450307414440091009025603414004080e109915507581c0ca05005004015900615540074802810203100c64038071102d0300c3c2c2d00c414a503501d00107100018800e04641d140c0150140b00104000d00240710a9000001a4122a08038503100d40e41c0c104100b2800d1181a8a49000d03440410bc0e204001c2026051030841c90350700090042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 834837230 1250 834835980 834835987
    0x10602030403240f0b03120405030307151803080411150405101112040504060b2a010e060f06030f01050c0a110106091a0a0609080303070509042c010b010302030903071205 75
    0x10034030f40440b413030109840d01540c2c07607408035802818180000354242542ca0280b0f45001e0500c008170356a40716101000b00b4013015140c140310000c2d4944d1061b002481414045c08107804a41030040458030240d03010380d644110100060360500d48000100c8805031401c440c84d0806140104201e61441c2140510040c01030751740380072008003402d20000c482100b004001c25105d03401c00c030034002214080d40000440b04410044590340e01f041d02c0f0622850385540c038411078240d41a6082c03034050005002c203402c0e01d00c640402d01c01d5400340712510b244100345c203504851580100c080c406098600540b552901000708008aa480c2449a9a01080b00b1038603070011500b2036a0b4900f807001c46e0302035074456040701003c109024107072414210700c02c000c003020b1403c03094060038080c103c0d84901c0040c4c9074100703120002031001e602c2c0e00c075a00512341e006145080c84007000c100500c0c019000054018518141d440e040b4500000d60003171083d240a254180011030828115075144495400c43d045034205001091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 834838480 1250 834837230 834837293
    0xc0405010801020319061206020703050c0d0801030303050a200f0705161d0702030a0503130b13020f0121051f060c1a15040c140a08060f09010602030403 67
    0x50242500900c604400141d8a00e40149220b044c509480248600e43d400c0c02003c00100ba541c41d240100700d604400d00580d1840107281c00e039500d02c600c00710000c06000f1211a4143c20b9002000541228000e40303090015030742d030380740c8042107442500108426480620181c0c1d444030200b005041000000b41c0c0f03040c608203e58845610b000c401d504e4021902c0c24501c024021000ea00c0d2107803d500307541407481d00d910f0a0540c4060744a00505201004000e00400010800d000310301c42001141e4000303248551600704105201c104000c00c49003a0300648140c840d080c0c01c2e5108088485a204004d00303048001181564030030042c040c050200c001d04040740d007941d2280200e4103440001002541ca9aa101002034501400b0141c00342c884114816800c20401401c4041d901c1c8001002600321000150b45c002c2640c1607414001d0a0840a6200d50103c0e0107147c240d00300401e031f8010102100c6d140503803031302c00d070030840f4a000074003c440c01a04280001c20004c1d6418103a4841418800c01211802c03980c07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 834839730 1250 834838480 834838489
    0xa0905010209121b010c0309090c090b0a0f1805030309061317070f0e0c0f0a0908060117190f140703051614030706021b0114070f1415070f020c 63
    0x41050018254010007013400d825030b54402c40005046080c00c0c00d043c20290742d03c0180504510744515031625407214031110100e4442c040340700240c106c0c1414030b511999004402004890001c1c803030000b08200540380e105908100120008030b4000400851810903c40c1c00e214407500710306020301e1001204080480c130400c03c0813040222142c440020001c1519000484070603804030703800821810154000d1210f54400c410403549103c0003000d16554645070110200d803000404d030702c07a0440380503850010070b5a02250300d103401400c03a4042200c100c00410320b551041c4049881c1c1c02000740442582400000e07002c00f504039503024010082d1001e8541c0d83d21100d08150001c07201c1d00c2c50580e4000280000b80c0d8802c44040e01c0384041c1c00030000d003418480003030351310b85400310100c41c030a8401c43d107018240e11480e6081d110b4018940819115040752401003507440c80c945044442d15081010100d001d0380c002580c0c1d80f8041c05010004240d100c9690665900708604110000c50142c44c491842a0300c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 834840980 1250 834839730 834839749
    0x150111030301270203010e061002030c0601090e1506033c06060117130605151306060e030312010b030c121504050105060418020d0b030a050a15050f0a0905010209 71
    0x50b85812840c2d240260f400d2544603034030a9002c00c0d11403050005014071401c0001d03050b0b00801c15660070102c0519940140c3ca9030186085115240c8202000482d0024654105103540024001119407c0c20080c2800c1c0000d04111195074042c1c3c411442c2107038590750100a031071f802013042114200a202e20146482c034690389e100400e9250301c080c0512200756445205864000410814000c0c107007400c406c0d15130780c02ca42c484007170f00094507a80851000d042c50304085222354002401503454494000d0380e82c021b09860304c1000041825014000c03c1401e011080320440b00081c041c80400360b0910310f07074641581004c2e12401c0d03811014040d0411911402c1a51400f80c01c69245c0c2480c00c1c110401007000360780b8143c101c14040c00d0180002c00441c5c0108040c0410007000300b00142c0c80b105c1c40082800140782c0d9003d020341c90703c903109554041c040b0204842c69554056008500b415103030001302001c0c5d40042c0c600800031072603030f80003941c1d5030204d0380700320403161003040054508080900000c0b040308 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 834842230 1250 834840980 834840989
    0x708120d020a0e09010e06090612150408130e040606140a06320903010c03020c030a11150403080a050a0204031502070204091502090306010801090803040201080903070b10150306030b150111030301 86
    0xb06c0f032401d0014501e003903049298043c104540500c0c1542c1c03104d050f503444105045400d4656200319000ca0200300840f01928804110030020714400c542d120a0b08040c00803d840549009103891404100da444440c0f0050b41200b01030300800328945015070454100c1c45e81078074002d6401d24406000e0401401012a018021646200315141d1001e01c04140c21680c29a10b050181841040348100c044008000d840d18107540d07003000401c40500c2e2441605143d010040c1207480300041e8200803c168015040900841d2a200c0030040c55890461040491150b8000501280f00081c0e0b4000b00c002c0c15001824018405440480d00340d00c10740c0c1cac280c024001d4076544d0150703d40100f0100038030f060810810340100042e10003444180000c1e103074a00584009000a81000032020000c0c04400c0100304035802c0a51001c005c03031080c602810150020500f034040c0c45000c801c101c220342030545c400d016520030340341c10900c1071406448502c01c00c6281c0e21492803050601c070a1403900350104406201440c001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 834843480 1250 834842230 834842249
    0xa0b010f1701060e0105060903010f020a02030c0601120506012c04030f02010c0c0c052e0f320904061e060311210402060d05070c050708120d020a0e0901 67
    0x20350a203031441100c4415003040c022143c2c5032403400c0080d01031105007107044600c203803080b42ea40c500800110740501107240d0030140c624000110784454550002c000c0c0030301444402a12000d98841c414010318943c10180a0300c1c50340400018000101414014841c994481310f02901200c480c0e0800305040c40116803c1c1c01041720105040d04040c0c0a0244c44000c91710b40ca01002801140e641eaa07083c0c2009000d914002c42c0c4004001281d0324201c00c07102c0000c146104441241c5007201030041a42c080c61a0b0702e40000c0240340c00498200104280003070120503202c1c011007400e210b0038444106d4001100480d40262580400254403282901c3c5040c0380003555541d0805030f00b480c42c0070b002d50710b03401e510010721002007240c2134002402c01034210040e2804240c4803020740b80c1d40000b510700d0051203611b60f00c40d8075100c140a485900078104010325803094050311810350b5618051038458200c1d8404080001007041608940c0c1444d41c010f040d6100c1a040c0b40404000e0080400d0314610242c0007003825 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 834844730 1250 834843480 834843509
    0x604030206010302101701170f10051909031b0201091206020c150405030f160c0b03040203070503060705040e100308030709080c0d0c0504020307030b0405092104030b040201050a020a0b01 82
    0x15070a14410007540170a15007420340d00700c692410003a24140e8144110090440484907040542c1070510201100194900803164941d000c1407005004100c1550b900c01c0303040548000c0d04000c07070140100c0c081d16805855411640403d42825050f04981e410100c1c100640400046400041e9280006c8014003803440161200c080082103840d000412240048808548040100094001040341e144070b20030700c1100d8813590b01d00b085080168071038000504030716500c1c2c4040385181a440155100d940210210703a08555542d0900d504c6030170030f4070028001801080b09024016200b18415005410a03c000e8001ea64030380700c2d203140e9003095981400040d0184401c101c0c100b07040041c10812001140d00c0c401200e036503550f8610100141c407800d4016900031000a900b14000d034042100204043e000b0b202c9850250304060f00d6452500c0c1e0b80707200d0103010000d03c80f03a001c0042500c2c00d980c0e10003408040c0d61119001592690003400081085100d1420700030000358040318201e00804480c400b1086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 834845980 1250 834844730 834844733
    0x905091302031f0f270503120a091e170a0c0b07050c060f01180f241d0108060703050c07141b04050930120a11070c0612060806040302060103 62
    0x82e00c140d40201c1101e1403d0488000c44107007140d45d8514054500099a4525210340c80e00134158002c25074000c8a0020311810071507a100c2c15007010254510843e50b2110300000d01d09001502d802c2680c000d0701c056030303c0120341c890b00140b200410900e01d807803c014901400c20b90ba81d41036100212216400110082002d103244a81086960b0b00b04d28805d501281940c1800e42401c00c40024410481c042d684070480d8049819481d4000c0d50103840c40e084010000829100b40940948070344114048201c000c50343c0d86d501e100000305207050f5920a00605115140c0e4501100075101c09420420102000c00c904400203a01120607003011580c0405414452103100d90315400408820b0554021414507042016807200840e68040d5041c00c0201504a140500f0b1481c6e107801601707078003203050040010030007901c80382400c106105083ca5401400304000a00ba0311140d4000c84100400198103003405020300350040e00c0070306050103d200002012585c0d00e81285c03030707c5ca0544068000d40c02450045c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 834847230 1250 834845980 834846043
    0xa11061e0601080702150402010c052a010513090b15040f0801050f060d0b040305360409081207051201091a120d140415080a1b090509130203 62
    0x1580701c0001d0801d82c8851401c0007019442e407110500003c4101d000300002000c5a00039591280f4860b000341c01c860b407003c00c5060309540c44003420108580c1e105100c810311100d40c49141115220007444240c0700242d4900520f4030040c0800d480040e51143e07030307681ca0b0028042c055001d440181045c031000964035140628041c2164005021206414a0841080200c5d00c41011a001e207a40c0310500102c1940c0e60300303040b074545c041c0d0411900606040180752043c4a089001000e608080e000c21490600c1d0351b50070401100d00751032008111440c01c2c440903480200075002294080220700300b040ca800b62107040040d680c00c0076040111100d94400c02e8070000704c490812002c09400c19a02c1c0701e1402c02c8103107810741d10b02403809d00004222039140030040c40c40c0040107030350083c07140c0907241000d4903081c0d4000d00280da0464201410a01d049100703d80740c03e40030b001c0449101d0649800781220f00b08400d02404c1c0000900001e110100c0103108401600e04002e017200c4842403010501003140c5581e00c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 834848480 1250 834847230 834847291
    0x102040b0c1605010c0201080f060429190303021e0304030204020417010f0509070b0c10020c01140a0501150806011b0b27060604020a1107060915030c020d050a1106 72
    0x20f504009803001c41d00010b0740c01008580d0400284100712010396951000207002c1d0082e00261014940d5480c0d50b4842601036140e0302d050b83d5800c5881c22084100301e00c0003150001588400b43c0140e2018200003080d0b121603586440c40143c0205523460a0380302d80108040c3d9000354000b41c2e0340301d110404500c140000780b0404101c00380441d1b00b8032560600d600c6480d5a10300e28020840241d40c0000c000e500c1c1e040800c05000d05415903482903458081540c0b0150007411040c0b0b4884200c6610000110b04083c24414181a40c4030b06560041042ca00c50040768a110002c2249042c08511511840080f14403603d920495208044030380070307854942c84c142e440c03030400c078210100c1c032440c4c1080a151f10408070f00a42e01c00c000340c0d001a159101a4006c032808242e4002030112030180791380c08221941c2c803c80309070566040006600400c040c40380102c00300c810003d10040180c002d0b2a41c1c1003410304c1607000340f101800c145440b109074030348030f2091401d00c80b0070b840140c2e042c04c40c084010308802000114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 834849730 1250 834848480 834848489
    0x5150f011a1306030c0905130203060102010b011404030609080903030d1505060c060606250f0629012304060207030c0503060c0d2403081809010b0a110102040b0c16 72
    0x9410001c0a0b0a02d00c0c1030010741c014042030645170100e10440381e105055010042c0801080a600e101525407100c000b50300980300140103508140e406100b65015280381c110700c8104a981078500307441c40d1a05001481480c000b200c0d01601000b1400c0a540c040018108006000c60001002155010810706080c51a40b00f140181402e100c040844a00030800b554460000d8810950f47d00e40d48410301102e00f030103140744010740b000d82c00040c1401a103151043d00d0303030301c1032808014041c1c0004020440010400800000a54a0003880d400c2d5200b6040b6000311221450940380084414009000c550840d400500060b40685420024085090502001080190003030100c6041c80303d1940310360322a03003000c0040507480b400318090035541d400252801965407041d0103001501c3c0c0c40d00c0c07802680000c980c8542050001c040540f1890943c02a504881e12011000c3c9440f681100c1510100b20000c2c0c941e03460755013400000f031042c503018010248000c0345001340210854200701c000400155421 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 834850980 1250 834849730 834849779
    0x807090e0c041818030206090d0e101b0819170108120708041e0e090c0a050f2103071403190c0609050714040c0516080705150f01 57
    0x611492a00c0402240c0030740307600c5031030841203c0403807488001504d0b8107254900f4645880b040142415070100b00240141072500c243c030445454108111921070190903141c0c0e100303480e460900034080c0282c18000e01010104107007510300b40961140702e0079801c141811302d00f191180100b100c21039484210b6052003220780da4030100b95410300030801d03030711000c03001c0c4e107413006800055140900225000349d17401800f08a5a1b40d1200f20010540c43d2440c5540c480c80343d541e45400042101f0010100c0d0349190306001409003c46980b402e010080c21022480c1c4040c2c0189050181500c05028403000681804230b110066941d03043c00d291810f200e0780c803071008036101c1d003050005d49400440618500b165079100e19140440201d6801e0410040601c00c000824511480a0010303049052004081c03180c0f074110780400041c01120800d84261003003200a00480540f44240c40018808502801003207005200b1110f04001116420004003c143c5100c40c020f1a03100040040040c010f04002d02e40a0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 834852230 1250 834850980 834851009
    0x2206210503180a12060609060501020c0f190f0305010e24040206070819080a0b100503041401060503030a0203220e041410090807060507030204290403060c080709 71
    0xc8031580c03680030b003a0090114007080e2220b400e403a80d034510b1210280006840f15100c5082da403802400600c1c2504c40c422030203081000003d5207600108911100c0c0002034204c50f29a20b402c070800611488214904950b10300b40e98000c0744404400446601440c424400001c08440800c1da5a01e891200c0b1802414403502100f8001002c40c0703000320717a070060f50507201a52640c0061030103801a015500752007082c41c888071003013441a580003440307501a0b101c00e5001c100340005801030041d0b6420100c6224003040c410400b1a00040c0d16060581d0500501e10000070800e866800007401c6a000b03414820040c0d0021640d0800d22075803075070f216014401000d0200003245000b06800340000000c00c05820900c10b0503103201c0d01ca0050100240d16060640b04000010141c0b824403120b40206500341d038401d10380b10010b10054060301c01c95007910600082d203198416144085000780350408154040810203102c0040001e2041c094882c42c5425a00c40c00c0340d500d42801c0081650341154404c400844804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 834853480 1250 834852230 834852233
    0x1c051303140c040513030305070509063009031c0e062404020301051c140f030703110c330403030305061309080a0507020301060302121606030515040b220621 69
    0x261085c5d01a43d40f41c2808036035a9500801500c05001d0f40846035004040000c40442d00c21114000c403540c5810600714080000ca0b0740f10000707600c203040740c200c010342e8010480318056010440c01d034803000d108104003103800380d440802941010015500041c051807400960b1440420342d0102d01c000401c10340d8218199850040014149408004135444002204140c1c0f4203014201d9480084c0c03e03405012030310f076642c501d01c00765030340d0380728034002d60000322043e55002d507030580480c1740b0460400040941d00318450140c043c003402c0d007550b4541c8140c00b40080708010041d803010007510056000e43c6000a0320f281030424002100c610a0206000502e420381000c0021099021b032a0b8103411490060b03151519440420700510064002a41c0b041c14000c0b441008040000e41c825103580c0b00c41c044440b0fa58403c41138007510700039111411900b89004804085081540c4120300c0d015000341050707062445c0c1900150f008050200000c070b41030301ca603010300841d054445a80fa0b14410722064880103100c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 834854730 1250 834853480 834853501
    0x4c022401051c020d080406200d05030915090604150b09070509040b090405010b1c08040902073008010b040e0604110702090f060319051c051303140c0405 67
    0x5000700e6100d100c01210b4405a40103100c803002901d5805000c52020103200d00301581250407501c1201d00190313002c00c0c02c00a000d507410a025440312000f0041041e6214071000740c51941004000c2c400c01d104040c0d0340300509000060441c040c20300380010f800c027810542440895480c010301180c0c4407900700030b040503035038481d00d03040b40e8007a09a14116440d1049480003038060514203070180c1d400785807001030000f40003043d8800525010215696503c08051404100045e40d00e15005014003406020800035203105030000c1505c18880c802c4050014024401180c0c441440000c0545140c0000300c002c40c1e0300d4100d0415409004038086160800d4039150450030a2040100176138080d03520344030404003c03115481078078462a0300810b0400e4603c0c1007048480c084da012518140310b0300c81c80c1d40c0a902d84114100100d07110b508040a043d00c1840c0806500c1c1004240c0300c0c04040010800615100d81c02d07590049000d90b2042c070b501c1001d50440090140380c58100c80303445124510744820710854031203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 834855980 1250 834854730 834854803
    0x5010b0a23121b2101051f06080712090b2509050a06050906070f1b0918020409020f10090305010b0f010507020d0305130b1b0c4c02 58
    0x507850f1407000d0428001000c140d000d03012041107000d0041c0da081315018030006400c140e2007810070481886288140040500c4100788a1042c0300c003003040c490210342c5a40c4250598821590f04039008640c6103401d5807102a05c0c2800c5680d01e0201e181c41c00c1c054980300952010b88080210b510b072030010070782024006940e685151046c41c2c280007000139060032549907281030b82e8601e034004221040b0f07072103036060910040b140d0345148040000c0401d408510b121603841a000107046292b0071510f01d10ba2a402c0c8070007045544810f80e44407101e00e000f0903040e940c1c07065800c08860240e0b1000b1815155113461402e4504c001d000c2c1d4403070b1503901310980c4140d91020543e04c00d250101c4801c0911809420203a070349226084125607002d0b00f81002040315003143c8010329540700e01000c5040741e07100551140e031301c070640040c40c6a800622500010418403915498103512984440f00300390105601d9030840403401703a8100c0b40c0d02400c2001030316810701e405020a4000a4981c0444a064115030700c005c0603050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 834857230 1250 834855980 834856003
    0x209030c011e110106030b09011b0f020a0312090c080c0f09040b0a02071718010912020a03020423090c030d110a1707060f060e01050a120f05010b0a2312 67
    0x315155400b83c5030f001c00d400420096400003002d04079810314106050180815132a041e065008110080c69280e01c01c1d0110802e000305507010b41690041503030110341c2042412035418100751940d850f903000c1285200294020403540c0b008050107003040303052000c0c82420400070b5114004100800021600c5034071016844103281d00016034501061801c1c284e0b40d2650b40d0b440307117401000b0032070050701b000c4550201c00c8440300762602070f40950355060a0051b5014110003c1d080502543e0400050801da000707206141e02035601010350818003c038141d0074180490b400c0d050360303009180d051a1820144104551080c051810b940d08805d80c1d052140d854080b50001840700d80908a0601c01032a080d05654a041c0c0c04641440000707904a4690050b0405001c2d04a00b004130a00003c0e051030041d02c00c1007110002c030070303808043d0320f88e03100e0200c0c0940d00c00003070744e0b15520b900c3d000005a94584d089000380901c0e00200354034083d840245100b20300304103003090180108240e1101c174400c00044111518 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 834858480 1250 834857230 834857237
    0xe1210050a230f130c1d0f070509040b04020d0c120f0b06030723030906040c0905070221070b040804060e012f071511010b0a0303050301051c05100209030c011e 70
    0x5031134206030244e40100d001000341044e102c06a0119007180104884892544c59a0100c5156101c240b54900d44800981e04200850b1040028607124201600f040c107031920010401414a2268805501600c0c0c0c00d200040028038941da25020601c02481209400c9212000c200302c081400c5002c1016484050510300510040b2950100c1c40c2c400c031401b20319444c1141300d41503103a0501078206569028251000c842582c03240304045104201031240a01ca00080d5000b06010100480c03103100c2d00200310b1121503050000c10160700400c0358444154000c0e8131502a05544601c1c0800060400850010982c100103601c1808410410007010892034001c06222030f07100c0c507508000780382c0703403e01550090036610381404031443e40744d0304a00140d900d11a80c6009001d4001c0f00810480082c440d40002004520107000501050070400b071312440003001c042074007000c41202e844051816403803038218801c49800003103031410343c1004d0181c0001c0090a083c02c2081d206143c070340341480c0c01220540004c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 834859730 1250 834858480 834858511
    0xa08010b160203030d0504060507170105012006010605071217010905220302010606020c180109050615040807060f030b210a0c0e0f1f060e1210050a23 66
    0x201014590104010740d4000c00702c0c0e540e45010903ca6001d403070102e6050f500245032800042c5c0080c0510b0074580740005014a060403a0f08250054035089150b001600d1101c80000b41412149410051207000c0c086541b58240c51340080c3c984410820f54035580784007081540403840c4c4840e80039100c0d250646003940e001003001e50f14001c007580c0001042481d1071810002c40c140d107082c150103600c5441036840b1582955080302200062003124203107960166405040000108448011648200d030444030041c505e819036410a44902e80d6a00280c101c0009904103d0080100580011070100b40c08030608060160300c1c180d1002030103041c800910b10b588061001340c04140118140040032a0703c0d404125504001c0c0c0300d0700d12520007641141c01322411440c007004140000d286603451540e54564400c6c1007091810720f4411140c000c0e007a82080e4005800302010781ca00d0000b40402240102c25660000311807512104130b0b015129600d80d16100c400d070b01115042406002080d05901041c1f85810f00762 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 834860980 1250 834859730 834859747
    0x1027030309020d0204021c0b0f130f090203120a030c09180506150c0c0f15160203030702090103031106061906080421091406041d0a1b031d01020a08010b 67
    0xc0c201d111500c0254046d00c0029228401c40001075a02046402203801300824151001441000707103242e10515031107941c544991029840c81d81103c1c0c23500c2d81d2480301007000b00d81a808685030810301c0d0100c1184000200b28001c90650521400d0041e400600d0300100852408103c0181c2d0b00b540408003c503a1789070000248991100708800d154031207400001e955805440a032942c0780c3e0040001740d442050070304c18103400d5251250813a00440c1820f8003503894030000083c0d52a8800070300d08100d800d03000c00e000c2c0001503030f10610f28030300841c0030780c44024440100665aa04004009080611841d50340009540a000840603642990024105601d503500d80e42444504403864000440701468072940241042f940b01c41c00e4000c0b140710103040b802025002c81008002d0146006520003042c8a00e42d82000c203000c505890341040c0c0d151000507020307001081c0d81005070300c58800c12010940b100283c40c404100c607911259882c2c2104000c500b44440f5041c010500d50041c428445403501c08544441d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 834862230 1250 834860980 834860989
    0x6142e0f090e010e060408040e07030f02070f06050906070801091e0e010204030c06030603023007230603011401080414070806041403072f040e102703030902 69
    0x2400350000003280e5000680d01c124140240c80c034007055000b01d5007002140d03400e9440c001003440c016079011083c4c500b403c0c1403071811a05420000c220303200309900c8040b604000701c0360344010403100d800b40c0c0c068003946c401c9003030840c256200607003141c80b298001e5041000d8181c0c4406002e05640042202251100004013000c424403220000100781c1c61500041850007241540180100d900c244501f8900c103071303079403030650448215100181d006115601248005092110b6014400c44007803d01e61803204c80a22035480c008140d00050300d00b500c01c00c80300c040703580210290701130003404444803469581071115100204100940c40f0303040c00608000700d801c001004e40665044a401d0b4100d8007907654803c911542e4040641d81035a8028554244801c1100c0c080300f20f0340c400b50003010314039044484a09400c2110040310490b4484180700310310740103503501c03405080414054a40108a601e00d101d12040481e02c0030710143c1c5503038a20541035425804507140c000301194041c00e001944150900119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 834863480 1250 834862230 834862321
    0x4060e0619022209020301030611031e0604270302100e030706090c030b090706120204052404120804051f0804030509031204090203090d1107030609080c01090305070614 74
    0xc00c2051400f00022034404a982e02840c100e9000d00c1c1c050200803904040700790588002d84000041898544075180d42060128119030003001c040d10000381c442203401411131700e007240c40c0c7e0017032030b0b613201e14180c405d169040060103480d144a4038200309948552000c142d40b8452984028144d0783c40d481c5070304c20310290b09220380046802000307000c441e18000c0c40107621111180500000705800a010013280300351842542e041c1e54001c0c01d040c14040285228840d4003e00302080d4204640420006c281d50b600714144454147c81110156211030401041080e4440c0103001e0300300d00c07080a10a07202c1943d10080d610780094160a003039a5443c0c1c4800801c0c1005000c083d910b00080d00007400061a01c00c0c1d40c0210702c9060039505842e4130340c40c200800c8a14405500104855a0100780c01748041034844e8800e00b2414442c110003840e211203018040d0954003020030a601066000c107118082c81920300840c142c5004424821800c0d25040e10318003020a580d4507454040d034031080c0d00010226551555 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 834864730 1250 834863480 834863527
    0x60f090203190b011d040605151203070b01052e020c0d120809061b13030f030804141c030209030c04140a0f020405150708160303020304060e061902 65
    0xe031100200c0046110541840314401210b00d0042000001007101d101400621844017a1166150945507510354502401000d800d41640808800c4c0380850359541da09016455499407002e0350702c801c070608051152a0050b03014500a03a2010214640d83d82e803c0300071040c940902081301c40d50610711000720718010341d01c1204c5801c5050700700c4c0c00042c452030b030301259801c0240ba920300d01c0b10307920700815507241c0c1c1c070581e0f0440300c0385014905a4962000ca50142800000c4001850364295803521b03a15580f406184017500030800c4103061005209114680c150103005c80c000420440c0e0405076041c11040000c1c03921803c0641c0070486500980d0148203944a00400a00500c04043c541c20540203a0300c2c140c4200420398901f800302c4000304554000e68048801c01070076565450305c1c01940c0080d03940501000c544e006c10401c0221085551400304140260003076a0042c0c40e803800f0f00c1c10104070340c0b4590040909502075801c00c084280100304108500c054030708090780300d804400213600e1a401c991003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 834865980 1250 834864730 834864733
    0xf1a0a030213030f0f12030902010207061b020d1103120403050d0e010e040f0506030609070f05100302040e01080706090e09030a0c110a030f020f010906020312040809042a0f0507060f090203 83
    0x10700c0818003500c1d24508540c140035241030005409049011f404980b000000240942c0011030100282409124011031092007200c000c02d03c00c115a002032242d100200c0202d44402e00d81004c03038028142040710030541054000010302c5c02e429602c9a65880203100841810050040c841040d20f9120341140d044c110000741003440480c22400d400da000d0901168698000d00c0341000003440300030b00051034000c85021002c5804241e080005015650341c6108841042c50380030000010950b010030b00c01030080404001800090342442c100404070b42d41e941c44840310304084401e0000700d41003c000c540a03a001814490200c2c0700d80d1800c0161090100c02146e4400d400c5070001040c0702c0c00414070f800b19442102c5e10703842090713800c0c01540c201895004110043c0d106200861080c2c03500750700142c0141c0900005070034a07030000005400e507400ca104108035429400c0420300401079424101c600761589051540103030050541c000c0042c024100003805054880b6034241c40b01003903a0202030010f40250 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 834867230 1250 834865980 834866003
    0x4090203101d0a270816050601080706140f090904020a030204020a0233041b0305013b1908040509041103071d04080a200105010f1a0a03021303 63
    0x10101000c11001c49181015a09080c03005011107130f2120f614a14403200360071584040d01c00d03110700440340c1000503000704241030b40c100f03c400304000300880b5008000000080200030700b00000103004603c0da030030202c0b07a51400d001c823007109840d001c103544040c0000e8a07581415550f50000950b81e208039400650050301c00a441c4c40380644c046007100761044000302d1908180a002c0d030520642c40c0e420b00c40d650340142c1d0404240000c0c0250421142500d07990020740c07007103442c0e85030903085451014004959a500207a06c90317070b218007002980f8088001c100301c00185403940801a8585019418800390409401da40e00d041161090655003e03190103040c207a0586440d19010707800200284900b4840d10940384001034119480901d080c00030b803542e0200415407035541c0d5022141d000104400b06201450340340030020742051001100718103000c000401c0b10352401054014503509600140800380701941201c60050401c1c007103880d80041880d00694a424108445000410039000102602e0681 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 834868480 1250 834867230 834867269
    0x7020411090a050d050a03030c0909050a0c0f020318010f021203090303100e0c09130f0e1f0b031e0f3304020f1e0d1b14060409020310 59
    0x400070304032000e820758408140d07544450801a07440240b090041140c2c0c004110f94001a201f0b0b0006030140e030341400c1482a0a8440c004201552001c8038140c113615a00c10b040a522075100b9140b1403600000d001135407804c00f14842600c408140c0303500349414015200280c0720703098820807160304a0f100b48011145c503400d0100c0381c95202d60082c2c1700b22031480f915a8010030701c516080c101600680681d0741240c83c00c000241030080d940504150402580c1ea40c09480c0324104c0c00e03001d810205000700025000400492034154007204940116a01051070250f407940c19441c00204d851501c0324100c40c000b0240301c03082180e840c01c042c402c1030100134014015000b030501060b000c0c0030701d00f1429040b01c90150a0b16208151076035011140070750b05c000e2881c0440784c2420111001d80004400d0b400052205a40d5070204844058000044899040c10100684160ba4840750700010300800400070502519102c00034520b400381e4001c1f403034840e40c00800b11f0402c40780c822111000304a01210000d031841032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 834869730 1250 834868480 834868511
    0x60521100e15010609080d08060109090f0f0501090501060f0e0f040c050a09060338060a0507020307050402070834120f030b220b1c1716020f06070204 66
    0x10000c00b4094001000046440350051841000344d800680042402ca0040307c8219a6080e024040c1814003582c004046043c1c0c030b071030107811480b06010030045408050380d82e107002201c6050348051461842c180041c0100c40c6d004051084103922894144c540011703d1001601c21900340040b04d0f4801c0c540f643d000c1c0f0890300b0402800f141a03071600c54901c1691755607401e0703042d244003000b0740301c50044180002042002a100c040303490480000014101c11002000c207515502819031100881c00101e407601c210b00c4c0401540c1c004c5d007415102981400e01079030710315815004116104023a1160500c01400001c003100c205403507455000c0c074000081c070b41401c00c3c051240e0116141400030316462210038901e4000d00403900c2e0110041c10500301c094041c19000c2c0300c006a0114440d883d071302d402d0304542c1c0740d590030305550030300e1a01104905504064941708004000810003080310300e03020b00c061074102060046400d030103a016034046a055891f00005003a920849400944c4103241c403d01c5400003d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 834870980 1250 834869730 834869743
    0x30d0e010e0d03110304121406061503041b0602071703070f110303070f03080a0b09040314130503010207230604030804060c090819021513090b0402041505031009060521100e 76
    0x9503146015484813048c1181c40e114101c40e40c0750800b462202c001c0c8403104201c011588a03000e0468000790070080314400b0742c06400c0794130207001079000300010301034098500c540f601070140d0700300114901a099907454003001940c1c40040c0440c00c0601008005880034022100600e9000904082c000b48620300a0200c0b00c054400302d001501c3e18004091390705044c01260f0155416440300800c900900c0444505580480a0746980040604001982ea2024009850801e03c00d045e082d640320394901400e40000709140301e0180a034021002e010100350804011604a034002c40007003203068840da015a01e1100b04d50003144184a00760030020411200a0090641071084480e01d03428100e22082081038044e84514802589541d10200031400d01a4070042c500740c0060005818a41d450000000802820300740801165000040240d074402d0000b4500251040c068204101402d210100b1000728215508414000141c11070100600c0100251504001415000c0c013180c44445240b688404c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 834872230 1250 834870980 834870983
    0xb0304080d270f03030f1a100203090105040b09040b1804050f1b4513080d05060a1e050a08061312090b03040b06030d0e010e0d0311030412 61
    0x500e001c00c102001c20707403000b800c02d002000c0020110051480e0321641421498544110b0a042d594052660b60120380d0041524410188500404c0d54903018107001a440102c0d01950440d042003003d1501a82c20a042d101031f14000460240c403030244501150090401000f031543c880048030b2070311032540407516030134031891080090340e0200500781d590b141e480340008805810065010303040c10903414021003034010060340300b10403006410f8078070f02d1103e1a8403107400c48240d00e160049415070303040003803032281d00007c2c507003401405540986c4619001d4002e16810b10030454688002c1403140d940c01c00000098140580f0070340f80b0807041156560318022034880c40b8082c08c6410030005d00000041206441030b03c0140024482050a41e1084a0400c02814200c1800384646021070040c00d10806548507500c1740300b0440722828188109450000407031044c40401c00d6a10907801320380d9006025844082065910703003c054120b2a06a400c030a601c00442c0c903c0c800814006a0352062085805846 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 834873480 1250 834872230 834872257
    0x70201030b01140f090402130e0402010801120b01030311031902010f0b01090509010e040f0f0b07091203092318040224030c0d020702091005030d3002040b030408 71
    0x81001e64019115044020214502c1110500641c0406a0090001d01042c00020801460900090070800c920a00368210381101480f0600f000111350b08441aa809020014007010100d44e00e0707a20910380c0c01e41400010100b04820502900080c010800e881c8118205442e11664a0300b4a200034000d0a90071a002c02075801d2a0291030b40354010050380042d5600645520010b03820003c0280c41e48002500860b05e905a100601e00400c2c0402da4a000c00b034818001e01e030003400d000000400e1254180c000b01d0018008500d81000241c00498400854120b81101a0038001103604501a1420030044580104404902c60248401e0070b120038440e62007290500b14642d00b12002102120200c606114440300400100304c1031040103020317210280e1b8010340075103001c18503400f00301214001d903000804041c00300c10038001442d0a11001c50391003694075080114103038500d0398119101580c000c01d00d96031405450300081d940189c040310007420011210654a0400d8608088141d0080400341e100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 834874730 1250 834873480 834873491
    0x12122a1c03050c120c09031606110610150c02150c030c01050c040f121707140705030102030c0703210608060a150f050906180109090b130308011a0403150207020103 72
    0x2080c140708156480450b610840041315510403034201d000c1c2c1d00008000d5850700c64074400c00041e44140400c14040d100550382ca080846800140c2c504d01540608107842e10940c2c00c03424880c2c003010100c100c60020191a00366001c180500210703c18100c05025900140300c00200086010f40001c000c00750000d22000802c41580d443d070704a001d0f0300841c080c6c03155181e810101040138001010841c01801d000d20600c0310101403410702c000c0d01d6804180100c403c00c03003c6040190719074043c130504000300f02c280c0080d8130f10700c0c051000c0b898034450403c006040c412443e504007000062205500c00000b2864800c012440c0c642492543c3e580b01100c003103402900300200e50042c0d0fa07040300e40d001264900251454614100300c1000000c0000801a54105211039039152a00c0345c2460303114024040c80c5e6001800e05130740e0800b8800318030010908daa078448a071f40882c0000350700c040d12a04403050360310322003c5800f442519081620a582c40580420710718000f403200440769500030100c5c14400d807410800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 834875980 1250 834874730 834874741
    0x40b0c1c050a1101020c0607090306050601030c320705061602070602100e03070203011d07050a05030304031e080307020106050a0e15060d11130512122a1c0305 70
    0x9005600c00d10000092400e000300c0c2c040702c0c010071203508140d04480c005402c0115480e43e040c40c200e405c85042c000070740046000c10500c1000c0c4551904aa02881d0a003c14200702c132002c0c004807501c0d0b0805160480b0030182225500d084a00d1800c094100b5030155580c1e000e504006641c5c92055403000d01c0c1e04203825101150b1400014041c00306c03051074001d40414880302e4020801020782e41c0c010740450104220000044c0e4082c410004500103034101014807100708000c091604105402c854002c42c0703806003e00281e80c0000644007101e42c000420307041201000b40f0000840d4050350010f200c40c13070100c1030060340364040d0044002d4800a4800c00340c0190f4540d5181c1c8000707025212251200c0c0410070170040c90805500508120080031000f2500500c2170b2081075407584150f00c000c00c01000202e040c0301178903291007004001d0b4201e038000c12001c408140781e03147c144600080500d000c1c220000c10880181511031603401c03080003100791030050700c00c40312001c10045050740101c0040d00c3c0c02d00040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 834877230 1250 834875980 834876013
    0x3140a0312022503030603050105181c03110d1b0305070c0b040507150e090105060903031204020a0b040605360d050a12050705190b04081608040b0c 65
    0x2148a805569038907600c050714040c44025400b0f014616102e903900f9608000621001a401d01828460354000030860718600740300303007161400b03004130f00c482905c1e0032681c050010028202c0303528008035070004118142039606074001e00b002d1155a400f408082688044803a8540c02120b00c0c00c0c4a210040801d09070f0a402c6085600803500c08000c1003070440c0b1940802e04a108d803a902921030f000320f44445448002d2050f804c45d001c00324000080c40c44000518034141460100e00501c004d4400f9410191841e001035128040c2a03940d4a400d03100100050039540c0d81e817140401805829107580ea03036a01e400005115070302030034000d003010803035418021410710140740100801c0142d0f40d440c40c03841203040c10018124140c900a9506104a480607404100c250044410107203a036200c15603941c58618015080c5010b1601e218040c108011083c00461000c400d5507601942c00035000742e80b60003981c44908046942e00c3d000c0d10f4050701007804242d0346005402411030840340d90403200c504082d0034614 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 834878480 1250 834877230 834877243
    0x120412090602010b2b1e0c051807050d0f021b0d140904091103191718150705120a0306141f1e23030f010b09190b03010314 54
    0x458020180c03a2502c01420b030700b080102c406103043c0c9024110b18201d5100e002d800700442800e003009007402d07101c0e0b1b004c100f20303c1441340c01000140c562014006203050300500088005119400784030002030310959510340d80d8400c40d2644039141c82191200e0101000c4e03810701d18140c400f000603129a146a1203110701404000301c004c400b019096140c2115002800050200c2d40701c121114882604090510b90b07060080307424038030888031840700d00410760a0101d901c15002c040c80307024200403c005150519034280b4a40002c600783d42c03451400000d400c4450b55845281405442402014090f0760784030300700b40060100d50b04564040c0451900e9004038582004104a00d0742e020700740150b82d51800c1d02003400412401590306106103880795001900c03008000e10072110700007401448500c080b400c1d4052904a540a01046281c00d520f480266041c5448040c002c418290b84d0100f6103020340d0360340d0300c3c1e0311480700d016482c3c0c400086c0e42c6004000e06608280801c907030821645811414610b40002d48 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 834879730 1250 834878480 834878501
    0xa051018020d02151605030307021e06011a0d02030f011712030a0906180c06170105011b06022b0b03010b1e030c0424080705030c060c010212041209060201 68
    0x2042d000c0c062070382c20040c001218010140c02c101c0240030100d400034040704851065401040a1607481c504010000e041101081040c188901d40110718010301e00c1c0050464192070880c011076405030703008000c10307076a030054100400e00e0500020030441c007194101c1440341215001c0c1d00f04440800e0b016540381e165616440940d030480c03c1840020a42c1c42d55070132138843c9c10300a110002e9061484490381d004680074000030f0b80c5448408030300700b0401da4000f4184103d064a0704d60b0710019410700d400202501c18100200d2188120002440140b04255045a16865140e5000c0c1c01103000c0748140c4000700c21305480006420b20b41a510031460806001d5020310314001440808440d84601103218514104c2c800241c15210b00c01403840c0c0c82d15144600c0344406030341180705411121850105c0407211454110680681103081c00b08080d880005201c0a942c0d411200fa0392074907101e00351a030090044401d054805c1007024180b100b440800c00581c0607403807641c1d44030b000c1a41c503040107034203959641da503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 834880980 1250 834879730 834879739
    0xb090c030106020a032a0b01031703040206030403121104140a0f08031b1002030a05061c1101030f0902041406091006080c18033702060901050a110a05101802 69
    0x400400192040164480000842070300c0800c501000c82003e0609a1b80501290b103a64060010300601c85440400303c2458030f8111854954645940410558080500014244490400e016414401c5500b0503075007581d00171110390702c030703983c4180240d40a1100d0416500460f041d541c04281801c2500c0301c1d00950728250021071502142004500784001030354101c42d43c0e130080504003090141c5600045018915200c00032445d41000720821043c10b4bc0c030041c8a944400c4140311000061503100806c4903080c1c2400c1c00501c800018840d64003420411000070362040ca42002034607840850006240524070035190070081e80d0f1840010b001484250280c0c3c1d000c940301000058800b0042402000d001c0c0d080d800301c8000034104000700c1d00e0a011900e8030a03c410303c090380e9165407940717102441080c00f8040711020550a01c2e4007c01c1240c0300310f010300c0f410007200040b000c003990300035201502040600c400f01c5646524a050003500e0380400401440e80e2418402b240c00941064401c3d600d01315001003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 834882230 1250 834880980 834880993
    0x50d030e0307051902030f0f030a0909020c1005060414010305010f18030215070903081204330f02040e04080c19030e0918030409061a03071704020a17010b090c03010602 74
    0x211445008504c000c2c100d90503c01e0070304020080605114000e000e0010304015a22907a603c08040c10210641c0c00c903480d868814400103031060000180000c60f488040ca0004940e1035000110b4040c0c24034502c2810000e00c10000003042040550246980981e01c1a04215052501d0341c0e100034152204001390040e403104d014801c01140244a1a402100604148840030394966421150f50000c0b80490392901d440300400052041c0b5284840c800e46c070700340107200d054520800840d0001c0c05d03070032070021082e030b00d030300700e03840c00f2a00c0e41290302418000ba40000c0d0351429141000c0c281d8440036074001c05004081c0000e0b2542c41c038450005c0c1c4940c1c1921040a5041c10304180100b0010060201c0c00b414004506031380100070920080014103000344020030441e04102c0e00c08445140b00c041842100740c200100078800c0d0f44825041c4e200801e410103074040fa1964000100b00044e00d800c6280710f6550b50440c1080100154000113a580303094844500d950380f40d513500c4010340001d1141c840540c0155 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 834883480 1250 834882230 834882253
    0x151003030e0d0605040b1801020c1f0e0609070303030b10050f0d09242f07060b1e090702012007030c0c09020a121104030f020d0609050d030e030705 65
    0x24a4601c0a10002825842600b84240c50700c105803101610260b45907050241405a030b03c14014040c1c1130020010020b40c81c08004c0d015207079481001180c03602d034118440801f04000f540703030f8101140c02418002241d43c4e0703081040340c41d0740756815444100c0109203860380c104514103260507850040304943c2c6030103041030f40c00480c800c99940401448088180d888007507400240c10407140714003e80128000e0700b508410400c01400b203075110700c1ea24944040c40d4407562042d140d80381c3e0560050440058444d2100c00902d850f1014080902045900c800310b20545000c460b0000548105008210b821082d02e480742c0d10107a00f22185d8a0140b1507844820400c0703142000c15500500a90b4401e1406c038080c160b8540390801d032908141c01c03072410150002845880c2640c45455161561450701082184540e0103110a4483c45039100c02000300c094040c6040c15592403644034110150030040901a0020a00d81103072210324124035440860324002c1d0245083c08004140e820741030303000d0028100d08446 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 834884730 1250 834883480 834883487
    0x3050d2a120302160303060501020d020a0b0115020708010e01020702010e041a04050c07080c01050402031606090303180801051f06091211060c100e120a120b1306080303010815100303 80
    0x740304480c145a001c00000b20044200320320441d40130300070b940c009190342c01c1c4000281444855540201158843c7e110000854070384200241140d500080e8400d0a68281c40e09078180301241c3d01600155107881080701680c032064008150361407003680c13503c1e002c000b408108000c40b42002c96102642d80c5020650116041540c08240c1140c5000c19030b0741400c40e42e0742c440c40981d001800302c0e41903075111018001141400c0041c14078190040405c00d804600f03000000702918000e10001d0204034161146c0c11f040068060b4078005094008004d011a280103219111041c0c94400340e6410000c00c1c040000304a4482e403010015520182c0c03102d40843d10075100c0f94407445188440c1c41d8464020802c6001c0e12004010f6043d0f0010741342400701c0c481010500136410010080d40e00401031400b0800c1c1c155155001100603221600c0c1c1c1e20001c4c2c0e0400d0500420120204040509149482c004002c00d0058002002c0c50403182a01d003100c0c060408142c580450000030788400c91040c800c20010300001c1d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 834885980 1250 834884730 834884753
    0x80901030f0e0f07090e150f0408090d1103060930160308040606090504032705030607090e010f050a05010503090c21190209060f0d02030703050d2a 65
    0x2001002003902d00ea500650341c200b05204003c015581e1180b041045100a07034004e10120344908005040c4001c4800e0540c070400200900c007410514030500024200316030035080d07482204018180308402d01c400c0c1740081185a404a07001e10902c0740d90000385110704001103058000055207410751500c0c07044070050040c0d246801110350007120a20035200007007015040201c0140c080e944640c01c5080070f0411004860103504a00e0280d418a001c01c00401e400103902c0ac00301002102c035680711000601203040d0320300380d80c208a6140c001e9009008110744d00507403c109a8130520140011640c0c0d40c10f40d01410143d504c07429070080c1c44500704000300c4d070044000d15800304001050765502c038900300c0012649000e50b0a00305000c0e100380d104140880080200b201c0499540344031310000002034000400c800e100030700c064440d005008180303549451b8046240c8403198040c00b254608d50301c0746001621480aa0442e10005100803104500c109041014031400d044000310303040056040c0d1681e200f840e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 834887230 1250 834885980 834886001
    0x150c0203070b121614070807021914010e0306090a02060319020f0a030f0b090c03090a02040513030807081b31030b01090608120c0f0f0106031e08090103 67
    0xd04400040d800d24a2001400c1031000d4070780700c481600d00350740c0100004a403204020f0400901210152000058001b207444032500f0011603030b1a4507003480010031001084000c150782005003840081e02e82d01105804a03580d009894030407036404004145960b0f548100e03a50411a40201045005424048001e54120a60140e010700c0c0c40d9440e070307440c01681e01175007170712001c00d0b4009503c2140580c035104004640c030b41c83c0801d00880d0702c04d90028030300c0100a8950068000c001001c290b03004002c0140001d41030b8080c0c01440640340c044115401e10309d0264059000c6004040000c074554440d42d0f12034410001001d1428510045a80c45000d03508100800e420503100b0544c03000149041c0580e0130104a201c1c00c0d4140c01904510304507a642406910001c00242040d0040c4050a00170902545000d045070304151202082c0c54103601c0c0081d241b00310032941c0210709181c40b143d14190402800e5034001c1c03000b0040319400d80c18400c82000c030080c0191450340c050090001541c8260843d003a001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 834888480 1250 834887230 834887233
    0xc05130b03070e040506010f0e06130b1509030c0a0303080408070c050d050a061b020a0b0a09020d05060a0515010e04050702120c01021b15011a0f0708030103110406150c0203 76
    0x1540d240c04a4508415508100100320605003044200310041005a000d0044081f5075481c283c6440c4e02c0441008010b02894415032803003009521804469109580c1d030030000f01450030079030700020250030580c40081780398000c0c0a000d800b580c03e03050002c50181241e6045d5900c020945e80d6403103072541074100003000c60702d08464450016030b0b40d03904044045041d0003403002d004800800e20b400401c6601c850f6131008501e262391200007a847c1c0110f82d8002007078001c40d2803d810b40e0b03400116030051101a80096110108200c943d0a000340015042d1040c6c1001c1400c02480c1c54002a1000c06005034400c24002070142031283c2d510b00300f580010390405840c0c0110366140c0c0300480381c2c051641042c0d240c0c0450b40e6011403141043c032001c3e80e40741d074a00142d00151100c117a140c8148000740380140070305585403039036220124040d03254030112034001c0c5160661588a6405181034002c0ea4400e10058800721442c160b1030318145080d214510403101c0d20003440040100c030b600e051300e1084062070141e0b4113 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 834889730 1250 834888480 834888491
    0x1050306280e0702010e010c02030a0f05190f1202030402060d09110904030518010e0907030e0a0c060207030b181b06073c030f050304080c0a0303090b01120c0513 71
    0x5074403140c02104040c10340740c01c0300030140c070f00082c0007401c50301c01040c1c014141c2e050003034581c4055008811941c1409003882d019603003081c2e052050304c151103072040c03417072641064110f201101a4403160019490302c56558a030520b4641e404043d0a074042964040d50002d0208020000307030030b0b6035110030a014401e90012083c80c80201c0000e2020300110380940c049131002a2805200c0b0011100c0c50760313035009007044814041c204001c0340c01c043c00101140141645c4030902c030a1285c04020056410380d00081008007962aa90000d4135841c162008072080b10b003100200303040b180c1c042028282070791290014a40f010820712041c8281c0204011140c010604008802c0420044078015100c4032956020700c0000d0340c40103281e0101c41840e84601080d4510281e4600040d81c00040344000788a2850010384076112820952200c2c4161070900b0242c0c42854144020940c143d000690b540780503101c00141aaa910300005070f46100c804d0003001a4070500c810700c41c80c505080342034444081690000342 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 834890980 1250 834889730 834889789
    0x3020a0309051e07060c0f080a0207030f15050c0304050c0907090b12060a060309020603011a0d2c0c0a0506070c080105010807170a211710090e0304030201050306 71
    0x1d0040f800341404071880440c0c140002c180c07040100380024516407411890350190394447c0407001010503002086c0210002c0c1c1e810a040c401c00c18200519045269481c3c194424641088010040c3e10759114050038503002801803502942900e214036000405032080c1904081081028040140303a0703c00c1c050480c2020030b1840b083e00140c8582030800032200310504084042014049481d0b11079030405d41081610310044e115401540d04483c01806902e01a42520030003507814003640d1010a43c0d540b9000c1c810402c02c03c400c54050700d0f10b00d240b0940141c62143c0d034130a03841c0c0ca80a6801d641000c00140b04020381e06280c40109000c5001d03108898802d070b103402083c0c0c259102a40081c800381c0c8207120901200b00c000c0d0703403045000b1500f0000c160708411507851404001a0842000040c1d1004490b44000d600401284080c0c21008a190070280390045010141000318041d4103400c40c5090741d4540c901400000b241d050301d4058403100c0c1540d54550800c1240748600702c6050b1100d1622040b000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 834892086 1106 834890980 834890983
    0xb031503011514150705030a09030b13030f050a02071e032d0809060d0c0324080601120f06050126031206040b0a030515100e010803030703020a030905 66
    0x20b5054031030358000c140c45c0c010600003070b1031400000390f0100c59540c04502241a01c1c4100c08044280d02c031220303070251000c0310600040c0865100141001c019000f40040c1034148a1071045800c05901c69180000280c001c5089241d110f6034020b007403081007100d9120552103d2140508035584040340442040100005000b40800e040000c0e01c0c0c0c0261141c408996003469110400c0c000b1003225000100104040300e960b8001601780c0210900207d103a0f81c6003000c85111000600040c7d08000c11079000000c10752086807100c0240d11034400003180b0740034081c024203900b0b00054000800741c0e1003052084002480c84a20741040124000d10003a000c821500300e0000d82c0c00144148540c4049020708904c0d40000e0164231030311004086140f50211914850401403c0d910aa43d60744c0c0b42d01d05034a9020701030b42e03491b90028400941e40c68400d41c003600c5004a24030b4081a030810a48406 = true := by decide +kernel

theorem cover : BRFrame.Cov 834712230 834892086 := by
  have h0 := BRFrame.cov_init 834712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 834712230 ≤ n) (h2 : n < 834892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
