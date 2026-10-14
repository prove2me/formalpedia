-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:00.704307+00:00
-- url     : https://prove2.me/submissions/9a7aa6e5-5376-446f-844e-09418f5c8f89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558633093 ≤ n < 558812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558634343 1250 558633093 558633133
    0x12010e03030105010c0f02100c03080703020a140702041410090b0301090503191b080a08060d0f0605090102040b03100302030c1008041e0209090106090507020304030c1518090b04180302 81
    0x1b405a4514880c1c5c81158001c01c1801414024082c0011079080304201410b4210708081e8100c049840c0440c40c1c80910b400040c0b500b58200c1291027540c0000407100c1c01d44d9110f4101100d484009203044100d4141000044000000c6100f10140325080c00b000d06c0c1c85141c180300d00342801e50080c02852414804100c0e504d0300c000340103203a0040c07040d840f00300c206040c0d0300c4508040c024801c2c0091542e40c400c815024080080042040740b01e030300c42c0040840015206400c5880050344550041440d41fa081100c42c003a000e01e400c0340034070000200406c41c1041035515224104d030b0094060743c09910403002030102c180000c0803500c010030100790219000411041031481d80582400e0700218030000c41e400112801e40658003055503030b460316001d0205c8500f91042c0754100d81c0360b000661030b051560b41e903849842c1d12132040c2480f20304a0040c0000e4280181c0d0a000c40f403806002003807036962148540c000800004401074012480c002180144605d0089030011941d0140c00803d01c000541c152030684e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558635593 1250 558634343 558634367
    0x1e030402040e1227030d18081603020f030604021509010507170a02060907120b2203050706050c030118020307170a0b0f0406030c0b130f031112010e0303010501 70
    0x141e552044480c0340c0b007091180714000044400010780d2582d4a084a08280c0d65102d00c1d034182103400b580401c01558000b07140c84a42e00e03e828040010548000c0300041d003621540078840f140502c600360440244208410001d59108603113080c81c6800000600d0340d03c940403a0003d4022280c0b0740100b520340005405403001070014036205260600039550212544600c1e01304021030000807600008041d01449401d501500b280003d10401c0c0c60100d102407003010021001c2c082c0e201000100b8601c5582544651101d0b00084840340300745400c1c600200985c2c030900c0256511803408010034a46520b8008603030484844011168094038020503520080d031002c0c09070780500034000c094400d0344c624071031001e00c98000200700088101d04d00003401000ca0450b40c085211780d14042c0d082c000141030098140c00d895080131001c0d11005105c0b0141c5c428446d90308440c021919002000080114208402e035482900766180d903c00d80c02510490700380d40e40c40108010503041407005100c2544242c007403000c0c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558636843 1250 558635593 558635599
    0x92802090307180b0a06030209040506240702240a090e010303140c010f05011e0501030e0d080c12091c0c170d090c18050702030a020705101713050c04021e030402 71
    0x30a131410001901c802965880030740801d40100d0049440d1519124150f4000c00a03a44242c0c8103c2400f01924409070f0241d14844a42c800324500e030175525070f04120300000c2e100b08a11501c0407074000c008802c0e600006580400144507000202d00e466103098018100e0758141c4070980107031a0455010620340000d40901042c0d0350b55070407458401c4c09801341034000c002c069850040091281d02e400700120450700f180341894201410907000f40800070f061740a004641c43c4c220b050b40c80720241c82c411480303600210042c207000d80b000d0242c060700c08103502d0002d9010700d001c80a9050071550a480d100090817000e41401590740d000100101d40c100140010884c00030002a101c2c0c0c542c0e2132110102190300080351003000f07928901c070070300b0581c07103455040f0f0700c6800194144011244000e640d9207260003540d000d4510b41c0868100d0310300550312000d03008690315410490745030003804a2407010800a0a5417188148214180c96040505c01c54441030ba009048800d003c046040208041d84050000c0760 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558638093 1250 558636843 558636851
    0xa0516090e04060b0607060603112d0a080d050c0c1503040b19020f03190b0a140d080a0c020a05100f1d090129040509070c1109280209030718 62
    0x400e45c0c3c80038000c2039150b2080300d00050450a41c01e03c001400060044036000e003160b00030b07002d03100003130f41038000d0b5021b49801284003515291011907146d0001d40e1000006100c0d04191389941c5801c013000e040711b86003110480ba8814901c108118820f4000241d10f0602e80c810030118000c141c4100c10141e1141d481c0720804020b01c02040c02904903802000403204020b804002e000a0044201182c014511286418003070300709491b0018581051310711540b5444c0c0e072080b00d9140c041c0c03030302c40f040071806030060305050b10f880c10701c580176008100c0740e50100d1003401f588001003014607003400e041d268a0306070f41c0d036403041c1c0e818440c0039030340107880070059141450001480285075840040f41c50290071000c2052141107142c01d26100c0186a14005c1c1c0c610030710504c41407005490b108596079101c98586004443d440d2213040100001d603200d030005401040d02410820320140720b520640c10b021070030601e450b01c8419251b2600490013000c1406074140c01c00440ac2202161f140a1000f030b4403146a4002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558639343 1250 558638093 558638111
    0x902100e01171e060306060303190207050d080c010c030e071707080d0f110d080a110903010f2910050901050c010c020106140d03090306020f1606050a0516090e0406 72
    0x40031070301c040f1502c00f105901081d07401c00a0480c0f01c0000d820500030b40c000e28507420a140040c1d101e001d900e01c1444226040044800074510811482000f004060007001d405074003400c1c59019a400344048005540c03c0241c40b0601e507100b841494111035045d4080d102060910091300c1520150301d980803050b210b40c940100d004042408003100d05d8a0948803600c0e4000800c0e4040c00789501000d0350135131500417400c8004c20581002005a109414407400201c501c03480d0310101590081d60120b603055880c0c00780714030300c800c0da0b54001b002d244012041424854000b560509400c0c0c59070520301d8020107001d074403002840c041c00141074543c005040507401c02c036807528680c1c21600125002c80050303454800c100042d1841d44640320002c1001d540c911841c484a0f200034110480d42e00c0020070240d40060202581421281601c005084840300d9500f204010300f4001d005d08401d4481d41190307442c0c0808100c1000002d005a2500710040d1940c25109141a0020800e840001c0003aa440d50306e8200c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 558640593 1250 558639343 558639377
    0x102040b030a14010b040305060408160f0f020906040b0f2116060e0405091e031306020a060614090705090307170607030614030c060702150f030a050601030902100e01 73
    0x1d10300c40d003000780c03001881141c0150340080e0400107078024010090100b0050000c00c2001c500245c1c4542c0180d90b8581c4c2e84141020609140b0700004007900c80c1c40184100070801c0608030358100710b14000c54a00d62240c13108020401280c0002588581c410445d080c100d446050040201c0001d98008000700620301c1010040c2d424040041450201e00c0c2e040d80c82400040d82200d801c000780b1a050314100715610304030501c10307500c4640b01c0c080c00075003080320640901640c0c01c008880343c40d2046500c0300d0f030f0503589500103507031401044000c940c00da0902401152948071404841805032000b00516140d0321401020703075040d445844a2070f014002c3c0c203008106c02403805c08161000d9424070060a00b80b030300e102d0080c100d072083c1d003002c00098141004003d03a40c1d000034030b0340025882181c4007076079080e580c40003c180070b024551204403000085141000802048007442c407801070048140701640c0d03202c00440444480010095002c9a04842101d00718812440f030381d051001810810b0000b840d080700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 558641843 1250 558640593 558640597
    0x1050f1309060b1c210527060c030a020c1f05031e0c0408011b0e0f0303120f010512070e04140118060c020d030b100c1b060512061804060e0102040b 65
    0x1c100e110220040144d0204484c2900010300700b40000c41c049a444210702d80149284640155074000e54801d049840003160040d52440303540b000182600d680da10054201c0b91241c003c8a0303104054000e80010b4501801c0460f0503003820540103051855840b92003078161035681000d00421441030407003030401c0382e8040d081e410074010800c40b0340003a00e892034200c40900391050755031040a240c181d001d040c5c03116500035100c0010000304481e6a0000c0c52040c011a145005401c180e80d100d42098041c0800442ca011490781603c4040c1c03003d5448a40401801d5943c1c08607220708140b4103403850002c2c4c04140c003211100ca0842821002241600c5040c1281c510402012070540300d01d0742c3ca1568041e015010400d16050b00f80d5800c0034400e10162900048401100c21010340901113011140f4003080640744001444030718844016a42a803a0440200b45400c0712621003a06685000440ca052a2013003a44c0c410f200403a205c040250f4513a511000501030400c0040425902400003040d8201d070000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 558643093 1250 558641843 558641869
    0x1008032d070804090212060d02180c0d020d0b09060a0308030112080c010c0905040b240a030b0907020607020607030b0603060f0a1203080910020f07080a0e0a080d030501050f1309060b 80
    0x5d030321030910a0703420300000d201820451142e01c0401c1c0c4440140c44840583e00d00c001c410400000983d40c8000c41e2699100e40803c4208442c4006803880142034568030014051a060381c1c6080995200e506005401c1c07254000908104c0c001e000400046c40a0041801e202c1c0c07060035100d0a04140825403400c2d185083e4021002c0344d444c8a0912407400c0c0b51040b0150369008549040340d0825854000540c0b80009007080c13400400011100c011a004e82c12451107001c000d040001c65140c00c8200944070310040d2203840050248401003014940b09028031410000010b086601e143c8480c010440f80d90011a2000d410003003c101c0002e00044150f00d40150714000c1e21038901c0d51420074130131400d18a4600900c602d8a2060058440514405054400c55a40800ca0503070b03506484800b520a00107500303034180e108150807400300c0d1031036001c0f40b10b41c1d0100c45c5480a01580c0d803a4002c000074010f0f022626130f0084042d86100f07640f5503454200d8922940034246c001080d42039003000c02c0c0d8501c4141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 558644343 1250 558643093 558643109
    0x90302010506040b0a05010f051b0703140f0a02101101110a020a1e0512180402030a23281b05071a1302130f0e061008032d070804 57
    0x4402c101e4103040902503600c01d000b045034103565070b50902c4006090341c040c03240844100040132642c101004664203841c03242c0c1d0b00007000c8468a0741e80e8030301144440100a40608a40121003040c0081600040d4000b0001d6004007402e000340d10700c0a04072005c405c1310100b0310856480d443c0c80103903000c506004000c40c035681d40c003525841100d410104500e40c9030004070103041e00100c0f1801c0100e08045589420200d0340c401d03155441c0c90481c42252020050b08040f50b12910020900122800ca94005018200c0c00752000340303500340981c18513210344400c461891880011016002c201c01541d420154aca010b40c590010b0200c40d4940c00c040c0c4050303d01c0e41d110202d180019000b083c0010484c0e4034800081c02140c0c45514640031403000c102503e02d010080c003c44420780d48100810b841d4000201da680d02240401c90311601d05140ca41d501c405540300c000c000002640070904900220455441d1108800155882445540c080204080800106405e04024410500040e6906008100915600d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 558645593 1250 558644343 558644351
    0x30e0a090e070506040305060114152709060f0112020c0106260304061e0c120e090901090209240604180515031e070b12091e031209030d09030201 64
    0x2440c1c9540c580368250300550b114080c144810000039400282c981d05643d5010f013020810700750940441c040103402c403403440010501003400e107020205403171035100d141c15500c42035103120300c11402d00c5000d0300256296900482c9203215000c40e0f500600e204450740b0041c1500501c1d045070a440c0500310340d140c0e000011000d46280340090b0000e520005095006111009140341501e4035901070461500700480c28103026210300b0400d0650300075500d00042980040856682d0003101c0002404100084c2d0322a1051043e81c3c0415a0408140304485085902a110305070300c1c0c44000d01051410b03407a58081000015100215800707403203c030050402003144901c1c4403080013003803030380c00250b620052246600e2941c1d514940f9190b0b80026003280e85507003102030399210f002c3d4880c00034144412a0024413145400103441c54000407049016481103c0800031340b4121280402c80d07400202c100050444681c1c0180042426084d00e01200d60f00150304030100c0380340511000f0b100080d13032a015415009030f592 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 558646843 1250 558645593 558645611
    0x41511090f01020f07030f020a0b0a0305040303110a020c0f03010e1e0f010911040c0306080102041710050714180310050403030c18140402070501060b070c0f140607030e0a09 76
    0x654074801c080424005003100072071440c2069590f100c20700c00036210b000c20454080c2551141c5a01801400b000480c20f41c0d501c074026405005002e09aa08500082c505011950041481c0701076601c5401d02d179010344403507504841002821501e58008941c15561080d8142001e05c041091880e1226040f154055500036428103e0411040307113141c0c1c8069050402032030014440011042c1188012680000e44541a4200720001c003440d8004400561000402080c8907078400261400000c1040c1144c07000d43e0200190010b80c1c0f0141c5a00001c1a00f102804244101ea280504101d01030314084103002d0341c40c0c2001074600864012107180a0b6940c5c0b0500c000d26615000e10181d03405603081c40141a207840d0079105175210340740310340000b40118006044841e43c1c0c0b0740481d501075800000038088039466449100c240da110800c129464901c42200081045a500301c000450700d80d0504010283c01c0c2e601404420f0f800b400040301000400304031035129558944002e40a49100d280006440318 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 558648093 1250 558646843 558646849
    0x10032a02010f1802130c120e21030901060b04260a06020d02092d09060d08030406050f0f091009170c07060e030f101a030a120315080a0b04151109 64
    0x8203402e0001162400d01646c0c3c6001030b000034000c034035229402000624560704500003810a6150150090f2245003c601e42c1d02c224101e001460044440c4002080704684e100c120002e684158815015920400f0054000c0c58820a0812009841e1070382660880801c0381d80c3c1d00200d901184850604590229a030f5079941400003c0c1c10713046032640402110508104031205030b403d81c40c840d180c0b1640d500c0e000100c0c1501c03510302a44404d90301c950401d0702c90a2910700b08001c1c1400712200900d03411480c0c00a05542c13070080503a401110358001034410f08840b540c0c000e02070450413100360751440c503400090203590b2080d001016a00600000341084509107140201940c452600c0c1c5440307588006000142600c001c0303040d0441810b00d000005003145031048801c4c6200c100984a503150040c4514141801030b00c2403105402d81540e45e04001560340407062008440c0c103800ba000040d0f204107400c40000d1002c0003c141c01501410800540c0031003158294151a43c40240321481e0f81e002c20000d5484c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 558649343 1250 558648093 558648109
    0x602040f122f041a0d060209040b0d0b160516060b01030f02090a0504050910020a090f0e0c0d020a0c0c0f05010e04110703260f040210032a02010f1802 66
    0x80003007100c4296803980c0d58245450740300c040311140e1160341c2d140310407010501042c04400810b84e0182ca04406071101e810850700039003204c02118042c41c1041000159803810940c1c0784502c940c0080c0c00d862580f500b1340558581000240800c09208040022512104240103000703030462155902003205c4100c540010241d41c0c6447c5140c88403401130107500802da8521000d4000e44e881036600240725a00c0130000e0345401480058480c1c0c042c0b001810b50750f403551000030001621500b009002c0c0e02903a952040c101d0803000c6410f202461000c0c011044240415001807617501114a4a0a081c0145032130396543d0340d803580c0c030441e0009000281007203e542c0015a22036014011501000115600048d1080511030b00390020108090701d45e8441c65003400001c0c034640f0308182840d49220740b80490f4011a00c5606944c00e80c41602100300e000d100c28802d0050210450980704910303000f5801c1400104a01125102c0d00155500c45114154046c1c15116000d0410300d41a200d1183d074160340180f285078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 558650593 1250 558649343 558649373
    0x10b0301170d08070c020609130204031a04030507020d11090109020c010c050f070611042c0903130501030b0a0e09010b01080108030a23090904060e060601050a1b0602040f12 76
    0x142c00a504902d11107801502c269131280b02814440d0100c011880080c9182c442d00c000d0503803010050302c0c2ca00544910364040c0082d20b2003134480380125418012000860300e0203d500900207202044000c006007041e0310b4002d116031103840c00d071401040140c0054042a801d0704941c042e2580403580710f016103030034015440340400e1400d0031031030280750f1605032800e48034042c005404c0d44e440e0003d004c3d00365680070459004140c0781c0d41800929130400360901c0c074000300e495110401580c404c0880c40101000c030448080300b9603142d907580302c070703240100540141c2840201541d000808800005608003403078500c6119120a0000081c0e0601401c000345c650130781a00940180e920900000c2400c07a00090070846080916080095000d50200364455034442c40041da5004500c55040c0001c01500d42c02000b034000c0e8240949455541e01c10045441d8080c601140380041d4407420444072405c01a040c515800d4003400c005461b198844403007031400f84940e4490000c21289808041c00d12890404d04441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558651843 1250 558650593 558650639
    0x6010501090e0414031c0c091a07150f020d0e01050112080307182402061807170a02030304230303031b0d151203120b0a0605070302070806010b0301 65
    0x3410202c0300000b81500800080010307016690144d003024040043d2010f01c2031180000c80c20102d11071a0002030100051944042929a84082040741950021001c0b0440c115200c41c2488003e490b4483c1040040d004280055941c40100c026440c2d180001c100c0e820410f1008640c1c44044044a82103d8050b84a40c04020004200c00000ba654804494210070a4501441c030a500c0340000b600740c44555000030940704201e8101030001c16500c411400104640d001d42d0803590f135006461b0200c40d0740841c21105500404000e21403c0060402c81041280f410110344000c90260b0219203583d00641085004108803050307025017429000c4e0f00228260290091811420710840d203003000008010014118000811140c1491400d40e2000c40c080045030420107103e9070350f030000ca800041048003600000c1080c144c42e1211000d9010b40c2c054050082c10b54500a4035207407048581da04014011001c6025100c8000b84201082105034041c14041a149980394909003030340009800000240207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 558653093 1250 558651843 558651857
    0x40e04060c0c02030d031e0e1c020c03060709080115030203071e05060309031b0d020c04050408070b0a051f030c060810080102040905010e0f040c0b0a050403050106081c05030103120c1505130506010501 88
    0x400c234200071925210508405012803d0b0070303450541a0b080a0250300740390b80500c100800c0105195028080f0710403585068000c100c0300d000c80100071501c8d00c41c0d000180d0154422a070030469602c0744c1c1c4214a1400440c81055a915141d0b00000c0c1154026641c2c00325503840402d8000c502c4906038025440000600b0041c0320015200a005c2e40343c90201c49294840c070b83e1240040c0500c40d610003114580c56006849008c070749000420f610003444195514683d9842c00044401588602c0941100341c1b40c1001c3d00c0c8081600c0c1070012111004020034500841d00d070b1100000d490740342400540081c0140329130204240d0b040010745607054400525000b07a0401c07940c140004500010241025900030107025940c642075080f044d1228410b07644000c01c0c5600e40800001c01040110304c048190940c1070440c034032148009400c403054002800090303d40e100c6441c068030141e009820000b2001d10500140c442a039140c10361504842c012101014800101601304080003000c1c00b0850150000b400c10035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 558654343 1250 558653093 558653111
    0x1060b180d06020403050f07060306080a020607060e0703020a08060f391308210a050a081306050c18090c07020402071b0305071a040e04060c0c02030d031e 68
    0x2818016860486401460030007508000c1c060355404440185410008845d00c5000a01071540d031480725204240c0041e1624002080b40c08002c00c0700d40e80f05800800c1141044aa600d51400a0200a9451146206140c3c00000507214120240000c2480c000030b0143c030f00d0311004882003028002c1c40002c00041c0000a8400002070121900500ca10100340700c0448102e14207480c043c0c442c1034984040148d0139140021030100018022040142c0d410011000b0303000395181d11480c2c0258101c42005c100203120307910171144198840c1c0e40c010a02d034103800780403541d81ca483c03044030000d43d244668118009000301200c1c8109090380c1c5180d0098071a200c1c1844e000c21032161601400c00002e21541c0c0008002c024460380d04d5030400c046464194044406949142c00c42d0f840e0541d100d0405403016800003000341c520583c0c140d40441d95002c4090351181d40b00c0d5180801004038500860500c45a07942d5000945c40030041e040c1c40d0381090302c00154500b025143c010f400d01c5902040d44449040500310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 558655593 1250 558654343 558654367
    0x100b010504060302031005131a040c090524040f0e100e01090f061517070507020f220c08060a0b03010302030a0b040f060c030f060509060102120a050f030103080403030201060b 77
    0x12012070b5414900140c81b61244040c2c0001c090f540c1d8009540005150302103c20000fa561200840c50707007004440c2021040b85040c44161402d01941101141c000c1800f00201d0030031500e1601e0051000464480a2080c82e500302099009500003481c0f03007110074010f004d8a20300e161840d40025910221301d04a0707141101b020604803050140d2402191104000000001f042e04030001915809510203060010309400070054007404a8905007010034501003a00940100d0403104240e801502c03400b0342111038000c1c81051440703076015100701d0304081e0110203084c50610070502c11501c2603980c02d9041c00c21600700315061900d074100441d0413004100410050f980062403111155021082a113207988506242031905030b01ca5000e4215814000c192290a5065020030440045407a04105543e22203041c4200351200316002405603000c4600b20311880090400340038520f07020b1030064070b040003080014500f40c100303070f00440342d0700004181482056020b016480140101d0580c2034100100d400b41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 558656843 1250 558655593 558655597
    0x80f09060403030c03060b0c0d020d08130609080702040c0305060102061b1617040602060a18030c1113140105090a0c0504030f02010c021008180f0a020402160212030c100b0105 77
    0x4082c03580d2403034070400744e5000340c0048000f0318901070069129000c21143e5034030361003080790540041c09107003168000076009024090285080c141c805050210707540d2140300411a070402580c02c101c06101c44030060341da42c007036108019215a0013090604050001a1405001030000218030001402c010440072140c03040c0c030b240c0c411003010300100c8010307400c128101d00031a4440f101070140c0028007041d00e503000200140120030074441000969044004d102d000301ca8600014001442c42440402042145c0c1402c40c001d000145030f488a001002c21503070441c1c480a10bc2a49105010010042c51500b06030345a40408460424000c8000b11031005055100c0d03030000810308a404206070082d64410100c540440b0b9000c0e0400013110805c10000c1c04030541210100c04980080044d030340d0306800421400256102800100002e050795820003019401080207040300408041301040035075101054038000b1512000659a50100204007500b09040c41c540201c035a41007142c07202e89a40e0000c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 558658093 1250 558656843 558656851
    0x40b0d0507031806050c2119020a050d0207150e0a060b030105010311090711011406100903110d050c061908100819080912160f03020603010302040e121801080f0906 72
    0x3c0c16030719071404803001e00078280185c40c00348807034003204820900c0307081f2603000301042c42008400d070302d007040da18059102d0b82c0495000902c0a000c86501400a6005401d034180300700c5107601c08004018100c0c0c229051a1800021644041640350900070302d40304000c0459800e4000b0b129940c156211340e14000400d8051502030280300300040e090520540045158000c4400203000c18500114415a1040b064030903520801d0302480d5942481e01801d01c3e03404607a80107141d01c114040220070000352030030701c000c00d0b581401056440c100d550b841c01c0c0209400c410003540d040b1801fa001d8030003000d5260003080a80460180b43d0148882040040d9035070041901042d1518005001c1c94038480c02e000e80041540c12142c11345c2e180c030352002e0116034030010048010181c4600c507900d004034903090425210203900310404000500c09810725410101d10304411200700c6004194000342a14550701000a1510096940074030380e00d1507a008007083e8000c00d210311029054106840c6c41c50b240c11000e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 558659343 1250 558658093 558658103
    0x5120606010818071d1f050f0301020403060f020d231f0e0f0414070b0d2f03010315020a02100b03070b0a0201050a140417070c0506040b0d05070318 65
    0xb40005400b03403900020030f01064843c0007650b02c1c0f66565484146407140c00407084507030b6440c040c00035540c48415411482d10007900707000040e0b25031402040c06580c40c0395014064055400b000080040760b00ca00512441c4c0c0c035111401079a40c1c00200ca0702084030940d000005004032001004d1145040c6030700c44a4203c4a5028004070a185024640c80c0d040826403200101c020010100b1a0185481141d14421400b0702d1802041203400d0356026212103460180030f00014007071241e40c003100802e40c824010303068080560241a1040240c03ca00120b241c0b00310402010700000500070090f13110458110b01c12a1301017541816205136003e03403a401800c0303104626580d0350b40300054907907003008a0b8000704440388806558070780d04503009019020441b800907119003412511000b51032250341d42c500c19030300a10b4424100d406118414400e52107641c0503100481c1050000ca000e54400004000800030884265981e039443c04420040e61001400c11041c5450b1200c1c52501c05842000c0b105119400703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 558660593 1250 558659343 558659357
    0x320418170409050910050c04080706140403082704020712050319021c1b20010f020f0a170f15011b08030601021b2b060e06010f0512060601 61
    0x10000c401240225030044418034109001d00001c2203002c100151015414070083c09156100400700b0310502c200d128013449940040801c001030780c0b18090078481d02038221031441c03505d030756a1903005040d040340d60700700b040790703182042c4040142d120b0344800450f21041e10292b08001c26034540d4100110038089140501c000040001e05600c00a8046d081080303d503001151600001c040d10325601e081408140403c2e071400d003264202c80d25155501c19111000d40e90071001042d41d40340e201d80d42100454140e074942d01c40e403a000c0300070018005000d00c040003e01c6151900000c0c04c1c0101054400c44212030f031142e0a0701031013044817181e1026a032104102001d00700c00b280c440e00480300b4482c1d01c0d160050304003007031744181c00b0040500025406200241e007110242200900c442a0013441e1640c01e0b548810492416544e0a4500e0b0300741942240340c105c0994511401e40b20b4105940880d01044200d810500c018080ca03404441010041d203820f440f00401142c541002c0d03550b03030310080c0805052080d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 558661843 1250 558660593 558660623
    0x7080a03091403193503040602090118060203190f0f031107020918010b150a0f0311030901060e07020a0203120d091a0709091404120504320418 63
    0x401c4610f04c54011070380d02202070a0790b414159415a60000000b042000303403110002c201c240b0201039510701280312882480c1d911180d482800941c80744045c1c50600458030070b03104444520303641c41c900900750380e005950742d884044807916140da003a950074014440c01030400c05041d98064404a8100414280003400c400c1c90207a40d419805000002940326595000f0050020034540740100c08020040c001d0001244c400200001d0325036810504406100c240501900c040c8200b0800352014424100040c2903c21000155660f9000301c0d13502d0441c0c4e4503554100009020300744500d030b1090041c80504031002c0300d9400a43c48030520019103050345008101c150a40f041c0d81d01424030340758031001c00c104445092443c803c800301c00701d0384507001c20a0900002000701d41402110600160a920b03003816645543e0341203d0080414020420082c09000100e135002000e050b0b110105009804a034058181740b001030b405940c00011a40201d0801e501600380d40b60380701141201e10752005500c007039600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 558663093 1250 558661843 558661849
    0x50f06120432071d090d0309022b020f120a080723100513080910030f020a0c050f0a080304081e04030804030605180309151b010b0307080a030914 64
    0xc1200c806015034525503000c03540040c00021000c00700d51094202d80f0002130b021813525441c034821940e4a2094020f8901e0601141c40380d807043c000c00d4401010b040300c80310340e258514441841c140c50b0041d04507910a085042d0300d08071440c440c42207802c0f1802001c054911448a0301c508e000400200628008106481000002d844100394000460007598003c1c401e50302080e40c429910f640060100d2820011601c4e00302040d0340102626006200c00d40380540d0794050005020340706260340101942d84c4280282c031140380c0001c00c00d18000c1c1c0e03a14515090705e07080850406c60180100d50060f40400701110008101d401034903402034011b902280c40e180c409002c01c941c5c0300c40340c48000d40720320700080110070000440094410f0b81e00070902001241d88841080241202c5000e2405c444d9200380001000e501d0000d500c070501c1c105100c2e05a0800564648010180c51040e804400e103035190085c8041508041080314010100383d80280b400400f161005040306880c0c5c010b03c00b03901203200718000152 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 558664343 1250 558663093 558663143
    0x20a0204050705040e250e0301090501050429010515165c0f09040b010302040e03030c0712091815171005070c080a0801050f061204 58
    0x2500504144036528140000a0080d070060040e201c1030a03040020071243e0440f50b07200b4001043c5001c101190885c072030400d40d035910684000035071541d00c0b401e00700300261342801954019440741080c41020030302c100c80340700510402c0d1249004003110100400403a540d0403a2000401ea03e203d1a9950344041d100c60046d1210481000d013081103039881056880401154604e002034031004641c040f0341d0300c16481c0084200c112450310346040d0860000c0f00f03c44600e0300703005d017894008082c40600a0347d02d02041030034104950584407104044010825402c090051588400c06640518a140b410381c02c680803600030311001402ca8031180100d40d003154000d2004101400c0c04104203150301d00001308100291503840d03d02c401e480154500003610240c00d111400d020a00712024110303c4058a044400828000300844100811310b0107000200f0a10b100404030710074695280c44036513060505010034650710b202c0c65400345608211485e901000d030049980c001c0d9015002503042410301074449401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 558665593 1250 558664343 558664363
    0x220b0a0807030b092a130f0c0512090304181a0d050109030f09080d03180215071a0f040f060e030d14090d0503130f1506060e030a03050a0f02 62
    0x20744a120008014020006102c5103d08840d4007141c2050440b15941202681d88241041d010004030040e00154a040c040e03817841621162000900b0144440000c0242d810300c1141034042280015880d41450035101101d5201c64102c0065262a140103540b003514981c040d1031007003040c0d441540e240b0603180d50520b00b450b03110090181010006500340b1a0080032101021404910704d0258124501c0c010b81c0600100e801980145c40303c402c2144007a00580104180800c2c00c2d070748d505800d40144d9030014005000b6041100c15a160b14081c40d001804e0300c1031340102c00301d8101c540304001b00511261103c0d94803a60100e040d2210301103a260030406030035981003000301c900000c0380065100a8552201403180303d100289880e54540012a90703d4181c0e03a6030f180005141013001038a54102e0300520043c2600c40d4040d0600342071f4a8541c0081080c1d10704503002c00700c1e00d07039408022041d880920030511007000c4004c0c01c1d6440b8142d90152140c0310306d44243c0c043c0805200c4418450703000340103c03104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 558666843 1250 558665593 558665609
    0x30e060403150e010504020603180705060705031e04120204090317010305010c030b01030203060609040b0a03080301030803060901140a0e1e10060206070903200604031509060605220b0a 81
    0x162074403850b18041c22000d94042c0c16440c0d1030a51411a20f05050140c680200d030040c00b9107203140c6075402c0700c4841d0081da0702950036038810782100080d01d8640c04001c2034400e001c1d0300615264116000381c4d5003a049040300c018862001070100f4400503004001000b1f1155040341c2c00a0408114641512042080c00072030035042c43c960000000d1042c103402c003003e19070103950200b020b508030710010f401302e000a494290f00000c09003c103190509180c3e101180c2e2460092040110320b6072541e40c200c080c0d100f40c1003102d040c00048184501d6040ca42245400361034404411441000d00ca0003049400b0f40d94401d01d4582c0c5001c1307011900c2a08030804107400304020740b109450620784485800418403851240400501c60f80b0009012035204400302c4064a0344652148001c03155150105151882c0d4034242c2c1d0703c0203040100000141186031b003458880050400403800e0b019030300300901210352550015006201c0c1c65000001c1d04003602c82c1c181e884e140c1842c000707182c44112004c44c0c0c01da080c64124200c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 558668093 1250 558666843 558666847
    0x290d14070c120314011206090b0c0c010c05040510030b040e07090b030d0503010807032009070206040203061b0f2503050d0501150504030f020f03010c090f0e06010f0c030e06 76
    0x40003580310554003195400780d140c404100d02c0e81d1500300c08031031145140e0320110241e500140702000100c40c036161564010100422005081d8907006103240f010748030030b00a0800001c1c1418048400c0c0200700d8402040d00f48241054a4940400e034060340c440340b04010182c3d28201c0c801982c0d0307994040074000040c24111264180c13030b81c00c3c040040811503045442486502403c0d25410302c0342048030705032004000030300704ca1032450303a400180d0501c108401c0054902e031000c1415949452405502c9040c1c05d6000b13007110708041c01818100b030b4000d0701d4100705100080551408907140f00c00c590404400605c01aa64940300c0f000460b407140c0058aa91620400f600020500d540309010b000c00b00400c5000b042580d9860250380b204914140044020032400d01042021440e5201c16200740360014051076014180388000030f00f111030303602080c404540000001c4c400a840b580d600303c0174140f00d030404443c60074032000282541c2410b100071400c1000c1807003907400301403003040300031884600544590307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 558669343 1250 558668093 558668101
    0x7090605010e0906180a02070b160c14010b0d30050a11121810020129221b03050405190309030629030d080417040807031a01290d14 58
    0x6580503c0781620a104058040f0703c2b6111349003002d1074000c0d00c60b00d940d08151243d40e2007803204640c0c40c2c200d0030a956500c220102d00d44030381900201403449096904810985003030f0b00d528041d03600d418010920701d1480000345c001d400c9003c90b90304104a044c0820414102440549010b5488440000e01000490307402c800e050b00d11010351080302e04442e040003134508150224222440d0440300e00c48203040c96034400d20544140b20402d15000090802c1032002c030020030070107248a049804000da10381e00c00e543c0984c0c4c81c0e02106d80545460524060104c1d00b050b8071035680d0f4100d8261481c1b0140c40c14246d01e010140246036940007141c0c0800240001d00410b6214141c00e4200783e4148071ba104c6404d6840e8051a01044180e501c040548078184941c480761150328010039402220070048204010110301d0a80c01c00c503840c0214407401d0a40780171074030700b2520340c502141a032050301c105032000701c5035444003505d1802c3c482c103040522055848064848110019000700b500894070194035134280 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 558670593 1250 558669343 558669361
    0x305011418060f0411130503030703080403050d020f130501090b090d020402220e0712020406021c02070f2709030f080603070f12050706020c060a030e0304080d050301030507090605010e090618 84
    0xc6e02d4445524051100d90302c0e0341d0400e0544902c0303048070007400950302000240003e4019406420800c80c2c20100500f40ba12240100080b0742c0620591801c501c2c0c0d1150030011581d1010140005d0007041144070700346030b9503201040c600300c03d54400a224a80204501030038946142240e000d0596202c1411080d540e100100c82000ca03044d200ea50006408210304080429503001b101c007211a954000c04078064400001c41350703400340c540c0c01e00c00c50040010000710b00c1079415010000e402511240700b0341601036222448102c0c45001b41250140c00e20030b40e81b01007034126924401d1903015003811001c5590300303800282040e2031a04454043c101143c0302290110303401003550041d03441507080381d605544800d81a0303a030b5407003400403e9010700104079529000388240c0100c1c803080075070002c0780d0410351100101400c1c92440200c0900290000c0010418080100b10010003068848400c000b82c9003000c0000300722100c50001d45028064400104123691240b19084a070780700c6011040b0307600e05050b010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 558671843 1250 558670593 558670597
    0xb0301020c0c1c0c030c17031804090f0605090d020c032404030e04140a05060d050d050c0a170c240114030f0d030c0906081e09070e01150305011418060f0411 69
    0xd8990104c076040b100410b8090010272150f850041d0203103c401100b802d070400c000352161010848040380701400d030500094240c01541e020f03000030b0018210b4aa54044024501814014800d102e0fa00c400f00345a8000380c80311001220001c07520001005d0354450400b81c814044c040240e40d0401d24040f03180c1d5982c04070054150041003640c1c0103102c1500c811081003410891140080c0c00c503000300192103c3d49001d0fa000380062020310f41900c582c1c10168485803e8900341c0055107840c810001401110b02d5414800ae00381e607003440c01425041a03141240d100c407400b0500400510310601003040d20640e40c00c100ea46c62030907000c0304491043e4a6113100034041d11241c0d07089c001180c1c610781c002c102c09020b1402a03108807450f001038030b070407001010b142c0c1d041d043c054030030809406680804640a8040c640c82800b806403410041c01880b84040c0c0201216070590118291030104400c2c400c4c0c2c1c0d5155030010507410148642c40c0e0035616000e0008403070f80c1102250343c0c0d02c94900500e0003103014800340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 558673093 1250 558671843 558671849
    0xb0c07051005070909050906072a0b04110d080322141e0f1504060b270117030306130b061204060b030309030d0f0216030f060b0301020c0c1c0c030c 65
    0x9140810070340d4440140c806c0d01c0f4190b410b5411500280e000900d11031003011002900031103860004c40d81c5144451804101460f5207044c2d035030360010010801402a081e9808034005e03c2a10700c02908034442d00c5141c0c0ca0301002c1c0a144040d000f012840440c500307000030700010740d03401403568281c3d44064211a9900c3c4900e60219262480000d5680208000840d003000c070142554060310428402039440e40e504400108219042643c0d84035110b10764556a0750500031454015840704419041d2580e40c40464050f40484030b80300c00d400303844c0307005080403003030702d0f00300d1300c1030300c002404800070050700001e0a41070926075040100801c1c01d0024030109500180182e008130b00c204103081c40030060580701d03c500301c0b5450300750740000b100e40c041c60f1048160b0300c10303070b1207510642d5540e401d1000c01c01240c0d0300035403040da0058240101e0105228807486000e1514004400840ca84281100701030b4480d074004601c40e1003003103c44180078603040741c44a00001c4070303401552004010380303918000f461051940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 558674343 1250 558673093 558673097
    0xb03010e0a110a020a06020702060c011103040b150f0906010309080d060f0b18120a020a03030e09070816050a0519091809081209011b030b031908070b0c0705100507 72
    0x10041041014140308940c0c0506813a4050720748500075485403c041d41c0180000c903000300040111210b1100c0a02ca43c01800c1243c1002e241d0340c0c02c20703080c0820169000341c210780400c100c4841c0d14035a540c03500303919641c0c49415100c0d00c1041c0d41d9800103a00526903080080c28004000aa01c20680030590040d016141c1202d581c6a90729103403091101a4000c03401c459000328500e041000c19464090204960213407618201c0700440d501c6c2c7c0c04655213a0f10b507030045002c95444e10222000d132400300000d542c4002989005c2398070340703007241d080d00c0c800030100d00400a21400241c0c4811031446542102c01950715604d03018080da41c5100020300c54682031040300000b0551003412020030002e406905100c60b00319031100d007069810034450100700e80241c0402101d643e10361039013614101d24000080400346640340090920030f46814942004030900a9007000010303040c050f0700003800c0c00c0a952442d6000220b12000350754001140c45144211040a0514400c248d048051500c15801161062101d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 558675593 1250 558674343 558674351
    0x15060307091b1b0510020301050f060a0905011b06060f2c01050f011b03081501210209010216090f0f02281b05070825030f0c0b03010e0a 60
    0x790400c48100c544001c046038140240400744000b8034420424403950740e914003070003140440a0354503503250811000f0741e400d441d030300070004000d81d1502100b1b031641c444054078540c2c54007540040003401007000d4024641440001840d030340980c00840d00e0381c2e200992094080142d20348450603154000180c0c824256a4000083c10215104c998241800300c5020780711214620b0b400c1c0303800c1220703100780030b07002c541000030058100b0010100300400e0402d440c02a15076000a0400ca8440580d000400d084181400900000e644c000c018101d154100c0203c6400010b8480c0c108000403805c140c2e0b802103060507914400404202c000e99a8042110500030a20410600d500d0328055016405031641f007445040341e403c203960700010080007810340e001b250301d42007003041c030b40d6850000003a010755400d4400303900c5108180000041007080b4402c52654044284502c0b204095003010b41c105400000c00c0c2001900880e000c01406606500240841102841d269038680d1180d08090b0012103d003030711a070030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 558676843 1250 558675593 558675599
    0x110612041103030405030706120212010e071706011d04090b010803030f07080709060c060f0c090e0c03010506071e060920100206010b0a051605010c0f050309030d050408070515060307 80
    0x10450b001c1750400340c003600b0b2280c94408250707000e40b036004030321f40815000c0114150740303d20100303024040e10707515a414006080c6008001d24a802000c0ad800347c0c85074000500040e41c1e00101c0c8100c2c1c5003014450b10050240030000304001d002c00620080c29500c5c0040040348560021010314401c0408444450840d0703503610040310b003c00181d40d24404280a0803081c059244202ca041b100d6501601e4007080351140146038000312540c0c0c05c6010b0001d4030401050061484543d091600040b0901c034560455041500080701d911030510000c141c12080c40c010100002c00c2688004110380041040004036014182121248613508861510a40840c01008545043e8420000d40640303a03000300701b507a0034110061619803020345000d00f0f121080c0400b0200d9104266403d9030644540c0c0045145030540c00054807040c812404101448418000c1004848001040c0e0b06803482c03660380480c0316240d40c102050284640c4401401d0350040c10204480341e07405102c02030107900f06604444600755 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 558678093 1250 558676843 558676849
    0x1d0102030c0d020304031106012d051507032c1206070f030b01110616020c0d110405060d06020705011d2802031501030c060f03091104091106120411 65
    0x841203820a0740c01d40c0c00d00000e002d80c90540e0203540d00070700c83d013008448500744d0700145107000c100b680001c503441560500d0300444072005020f40d0542604001c0200c01e1410000043c070300d00b02805407924104000f26004080c1880342d83e800800c1002c143c01c0040225500c0c1046084031100c0700e855008112265020403480c0c00020441c0c45804140e498071124141c00c032040300039144e61100c55040000003414050645820303c0130b14051440310228100c40440303032030302904041d0043c0566118002c00c013540d5000c500e50254910700907404480000322540c0e4200054504c10001d24003503d03a52011a0b100100041580525507215007800c444205244900180303070b403070a582281031101d03070218480644d0036441ca0b680000052000301505c035010004000c0311344c0c003c1d0907032007900c0800f030492003040500e4000d40600004062450705012080d000c1d00c0ba05452134008481d42c0c0140d69070034051085c0001000b9040341032000501301740d41c03500e2403042d5007d030032000e59080d502102c1d0380d4881d0111345 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 558679343 1250 558678093 558678097
    0x10b03040f21170c030f090336030105010303020a08030a1d0d030f06060e060c1507050a0908070b04170c12071e050a03021002010b0d120e191208040f091d0102 70
    0x4c600c2c88110745140c3d1201506100d030040a000c904c443e02c024014405400303140c40c049130a65200700701d400304250b14090072005015400d90000e01a902d001d00600100b50b003c03540810f495006004603940352a8241400014402508000103107100034041d48115000458a110701072017070b030350510280c201082410b08448103417240302d011441e0316030421050b080800141050340c00d90000d40f0188000c43e2412400300303600710344413070000d98001541850160130030f42c80d0000d071042c00000c003881400c0400d00c0c040c5100d00e0144003d08003184038147c14100c07040007070361002e5501812003150701d203482000d6070b66080c20340101042440103042404a00c2c140d12401011101300406452005103560240300301d45290740000c8045548074013007150030303458182040c0702c41031080300d40d84c81d06000d000c4001d007017900c04820075214020009000341204030000d106d0050b100c00d02008031440d00c042c07610b059180300380c0e1700a2241c4035904000082981e690707803000340c2683c9a0f1140d040c0c014001d42c1c00508038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 558680593 1250 558679343 558679351
    0x1030b07090e0a0e01020f16020306010803070f0209061f05190206040507030204180827190e0903090a08100c0f0903080a120f0e010b030f06010b03040f2117 69
    0x4030b21448000348144225400c010302c502e8082d00018a051a40322900320f05a02a541010358004201203510449c01c0802c0210300400005020b503007460715a58a003400d108580314080e20508451020410941c1c5051803c400c21040800c5103c0301c01c034810002c0c04580041d9400310000c1680c00b10810514004900144501c1d880400b07411524215420040144005240008130307000380c40e200380025038490010040003070090750041ca21180c4c080d150b0003460511000038090502d5441601180824844c4e02c8141c0e0031005040b80030f641d0308040c3c28030b0f5004501070303035a20800e0740000144510000c251002d00210040c0107004001c440030041da14410b2121000c0000388103006c08201040882d0084c000e40d2020b45000001d21281540440550382c0c000c03c00c160303280da030362481e04c0c40480074450768140f40000e401400c4134911007001e2586a4a052081241c003d03c0000000c1c20020316800c645075980d8000022000090480c0109407900d42200548011410340e0004a035080d40f103031904c40c4030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 558681843 1250 558680593 558680609
    0x50a1407020f060a0e07121109011a03040210030e030d1b0e01090b0f0d0908091905030c130f0603030c03080105090c190c150f06050405040f300801030b0709 69
    0xca459030143c640041650f900070205c03e0295201c00300d80082d0401d07061003080c5c06008801c15031103200081002e00350040c3c2c0140746c00c0340214103652540a410007a01e510680480d8045050315056800f5009050b460141e800c1c14000001d1a032102c01d050341c40070301c640f10914012422400112015101415407840641c0450311910b02000300442120003040040708415081d070030b214100041d1019940700c05030403580c881c1c01241c120024100120f1100340c410301040c90100b91440c0c8404261031b5400050194000e8800580d200004000c641000d40c1180014900b000101e42d20300f402021441101021800920000000219854001034180c01001c118100078a4148159161307156103001640400910401c0307107007030780441d91081c00419089820701c40031580340c0100039148100c0d9225000323548114030384018440841c1c045200c014040c0e50000f00c03d04580c50040314800c644c039011400e8400d08901c4803940d08441e40c00040307141240e108902c8000d0175101c40c401501c41041078015040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 558683093 1250 558681843 558681853
    0xb09060105090c18100914040501050109090c09050d140d020f0607110a06091209120f06020901200a1118040209060a08010e0d090605030123040f050a1407020f 70
    0x840400200100611059102040c6900481350f01050041d040c0034285400301d04049070400001c08000b145003010b0030202c8013002598100740c0003030210b50207401440881c07559030324500a028040c2040c070b4041e14008001741c5541d8064940100b6141410501405a000c0c1000780c4610a000181e030420003441240500f41a03078072800221a80704a038020301410344918082c81010074554400e0f0740358107000381006840d0301d0a1000c090100c15442e840310803101004012840410710001e84600c1680d40b000c0d0140e500c1d15040c00498980c0d404030651000d0b2300700d11200070196180012404110b9204005241020011000f00444500515462603100710080c4c005401882d1503401d040e8428001006810070356103842402d030840303d500245000c3d60f0f110800302080c0c1c03908886000002e10f40c9240142ca150b050070031602040049180c4544100005010b00d015955680c0060090302420101009907141200b0040003420845007144800d104100104011a03c085003013455001c0b2000180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 558684343 1250 558683093 558683101
    0x5040303050315060d051e10120b0c040b16061a09060f01050c030a021501150906030c05070204020a02030702040f02031509180a03091d0610110a05060c070b0906010509 74
    0xc89010803e4009550055040004000c14103c2d0700c2500d0081c61420714541c80d44144807400c0080e02000b411081401264140030824141c0d05600641a15400070142c14a9107440e1060200c40c0565001105078440102c1c10070104d00d0f400d107501c2d624500070603050000d030713081110303c1280c045c041441c01d0300180b1080c009005400d002d004a0300e400c1040c54940c1c40d1811500000342503070014040c640068102182065240310701d002d0543c003405103058120040c0349103020103000c62800348202028180c641e0220500305019500303136404150040c2c4250343c0d5019201000b520f80e031019104900c61890b007401d100d0380308801d10170790b84036070701d022054600a407482003085a01030000b400c0e042c800c0182200c3c5c0e5110401848194000e80c800d4560129040c1454002461003807123400d050100e00119007044160382d100911042c445400d410311a40b1807061b00c006c107042070100d00000e80244034800901500c00c580c50010000680244418030260329070821503511041c080c030641d64400c0c1c0d140e003c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 558685593 1250 558684343 558684361
    0xd08040c0f12120905060301090b090115051614030331050309040f1e09032c060304081e090109060c0c0b031906060206040201030e0105130605150604090209040606050403030503 78
    0x20f4061104942080744549949400241e59a8000d130489100389484659880c1c0034141854001e0140c504540300301c800019100000b0014029499800002e0b400b40c01314800780500350456205911141040c1e1b0398a20f41201c03c508002503c80c80e945261103c2c0a4002c6000303080c0c00e5048205510001852612010a0801002e000c80c4500310b010745e5034413083c15558001c2e001d0070809040c614070740400d91500c1400e01408542241900c1c0b8214245268203541c4250b0f40e807241d061084003264415281e450743d09101199000744030110749162207a02600440e01c1c1180064440004240d035900c0b0400e859000031a0f6070000c5040080140d01e031460b003402460a03070406181e00601c403580c082c40d95040c24601c402034a8107a800f904c0540c000301e0512040d56414000c3d8000d4101c1d00000b131250303003800f41e0740404031000705130090400ea030348002040d40340c60700304108940001c008003013a480701d840e41c1380040298808110188280e1401d00e00107103040c0104281c5084a80540300c01e0304540c1c441d041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 558686843 1250 558685593 558685613
    0x50106081501020723060d050a15080303040f1514040c0812030c070503190c02210307060506010e0a03110a060206010803030c0a0203070b010e0a0507020129120d08040c0f12 76
    0x58a4011007581752035003102d03122800038000320311030010086803e04001c0d0801c0201d0b804108800b2084203184030500c589080007040f030341c1266008500c10510205820102c4241d4505a03c240469041588050082001c0c0340032a0003580690b400710034655a400101c1e0f80c030003140c0c3e16100c6003401800092064080385020748052400780003a20300d05500c0300c900010200f484452940403407240ac042000754140103401c08418100004000c0400d02d90440e4140d407402000d80c0100782d0764540000695991041c1650884020003a0002404a40701d2400c41030314040706a82d0340c000c421044000404620028080c0e04a403020406145540c485541d041d980758001c0c85a1002e5104c20003141c400540b1b070001560007040c190500c170500d4106400004181c940140c2040f04581c14072480840c41651981b6401c0a0210001d40080c0c0703000307110124108003030200225003130740110400c50b4001a000038000740700728418820040701e15114110649154070a001d04040b20707422000580000365200c076 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 558688093 1250 558686843 558686879
    0x30609141603032001020c060a05090141090304030618020a030f0804030b070e130b0a05040e1906020306011e020304090905030d06170705010903350a030501060815010207 75
    0xd010300040300c40130713490717820b90b440300222581c1640030300d04014401da003a1154541054a041c000c0c021411000c80d049040d0788074440c5a80219001310040408903041c039580034010003a2285c0d510389282440d24241c036070b00326101c2900d4840c18500707581c80e555100690100d1250380200a0800740c1d085858841e24040c9400003110b890714100008800300c1c84842440e4030400144c2d5a0100b188002024041041c3d103449040d81c91034100707500c6002c00d9a81c1e038410402e99109543c0001e1045104054600d001e482044d041c00300d40c491100c145c24015a90015803042d03000f0388800190541180031840110035107410640140c009200a00c41f001c22038200035860ba00a00840b414601203020f03020071181e503030344a04c2c0c503110f007542d803a201601c040c001ba0009080034207150380c0451843c1c81c0c90350004440210020251440c1d452103060305041e514010640350350004160f20341d40d1401001c3d000308000e014040c00714014400250b103100404004200848042e07000c0c100c420702c2d081d060708402a07115 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 558689343 1250 558688093 558688127
    0x71508091504140604060b0109060c0507090e03070f0c0f0b0f0a05030c0903060f0a0c03180f0804030b0703060305010b0f1e01091502071a0c07030305090402070c03060914160303 78
    0x250340c40303441e0007000703603034021741c01800c1c0080d66900440c005000701c491903000343d05100451000c0e90110f40302062100c104d521046002c512a07088801e614154424224010241501c4603920024041d11100070340079070b15115503118a5a840b100c4500c654041c11a803c9245c1d582080460001486140650b4100348108031107805c06940b030002034201001214010762001c10a000c105170707841a809070194245180c1010002034941d0340080da03000c14055005004c2010794801d082c208a2003004640c0116002540d0601604043c500100a41f02601c405e44181d0f007403400e407405501e86010a0050301e18002e00715070786030811142c0b01e40022090325615051000654000602e507810001c4804240416405040d045082101d00141c088002600010202e800d12580c105110001182c50507203405041c01c94587d0308100000e4080d11680d800188002002070001042040e15000385880358807414003801c45514082d1540c1c1e54818283e00356851500c00e050400c0468094240ca03085a0662 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 558690593 1250 558689343 558689363
    0x5010614191704050303070206241212030c13080c0109030f020d05030a052104080f0f1e04060e010f140703030207050a05060714070201120b01021608071508091504 72
    0x40a07001101000031102030f038131a00300204010381c20781e06005207a4003400e614800c1d02081044032440c29070041850101d802224004a0203c03038610030486500c40c1400a81031650760b191231035004045400555001025412944002c00d0101c03000c110362501c02010380d6204980740c9035444590f41d0000401040c4c1c2c01194140c009000720f581440206030759840b50719426603c1d0812032542d5103811980c0015200110600140000150908111480014410221358861040341c80070a0a88108540c821003001980207440c0c19038000000307482125217903114078201d24885401516200c020300025000101401c00c0c0d60049100d680241c12054084d10300141014540e985082c81e1015504042d6840da00c100204580e55a100c078103e0000c0600f02041d43c1010480c2d4000b0744010341d03440e184008141c0382c10100c00580d2007006981c410034909400304201c03e0762395240e1500c8102c03030b02a988803001040c02e900c03601c50040dd682401a80e10710b000300001c120a14442c000000d000e401101e501c491 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 558691843 1250 558690593 558690617
    0x210181506140303040b122518061e0518150702030c060a0e0103181a0901050604060506040b0903240f06010e0f04110408100204090501061419 63
    0x24410041184201941001808500b001c1210060260361840076100c0d0384100410302c2101b0f41841a06e4150013581448642501d81e40207200d29450359181d41d20862020070020752050785d10200350380782c04425076081c0c410380b502c901045400f51100c4000ca508c000085110000940c4100010b10041c0102e482c02800800e410300000e843d4115501c1c0c9603c0d455010588400b945024000443c00031b00440b012031405030700e0384002d040c81c0a000740003410b05903620070320046040038200401c1c501741c2c8020007040d02c40301080f9010110702c094030006400c0d071a02001840c0c0f801c0a12a010a0b180007c00407030802d80790903040c50082d80010001600350240780350204404440440c00321030010700c2400c0030b13440d1070140c8443c0d40311000205124108078404058400503280c2070f42600e0301050555020612514003c1c0c00d004038072842d40241c96034071a0310107400f200307001030303014209943c035007030040c40b581e66100401c80307980c0c804182000c03142d0720400000f503c1101c5003408019000840c1000c940d0b42c29 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 558693093 1250 558691843 558691853
    0x903021c03110d08041406091509011107030c14060c0702061e040b0409052206050406111303050705030d020d081503030d0e010506040603150f0b03010f060e100303021018 75
    0x1110f10443c0c02213200f041c24002003040c1ca03002440204540c0b030042c0310601d4115403041d40e40ca013034034440135102d40d46804195404029000846d0624000044554030845464000c000005640003595000b00000c030702d1400020118166008a600c600c200341441129000c01c00950b00c00001d0400c0c400121621a03400409000644010640c1c8500d45454a14024840094503c024a0240c680e8980c510304601150420300e408805904110001159039640c54160020030001446518100c8081030100c04603080020080a032803080003034406075680e42d0281651914420071a401682084400b14072251142c80ca599204015414103140b0400c2140820304503441aa0119103003910f40c10031a401403070074058a44c1014066408018251654035101d02e1620700f082c2403001517484984085e1580712582010f081d11000500030400d11090800e084000d02440c4503450001307402a0004940200d080c00c0a02241d4154000d4103680341202c22100003082c40101d1a080198070b5015600410703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 558694343 1250 558693093 558693103
    0xb0901050a110a0b101d0a0b0607061d01110c06040f1a09010c030e0f1b0d0204240e16030c200d1101020a051602040b0909070303030c0903021c0311 65
    0x68004c114440881c2007a1155500c100709036082100b5115101991548a0094804c9164032101d100700c00100d40d00362000050070b40c4151803020f0000d0b8200b074040c060680038035900c0c1c403034400088020002c4580208600c20180244040707111180c0001f8005808200c030960400100740c800d04214240010a18030040c00250640710404140e641d0414205025014801e04805010100050601f00006480e05595611045005401241154031f800c00c0d62110150304a03025401081440301414055900302c0d5a01e07903144000d000c40001400003229006141e0359402406403500c0910150b4001009030b014180352800300041100c034040c03240e48844207480001c01c40d1400c03405000b030142c0c10b09000300f0034440b402c078055050348100681c40c40b1541250459030a2401170302d034006130103424000a001086030050300d41c0c002c82c14108200c090301000c2040006d403403180d201042072649440c011031309c22034a800000c0d00034005c0c020f0b010302501104a02050700c0d100e03150502c21003400390700d00c50900c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 558695593 1250 558694343 558694363
    0x302030a3201090c060e0904140118050a0209060a030b0a1e09120905060f121909030207060f0c020d020609031c030c02062a0a020f07030803041505010b0901050a11 72
    0x180d6440c90031400704038003402008020045c5141581e00c000408000421107840940000d2100702c501403d0b0702138940c00e40000f0010450310408510402860034699281e41d81c0d108128410344801000458034030b0498018400d99030085807003101030340c070007150900905100d40190414000320b40c0c0d00300882c1d820b02808401d01d214101c4043d2050090101420710300180d0080303485903000380500302d003c16222003501d640c0411180044e0017615200d6488210840381c00c00402c0180c2070448400502d60002440400c4402c00d65070411850305c0450101c4404400e01d80007540100a0209900549003c001078030104400405444481e0fa0044143c5950308801290314003007a01d420500c80380e03e40521605a0240d00c450b03000011000010314042c0351401d401901500700400f061840e8998802c00c80502c14208200498601d2034403403d1054160b00110b4044032480b01c0f81c90014100c02e2603000b903d040700d1b503544a06082060000042d14103400590218040000403804203c44880802010005e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 558696843 1250 558695593 558695693
    0x50405090c040e100312050d06030507060503100609081c020c0d0506100b032203110106030317091f0b041413020324040803070908010f0608010b01090302030a 70
    0x607076460f0801044400c0303802000c240b5890081c40041022510302d2050008a04292520581d80c240e0b0904c102c1c01130026400143c464454444042600e5401c480154003074142819908a15941c8013001c07154a200e50040a0040d040b440c641d00801c07101012031082030300b050041c4e544031882d240c00b0a8881410080981382a48030a00380001100901f10b144007900c0071091440c0395141075524100b2002e0150450098088003010000901d80b00344120003e451a6000030f0200c13a60ba800d00406920214880c080c6050301c11001c50796091000480c04d03450f641030600c582c201100f0300d61020051032580102900079480d01c0c0740d50400010b0046151089842d1440380d440f05210b40103141c50642c0f0090031410b801000a100710b61741450380760741a40300d54811000f036503c2e981d9075012aa540c6056000c50702c50340c28004080e00343d0344075401800540d05500001c0103566045401180c49034010700c40a50160401116080400c2c0d07410340b2038005003a1a0013000740c00103000014800000e000e400c1c030070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 558698093 1250 558696843 558696847
    0x30913020c01051003120e150d0207081c0b06041d0601050408011d070b040e0f04020103140403030506030c030111040504090218010f06030b06070201051213060608030904051e07050a050405090c 85
    0x40090710403842a56020b1b82c0340c9480c03803c5500340403911601c0d540c0080510702a01040f658014106a0102e80c0010b5000d80182e8903000400301e0f1802d025509241c0e180399a0600544030700e1030410000b510200d46018003800700b03503101550f54040404002d080141004010040801c3e1481c0c01d01a00e41c0d419032801c0602440010003183c60f0503e03103a42c1007407501c6003003004200204d040341d00c95950071007400001001181c1b40c40c40107070700a010558404208026150410060580550060b0303c205400d0701950385070500e12040508884d54107045001c4500280001c0c00300d420715901842070749101405054641428a11180c4240000d034490071814103651400d100f01503250154544050f03003940c4050401c000ea41c0041c0960080300b40c1101013200010000d01004840011201410b03007000d0100078490700e8001d01078503540300e40400da0282d421300713001c151507129080c251740704801d4401450009271542501120140c0c05040d42104000c001c0c0004030b130903956020100e0007540c10b405515 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 558699343 1250 558698093 558698099
    0x4050a0e1606021204060519030213030b070818071514340309050103020a05071703090d020a050a03051c060807051c2612090a02040e0a0302030913020c010510 70
    0x130328280042c642c0036400d007002c1c0002c00c000368000d025070755150000004841007008602080303009010b04407500142c4041c8440010510000e4035a07503018004a1351250340c1c0c0e58601102c0b10280d11060300d2080340b58400341307007003003041c45900864804803d10b190011140c29170403071907002c2da00268207420350594040e419054807100c1e00744075841803204002444c80003010351006085c0380301a200c0c40703040c960000384005c1c0c0703d0722841c2114002c66004442050394985498464000d80048035040118825003911a024500000c2d52488142c0c0c424001c018120290342d003104c16403c040e0680e0700300440b541844021400900412018203d82401002c134985003000b0040e0b40042404004031402c0300c03c0503030010078080c03907543c40500c1801d0400c07071200800041580c0103201d010781d01d0740c44640b981c0600002c11004241c03458820700072034080c04040b600f04072030380e00d0301d400840081c003581c002c00101e40103041c16113070f0800c555040c3c48018201031880c02900d003034510403070307007103601d420701d21814 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 558700593 1250 558699343 558699347
    0xe0f1302040302061b010b01110d030c050f0c100c1b080d0b03070905040c060c03050901210903171f031b05040504120f08010f1e050a0f090606020c060904050a0e1606 73
    0x1060002c07c00d1030184041006840600d0b10f809601c1702e0401090f0f19120090115030090040780c020300500d0340d482d0707075440b201d481c020303140c003c401802611b036402c100405010340e1091070510341304007401030003004059031659142c46c0d5511280c5034071401034503a0944c1116542c00d025400081c0381d086408070f19480c081c90f004140d0401d0760400d01c00c2c000301c1007845000c20350000c26204140e600382040841d06c032202c40048440c01e00e900003200326a0410b00381c1c10400d54400b9a43c80c100c03a005408070b0481e21001003104814010400500c0340c81d240c203408101040e0101c115108101030004030300821500d804c0480d041d00d0080f6000d8802c860300d0001c01080e1540300c65410940f45880c07503c0c4a855041040300f40707040015203d501d0100542e4222421000380c0c90f8041c0b00109070041c013011a1b41d9070fa103a0542c5800d0b075032050140380f51602d000041c8450011400b1010000010441c504e0105003500300402020090114540300e87c0c3c0303c985c00f00016003003103015000c0000340c40380d5211500d41400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 558701843 1250 558700593 558700601
    0x5090a0f230102430627030b040b1e0c07120905010f0e030709020309010e1903170a0b040e0c0a17073807120e0f1302040302061b01 58
    0x46181107500940960002c000f1803050100d025010314044500401d401d59101144922540c0001d15038a890100050b811b81001c03110500c0c00310f20f0f46650030f0401401203989000d256100181c07402e81c2e4000010006500c0c0041c0c1035011002141c18403400b02500302900341c80000311515903071000005280014804d02461140c0c5a824510706030104505000001b0301011030b1001c501e05003e030403c842c0549503030a2002101420419404645901e071081c1001c1c081c01c1030000d0061107000f000e2500c611440b061010010494041c0c48841110707818980106110308010202c8640769130b1134500010a07078450048145800c40d00e801892091961010007a0751011907000200e600d00072401c881821101003860f0080f038800c1101e000306021240d003008100142c8818140205041c007058074800102d1340040d1200d203010382241404400f4001d403e0720340b00560a4503991101f52b50203090868a0112040e8110310442035001d805c041d86c2c0d50201c1c0694201c200b01c406142e100508910000e1f01c2441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 558703093 1250 558701843 558701909
    0x30b070306170a06050a0e01020712080c0a1b080d09060b090105060a02100504030e0a121a060603061905032a24090109031202010509010e01021905090a0f 68
    0x500807074050000042c0e0b540d8800d1058018489511500010100181c641c00155022101c5d0025959002117140c102e03d404c2800301c120300401c24540104018010202c162083c1408644484041004800e6000703c40d03420754500b208e99030b81c10070030706c0704454160140c1e00310544140400309808001c1d0040120030801604018060401480800103441d8005852407041607201c4001030503450314202142c2000f007120346640c00070b42101002442540c88a2441d410600a504005030132010380081001684141c44480e4007280a0020030940d244c102c1e2504043c3c0a01015000069a41c2000c03e061004546040105c9584000032080141d904000c2141054040b142d041809249180d0004001e03071210700301418190110321160705900550908010b075400c1440700c2105284000d0081c007030641141c00c540e513942040c602c070143c2e0b030050003520340700c03200603a401602c11020300302121250042c031419903104401c81d00005100150140c1700700a4121201307882c0031882c41c900c01d04c4110b80002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 558704343 1250 558703093 558703109
    0xf150d1b0504060804060e0a0b150102010204050d1101120614040b0906030a081605070902032d070c050c09090304080f15011511060a060816050a1509030804030b070306 74
    0x1110258409500004072002d9460a090490240c5c6450401200425038640903404610132001000300f44482816041c7c070940e2400503911446c140c107801242030740540e109191b007000c0c8051400c4006034220411450109041c03400306007106003004101c040e110183d04c00c54088140a00c2484941028081c0c003403208000d8491401c1e0b41040070109685504901d0090000c03000420070040b84135039808111700140d008000c4441d1240c13150000c000030f51054a420512514403d451340200310b8000030041c2c640f0320450741110f2552082c0e0b0039911042035100c1213803a0702404403641c02c5035490341105400740d0103050045486a040814242c60f28076140c14002a6074029400103091446491a05041d12000e02800c4c103141046207007070703806c000c26401020090241c6070801c00348a134140e02280c01c4030100303011507905150300d0f10340750700d641544d0160940151503a0024400e50150410303042c84242e41c0d10301000080e5680d11400711641058101300c0c0c00e1480d1100f0f03c1501036043c00350b20082c1410b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 558705593 1250 558704343 558704381
    0x3060103061d030f0301050108041a0c031005120c0922080702010809060108370f06180b060904140d080f072a050c13050405010f0b030303150f150d 65
    0x1300c03180c48180014450581044564000a020000ca130003030302401780008000f415031400d00e8000c0c03129170340080300d10b031141c00604440040d061424050a0f0b03030001c07502002d455442c01e00c40a02201e004018074455108108001d03040c028400d1110301101680545019a102d910900c001800300c1e001500c4078000c0d40c044401440448004039010942504c07001c5071410340078040d0808024812104624184096266840c5090046400c0c0e80d03015244520000c001c140c0070021020b8000c1c21400000d0b00b0340c11008002442e5085c403140d00764015000b014000710400b1000b00c6c0c0d82c9040322203a00e4200086000c0c3c14080d44030301e0403000726041a21800c00c488103c44c281681c00324084076400d448e21340c1888207003840c00d10200740b080c00d80d241d0000c0c10000003140001c100c08042c20081c0c0e0115829071031305c0071000344036000744a41040106c0c014080d51464482e010340d04c501c414003980140c2c2c0803194501c024501e50300d001c6c441040003001449240c4a229107000c2008807454401508002040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 558706843 1250 558705593 558705607
    0xd05090105090d08060d1e020f0603100603050603070f031a0a090f080d0b0405010b04061d0d0f060e0d110f060708190204090f05040510021e090f03060103061d03 71
    0x8154a190403846207440100da0b170700d10000030240204028040c15802c4118000c0c016030710703091070003440c150096840801149500c0700340b00180c40225201c91014007a482d0a11000c0e2003504030540103600103044803900c58949640764110000e41d0b00c11115031005095003042d0004541c141a0300404198040007428011b4440c0c20400c60895401070502800003202944003d0039404017800300f5000d8420002d9685138944c1440940c81030203070700007080b0500001100214030071584003403140040c1c5031000c011541c0e81d800b5000f04806104231589038541c1c141d44a0320310304100b640561100c5689a00309000201d9466003461135201100105820160410421541000c11182c1109110f00b002180008260782500223010b00d070084841c05080401401500407150001401140150103880d48403211481840c1280310310b800c07135103480c0c0c03517113198030114000d26028000001c07020b420842c05010390000030b8200a0241c00888100759264140d0b040c00d0245445020801c00b04170086141c6a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 558708093 1250 558706843 558706861
    0x10303360512070317030f330607050106080f010e010203060609190308030c1b0a050d050901020a05030d06090c08010609060c0218090703060501150203031501110a11010e0f1f050c030a050d05090105 87
    0x1030380c88c091510b02010f8800740b031b52a0702c454040303032440c6c2c2c2c00100030001a03860f840d1154a5021031100e807042c1c0e40c00c0403928042454107100301c9004550041009181c600000140800c0c036035003880f0768040d0902c440000003c5210755009506ca05036080b0b9159a42c00c08100c0c0c6903e2821810b15107000364000030002001640001e40d48912542e68140f00303171108103610040717180c5015648028054000032400f61030282440d0818000d49500e000e050050312200e020813695040248a12000107000610401400c0c0c00f5440307895456002404c868540c149210b03090b02114003c0e200c41990340c2c441c1000b002480150310a040c0503021450051081e8204507400940c1c0b40405041400550640410000341da07014100641c0b207000750109903010006d15040400d0246055000b4601199105001034030514014600c0c44244000400c010900300c0707980e510001401803030748030105200d010810824450020070240511120998a0b00c1da14a1044212010340e64050150215603040001b40300c1d0b081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 558709343 1250 558708093 558708151
    0x2010b150f070f051603030203121b0a0c1a010b13050a050a0302042307020607180e040311070503250905011d0915010303360512070317030f 62
    0x541c001c2e82900343c0403d9400c0c0700d810011564105030803c1c00c040c80000030960080301515040ca80c03055070300c1c4d203a0396417a861110343c910000c003071049400c20008194414056000e0003080c5004e03009400780d8641e1500004204070003a0014404c103403001c20680c0c81c0358400707904c41004d041c2c05d503040d18800d071810380440e44a44503400001d2080d41c680d00b002d44503040e14010b050340e010284550000608003060003946030501902d0b45030004504101050441707101114280842e00708180158060f62251001c4070404aa0311845c00140a103a0000501d03603000c000e41040c04800c4610141603e101c005201d01c1030120703a01042800b0b0901e070040004040d84074403820440d040702c2c12440c8650b209211507041c03201007270186441c07000e14000801070507070200540c0740c850b4144855200d0401036001c17107080384440c08440000700a081200707010904110b1035134842104440212074203a5241d40c1c0e8100142600344d1021402c0c0e00120400451900405076175030043c44040c8004500500c540c1c0b040245 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 558710593 1250 558709343 558709357
    0xe041e1a090c0903030d020a05070c080304060c062c07170c0a06030b1c0b010303120203040c090e0c060f18100e01030515090403020606040b0402120f0a020c070602010b150f 76
    0x81401003880d4015131010f0081715241d20400c20219a21141c548000d09160454102641c0e0094020800b08241a0000c212026140d003a10760790303241500e50b59441d0243c810307281c160181d03511400c8440782c035582c80982208044d005601401030182810055030113114041002c05041e07001c80c04407092500c4070151b1105640c07282c0b601240700d4004601007a58603621004502001a0000f0460244030805480d28140d80c42680e80103504020517880005074003003581c010b051b00b6419003040140b064240d20440c6488040c400743d9a4580c54000090340d00c0d002160901120080001c2d041e00f420255440711040001c121aa00c0b00c29407503440091500bda07610f182e134145680c03100843c071240c082050824881c0030003400486145040d107130081d21000103030307203040c00b603814420820a0383c42c0074005d8172005140742030200c02541c0c80c141c40115a82c0e000d00070b0401d01d49d00304281c81408506004c000040c0c03100740c00109600001c5400d11004440c0115070b51286007040c0030751403014020004549407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 558711843 1250 558710593 558710611
    0x702161214030714011a0f130b0d0b011406120a050a0b0d08070b072109021201060815060118090c09090f2301240e041e1a09 55
    0xe000d149140c2a26030031150301c0380041510010071000100000c0d111820b4004001400901403000702495a440000c44091665030007555500c41c100c80b4209400c80303a07502800400e01145201940001c41c1442002d40415a09100410014000070030803a10b2104818010f484041c070b0200e10242c0043e500f440603100400103030319400482d001c4001307600410b111f2280100044403680d123503c0c080078540d100a0b01150242a031500141103180100e0003507c611a96425041040010f60f40c004000e2403004000c0303a02030512144010480805d1044030040c05541d0b000349070340307400f000c142100403100130649070400c01030120308080545c102c0d00c0744044600c0ca140114010303e00c15410344172501640c10070b00e00a0701c0d0101e20a9101803a801030242c2c202d20392125203c0240b8031072075441c4918240100d05041c0d5850655000080c48030001200708800792800603260000100081c05072400700d80d80300c80c42d208032110204480d4980c032a00701c2c058500400300f03180045280226040c2c1c1d01c02403540700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 558713093 1250 558711843 558711869
    0x5011e0503060f1603092418031215031403030717040519051c090906140306040201080c0d090506060906030a1106130315200301120b1306051608070216 67
    0x205140290040b01003141d1100c019903442c02c60b4210a84c0201d4444503940768982400700100c050b0a00411544299402d9500d030b1441d110706000ca007000d0b0582f4400505080031030307240000402c01c01d1464030b616085500c007a540d40d041001c00201410304090302c11060202d044c0c14030000480010300481209444040810400024100241800c0480220903465150700030f089190303541c0150103070306a03000720b042080341c030752030341c00040101600e0511640c044d8070000210340598010311545511200910f00305290151040c0d4082c19541500743c00c480c0c40d400901881854504000d5441d8450010380082612207000c2e16107680040d0380200039406200000384020b252400320074810003840e007288603e4490805400314000900c8c48450020303c500c081c05c1c8032624140c4d1901100d04907001803000310120300d03c50b211140c13640c1015008400b40300540e04400300046550080d588641801b810307946402880300c03c003812441e8000c19000454002001d07616900303051011000c1981c000e001098 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 558714343 1250 558713093 558713131
    0x1804020d03050408101d03210a090203100c1d130504080f070c03111008160309021503060909010b06040306111b241005012105011e0503060f 62
    0x20b0307010b2042e904441c81c00d001d0151025101d40d02c1d50817030664a0046000c05941c04030403a080d985900034072115420604102d08004600341094181c40d0704200300b100c0025100b040c0741c0c00a49841c5071141142800c945925007001c4682d00009280518401c52965101141904000845500c03145030f803442956540e8020401780b00124041c0c44401042106069880f5002e081911140c94144012220000c80e0b00d08402c0e50b007051091000d80080700e40300c0d0115038417204524055006c603006030800b0235903917900c1c25001d40c0d280c2c0c0c0540700c4080902402980d0b828101c0902000038030040134901960b041020422098072501c08032002c07242c0100001800000d0f0f0140010980300b1002e1840d07040b900c01500310000b810101e0301541c403071010300b110005482d0b000400c800e000b03001c60380c82c051311100c483c1c1000694014602d52010008101c1c41158110200004900300d070740a8000500b00103190103011015010b070421030001e0304045000304400d2804140c000201100101002003156420000c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 558715593 1250 558714343 558714347
    0x305070c0b1008070902090a030f1109040b07020d0e0a05150417060115031401171006180c030204081b06070503070809040b04050601020a03052212050c1804020d03 72
    0x55424940c420505401e80c20301c01051502034580d0702078084a4021190001045503282c0f00701c1d5075100c00a40241c0600d855034039981007102c4402000d40342c101c0c07420269030003552030071660f038030992088402000c01d007042940240ba01b111480003000f0720401e46401c0700d09564510002d0104d40c3d04440001c408401009255040d01869104503008110039016006602010070114144c41d5030500803540c4007072402084090b500c2c0400b049214248890043c402e0b031102d54035951301c04055604641c808903101820714100c442950290106903000030a80343d440f242406003213118502440c0c15403c2906250705140c4450000e2074407402070308050400041c946940b015100e43c15002810b590b140c00840c10080c0c12030307010a91f0309100700d240a00d01c0290b441d06110f03181c061101030f802850400d1132582e05440f03947c8030780d00ca080315091040b00f42a03210900d03451400a00340101c5600c0043c080c915100346000c000e1003e45204420752558000703222070500602d640f01d50115152400d000c464281 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 558716843 1250 558715593 558715607
    0x20a12020c15030406110708030f0402210a0203070821090d0c08010906050a06060804020108101a280c06020a121d0c030601150305040204180308090114010312030507 73
    0x3550021164502c1d42aa814014003962046001d00c0c024081240c002600102e284240fa40c014030100051020074a40009849d2082d4014070203040710f60346090700291511a0040110988000e6100d0030080c0c007142401d000c1103005100d154001d2103900c0d00d50100240c0c64a00f0328102c101c01102143c1840780d665888a10a03000360402c0803c1c011a840c3c041035130290140b03c44c00d882181c100700224125200c50f100300e03401c942c0559215406510b03143e00441d09144050424581c1c0390b01000e02084032080495103020021101601e25a14182c00405207000030000468a1002c4582c40000d00c050760440300c4010b0300d41d0712100069507452151400e070380411303c0b580d030807407014a020907581501c1014229017403500b011f4400c55540180744010540ea41409004401480303c1d0144002e40b4a4060341048c1c0c1c102e8402003002c204d13442109d401c100072080b0018240c000a01c1c400034045e21007400e210300300800017114584c900941c11a2140c06403901410501c03000c060b91a00000c04480c0315000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 558718093 1250 558716843 558716863
    0x1c15020301080d0206090c0a050906040e0f0106170708070e04080d06090e160b0f0c071805070f0e0f060705101d0721060504080d090503030f010506030403020a1202 72
    0x1085450796110824140e0321801c203c80c41016204890110b42004030008503403040c2e060040c01688801e080009100741c03c800640341c650816190140d0f0000c9080500181140b543d6102c0005511403400c1c10104441f03200c0c07a2030381c2580d0004c1c20300b80a070860200702541907800703003a020100b41d2120719215209116001c074004c0010320300440403c07101c0781038000344001c015881c115110201e9441b0400c41c1c03458544150b00001d0030030030600103d144840050000b6240c91401e035603142d40d0315101d807a03c4600701168024115603c10030442e01030707040124807454411502e00400311803845004190030782500d80b42e06128039408618281040810004000d503d0b00d02a8107021091040c05264a80310940c0f41040f07660299140124094241038005100030035113482030480301c0050b031580e80041001030800d44a0b500200003120907a0041c0c0940020340b445a00250750303e01e020300c0207414029040c1c0225110300400c005100100b0345c00109250340a801c00c1d040c816442c544402070745004007200c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 558719343 1250 558718093 558718133
    0xe060d0903110a030903150e0c040b040612050705120712020f04090f1101030f0e06042306010b1e0301050907180f030b0a05060a0302010f0c0602090a081e0102091c 72
    0x16103002c1003680c0300c400e80046034802e100140740100e4444440701918030303041c54038210354027840d088012440c054008103a848400351001500c03a40f030f0146800c2e0b042100c1da05884175800110f0400c020305205200c1001250980c0140c0b140d1403c284d6200c081540181c1c0103072250081a12000203591554020105c007644410002c40100a40c581070f01e400f050b49409034003080c82d1804d00f41c1140403134000d980390f04250034003809032580c4035964248100501a1503e00b90b00140c1c030030107828081049024040c00e1102640380e01e4207170b200d46080304925817004180344181d06000400454813201d10060308401242008500464200e128840640340d5901c02194100054000421300861094450046048440600c0381d65507200c00c0c00f500c180c20b0710000f800584d19100c100b6109201e0107641e1001c0b4030038007000d880c04081e4400101c030200309400142e29031304200400241d1031080703086488900c0301403000303500b0101508001480547d602c4102c0c0300103003401003001c0401040c0340280045403100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558720593 1250 558719343 558719353
    0x715021e030a0c020d020c0d17130b04030501240501050706090602041d220314090d061a192115020304030f1e050903011503060b0a060e060d090311 65
    0xe10082d20140c04902400c0300035015400c09042014404985208181c4000d44000302c48549907803408034100c00403801090a1030240041d0086680301100d003001840c1400c4210385840c21414442d00319441c642001c02c400070b0000d5080704d900082c04040040b45c50034245161200014200700d40584440840100314500c0000c020682c1195140b0754800040300440c5440361356a02e411800d020b81007940040c06548100d0150b10009104240d015048944022020b080c45404c0303001c161508195481151900e4440e0b101100c13118040e2201011150112181094010350a2402e0a215090b010340ca070103480140c01c1c1b0340144285281c544d0070603070103262043d50008011055000350416601100058401030314411740521400d00b6030101852011003892141da0184143c03010b900010402d5019500d401e11035006041903403405000718060480480c080b030042d420421102c403a0740120051080034510001c090b1621401e640041030f4079000013501921a08003a50070301c060018810380c0e8031031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558721843 1250 558720593 558720601
    0x901020c0405190f060e0105060a091d040b07050a0906350117060f0a1802060c070f0b040807120f08070f1e0b06040c050c1006080606060715021e03 65
    0x307103402540f00c10050420411044903034900c4681610705070b100740400800c000005000c0c0c0d00d410b5000388100c1130780c0d0a02d117002941e41da6014010f0426132120140171001c2004120034000d06e901c02070f42c8282c0c989003c910300130001101805441c000d014100c01c10035061039800c40c0b0440c9030303296000d40008040314815007503540030304485c04800740110a42e1030840f0f555501c40f0040060a203000307000d0100701c000107030b441c0b0106100520101e850250000c4650f841c800250310760200901e40044094082c0c02d0b050f040c0043c0c10946803080c0c0c000c460712002040204603c0c2400b0580000743c071003130750441652003000e003400403000b007204d00b0180109900180d01802c100c0070f005640803481c816620801a9025003004a11000c0310b540003502d18601000021164905039200600c22107143c280302d410649800ea01524180d0801d908500031361340d070003080c04841020400310b42d03c1001241c205181542c41d42c0d92800e01c420703000c02d00d29143e801184490001003000200944075181d600e9598a0b440c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558723093 1250 558721843 558721861
    0x30d080c0c2b090e01140d06020406030506100f02070303030f0b0303130f0605030103021f110d020a05010b060a21060b0d050103110d0c1a0f0a09180207170901020c0405 74
    0x34524146010b007845016448544034040c0c0d2030306003120412020350202d42e00c1c0c0030710f4145005045032039a521540941c0107200060b803c3c8003410150065540c0018145086028400c0607403130400a441400304c0780b1440e00c075180d400980239040c0d0394185004a41d076000750381410b025180c84544594140000b14015100506605403001101e00403c88070400ba6500c44043c1c442d48070a01020750400c01c4410041034001200c0340e0240060320b14549510a9114914064108103090702c1000060300200e24920602c8000d008641c04028211181c518003405102c018000c0070040c1c0c0066401d031403502e2105561203140d44610010f00300c1182e000d80e2000e070469240c1c000c140074001100c032456071a1a0a000f420414801142a1b41c81881e450810f800c0c0f202d4421076040d81a503401c20b40718104942410250a05e003d860050459203600364880d0070541c0841c8605910680960000c6c411700c400700c082202004174590743c6115603610741d43c40c1c00c0400103e0030305100241154001b4140000d00ca0700d11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558724343 1250 558723093 558723133
    0xe03040e040b09060f1005010f020313171612060e0f1005010e0c091e130f0212160824040926040501020c0f240a0206070509030d080c0c 60
    0x2000391001e940700755030b0711900802c09080c06d64000385408a071002c14040c55006204101c05d490440c0101c03030404001010a0080241d550444004417002d1810040e4107002042800780b071840c0354582910380b9003071a24a1940c10044107001e00040d80790170340710400c5001400344002044100c1c00b5200d050b8000f01d0000d010308401c1c4100c80c0341c00c403c003000840035080740d0283c4011030401840d400640c01c170391480c504402c440d0550643d0118420140440e105254400e802d00c040c40000090380362b411110b50780c1003142c0000c000f07501c100200f00b110720140c2e9002104039448129100b0803210030103200400c00388960120111900585041da00c0414003030b000a0041c48071800100d00c1c02000041007070b86079a40103a01c106800343c0c0c0000c1043c1821300d84801303020401c03803018000fa000d0107203052850001d94440310780703812000700c0003813a44a02c41d414020154803450500b041032030500c80401081d40d410a10380c600d41001100c1022035031000048044034849a511001c03640c0411070039210307511103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558725593 1250 558724343 558724351
    0x20a020108010510120e030409020706092604030813090e1506010e03151b120406050a02120720032205091b130b18130e030306040e03040e040b 63
    0x201c0e500c9800000c85160649144440003019039809803142801e0f0f900d01c0107040e00a1704c0d000c40340410f10020031412980e1000d400e1381401000081607040e0b8500b4555510220034a200311f0a07409c80c10160302e190440030894044a81c042201070399440350000d074038400e0000d0b400c0076074040d00305070301d6414601000402035130760f8508405000d210307210f0300010340b0040b0011481c01d8240e0003080e00400a03460511001d43d200c030820b40341000c00c4111a90151203540408001c0000c036004400348401d11945104182c2d0021035482c00310700d4400110b909805c40000103010108200803010041d54001281c469580c4908580f000c85c3c1e01c405540090614000161000582840c140e1100060600d0000d01c3c0d2401418040048640d00d000120b4442e100d503c409003030201c41070041d50000b00c16400c40d0081108400c1340120500a203003c0c001c100c03000080c0f5403419522801e007000200d4641d000300441382c2100c0e0454000504105a01a5030b0840c0190b901c0400c0700010181000b091029008192b0b100b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558726843 1250 558725593 558725597
    0xb07171c0e0d0207060e0625080319060302060d0c200309040b1e0d02011b0b010603050a020703090e060f040203160f0c0c030b0402060f16120201060602100f06050a0303020a0201 78
    0xb40301001001280d843d0303202e1040c0ea00040300d00d1240161803c01c3c1b001426410a0411440c90342c5158001d42c4264880480085641c02030000800c407616441d0300c0141e42d218000101408107500d590006400c1e4002c0000c940c01036a40c820b0b000c603696000384030b45e154403802c40c00e101240c090180c2c415602d0307400801c0594010b80c06d0030400010b515190501a00c02c03c13200d0421021900031605001c4031406c01c0d04202d060200d1041d0540010129036101c9a039180304240c1c0210b5036041000c01015900058410034034140184035990009800000c4803040d508008841c038543c0e5140b40c00151861200740364190000d00c00418001480e5905421403002c0d829500c6420381e40714090000c561681d4220005000b00c684100c0070b10002e02035000c401d4105000500080c14103c4c0340903048080d0b803120540040f48500408c50204014072024a043c0701c1e07100d030000b040303880d1030400b010350ac801413154029000ca44d80c00410b02d003403407103910101c050300010b0300381c07442c00f51603140281d980d07400c1120a80c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558728093 1250 558726843 558726853
    0x3160905100e090a1e050c0418050103050d210510090606120606090e0f040503090a14120102040f0608040c080d0207060905090705090603040309081917040b07171c0e 73
    0xc0b080d403440c01041e82281d1110344d0f82114481c0240407500621b40640300c1c02003114108070025400315200c00651803a200c104001607903500d14a0428a00b003004806203050142034140040c2c000001142480c035280d55040200e40ca990b8847c1c13420420041e901b2803503080e4035100380403c0c01c41d0300583e40fa070100418201005420389802040d541c09003584240051408044005600340c00c000e807a0640041c45802103a00340808000007800090040d0001d42600c544040b844045143c98000c100002c3d8100700210b142604003403a01a0442c0903000d020103012035100850200207010742d1f40801000c5440a42d2301800c00718400035165607040c4540701c00a61003460118640c504003e490380180d1254490f5481d104040044c00b5039500010026001c6c00031002c030004209c1c0e024044001c00c1018504a41d10700513440c41d100e90608110441006444c50900c0280455800c0d94100c407091500090010000390100b546410b0503c640004480941c08a240f03130050360100b500320512680903541510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558729343 1250 558728093 558728101
    0x605040c082d070f06110102040b030408070203010b01030509031801020a020a0807060809010b030a060c180f06021501260a1406010314010e0c010509040605060f09010305010e070503160905100e09 86
    0x15641c0c6480d8090450034030303192181009a24002c1b1400e2083c80000701c005410280d4542004486401c1101e05483e1110006040f8045203420b22500c2040d11007401c080040703042043d2559a207000392041101c6c0752040940b1032040b07a0080006039229036004040401143e1501d86103601e40340107110f43c20104e4050400b02e00b031600c0c1030080100380c4001a00170020705a60391200000391108240c1441440690311030061160200204007001e407061408003880c440c031780031000f4501200c0049140f4582d165000501502d541216404d87c4164840146851100860201420140c4412000340101111319a820a180e0007044082c104c0c2d005141c1c00102c0380c5540421744c00e030380b00080d54640315003015002c04c03035030340c0510050003085c13101901c0050795945880201b10103510403400e041d003110000c035500c0d01542c0d140c01040d024100200030b40364a401c1a40000e011800060145511a4447c1070300750100c074412200d0400170000144040d1032035010507006405000c0082019002c0c280d01b20001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558730593 1250 558729343 558729433
    0x916020c06071203272d02030309042705010903020606100509010c030e040e1f090b01030b040501020d06140307170d1b02101206060f0c0605040c08 65
    0xd9818a90001d000f0a0500c0d5445011001080203145043d0040380000c0c1c0d803000c0c141003080400740e140c85007400713103820014580002c880070001e501c4450301600b65004000141c8012040d01c0c4000000c1d1000300351a030410900c80300b951035039880011250f01c1c0302a44003d10a0541040321503034000c1d000c0d54040d0322746205001c10800e0860118000c1002044a001c0c1544607010110a19000c1d10b1b00e00100f00401e40005c0540300258034034880759003c0c242c0140e146d1100f01c071040d81d24107107007001c0195440659641030702d810144800390030460000300003424010290101c610282400c20104202601e48050402e103440800781180280705c0c81d880800c440396002c024241c00b4040313100130401611100412118006000e40d203148ad01c10114040006880e54124840c1020340350716044c20700b003004035040c4215180360740103c0410080ca828010820303003180d0700c0d800980e00100042200e031341d14200340c41c00122644c004d941a1140384402c40c0750f0000500001c19044042001202040303140e406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558731843 1250 558730593 558730597
    0xf0b160f051506190608060a03050717070503030a020601050d0309080712350904110307050301030525050603042306150a0e0f040c0911040f05040207030e0418020916020c06 76
    0x130400031024004007800701d14011020b141e0b02800052160744c07126129900d41c0d04121095008607180c120111209142c003c0a100280190800390011030400c07101c5800250f40303942c180700321401541c1c00301c5090149841541110080e0083c01c2c100c3c0c1941d907840c0107449000f41c130400151181807200744100c20300504c2441d103040b00c0501b4501600c4841c46190004116401400040e601a503600d0b1400a07441c40c60018510540803510b8081d100d6156040c01c42c105841d43e195005024580105036511081303554050064400669003151a9511031403d40c3c0a09005440040702c0608035011804d5850001103040c03140c800641c0e01c0d80d05540788014481e010f00c42d802402548190000021078071031008059642c854028140d44440e21307601c1105c4800c6a81070a02d2070760f0300c48006024000b132541c10368108028001036400f1413418006483c01001c1c500110b04843c465501e034107000c500040003e001448a83d0000c1090240d810109140301c58140203928440141c003038140c0da0480d900d01036003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558733093 1250 558731843 558731869
    0x203090a120f0b0a020c010e06160f021216082208030405030604110109030b090304030c0e06010206060f0303041d01091b020316030c0f1a010e010f0b160f051506 71
    0x56510aa80b4150b54007807030004001c2c090011507600f400200340703514003402140401c0d210000680580d00704580e1b24210b14001c4002c450600100b80601103440e40d0001d02000c0540d0814501525040100b806603208060810060b01d0b420000c10910940c00e0040c2540c2d0b0042c0e8104403420700345941d2400c075922401544200c0c2c2c0e15410070380c0007a0201e041c01c0381d8484405414981481c02e251a81c0d912980c03454107807000c121503800810b0500800c0440301c1904041c0008103026600c81c94000c000030f580b0f040040600340104c581c08480b80290701c04209807809015001e00a01450041d035110703034008902407180701c42190901d01070048010700d00c0c2d9000640d00c0681e026614100d1007500d0107005c0699028110108101c80d60413070041501c11519031001392040d810310856184000ba540300720401a0410880b03050444010003030f4000d108116000c588250001035140c4e00b04902022031028000c038050404640b4050400030410040703894240c40b00c440c020816582c95180500a00d10f590300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558734343 1250 558733093 558733103
    0x1103070908070609031b0f03150b09160c020d0b07020d1b081e0d060311030f150610030f0501240c11060d1b020303061e09150d05010c0203090a12 64
    0x4200b0b102246002c02c050030f0101425840c256121f0340c031940c02a20080d164001e5501442900741c0c258440100e002e1202440f13800c54110840b0b080000514107145a854a184d0a201301c580c40c0c1400c5407030380280c60000716000317402c1c07440c89c0c81c02c02806074030344940000403800105441c110000e50100c20f00294000c03a0814505402d20007445c032080000a04801042c9000c00103200584a800d100e0186401a5228981020144c400c00060526010100b42d811400390400d0444a80c410601001d541d4011340c201d030701680d000d001030419001000e1503108201b45504040011902c00e900030050542c072140d000446003031920003c41203c4c41300798a50011301b0030080e1440458103192442c0a0000c84000542c0000c2680108203031b002d50140c03023210403026800100801071240340080010301400034658003a10580842c0c000580c4400000b003070b1040c0b500c5039001415058035140c10304c04c1d00f2030703100000300001341e003480020f9503d8010021061081e42d0000b404a40e0b05515400c01d03001d25442 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558735593 1250 558734343 558734357
    0xc1b06180b03060405061518040605061207030f060e040f052e020a1413030c050d02030c060a110d02030c010b100c151e0e060c07020604060c110411030709080706 71
    0x902d0802000d03000280ca00d66210071007c682c094409101002000407104014030b80700412052001c0c04180d40040c4d00c421f200d00414040840800320003804654000d0144c0703800a00c00c540e03909031000500f07058004100060221003080308100034402d00c004400d004e60b0450307032003804825401c1031007030313185013a401c07800401e00c0b81c00107402c085c0c0c01410503040541400c40a00140d2488504e20b60455040e014031010040c00170414440b100c01ca420103018103540070304000120360082642e8000c808505030050f140010846a05417240006038038a11165003030740d00034280708174002c0d030729000148450595460045001e04514020003051811207440c0c888079000c1c402915505664805628492030b625290002c214100204882c1e05002c908c410000240100f044440d20b4a00140140b90f040107690400c00180940e072040213036800c031429441d013142080c4c8649080c3c0020781f8030440e001c3d0007600b0422100c20802c920b80185100381c03d00d540708034915640e940803c1c0d881d10b481c0304010100e508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558736843 1250 558735593 558735601
    0x403120903170f1303111c0c0204060609050612100825080109030e0405150a06020706020f030301030b0c030403031e021b06040c060e01020f0f0a030f0c081206010c1b06180b03 77
    0x81c107403580000303030202c250b0710030020106200840c0c208580444c4006900306414104612b4248202c501030500307854a568207906100210b11103102c1e04107031240d4491100005541c0003035040251000d0800e25096a5980c450790b030700000b0015035a045003400214a0701c0100d1b00039414802c420840340c02d50343d080d0701102c2500074800184806482900d9142e05641c00c001d82d500e41000c010002c01e0284d000344030320303460014001d08003401029100c4007a0030410040004c1400600b04a800c80040d41880396a5219460709400600004220030b03601410711010342c400d422180d010b042c403103d20146c418130300000c40c0001c42d1a0b080840b4010400001307901d040c00024070940c28030780001c5040c0112401c000da0880140e160135102003001300c04c3c1d03024113014010141d0210154204103074509141da404804e564403e0154040c9001030000060320000241a680c843c1c0c240b07036072070f40e086a180f413250034050905051100e401c2c080d4201058014411401d41940703560302c44d0490300c01c40072590131612 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558738093 1250 558736843 558736847
    0x80a11010813050f161d010306020c1504060911010e01080703020919090c020705010c120e01030612050d2007090504050c03030307020312010b0403050a0b0403120903170f1303 77
    0x40180005803119112180781d00001c83c100074080203102010001e028004980e03140490008240d00a010072080c101313400104030fa811150181500da01100240c3c03901110100321380790000403c0c0c41801542c1c400180700602115510100c04a07014200050501d0441801510342d14912429203002801c00300009441511a0b4090082a50002e0180300d040031f100c160425200342c01e400004a07655a500049600ba404110100c0106820301708442c0d000c0290315581000b0605d66254014008181c1c4142d0b4036038071940c0304401a040308062a984d02d200c83c104076a0f60651900c81c1400304240c101c04841069900100ca10300405040040481c0b90800e48210003030403001d80100d44621803071007010303030507038090020714890300f000ea004503210b0350f04214046440361706074030010308004208800d00100b02e01143c419082a040551001591120b00c1c2c1212408100c0c00c0c003448091403d0a900300b09075010f8403150000380341000c0c2090607140c001c64030513204000c0d41e10b40d0000c0d10140d68507000034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558739343 1250 558738093 558738107
    0x30c050c100b030c04020a18210b0a18030c03030e031303170906071b050f0a1413150602070e092d031207110a030f05070215070305090a080a1101 64
    0x110140a99402d00b1302c1070041016a0041c1040c00302040310b103005219501d500404000050502500ba414030440701c19400c00c0030480100080c0c203d013400700001e01884803903008070454140709c5441500302100d41c10002c050800c2094106e00282c00d01d5807041c425000001982d03003103440c05043ea00c0346440c40d981c0f0821400024032281e600344051009600c90303601c06024004a9009000f60240348400030f0044542502a400041c0f1420303610320049001d840d1f02c00d8400580300d821a5400011541d10001390107107031511a010b001d0b500317001d0150050b22414840408880482d003c803070040703803151030b0404945000c0303030844001e50045449118020950303210100e840c42d401c9074800001d00c0400303181c2c00c5070300200c115100c11010700c0c1170002035948031900303103200301d030500142c201807840707a40081503041c2d4142160308002c070203d10b01c01950340728207228084918000001d6500c0c54149000740c09500500302003846595541000100c011002c00d0f10440103510101941030141c200380190740813 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558740593 1250 558739343 558739361
    0x90c140a0507020d02060d0605030609010c1e031524110c090601120207050a0c0608040c05040e070f170d0c050a0308040303060b03040f0605061903170f0307030507030c050c10 77
    0x440c0700c004800150306c5200c02000e09116031680440e070f090411081c94074288001d0518109a858402400f030556480b56070340300c2c1c2100d460143d0400c4c00710281e0880c00f0b0301c1203003403031624080d03c0d24000480400410729801d1899944072a43c084558281050b42c400714400c085143d0b9401058031100d0700e20300007a41c5544054141003801c5400115405041280c02c50701044802e45c4c0800c090105006050403050700800151402c10521f1030b00707a880c0d0794125074074030a0720301403522622640d05030f9000340301d004054122600325414941e50341c108200311450300032108030346001c0d0f61803c0c00c1c418860540907071956082801407003e45496581241d001c103009005034101503581c0340109840b8941c000560145001d528000b8818030395041c80001c40d00050000351140348000c0d18200c1c0c1415184510049940202c00030b102c01c10081265055803056500c0760116400c000701700020160075500050040c41c940d60100300b904664103003503d83d0701c2080740b0702d007440d0301c49900c1d0a0fa50200790030103804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558741843 1250 558740593 558740599
    0x9030311070602131a1206013e07030f0809030a0609080304021503090c0103020d0908130f09090305030133020a1104060f06080a090516090c140a050702 67
    0x30341605030316500354a81200000310303035140c1c001401c40c40b2280c442015078041e00441659114841c01200300c20024810585103441c4507001030005030071607004500c140c030091010203041e043c5000d2100c80005904103026400d04007001c180f0b02c2c00c29458001210001c1d203a010708007030707409040364503030104603003100b000d55a00d4800c00000000003221340c050443c015200d020300948a003001d104102c840c04c200a01025110b00500402004410010f00e009100b00e003070800603518030701d8080080c09091a9100500340d2000043e4040c003403140f5040d014222074112414403100c54981d500101600d802c5540600082c0007803005200c0c0b041c2100a462040013820601c07103002d0088540300300d02002c994510350150304125045028001010707040381007140e0407601040110304080a80c1c4e14a0800c1c0140020048fc5070700290070403070141d203c14012900a000c485245081c030702560000d041500920305c54600f060b5101000d00e001c0d401010b1204148084903041040d04079007101c00da04081005d0368 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558743093 1250 558741843 558741851
    0x15040b07030c0507030c1d2413020409020c0c1003020c0d0f0c020307030606060e010314161403101805131b09060f03050f030711090a11030702010b0a080705030a0204090303 76
    0x195000d2000002440c440d5a260101d0044806034028014003c0c400da5141e03048c2e00c4100c1100d1602050b40301100741c22203144e103890070782041c800024080c0c3c1d00f098807440e10010350f10306907480004010395100d8041700d1400d210044450304500742d0103200b043c1200c41c2c0c809003803104030303a0181500c06c2c0194810302c0d28011020450300002d241c2111540192a07480d5190818004079910842e02c15801b8803e0078180203900070402181001c0000804021903681d5451034903081e244039100303a80d035020321014080e44a0600188403041e83c2c2c0f01d40b05614079003141d50005400c480c03141c000d0910a40d06040d06a1003031038a42c554501a168661114014404d11200401e00d1180c5214400240070041e50300c2094a040d0f240482c030313201c0195002040c6034001d00803640081d1307070303104102c86004090314030309002d48030200c0610180203240c80c10010b1040c04000c1220b07644d0b0551004000034001c030b40440020342c1d10101c0c9901c6085901032941c042d04094441c0c00942800d4003d0f0044620900d0001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558744343 1250 558743093 558743099
    0xa0506060a03080f09061c05040b100e1f05031204260309121204030b04050c030f03040b0f0904020a03091703361c181202010e030f120915040b07030c0507 68
    0x7485240b41c4260250240b95148c1c24407061005090450750b00030414420048090b00b13000009502180040c1482800015400161440c5a4040e01c0000412015080710040b100c0e08a00c0c1c4030a400c24081c00540380004449140340103510b0900807003011041c0040d500d0105c81c14280702001c0c92400860f05184034260300c00e04800d80000040000b14069080341c40d040c2040d01d4410704003203d030600a0703c00d038040321840e40c41c00008000c41c1c00f10f402080210b81e4850709a8200044d07401803040c0d0690003840800e5107080560140c0150040764032821507900c15031400d00ca010b0729404103445184080fa40c2600c6146102844000c07441c0056015400c0d0703140881c018503107413401045003412564000820f41e0b03d1a0300c1e80003040101003c051240b40e0350104e00b02076a01501e040c100c00c01a0400114403030090843d242440b200c5944440181501c1581001000c190360507401050001d015160301f00780d85604140f401e080d0b40a480c04165400e18004040d01d0481e0080c5102ca03042c1c48034040c3e040c3c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558745593 1250 558744343 558744367
    0x306050a09150e06210f01060303081503070b0d0213050a0602280b0403080c0d0c03200403020a05060705031c0c0f1d04020a0908030c0a0506060a03080f0906 69
    0x804020034621001050780500903842d405007400d10b5024007550399452092005650b11602c06440e0703030800d25220201d506128107960b1a008a0707540c200661f51900d440402450b920010540c4598070440c41c0070300e1010741c4024581d0300c0e03401c1d21581d030300e0503020300401889036025002401e6402003584900c1401d07071907a0000b1204000f40e4442c03005680108200d000850328506c002c3c2021840552a41e02e210701a01c880c03a140000910007001c11800d01d00041d0000c80c20301c15101c990851400c02c0080305286c410141c0209100a02030b0302d03000c0755060740e48a4983c00002c1f18240d90b8040d2111550074a00002e011442e0810101210980000d11004154441035200500342992403180410106900b26001d022006c001042d10f0820844400310705001c820940e1001c0c1e248000d8800590341c1c0420309003201e03203a1141c0c00004050200140450341e10000041d4001c10354041ca080d9109a192401040300707100c08c07480002c3c101c200901c81c8099520b02a00505101c0300c1c054850340c035200c1c804200c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558746843 1250 558745593 558745609
    0x13060c0207170c012a061b0906110c2e09030b10031a07090b0d061805010503192303090a09140a09020f0604060c050601081b0d110603010308220b0904020307030605 72
    0x1094520030601f0040b40c04e900c11101030042040d0300300481e48981c000045030303c1c0c01c03c82490500880095450844c900342500707401921041801d40c0c10407a0300020030080100c0128801525810a0540468201804880e006003103a6000c1c1250b0071214481002806400c4010134860510401c2c0c40000f0710404031070010b00b1040304084d80001c155007880d203d400142820306840e60143c2ca0003005100d95100021060211201407420340c01c4d544907440c0500421000c4001e4007203481ca00c8590807800c140c00409044c106204075406402e5075280c00d5981c04407010800711034200d41e40003001c40e05100300d036070000390f400303001810400400c003400d404240c0d294041d507c8000028007444021040c0031041c00300701e0241220502400c80c21486400250196601c0c0c051284900c503040c0c1d204040000d0346868209001d400742c48030b5180d41e0341e810450003075007080c030007110100c89880081d000b50941030038060540c0e21008a0038207003070741402400025040200200b003499541c00c80803c0d5030755441e00f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558748093 1250 558746843 558746861
    0x9030b06060412051507030c14160c290c06060607030311031617010503030a21050112050f0607051c0e1b01020c012613060c0207170c012a06 62
    0x100170301900d212008102103154004103801c00b01441c0191240c00039502a540c0350300c160b032840046803078034040d0040041421500000900c00d0075a20301c00074030407991050340b07c2c240000700414910904181500b50b07080c40362407020031094100100041d41c0c0c1ca0b00c60003400d90540070340750018214080300c284c0c4501d40d1040d503010f4103081e114001320720742030340c0070207481070a008030700310f4126551500020984d203000300c0508d80140003402c0e500d107581d180350384200b203c1403420100901c801c0d41d549503000321083d10b41a041c1e40600980140b04080000090030318040e0a09583d59032505010601d44c1403040311a8280d807d401b41c507003a14503040034041006000803114212000845500d0400180c50b2048800065041c003040303800019055901408010008400e03050424180d5201080c1c1d02420100c254000c10789817500a8100c1120342c0000d0110599020140803103452210240940c1d843c46901041c500241d9680540d000860fa00b01003101892554402c100c50421240d40d02015504e000b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558749343 1250 558748093 558748103
    0x703020a120e1507240f0906020733110702040c090603050a06050d060207050c03030f0921030d15181a090105060706020304081b03032509030b06060412 67
    0x54104070326482c0c804406542d03103c44424141c5410200c1d56030030305c4c1144c62581d4a440e90003460105042d0310141d048400d1440b4100000c0001c0000c6140010003900083c6041e40c000084109610506081020302c8521410412035800e924103071909280c0034007482c001598603a1300a00420005888a0140141c10640ea0300e88120450605c1001001c84000a00000c1c01078101340b82000b040c0ca030805c40300c2d8a01e40182c0c015a85140a0420301e107880c1a03a030b825509032000140400b00c4c4456400070b040c00040460352200381800080c4503079016035000c01070340d005070000c0020b000da8009551040e0071030307034a08a8407800940d646a039840e0074008180d10180441d01d030a864851070b01e0395a100d9001c01802c03101e80725194184030120b5a94003540400038000303507000000c1000d002600e0292400a45c007080f100c400c09010039082e580382d400564007a8400701003d84502c09201e00d40207025036503505551107840c1640303541c4800c191000d0107890f1035000041084040b504100c0070421b0500b84c2d0140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558750593 1250 558749343 558749357
    0x5130b1c0203010b18030c101407170a030f0603120c020f0909030d0b0334080a0f05010e060609131104110901080106020c010f030c030e07030302010506030d080f010504020703020a12 80
    0x90144d1010580c403214035109400122a09030b1f10754071541103010003080c51401880c00f0b810480340ba807140c0b24500001d400800700380e040f90802c107040380041c030984850b40d07014061b103131105407154161882400024421010340000d0601c19110b0081d840ca9140010103140e0511801c01c0070030120101550310010301d820004959420300c2c001d005d1481e0640f001e8000742440f102c824102c10740601d15807070b034040c00e003682410902501040c52803c3c01600008003604c0d04038420b40350480c5a42d1000604454035400d1405940011401144182c410341c0041d20440d11923407083c1d880c000031104040111001071b0302a0201c0019162840741e44441007400030202d030f4801c203000c005008841d059000108560000f11589000c0e40d0210a01070440000d007008511003814842c15005000d5112030072311640b2070004c2c0041419070542043e405014142c040e02d2a44640c00740480c0c2d0058104c5601500092501c010892410700e81c0c0207080e924000d2043d0b075040c1d101c0740e803801e54000038070105600144035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558751843 1250 558750593 558750607
    0xb100905041a0a0510023a1106150a08030f03041b080d0e04060305150703061a091212030f0403021002030f060d02060408100204090b0105130b1c0203010b 68
    0x10070300c1514004201d20001403042d00a020005020034038602074a0b001c2c1e042941c0114a4034000c0040205120031040000c0101058455480c42211000e4012408140d03041e00c4164660040c0e035040b00b410b0078080940301c01d6079144080820301640702074807a08248800c0000a00030810b0000d00099046103003404c1e581c1c01e003820700241c81d56030092200f1011102c040c0400c9001000100d880a05549041c800ba02d0007100000a0041c01e29a00143c03050003024203602d468903403c00c0d818803405594400300b01c020740700e01406c01c0350028101d4200d12900100103506a9160060900c6444418201228003580b080c1c0c200c1c05003500181c032040700e0a40084c0a0004041d010b011925100200446c114298030b812801500c138003501030300d51400f03a03c54402c15429501c500c01290b0240c02d0f80300072140c0255003010101d00a43c410311480007035070300d031000782c2020758440c508848440000760040568a410041e03c602d1903485a15803580b401c600c201c0b1031841e0790650026500030f1181444854407140b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558753093 1250 558751843 558751849
    0x1215031f0e010f0b01120b180106050304021305130201030f02090d030221210a0b060307110615012003070f113c060702120f150705040e0a0b100905 65
    0x303043c8402042ca04241800600f6680030b42d4507681944c0b189000703e41c83c1d003d0b00106201c00083c40580e04d6201c0480004140e035a0410001c5004910a4a281c0c030450344060704c0c441103c005a80b402e03401503607000307540090342c86a0040c00b1800f0070540018508a241e800050500012403400c0f405604518030510590b15030030b00082000b150040712910f17010b0002901180044207070400180c1541a030003042c3c0132103065100c08450301d0040c3c80d01d544c80c02c001001900d0702e04521a070071440e03c100c0d00050282c8207250307100d41004c0010303110814001e01c03a2243c000006050180c1e00c007144828804400801e201081904440c0c1c050001c070102c403104141440556010455501c062602840b14030400c0554254a8150341e000c08043d49c400e0051403000031690f1003172441c040c3d4030200910000d00d0140300440ca80c65040d46000c01c54040c0200605409541d440499043e00410014082003083c0c0d507403500c0040d40000c02c0b040c0055030700d11102c0056180c0d01d0000d81040096400d40c0306000700e003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558754343 1250 558753093 558753101
    0x9091a090601050a0906260c10080610030207020603040201030b190906091407090603020903070f170d0f1718060406150f0f09090201050c06070302090310021215031f0e01 75
    0x4101c0030014004541010b0220354400040e4041c00c503d8047d60200101c154402d010420340b09000408101d2000115100100b00302026105144184071924464607031500901c21079900703545c05407075a03017140e8540c0c0056008080351010540c102e540700140706a84250a42c007500a005400700c00220b080c18440031008842c0c12002415061024205004545030407212403800c44409240150b964400c03500400e003002003d0b409807410f1007000340d000c01d10a0f13021106192001004046900d5403207003000440d40c11041c0341c10305010407000200300500001043c141580105040c42500030b01814055051a09004403401e842d01d0b50f46010540c5448404500100144010700004040b80d0402919140900031071043c80c07a643e40d078551810469004209490851680c80180c40c002c0c548404054065403059140c2d910901540410000b040050b1003a982d64120300000c000c02d60f90340f00c0010246c107200e07d40465051280300d540c8200700002a4104102e05050000420900010038800d0700350f07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558755593 1250 558754343 558754349
    0x80412050a121d15040b07050f16062a15050709050f01120b04060306062c1909050a120e0a0b040e060108070e0603040b06090f010b0409091a090601050a 67
    0x403d10440b50a0280c142c0825066400312140050803148154165481c82581d10066a24101190901c00d2120102e04030b001c580c0d0041c04c0e600044e821070400c3c2980c491900034607010800d120600500300116040c0060401d00d402ca112591411588450715001c1d030314440481119107079020411405d620039a003200400080d18404041c903000c20000e09403013001300030301101d2070b81c0d846004041c0d81c5607048400190742044c2c0800c2050340702d4850100102100006080d0612000c0855024441c0401c80320301c51042e00b5401c46010b00700040c03a4010303040c07281d020b844620558124601050b01d000c103062811445407160041040290103019040b083c580c02000a0310041c402040601410603e860b0320000928144400e0340d1140c5050b522042b010040c550000c0780401000b00f0094200c0b40300b40038030300841c0e141c0103582d0f804580c03078900e060902480700601018042000210307042d0308403004640c8034100e52030395205080500d50042008440c00b00140e4052001040181814042c000107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558756843 1250 558755593 558755597
    0xf0b040c02030d240312080906060307060e030309180601020d0806060a0804030512010810060503192301020c03070b0f10060f0309080a020604120f08040807080412050a12 75
    0x900002104065124042c855003401d98644503010380d400401c1c01a0f030807a0300e90103000c130503e405480307007089810540103910120228441c0300202c3d840020000785c0e80d102d0000100103003561800d000049440400742e090f000d0305031005020400385c55695440c0091804c89492503084240f400b02d000900d04417214030044203000806080c00042d44800e0101c8240c4100da060030225510f640c60704076101d01c249a0941c005542d45000412900c601040040c951034034800180000d030b44030380405890764040d000c409410740c0c0c844580d0b40000c0c0c40c1400c0e10b0041c09000c201544964800c24400c1c26a0b20258030710340581c1000a0f0042001503214440360080e404c00380141e100c2c580081c041d161003089000b04014049803550010f0030b42d209401001038142d0010b420341d120040140080e51fa0700c000d4074222203110042c0c0080780c81601c90040041c1c541d0440c5c0d14100075031a01d4490383c0d4a41d100e408261101c500400c0040359044110301021f039140c0c0719030000c1c440740030325040c242a45d000540c02d03201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558758093 1250 558756843 558756851
    0x50106050a0503011a1c0e150124020f07031401050a0e030a1b02040e1c02030f0a0e0f030d02070f08060105010818070302191a12131506090f0b04 64
    0x40050340482620305440c0e40502046681703145140f4030340d482c0914039044800780750b40a5292002e0119402003a0544e54003011214526141c041410030f01109018100f00c518031500400c0c0641d01c01410224600800c0c010b4030480c1c1900c0e044075003040115041a28000c80c00348010411034024414281c0c02844030344104410142c18071840c1d1240f04204141003000500b103040b1240c8602690129280da40c020000c002c0c20b8200c9114a0b1504040056100700d00040000c1c00511400882103c5000c0c0313008c40414a040714850302501c64203480402560020300c2c040001103162810403040d6020b0502e500201803c520300800d4010900392900316600640003900100501d0760456181a001038a031030a0301000c0d01c10001d801e28102c540d0f030020b54416150200355222902c085000c4040c2c400c50000e12003d400046400341c818400e511a80340c680c00d4000000380031445001c074443c9a940300b0951605c2031031041610801b80c69142d00014415542ca200c655a908490300c030b6640c18070b80645043c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558759343 1250 558758093 558758107
    0x120d051b0303070e01051c15030308070e03070501031116080910020106030807060209060c010f020a021504050703080c03070804090f06090527100906020d14090d0f1106040f02010305010605 83
    0x1807810300507088942c1840404140387c1002050581d01c1034104940050030002c0440c2c101da034030f44844a603c0254040b5205002282000b4440c10101040d60301c00307001080860701d44801140200701942c5000c41220081c0582c03806004c03e900c840c460240112541c940b1288001e0821441a041c08240029a03140400400000c1c10041c04e0700c42c2e0540201c401070710341d0b03c5000032426134896900e00302c2c125440d0085817204480aa40540000c0e01c0d150b0894a820345400d07189500d00b101610054001d6105800400010360345c1c000070410705064209403424440c440e03407000c240b0381298022900c2d050726214983c400c103456129040040204107410702c1941807040c0c180081e880b43d03440312201c12241450700046844208280d404e60511071000304410825400d007600290805040108100d08000110458041c0041e0141c011484500940141c060b41202524903014a5100038144001e501d407004c0c03000c03810300c5824030803401003840280c010754502c0010100c5805030018002c0c060140001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558760593 1250 558759343 558759347
    0x5070506120f0a06090f090605010f1220060a110606090f070e1c08090a0503010209131e05070f02010c020303101206090b0c0403060b030d08070e120d051b030307 71
    0x3250014825202080c40e901c0c0c0f070310300ca0b01130015034101664207800e0118801d51800c0320361005d00c1d40b5004020070400c603621510060180c62552003003052620325200b0403004982008008464024005581c000c61001c46021540c190000c1c2000400301e00d0801d007103e001c40003802090750142040707807004a01d21700040000001000682801c2c00c1142e0305808a107151074051605d444204640007031802e051040c034100e5100d62000c4e034180d01030719640400082a00b014020703244030110003024103250b40c942115080003000164052007103a858445920420304491107414003c0e507150f075802145154100c0d01030300352085060050215401003081102c48810741c1c54482c180e54416220085200107802c00b58007803c101103010304412418801d01c014100e00704020310450344500018400f1000b42c00400da101c940220503040402c080364000b5004900c0b4100700101800000c2c20540070f02e100c2c0c10894a40350118241c0004100c00245050803c0401e811101010040500462941c5888000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558761843 1250 558760593 558760627
    0x819020901120221010b0109091406091003020d11100e100f0504030804060203070c082a0d0b040501021305120316031106190c020a03080615070f06050405070506 71
    0x5070442c001890814004554640700d042c01824440904541c0e42c82880180300e0080103014038150100f070240100050301d00720740c01841d4640c4005900b40304e46a48410610101041c001c240e01d490703100000011005949107032586c030f42c0c0790244050701d607003407000f0b0103201e600c505d070400d030105100d0701011502d560358500f0851400c01c0d62914100411680603802030b21540030b25040200040d201007030104130140e0000261500300e009103c03402c0c0c40c0d60365020082d22400ca030b03040924590201c10100304030301c0042d0320b51501507001514045040c0500c0c0ca9008240ca001d0790202d035940d40001d0341e1411529524402c4010300011980c410341f503400c900700d4a80d00d11403201021451340050241c0310605014000003c01c01036000252003a41c5449002d2004602c0f0150b09500140d1800208812084c03001130840352065264a030a0308680700c1808200b004410b01e4440701900c80200800e0380024104128070741e5151044c18089003d04240c42e0950030035001d50020750140c82306201c2000b80e146240b41c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558763093 1250 558761843 558761849
    0x803040c0e190b0301020c01061403160e1b070f050106170309010207050910050d0b040b010911031503120a030501170604020d080c071a0d0c030209060d05150d05070819020901 77
    0x140004030f040042c0d0201c1e000e8002c299211406501e02400024945200c5402c4801ca001c00c605442d2200354080b2606940420340c001c13030245207403020004886440765100c690310401a1004141420302c07030b0380c1c0d4207451840c0c60400c6600d03945500c010404049c0174040c02c20302d50b80410166040002d5080001d641d0340a61003000c0c41074a401001c00c013041d040c0203c00000d0071300038100740c80344080e605140d0304400003690100c40303900410000041c40100c92084035050009160018615240d00f8601008156a504e499a0500841610b6202500c4000c020021040f0036100825550314141b044c41c1640340c1c2a01402c608c0d00181c0c100401070780ca8200d401009940070304001e840d10745d22030320305280c9850354001d401e41940d100d00101c0c601301414040d02d402d4500d0031051142c043c3c106c0c0c0c101c0c1030740500c002a0b60041c1060000114200240e00210341c4110b4110310301d01c040a0003800a0303d4084200001e407442d801039030092103c00403c2c440c1c03003032040e107136441240c2c206580d6002c40c2010344144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558764343 1250 558763093 558763141
    0xd020a23070f150207030f020d030501030c05010f03150f0807080f030a18031a0603010c020f0c01110c0301050106200d2001140702011506020609070905060102190803040c0e 76
    0xb81012040100d680111540d14121000c11500c1d80018030f000f41400c9258000c02025108540d14000c082b440ba002e054140e13940089004038007031810006450003942d0700311100038162200204501c2036220b91100c8003c0120204041544d440c01004600740341403500007060380e070004c041d0001440000000c6a140c22840e28003c00001c0030101c0306000e807022900001c18103000400c03d400f21045d00b103105030144004070f00800a0941c03103102641d0311a1241462201071f0002c04a150306d660090f0041c030841748a4001b55907032103403080006030031234100340c1145000c2044039030125410118001a49a21501007000303140b030800804020b00300c1d450722180c02e000c8c003141080003800c0c03903420f422107903041040000d01202400d100c40068080e220200d0010001c0048500000d421480096040d01940c03c0034050820582012242e00c05404010003c605500c1601c040114103002c1c40109406980160802a120b00f42440c00c400701c2c3c04c00f035003c036180b00e145500340302d20030740492940e0000d00c0f649 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558765593 1250 558764343 558764363
    0xf0301060f09080601080d1b030903140109140a0b01080303070e0f04090b0709080f03070201080a0504060b030a0c14040219270e0a050a050c030a0c090b0d020a2307 72
    0x7100100d5201d0010340181c3d24034001c5500004000348002100441d10540303458900310248107400390940c2d10b200d94005000185600c4040020803404021070380d803c4246c3d800030444c4a480d86a2580754040c00c0540d0760150711100008081c080c0390610940906194405140b81d03003064200105481d07031002001d03115005000c560901c1c0c0e900d40d072240904552010b0001328510300001d01a0030148184106800c074041c103040d5012500011003140c2c0303010b60585412040351604400300c40100b00c010004c03160140e980350f4584c0c56a07005c0082000b190f2003000c0da0300010342010b441c2d0a11200040314103020702d0041c411a1481c0202401d82d14128169291220210b411915450801044040c0640401080c5031010030220b032017004141c0314114080046c80703a62180702c180c3c0c0859200300c170b02418100c814400b0072030590304c41d04414181407061600709142c03a120514004281d0002000c17010b1a94002401041150040c600b460306200c000c02c42403040540007401c120912a60500801c90b8502e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558766843 1250 558765593 558765617
    0x908040e06190314011b11100c093803180604031e02101503061a0108041502040504020a0503010e070f050d0b280e1b0405040f021620060f030106 64
    0x95201b00781000762000869103010a160000d0042c00007a90902200e00440e042a0f8607900b0b2406000007107881c82c0d03030300c8401c280b900034042c0d1924044820035400e20704038400c1c1c060342201c4140144007600c0c005d2074950f59003403111001090058401e4002507a0300440100004280c0029140724025041203460036001d58860080b800c20b0340f44e42d140c201041ca402401c45005001420000549201d858200100c00d54500c0240b0100c0780c5106160020b0611400a80041c881801d0314402e0034102c42c002d0b09044d202d40c006000da800031140440051720100042019180505009400540354200405000c41d80341000f8854400c10a0952103203803100105403480d264251040c525400d0304042d005801103241550000c0792042c46074404088a000c003103a2240f4172106211300408030705850515051906040c400984a440c3c906210030ba4240022040d00c1e000b012a03102441c0b05107100304074001906240c4a841810101c030074010501808000d00aa000401700c3e030664041c2e080c0442041c81c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558768093 1250 558766843 558766883
    0xf02030903010c0810081204060f050f0307030911040207050a0201180b03040f0302070501080c040306050411060310060f021b120a050d0302030a0f0903020a0b06040f0908040e061903 80
    0x1280e101255015881d0000c07a401c0c5a03804030002e4060707004000211141c0ea030f01c1002541d034510300030741c00ca0801e200b0002081068051544601e0446003401c050342001002c0d07840300c01c19042100c8800c0882d4445d02e5074010014841c3c00303005085012901113003800081e40300c40b50f0707407111444003e0505c091071021014107101e140d6840000c200106503140d40e8602860a40000300840c2022400b61003075007400b040035800791f00514422459580b2850070540341d529200c01400001c2c000740c510700708880041f030303058854100851207024081c0c00d0344241c0c1c0c5050720081000c40d0501c035100c21074000031000161001e90000c442a4850225080303507a046039800d4440c00c1c907a600c01c004100e4030808144c3c950385901a005075125251a200422400d08103032540c40550b01003020090058000c1c0511034000f90142c0310151300408043c2c000203d010100f4500c100b1166086000d440c05003022904020010142e0a142d034004002d4403c2000038041c0348081500c04240d000003083d0000c0020a242040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558769343 1250 558768093 558768097
    0x40b060a0504090f0507050103051306020d020d0c0e0306010614090d02040b0301020c28030c06020a031d0c031b060a11032106100809060a09050703060501080309121c0f0203 76
    0x44002c10820001280f440c01d042c1a90600d00126514014844002031540c040e01ca110711800c4004010003024405540704402075022a1054a410343e0078800e0f0351001c00244a51058140b0a40740c000c0307043c00700410180341c00c1050b804403007084100d8048001540c03401c800ea881e4000140d5920041c400c5520002d0050710030200d040c0e070150301c04030f816040c8020004031290008100407505501c0c04142c0940482040361040140104800c41611400204d03280d00400456110b80750000e11f001041506a0400d5107418400000d98460410384160380f030b00340440d011003a4501c183c04130341802000801e10901032180502c05010019039026180d00041c07040302e0004c0d0003800e032010003880703a00d00c40d400074801740d031158000c90414032031030343e9907000d50030b007034094030b031100041c00b16a8841c1c0d00c07400642001d0404403800d00627000c0000000d4014024980a440c400700510f459141400034041407141c01d203038600e2241d1000f508103280061252030040c1484051800701c030019403004082c1d01c2c40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558770593 1250 558769343 558769349
    0x250b0a0905060f09190806070518030703050106090b040203060a150212070c090507110a02041a0310060503060c0f04140604030b04120210141503070e15010215010608040b060a 77
    0x38000810051101c0f0340760003445000402c9603031848694507154403180d8003072a8010020070b944908041080c1c0c2d8000d101038220030b16180c0d80e181c480c03902c0b44003080c28075038070b640210342903915040c0134001c42030b03e4000c1d00060f58003030710214203515104000039580c80c1a48035000e400c00c5d190500022451091140e01c685584000c03045969034128640110701d20501c1c1300b11440079190402044003948030311412200605807e005185000994013007000034503414908558601200a0314602520240210038007a55004400982c0c1d0b450102030509000006002804910342003010030804248101590243c540d0101c00c0070380c0e45600e10114100c3c2c40756400150000b07007210100010002c1410b00f003000d4030700c0d035401d88100c0f10f1040400010341c0d000d400180c24902d036071400038240207500301c00344070700caa401001c903022150380300760040c00d42006a410382107104401c9010002035030100810021070788048550b210640c07410340c000f030075041c000d40300425038032600020520755540c18683c1806 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558771843 1250 558770593 558770599
    0x905060f0919080a0311040f092027030d020a05190c0e07020307020618040c0509100e041d0d0905010f050f092803031706010c0b0406150e09250b0a0905 67
    0x14598807655203c1c07400c226441b427824030710b042542d07029804d038641002000400303891040354200411000000a42030024150f02c1c1e411444206884a50b5420071461001c82c082ea009800c40910314100346003846e034960007509090b0203d114140002c0c00702541c0e882210340a41140402d0785070b40300101c1c150300c5501c0019610501c04580c104004840c07100c034030400c1740300f114100408803c025081e18a40592a103150b4807204d528034445e075482c00744030464800c44c0d00620000302918111140460220407050441e00744c2d0040c0c03400701426070440c85c1100908000d081c101c4004520000084c0103210350981c80803070b014045110091a01c0704074044140a10030b01c103076099000d2880c2c0807940302034144001c1c0c2c00202d028403078240718017003091454000d40c81a580d810801c01c3c0c82d285e0440405018108443e01540c82c4071244001c10035080d58000740106d0004030105050880500745007c015148040180f0400d03070703a888500000203110030440340502d4040f5100c1c81c480c4c10035900c01282e41d022030f030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558773093 1250 558771843 558771847
    0xb0c0a051c0905160e070e01090920040f0f06050702060702010f0516050d090605090d0206071a2409070215060406091d070b0a0806090a0b040905060f0919080a0311 72
    0x134002c2d0400c0c220b107041c1e958840141400707a455050842e00b408601240c640890703d80c003010f00c41800190440d0034100440000d400041440401c1003000390b001e5408000d488011450031701c0316480901c0b0030402405103103003650070100b55400185c118411588002d0610510510f0f8546860094060b94800c8104111016440715981851900e8000b03c80e8854005120b144001c29910b0069058450300c1c54040e1008e00780301c02550911059501001d0152007040600da40c85507158042d042d0f40c0c0c41190b03810003e0170204804100c0706a0942c002c1700262082c0042070410801c80e600280c64102c212404d501350280d61100c00c0880d006242c44c1e003000540c03904003d24810741140c038141000030614000c0440d138a0698a180c0c104850160101d40c40c0003e2085000c00d10900e4440002d03a08440210b400003940d0302d040001804841c03000c2c00403101074006008201000e030010141c00d5000b1410006840078000701c040d4031507100b660250050080c1c402151040c405442a403040c0380720703e80c825102c1e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558774343 1250 558773093 558773113
    0x20d0b040c030302011d03040b0f09060a03060501020c0603090c01120b06040306140a060e0a021e1206090a0e0c1207090c05031f0e190906180b0c0a051c0905 69
    0x1101e128150700098000d0341c201586290550011000305101c8094100554140307030901c0700e030603119070142e004040e6070202440803074055550076000307000340d00003600c000072894a890006418040c039012424440c40041c01000089071000c5000c044c4680246403650310000314a405000400c02c0006058100a010a022007007041c280d00c600c984c01502c0808100c1640d95900700c00aa41c000d0041081404448010648441b240d4000d410301e001644003501c0481c1c44907240d607116800c4507502c0c03041c00c190301c018003004c0d040025407241c00400aa00901c0000401111965100800d4644031300031028400103c10062090000802401c1c1d408000e101000748500000c0c0150010344030001503119400c01c1d1720701003001001c1a007c03911080107518050380c5200d201c1400000c0c0464203441c03140c07949082000140c1c0e500c2500c0400401c80d41c034410342c1000f410324810000000304084098901004198041508607080e42c000c0e104980745000e405080325900c10182410f040003d142e480784400c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558775593 1250 558774343 558774353
    0xb031b01050705070b0c1612050a0b0414013e04140a0305030f27091303020a0506070801061211070807020607050304080c040b0f01120c05040b070c0311220504020d0b04 74
    0x700c1c84150300000d800f4500c8e807a82c2d40801e91000c4490300410030341c40140d201d000034085d026595482801003003505c00304d03a00300400501b076507a00355280c6101c102c064040100c0400d00441c0c00c22904c12005806c880307001403c1e440780d952103640600e03450420b041616200968914000c00c01550784082500e4480e20100900381054010781c80c5002144900807000b540c0001d012007154121000a1170381c0d565403140085403000e403180110a030214004c4100d003070007180c400c00c80d10b030050001d60781d01d20966140000c0101b0300c1c208004d40d150b22909218041400d50b08040c2078a400e103800c00101e50fa1610244006600703441a0303a0020110700000c1400100707002c1c04141d4a14107042501d0520000d00c0342c50800a00803503c14009010079006201c0040c1280c1640c801c140300707151350901615194a400102d90140c101c0c20781152040828801481003140b80400e6000c00e41d416258042e00c000c00742211035800c000144203015680e40e540008040d9a00c0c1800c60741c100d5005550500c0c942040e00b05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558776843 1250 558775593 558775603
    0x40213080c0a05010c050d200a0b06030c01020106031106030705071a0103020a0f05031f0f11030a061d0103031101060e04030509090705031905060d0b01060c060b031b01050705070b0c 80
    0x4014480c411403280000c041d4000d0385d140c24420ba1000c0036100d100f80f00e0718140d03483e691030550b03043c03500303171070101011110f40811055000a010308002030346498a982090310307000b5110314035411a410080100005100a89501d441c000308a501940700d588401c001c03551809a60b101910400c00c801d240c0482c025550304a5050368026500445442c1d196494881c0100306c80c0b01d100c0e0075622014100061941ca0300e00c003110103059180203d59140602008000c2d83c09800c04681c400310700005104203420248101001040c0604004407001290300c804007141a0510001d401d000703041c0001c8004103c21341c090000350208500e41c400e00d007000d08005001c0d030400385001e40101c0034200440c0c1d03098040d1003605e101c0c2c0d00b01540149200f04800451016010180a07642c00c07a0066010720005480c2c0070403140030301407d81e103000c02825a414890180d8142e141c1d5640070307402c4020242608000480e035464515004e081c1565200784078a415886e140301540007000e915008107104086240200b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558778093 1250 558776843 558776863
    0x12032a060f22080409020714012d0606090303140f03010e0402030124060302070807050f1515180405100608011e061202150d050c0a1d1e04021308 64
    0x15000d400104102c121080b840c40c5500140c044241804204125442c5400400089110325440101c1c1546041c1d000c1c2980c4540e0300300b052514030940700d002c10171401e145901d20403e0200013445100d18014002d803809003940406410400c0e40c0c201409014441c400300e0700064042d03110f481c0e40c0d40c1e59007010b107510b0205032002c078803950070020500301c60032201035100c26202c1032040782c207016490719009030000c3d400f40d54210f401101c24403111001c50402e02118500c0d900420142c001804647c0c00c1107580301000b004180188074240d000310141c0c0302c480c190220700f0020301800500c0e45940c10000d00d008540d00003900043d0501c44017051a040640100c40743c020f00990060703104030310207016002e4492a000b0750314401242500103001d03141c04c145500c4144883c110007031a0110030b0300c504007556011180300d10134a030000307007440103030354040b03040c10203011607042c4400684c0741080028001c941c00010040325004140010005944542c121100b1294000b00001c12981c0c96240c241c64a102c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558779343 1250 558778093 558778111
    0x110c06041b0501210203090f061e1b03070305040c0314070f0801060b0f07080903030f040e0c03060f01030b04060b070b01080705011103120705161104050612032a060f 73
    0xc41c001280e500580121141d001281c030b1000440e5441c0c00b844009400003030030342c8414443e0034680b00030000c062109a00851410020040f082801300f116541d40e41e024200040160f0340303683c0d178021510040140c2ea00580c861401207074a40300c0e0304100d00762041641000e4421180c400b0501e00c01c1c040000c2107000c8a024600d61600b890b51100694202c44182c803600c3c1d6003440c10404500040e4801b001064107911030343e135150500781c0c2440403900e590041303210340c481b15000007020310400e203000c0c41d450792140714004820724500d0020007007500c1c102c2c22070b4003d041c50f0300d074003c0703d10503a1150490f00c0a460140c1d0b42507221410f509080440003002e1280a51600072004040350551240c2d101d4001400000011817400100040d16680d01d03c000b80312904109007030201c03026513400c07000c0c0520700034000c1d540800d01200c0a000c0004a44015002511450441c0e040c03100385031001c030503540c0700d0180c0b41c05140c1a0325400044004007403c05002c070b009004200800002d9042c848900b40503104907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558780593 1250 558779343 558779393
    0x170a0b0907050c0a0206030907030602040e0414011e0f0f0f09020f040504080306060a0219030c15050709051c020d0c060f0f02030f09030a02030d02010e12040506030a110c0604 77
    0xa02050340d483c4506403d011072034200300a29409402d05e603000b150072900040c00c0b101c010b0380d66180d00040340c000c0e401c4012170680c0e420503c01408410700811a5142c07205008000300c014000b0611205801d40318108030b241d03213544030521008102e9202d81030381803280780c080c01038503031800307520009061217a8220320441c01d00c80c40840500f09441068401e0340e000080c9451a2a24400c226060b08003018190440c85240002c0a00e00c18440440013070b1807080d161101e1902d018908041c10000f03540c1e0403556640341104000006a01109c01402c403141070b520b40d4042000c5c03405203184d07424162006500908020600750030031041e51200300c1140c00c284d503450308044801e80202c640c4201202c00200691041c0461140d049000c001404147d42c0101100c4041300c1980c08603003031054a4180358050703591410088140c213030034044072004100c00c070520780c0b91505040c0041d401d4040600620041980e44882ca00c2c105100740c201c407032010400040b45c1c098980361400362038085140100c1c000032001d0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558781843 1250 558780593 558780601
    0x1090c05120921090901060305060604170a0c2405090105120c0702041506120b0109150c03021b031b030a020a0f05030c09161409040221090a0305030c0703170a0b09 72
    0x30410581d0b04011009181e01d0851f403074030740120040c00010380120703809101003000003001722442c0814031110b0040c202400c1c142c2141e0071300d118544540d61005090f900c01c180c0345c0c00c46030740440c580c1202e0101d505100c0e855140686c012986806860103100d0709846060522041c044008003404140340708072828010001d10502c82c0944045500c14200400c600d80d41c1c50403110309a4000d5482e000041c980072100079500e4804512003068610980003003183c2c00c2130341040c9a81030050810380c156000e80b0319440e0401c0c4011964400c40d020340c000409500c00d004040300c2d03030140584c1c100c20340c00404c00d8104903120110301001541600c2600c0c440d10a03c1c4000c5400c2c20b11101180c8140c0000300c0d8201074a101010030340d1055030310404c0d16440c440400512440b952a84064054104402c600082c00f5013481c45c49113842c00040d18412186d802403500c50300096000e41202d40c0001449034444c3c4504152606172045012005036840b0707401030f20200f009882c51544180c2400904032040d04250322 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558783093 1250 558781843 558781903
    0x2119060f060308040e04061401030813060f020309060d020d0e07090608071214010915140f010305030307112b0210090b0601110c060304050105070f02030c0601090c051209 75
    0xa6a40702c028030008090008204048a13a802c2070b900c64001c030b00c04900b07400350119001c0301220980003103900740c0c0082041c005200e101c2c80c80b00040e051508000010040c6243c000c2d60328003800440c54071404001600d0294121fa40d0141c40368a1094941071098440302c030219501c1d2400d40c0611008070b450700e5000522880001600022075480c1170700c0000002d03503500c50030103112595840f058070350b403600c180c1c0001800221010000c1d0a80c8000010162401180d0f0141400050105d40c91810f03000b006001240010048a4106c60703107041040c0b5100450030001e041c4071b481052456003078560405c4d43c0680554014081402e1299425966500e440ca10400112404600d0103080940e500d00041c403294020f40360441d5011144046071035201e44000051842d910407141181c4903519071081c0964160820072081d100c203902e001440c28020040005561541c0500ca64024507454014140140d400350040342d5a040401c1c40c2c03000c030362800f600590791311510b140085d401081c8002816100ea1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558784343 1250 558783093 558783101
    0xb120f0c070809030a0b0a05150102072102030a0f030305011401050a0905100c15060509091f0c17040c0807050f090f062d101704022119060f 62
    0x50801005050402039101c2c042c46412103c0e800d500342c81040300d2840070845000009116081d40711000c9018a05130141c419600d400c072990a05641c0240740a102c3c441c0b14800814454031000d0b00040c5a0185000185ca09000ca800180404107440e007c40107241c1d054101c02d041c3c42c05100c4030403000a160004517964418515401c2c00200510024060352070241e00c196400062450072600070310158503041d0240c003001c81c001c5541e0395609810445418010500d40c0d0080308840a84426454000721480407285407010b81c203142c2d581e07103609065900a000360783c881d4050441085680c5000d10b054003030071380c544c0a00d100e603200344a00042d030b42c500000c2011650304040d14811158450b40c04981c800071000d0009a030104d01030070310100040e102c05280b60382c1e641e0708a616204244d400c0c14054034043e00b0001e0401c0114a484c0c0a0703440d001c0c694516003203541a109402c50503004c00107200d0701c402c50940e460b031500510046030040303101144010029401f404040003e0244141c44c60101d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558785593 1250 558784343 558784351
    0x7020106061d1201020c0106140306070306121203110a0e0108090c060a1206051c0b010f270e030309280b062103030103080a110a02220906060b120f 65
    0xb145818003040501d080c100d1849860024060000d810410884103035400c1d1041030304056103020b00c40030862014a010061240c1103026410200007040c04c1a01d018000342188074041c08114000d000c1d280300610a41c030880b08040691952902c416642d10700500c00440f108109000844070750208403800700104040444640081100e46024506d82c005d072804040e54955508081d503c1c040018541c550380c0c001c1d420410302c503500b21410742d15403400085aa00c1a00321a50400503a44240800c0c55426404202c19080040ca010a1003010b038801000d0f2480f02c00c3c00980b40004003e1240e42c02001030a401d0b90364042c02c1c002c014007407100d401045808910070281c54610720b5404242582041c4ca402074401440012000003141000c02103031844d4820f03401211903080000d40500040d5111580c5920184207902410080c411600001c24032030090100118405044001e245955816030014400540c01203092002e01d80c2e42c007440100750001341100310503000310b01c001100142c00e000341901c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558786843 1250 558785593 558785627
    0x90b0a050d14090303151c03200a0c031713090510121a0405071203080732220306050403030509031201150507050102133015020906030405060702010606 67
    0x443e03407031610940d01a4000c6d802107400c140804540180d0045248000812501036107a034920640710820000340c4248820f05805203400242400740003030b070b903401e40e04100c903001000c000140e1070010400d14640300d5400c1156540345001c00000b01041a600840d10070744501c12103003042750760b03071001c0001043e1008004040d9000780c5c000c15900e02411408503085030148049a50b103d07155201284420801d07481035011655003401c0010b1641e00c500c00141c0300320ba4200c01d40c030144c031088100e001090302c09126803403500042815000d80c413012840e04d000d80d00e0344d015175400701d0b9030f801c0c0b040c02000c1c150740c2070300001d0400c000904041000012501a042d502c0c1508845038a0602c840078500f020101803000c00108014200110360240007a0042075040b0038004101c0d841e00040b0324118104402069169030950b00d680740100d1440301302181075800007100200321030074403d10002442054151680440c01000b80010711100140ca188140c4076038000304282519950141c4d4101c8a1900083c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558788093 1250 558786843 558786847
    0x2160f060905091b0705030910140711060c0d0c1a04080703140f070b0907150e0910080616260115032913050c040312090b0a050d140903 60
    0x4410300f8007800450f03101c6141091100112040814000c0e158002ca80035203c0c0d61012500c203980d460040106142201581800700d00401e819403098101e000e182006812400b0350842d042d402c5e12603400312241d00c10301c81c0681d046100b10780c030043d0005407502001e0720481c04690036503000303032142d520150050b0380007102c89090070040d6038100c0d01c8048910f01c800c800a000d1080e1020621044050000c0d544641d240c40c2c02c83c035206000b280740c110b059000045810013000000c01d042d421901c0304c1c902c0c50342514860010743d5241c02c3c2c4000e0610660040071036102710744c20000c8680c46001105443c520715650282c1412141aa0021960302a1860340380d10801e00010802d94400e020399001801c00e608020584045207034032132401001d1400103a840d0b44030310040030198940b04c000044105000071041040e030900103030148003801140001805001044942681705010708845c40060003032012003aa16240f10a0050040d084440380442081c1007161216810007078940182c0f00ba01a00002c44c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558789343 1250 558788093 558788099
    0x4050a05090c09150c0f0115060c02030c100e10020f0d12090b040b0105040b04051302060304080c06070c140a050d2105090303070806010816080703110a02160f0609 72
    0x14020300005100b542c104074402d91502e03401d585624080110a480ea299007581082c0c80c10000440940d903050b13407400020015502203058003005036640c81c501504448102c0c40424901488400515441400c031042c06541c40c0e0300c068015012402a074100c560500c680200341e80d1081040400420f503000300d02600c004610607d8000244070462102103099000703030321965060030307043d00d0a0743c89ca030b0b256005100c5400c084c000d0750024001910100301d0b610f006041400d4050380301d50028070039600000400c06000844007583d07100408582618090300380f40d08054000b0414040849248003102c10300c1419000100c1c1d00d25242d07800c20040c00c00740041c0c47e021507402020103601001c4031488c6c0c0f403541c558403d501c1110320400c4001c0041d60340741405007000e0b185a20041c002030420a07000100113110710496401500703003282d41004400e54a600030700750003511308040e141001d64408580829015030004410190203013058031005041c2d2a9100341d800340702103000b03000104e40104010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558790593 1250 558789343 558789349
    0x7051b091e060f13290d0f03020f0709051f081c0306120804090b03032523030715020a14090310150f080a1101030b01030e070603020c011104050a05 65
    0x1c0d5403041c40144a0345110103003900060324041d081200b07451455495030315a41a114802c00c041c501d04854520300c6a08604900107200340368514402841d80140716110802c1500801c00c00c401c2d060400c0540700b58580f2490804010039044400749241e00c90705c0502403076007040d0307600b0000355014540644241201540f8a243d0341200140b0481010355424001036207000484030429076500c10304446660300d2400c0000b8040c2d0b2038032284a44070f034004000c0b5482e883d244140300614844a8030001c2007083c1079043c8102d0320560f44404901c1c200e080c0c1c8000c001c05070048010a4a03a2085402c03402102d034907410401280150850b80010030030b64824500d0000a0101030309500c1801011201c000300030111203000d4503158040f0540c2c1c84d1440304103101c00f00c60190703410040c0010070f0091454840300e0702c0303031074060f010030f0052414140d440f00c1069959110b900703c481b4048541044560a6564050050003580325008014007540b030f10304140c807040c03000381c101e9048440041074001168181810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558791843 1250 558790593 558790651
    0x906040506152b02030618010b040c210e1e010516020d051b07060504030201120c0509040e010b090403020c2b0204020a0203040e010f031202010c080408030a06080307051b09 76
    0x7812a120183d0468000582e410011544103521302d100b010702c480c4800311801e080d078241c001e40500c10348c20040d600042c1540404c0354000380c8640103048d82c0002044118100400300118042c00e036000d16920304000b40c1c1548500c41c61201c000000b00030581e02d200c1d82d48030143c03076007071080b0041e0064480c2950f528842c40c060000c0c408900000000302507854015880d02455500040104401080410035503170064066895003141c0c100a0118046002004203a071241c00122441181d0b06c03410790303103c00025400f01c0300080010f800b050342c40c05c090034065521107100c29906d01c1040e008020340c480b1690f9a10304200c644100d01c50049d0b12010317900b00000f07034010400c5441141f20602c0005104074204070302c94001e00008200d00300c29070039030030a4031f22031510840240540e8107000c00c5a1100341d0004825900c2500310b0011703600c2381c8030070031b070b0348042c1c00c03158890039040c80049001c0d8140710010424101031030000d801424404494801e100c10b0200072501000e02c14a82c1090b06c0c504038130204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558793093 1250 558791843 558791899
    0x140a1e0f020c07080d09050307080705092d01050a0f03023006010b0c010c050408061302060c031b0c010e09070c0f0f0609060606020f071814090604050615 68
    0x80c0581051041c1c80031501d42070716940551150707400240c42c0440140c00c04e002d0740103040b0039409070459606009200c1d40e00d2906100300d0b40140c03141400603a0940d100f2207407071203094108195540080940502803007603903007805a9441003011040005c0c03d0650150340e4021268068410342071103081e405940c0f0302d40007111903110041140c4003c2c3d8940601400018064003a25046c00d403a0440b40901c5802c4070107141040b014000c017001b0500c0381c0030001500ca507000c0140703007078000c80103050300c08070b5498001c516960b00184004030b40c0725a1010030087c40180c180141044913040a001c000450b2811651401c05070005003d00128080d24032030300c10720140e18042d00c00f8003c0000d10755a50441d44ac400301058034556501c1094008001990044070014400c9200070811f003050b548040e42c403030000d40304982c000030345a494440c0800c0e680c3c002c100103600440c1e0b64082c84c0b40c490716242c0c440500701ca00321101c1c02a4000a070051a020008104010001d030044004001803c00384040040c2c0070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558794343 1250 558793093 558793121
    0xd020306010905031f02070f1202060417090d1101090b0307030c021c0f05180d0303090b09060402030c041a2e020a08030105060d090f05030c010b09060d030302092101140a1e 76
    0x6680c502181c8103058214545581d68020504cc0c0340904000c00f00c0d0003c4020105022010040d000c05a070341e00150040707054100d5030600d6503019100050390400f00542c010702c0d18036004800c2000c420b405070b00020030b010694094441e680410f110012504400ba4075150110f0300944154010520650150003441c0c2400400380b081d8402c000021076140c114441280040c2e21112880104010740d440903410118050007404281400d5001030f8461003840c4c08107005660341d114000301e818000350703c088080d001070240260b90022880c0d15030203d29088203454121842c4101100240c4006003140040d0b030410b8400b07040d6403c00b0100840e03503120082c6200825110416080401d0380176455506541c880d900940d81c484034091a2425103100300c440030303c1000244204002912900b2001c403509905103801607440601b40c000442e95032181c4200300c11000000054054924158041f6080003080c20308042503a96994400d0259511405070140302440c140201c60204101d4000f00d140500302 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558795593 1250 558794343 558794363
    0x812130611071802071406040201140d020d06030b0103210906030b0a05040f050a111c020901020703210e060a02031b0c1e040605060a0f08060d080d020306010905031f0207 75
    0x307a003941400c0c6807074216540f0b0250780004c881c402c2040d0820314581004405001d46007070b20b03040d00040c040c85c0c03814000750308000c0d0000385800b0300512030781180c800c1c9140c003070200001074807030502c445202002d0008590260b280c40f24051102d419100010424000750f075154801c1b800c00b50100d004e082002103240c1c0114100d4400300c0c80d40da880c026545600710303c400005140c0340208242e0242ca110840858509004204910a00c01540700b822602140c100c03015a840149200403440e040c0b25038809000c032450000ba03140d4030110019506d60209469803540d11224100c070070041d8a10594405030007507801007050400c6c0c00d200c071000c0714407404003c0540b8034219412007c200e440d4007441c1e03100400406134500603964949480703260081c01e029030b280b03400c0c20b01c620b20150030365003055422020700012500203000b6136101c944e200740550788a100140c89901c205c556201a41040c0c40795400302d00100f0022440b400c002034941c01a0448040d11840009020400c0009500c9040b080c1c403440381c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558796843 1250 558795593 558795599
    0x105181902062b0b0103110a0c05030708040803030906070e100809010e0d0201090201030e0a0b06060705070515041410080711030f040807080d030504080a1409040f06081213061107 79
    0x3080400746404100101c3c4a014000040840411140842c080905240c5420307000b98500320f200e002d4614007485800d00034413014142c20310038035500801c06c004100100005001c00c0c0f07c82c000c40658010000142203c200751079440c41600c845400007496500441c0e0030402101503403140144541050b035074000080c1c28421240d182d410820041c0c00d0201503919584d2450442d40e052060f02588a0b6813400b81c002050150f4402a5249010380390034450080458a4414420305019441c0288801404503621510101e078400b440d400a00c28141c00170080840c0300d8841c00c04420380b8102d04001d40e0341d50210740c0c500601f60340a003840c00f82c0744590303c0144640c980203441d4100500240002d240203268007803904150303d14080c01140b02c001054282014400066450410303215213042c581081e8815000440c0014160f00804510b20342c803d0915801040e4200700b54403002c15900c81900b07031083e080002d40342660702d100b140c84e4101000032400d400c008840c8907580c1a603444a621058034502aa = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558798093 1250 558796843 558796867
    0x9090c0a020d26010602073002061b0307030c0b0109020901140c0a0516080607022406010e091e0705090117040219090b030d03090b0601081512030903010518190206 72
    0x4090b0044c10150303001200230b100707010119801d040071711a03801c6c9907124030410480410b01034150301c40c024001c10001c2516140601008c0c1d481400282040c01c5a0701e507142030400030686603d08c030007585c5813425000041030707411150080307500d00801a110220f49152400c032403400e0f07501c4201040c2030b40c0140040c60f40012400e0140e0b20b280300440c0c0c0c14011090400c1000c504090000e41208155806a00c0e6428803c010b01103150106070440d501c0c1a07541d03105401a5039541a00700510350003070b404c00410406a10120030881e0000d0110303120095a921a0350076a040c1c81070002c2c243c04a0202403c014440001200b400d501034806002500c0c07041781d198078580101a01d42001d1050350301e07942040d103d407c0401008580503050314041c01180c00d2a25010403000c0007406285c102300100c1c0001c3c03815a0442c03071089400c0b8014205003000500c00086035241e0b000311600901c03039401c16010070340c410140b24292b0807060700300700135107a00c0c1310900c41c032140e50469481c12030700201d00b4000700c82540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558799343 1250 558798093 558798167
    0x30106050d06020d15151110110a030b09071202071e050a17090a090e0705030d020d030b0a142106010e1503010509030d09110a0b09090c0a020d 63
    0x9110740b6000d0703120440203507484141c601c5405031007001c9910600070411280c400c12000750016050400c00120001e10760b00a04100e04c2c10600308010341050142d4200c40445c10040040480f00e540030000401e2101c100039400b00c1c15150000007504000f03010414045950040c122280b050100e0b110b503100c03480c6034400110f100c950668864100020241c24081d2004c1e58101003090282180d290042c840001881c2d55014040c0380d1401e9a5050080c1c01d00004000920107440010100c8134140b403944002965080020700440010341001d25030b00c49810036400020903a940121140364401260050000d14040d43c130900004500d2207440c49801241403045c0d501801074030011203442d29000711603001001703015000724040d1f850030301088600c40c030100a480b0000e40380880840c01401c207080902800c841080542da010019090002c4e0308001400104403001040d104d603003e07607495400b41d1100b80141c01520300943c000c55004585584245c034030b016014560450302021600940c0d100440e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558800593 1250 558799343 558799369
    0x80f1602070302090705030405070b0405130203040f0b0f100e060303191701091406060a0c032001050a0213050d0c0504020a120207060f0b06090a0e0603011b1d010503150f03010605 79
    0x111b4400028070003401010300c62200034012091206180500e40004520895a030f20143d6040e03e40c04004101000500c080d0782d41e80d681c0009405080303050000040701060015181920404a00b4400080b6090340284c4c96215010060240d4100585d050103518a5a003141a90b007c02a00403611002c0700c4116411501824070503030b000030f007070240d803502860032403024140512442e000d0000103d09540144000b02d165891700d0007029411000680581c485490325a08043c0d50a06007004480b119640c050302c0f1550345641c058005590302da042c01080c0c003000c8000762500d11424001e0080d4101500204080c034101c1c50701c114400c082001d944126000844101c426a464401c0d4407150301d0b0a002d406e6101c1c904944091030690804000b441c02c0403d03114406031030940320001840d50390294000040710a644010110140e080701004203401d0740410400300f44240b01076410800c0d4490816203100301010347c181024019003008000c08003065198441e0b240d0740b120000308240c0c468018640724 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558801843 1250 558800593 558800597
    0x30b0a0b0901092f0904110d0e0c0306010f030201050a030209010c1202030c060f16080402040207080a090602070603060b090d05100c0c03030b0415180b04050f16080f16020703020907 80
    0x50444c00c44500030b81424284c03d20f602240300b2000d402000c0340040c200e40b08090100e5001581d140980801460780c040e50165000580c0b6004205242100105410402c03580490940718281c4e00c0e8401c0c64a294002d01000c2c3c00601d0520201c18424020380c000c0c0540101418001420a1280d42c1c041c0040702c1254400016040443c101c40804801c00140d500860340e0541004113103009011340180c8031044c94081c04200311000407400395142c5a0441c2ca01070f0700112a10f54038018140040c01c3c018051040100502c2542c40010300305100307102d4902502e94040340c062814840d0b404102644a0320901036036180201440e4507142480f80c401d40c6902601a20351550f81c0c0c00600b00601243c144003103541c000e60420004181c4052b800040c1016650700d5200e0352003001d15094000020000350400300d03007107464032007401411600300466034880c1a41c0d809020700c1c4083d00c401107403036001c02e07544088500321150200e01c64030720320001d0180554a41c4101c500c80ca0b038070740029080c0b40c0140c0d07038400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558803093 1250 558801843 558801851
    0x201090b0406060602060f06031002071712060111010b0f04050403021903090515161e080a0507060e0a0b1b0c03121005090108060c070c0510080703180302030301030b0a0b090109 78
    0x2545d40501446038040035000c807502182c50f0000201c0c1e124903c40040c00500c95001a01404210405584012150740c9903000350310303100c1c40141400d050301e041c1c6009000c145400c05121009405009003032011001400001030301c0e44030b1050001500002d4021030644c00b41690310f000c41032040e4030000003030f40a640c03601942c0c0e00d8034080c4000030f000c00b03803420303d000da080112404003880030801150080d400340091350f03250080025151622112040180180000a03280101c2c6a10402a00259002d03440820441000340d103469610004110000c207859120320004a11301104048070f00d201c101c01ca190740c642081e0f401864115845400740d161049511801d004101d81080e10040280505481009480d41060f205940ea03800003401100c0b1079400042210400a03981c00d81001040050060400b1014090010f88105804c5650b100000d242c03410080b01403071000350031b1400d250035401840c030356401c41c5c0300c5100d0908002e100c0718542d912080c0d00002a20b90042c0603000b01841c0800007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558804343 1250 558803093 558803099
    0x10f0504020f0102071a031f06050703030f091a0411030f16050604081c02031207080f060901060e0409020402041e030302010c05040506220506040b180916050a0201090b040606 77
    0xc2d0203180426100d04650040b40c06000c00400c0368201c40d0309420955003d5180d0340d55280358000c1c1d5107441f40d00c0500390b20080002030105c0e042006844524801d0301e0a1010017003516264040761007009014000c00703010000404054031003005c4caa0050300442210018410710300120303140c9043c3d1498020760398090400c04580752031000045028110072604d17245000d25224200c2d513100aa9003401c20300041241e418400e80e4020012241e4803802c81081c00b280d460188400382103103c0c202c403410705101e120000900d0510342440018180e481e6038841c565843d82500901000b403040c940201d820a0f4204408100c9075280b4502800e00700b1400c1240c16101d041d49030007800c2d1342500440074140305050000348410341e5910142c941d52441200042014030410f00c20601c0d0885690180741c00c200e00003400b1400f0082580100b552202c1019816041841f0000344000d5900460b440c150304600b510050a42c24480c00041c01440b05510001c158941c442e00d07807650006041e030701198455601ca13820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558805593 1250 558804343 558804349
    0x32a031e030405011809060b180102010c12020d0f1503420213060e040c140306240408030909091b010f030e031801080f04210302070203010f050402 65
    0x854401050a1910349000340c0500c0201d50340c0c001d50261a041c00951203040841010180341507005001c00c4400303101d140d0b5078039002c0c034485d0f1001040300152082510340c02d0065005006000c4610301c0e03983d0b500a4210031640001c02500f08904120720983c54600700804401e0b58000e841e22988607101c0020f00c0c0d855480c0c8185100c1680240c1039806540d00800f059081908080309452240004035001002503100484002c2c8505000c003049445d64071804580158071004811848900b03480800c0030300c00300340040d100d40b640c28030b21031051001000000e21902f0150012103040c0e507002c592941000c0301c52801641e60300a074115400580c008580e08840c0e1516064040d000303a00d9101801d100f00702c0c000d00a00e10b241c1c1c60680e50511900c82940242680b02e64040c114003841030060345c2d1241d084084060204034546107090005042c0c00c00302e00c0044100072141d00450703000d5082c500164076110290201003501c5c3c0744005240c2d00340039a00158400b0b0044200d103030f06144000845207428410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558806843 1250 558805593 558805603
    0xd0e01020102161520040e06041b02010c020d021f0e0a05060408030a05010b0405010225080a08030a06081c030902270906010b03070c020105030402150f0403030801060302030c18032a03 81
    0x8640750180c175000c01001ca81c03034120308a406513030101042d00d02ca07a40b800b001c600030b00210048560f0100c0641000240b841e410751200c54415401d9003030f61061005044100e07030b20742892081035007288521240c2da0080f403680d40701c20106034610040d103140c1103085d200d050a28408a6003918804000000c004038414144a001c0c0507003240c1c2c004500303060900c40000d640e651420f0348482c64100030040c15502080d918250001000050700320b0740364000614051100c3e402c240c0d40c0d903d42d582000000301d40020045403c0e20781c0d041c0007228240035510300340c048016201030391050317801c612155480340082c800c410245807a403410b00b03412040c074104041c000303181910581c0010702510081c820b00911543c0f0022500c040b03902468134640f0b0392210300000c0c03015050008402100e41d000203803510a41d00d03490240c01102d010b501c4415461380d0b01c2005809034401282c00102c5403070200039400850b84903003562004100040e0440318800c40c0c3c2d141055890b103004008030a42901c0c0200b4081528082107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558808093 1250 558806843 558806861
    0x907180b13050603040212010609020c010f0203091c030222140d0308060f06040e09160e04081e1209030d0b010302091c031205070302030402040b0f030d0e010201021615 74
    0x11800e4509a08040c0300380311100c0d2401000e1082d000000404c06640da140307002424154800001c01071250355140744002940a01c1d0b04611079401c00e00039801c608007900c02da1380720320019409024007000710307034020501e0f04440c8107a40c14580e0a0021011000480454901d01f43c2c070740305242e07001745c1098131101000d030000c40c046108500200780300c00043d80c0305c00511f40040d0192208803e0081042c000348403030040f5013144410340d403080200074111400140103600c0b1503a100d04200c0842d10303460096914a42220040d20404013048401c0d900d4000d100c03080000c2c07181505150a0512901001042030020740303402c0240d61011845034010b40b00c0d4450544903442c2420114942008200070a606a16802030751284003000e595400505005d0100e0401411104004000c141740c2148080c009403c01c1d50183e008926211052845090035070015140c407000034024407a610b6034100440c4e000c0091402a170443d5000e00c803440c201203004584082e481d00c96007044000d2590390b0050011526644 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558809343 1250 558808093 558808109
    0xb0111030307090603051005150307080c0a090b030c250210020c031c0315091a010c1a0a150603020c0c0603100905060402130801050a05070201230411090718 69
    0xc1071000c5207070801803103c1120403905010403540e5518082029999031a8001d50b040701c00c02c1040491007560034001c62049900e0745a00c0c95940314150390054600405003090081040300105124545e000006141d02c4600840d1091501d45039007400030340c0e00c6000a80300900010542c1c05001c51a0550140d40040d41c2c51000340b07814600720f40000e9444032050515407200c0000c442019505100c5d0b0008001e004440c0c441c2c090b5190348148400060200302e00b8801280c03101c800d0b030442580302c0d182c0d140300c1d19003102142c150f60403009031300c1c0d90701100070b040e0f00e4415541d42403143c100f641c0b0410490042c230503a200140c4848400f0016810300e4a014440344c81010300700108410a0740b608028000c0e110340c08400a2070b82e540b0340214000b8440c45580c0407211048420000d0200015004644200b01c1d4801c00c1c01280c6403800e059003a03031507400b8001101541d8050102210b00d0425007590320600440b40150181490740c0412003d51007500d40c200061300d82480d2031036a044100300c02000785921 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558810593 1250 558809343 558809347
    0x414130e060f07082802040803131d070903030305090a0b1302091b07080c0102040f0306060305010b150405040f060b030f0609010b030f07140c10021305041a040b0d050d030b011103 79
    0x7600001741d00120700d0450703c02020128442d00031520059041e200030f010843c04407a5220001488610b0000f040d00c50000303444401104000c3c003490705003083c0e016000700d855480406066990a0300038100090034076856108a10090000c01ca55013102409a010035011810041842c0180805104000c250390208007100302c0c03000b0281000811206015004180103440c0d00e040070905029102d980c0c8011181c5030201030110601000d503003d001101d2080c8020800765005400340114401000450040400240801c00241c00d241d0404001082a86000502140c851010010b50f400949502da2101c20200404c9403900305480240c0c00350024218071820347c90003044990240e04000e199008100600300c00c41420701c004000e80b916010400242c5202600102c80c130402900321844081d02e445401e40001920704081c031428013429403001c000c20495000b0f6080c0406042d40c4030381260089481114400801c0040c0b100c14100080755601080c03109210780010618038007400340d07a0b100d03041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558811843 1250 558810593 558810601
    0xa0306020d06080a020d0b090a061a0909011a10110a06020c0f031c0213050904150f0c0c020f010c1b0317190e060f04080709051b0414130e060f0708 65
    0x6d4503c0c03085a0301c0c5d0010344014680e4403011074508020410500404403410842c1c885c00c68804101400034104040c0c40f200250355640320742901b80d840b1070202d40e140c0c52a91003010100d0425898041410700d09041c124456805000618500400d1305005e403101a8042507030b800d07020080c0511512031802100440c14000d460350b43c01c918681c5111407103009a40003a050a1030441c4103600c0008100080074070710a1324060904420f2500a5560019003a00c3d01c00301d10518a1144180c103910340d42961207806114096084c1b1859045107020681445540c103400320002c2c007040035a048030712552010716003862a52404204440340501403880c1c0101c00c0c010030044140c2d064441e94130800d10310307118035104516800b1800070301c0703510560700b08041d00280108001800190182c1200d403540070421459132810003000000c6107a0340c030420420010401002010700180b03a020300d136603006040c1d4030107140c446940300807150030000d8070100c0c3d0444404c0200c1c119001040e00d07804945802c14450301d183c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558812949 1106 558811843 558811849
    0x11d0a0501050601020115050d110904120e010503041e060605060a0e0f030f0607050c2b0206070306081c02030904021204050d050703080f040305090a0306020d06080a02 74
    0x82480003140d1503500c144100707e0841880460340d920981444100b00e1100c0e8201010344001421102c1d05405684c2ca0340f006020364400c40c241140c1191a000c040c0c83c0030040f42550b41440720034030420001ca4600d8000172110300c858804052001c0707051400c0c800030a001e40089820900224644001d5074114060100c200c60403940400080c044a04141e41c800c00c040304901c507600074502045c4014011409040c00da080d040a032480740701039040d0040d80c601103001410b054040700c3c101101040d014030100b9003020552406100003414048629526809040c180b450702c000e040e24000c2a034824826100c0d1800300038000c0d540c0d1003414030b81d80341411040c2c5055030240190160200050300480448061303d80c1521550016030340c03601c0305960050300600503024407104000504d4035a0b19082644080c0d4810400140c842e0f2000c48004100c03291504614000c1e40400c2407000035903 = true := by decide +kernel

theorem cover : BRFrame.Cov 558633093 558812949 := by
  have h0 := BRFrame.cov_init 558633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558633093 ≤ n) (h2 : n < 558812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
