-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:01:18.79109+00:00
-- url     : https://prove2.me/submissions/39d69815-805f-4248-bbde-9be0161004f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 579316546 ≤ n < 579496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 579317796 1250 579316546 579316567
    0x5091f1502070602070f030204090c0305030304080403030e1215072003070201030c0516031d03030c010b2817030c06010b031005040506030309040b0307090911090a050c0301120303060308 82
    0x8810000d00003642200d402c0c559460050b610341c0c2a5001d00402e852415100b0720160410b9004040140d05c101e1400711600d03541d032a07075400c40d04161012a20300200003400c009156214212155015085500c140382000c90034815544000580102600d4282e000005454034007134100785402c500792004420034a00c1e20100103480c1e511082c4202d003c20b117030200303154a071403140017a107860300d04000100d4000e5025480695015100c6d025640407421002c00961039602c080c4040c0250004650002c1103008058041084091a603000c0c6200540802d2142c1e1000c030a1048030000c5400034490100c803240161007082c01d40c881c0b0707100c0c1e054921541000240c5c0141e118015842015055142560341e0307241d00400c8144c0b60306175403259060b44180f2801d0682c2c40c140c0e100881c01e40005040750300556030b5400840507509514001d40c0e5078a080360300d0003801c0c00e02403244c40c0e100001d60b80401075840c0c84044c0140034001805a104451030845581d4101406944404091074000d6015070302c4450140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 579319046 1250 579317796 579317819
    0x60c0b090f10090c06050705030a030e030706110a030b0405071d0a0b071209050609060d0c0c0c0902041701140c07080d0f051504060e070c020303120a05060306071805091f 75
    0x1d004844c0c0400c642d1000403200c3c803e01c1500c5886078044091403910000c0c1504902400c8800b162485500003000703503000041007031049940c660640101203460358042070001d0215030030f41e0a61750044e41070500300260075501240d801a1840311071401503031145000089428450540c00c5078400b4040002c104040c424150300300b50720f10640b42c1d20b1640e016200c0c001e011440c0140c01e0502c0d04400240118054002d0903001448007040b64900103e03542000d842e0700300e02d4aa03075400000b1840d400102407240424ac454a480d03950000d4000b0321100e05092009081c02c08010480f90494402080356410002c0d0030086031314600b41c402051001e0201590684020a001d40391420070754900c010743d00c0c0504040c00380344100c0b092500b0000080e5208401a10001d01c4020f04a0b0305000404c09882410a50820b15010300e80d42800001c9600d030481c2030500d400e02c05850341d0300b80a10600b01004c01d0140d00c01d5082075400c10f48039000140c54004003589110034110085052200049000c0765210740034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 579320296 1250 579319046 579319061
    0x9061701061820070f2006030c03060102010f060f060906050c0303011202010c050d031d0d020c040c020c0904110a051905010c02042d0c110a020409080f0f0d0b0a060c0b090f10 77
    0x30b009417151454078801c0ca8008006d421065a080340d01800007034290341c00840a0b541c012018000031440743e61400b805d4080710303525088080c2c4008a13120074403c4079807001400d8050580b50401c18503100702415816500e00052007264400d00c01203000d241164401c1050681c40c42d4094111122501c0904001d40070f89801100f80d040600307034042d000817100300011604400641c6802800703c0219440500019100d401100c5066201d880c40218064a859036450310690092000b80441601031003081240310b100da10013442405a42e4400381c18800c01107010007101e400f400d006c1d8503680684081000303811001e805003401980410700260712640b103000b0200460b00034504000d0124240410303105040d03981d88071680350303001c0e622090050810b80d103c610200d000c0c9107030a08214480900e0007440e4070042d045850383d8404614243c1ca65200e004e801d070b9540f0b007103a09411003802c004009120b0321400002078006122040811010001400580b0b5061548025079801c10b692802355409080d11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 579321546 1250 579320296 579320303
    0x3020603100e0c160f1e03120b0409030519030b060d2c0c06030c040e0c300a0b0d0606080d080108060705091207080102030109061701061820070f 64
    0x8000608224550084489580c0400c0c5104c140c044962907909281020800899a4001030ba0704040d03421107041ca07110f602403283e5961a6100030420520381610384030800c05000d1410200740e1000030b40c000091f5004240e80c0c40684004d2200044200c01428014898035000600000c520781c01c520f25270001c1c1d08488040602c0c50071158407039030644921203040c2c0244d00c0c43d0010494512240303003000c02181c10800c2c03108901c0c14031b501c0e4844e660071840c09031000c000c04a80020f028003c0c54110f44c00b1544c20200000388003e20441d24044015490000d000410441e030700e980d0b000d0242c0d1041c1124907555000002001259158582d0700d0f80c4103100d058100100748000c00001e5012800103519200e8001590f5207400d0180d44024407100311303c0628800b40d103000307440011032420001d10181d070003002414004921311780b1381081e40d01f807100f03a10035001c07242e4140341c410b10a42480c0340580e0041c1407560400280300f80c5807007031041030102d407860b03d0b0800310700002c011052082807226520054007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 579322796 1250 579321546 579321569
    0x1410090b091515131d0f0d03051e0c070c03080a120510140d0b0c07060e0c030c01210603060b030f0d0e010305041110020106140d170708040302060310 66
    0x844000ea40d6107044602201c440e21034100c2d02c2003403d2a5103030126410750250041030703c182c5a514901c0c0140c80c10081c005e030703503c901142d1014920410101031103070440c1c2410030903400c10300550b00e94002d500400500ba00290004294075084c81011104240d8011b40c00d80c01890300c0f89045001c59002d0018400000c1140030030b41040121480b40d103009105120045102900d4640c0501080f04989503040c1d010929140700700104120442d864441d011412020703503640da00340340007000c44001526910030390f400011800119100040c00c01c5c00e0283c242018a189481c0c080c0490240c490b504040141c80d0800d00b0000c2045500e0f004581d64890403070558115540d26a4516500c034000302145c00021170865024207154020f603c0180c100c3d0152500c0c0c04000038050202e6410290b8810850050703658010401c00b200022081000c0c0070000c40e01e0001616103501c41d40150031aa2541c8403d43e00c00040090030407505508a07002582d001d00b0054891030300318003000203160384d449100041c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 579324046 1250 579322796 579322813
    0x3090509192913110703080105031e0d18080d030f140603031b071d0f16050d052203110607020106050a0b0304050f1f14010509041410090b09 62
    0x601c00340300c0d40302d00c0990120301c4030328a949420044030210701041c11011aa441c1110f400588043c001001c01500a444141180d40750000f4149084082000d0b044252000a44810068000310f26000380111a10304801c0340d00001921644038150b60b4000100380c42074002060a960b0960810071202d40c0c800700c10007158180c505082d95415045440326856001042220408490010f000c0104100041181d42c056100c210b100412010b604503102d400300498100100c1c031680d0341801c0d500a501d4405941114260031014145005031400304ac1503a031200c000a601c41058200322048a20f1200a0031100d0181d05010349110030300e10710080180503080004034079034014003400045035005009102d402e85010131641c465000948110ba4900400d550f28010b1403040000003215102140983e0031000070881002c00c40b50103403c1805038841c0d00b40108540c0d900c4c650510340c400d0b0005108520001e111101504003000141403051140c0340120700418012407a00741c0d4850b1041404903800c0c0c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 579325296 1250 579324046 579324071
    0x30b0a29090a051605030405030c0a030527060307050705010b1f080901050c190e09040602030109060e010317160c030302061503010b1f09050d21050a0503130309050919 74
    0x314030460b074109810369250701350308006105200450344640542c091700c2c1000600005a8140000e2890950000d440880c68031410404441c820364402d080110f0035051105100201e10700380401000c08047c07050100e00c01051280a410103699004028280c50f40529004144640f9003400701000300000c00b500700007038030a40144545800368464034540303070822146000008440e0301c0400c0b201c0c00c0000c000f01c0d21041d9154206868000c2c0e10a44d80541c580d810009602c04036aa6a8040c04200322807600400c040303215648242e620000c0d40000c2d994808007a15048040c02d005040180400f60820001040c503601158003030192888005140c509403a141c00c06080e43c520464495200c3d682c00b58285020b440c01540c0d80c0c90140c24280510010b5442000074100c03d03c0c298291400c101c041100400004518010311034540542416810720600010003005800300070061030104440310031250034140511385000042000601140c01d0303103046a00c80300d0709070b201e00541c01c1c0e40b400c0c0915003284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 579326546 1250 579325296 579325301
    0x40606080d08071b03120e0a0501110a05041208040f0e071808030307031e0c020c030c0102070609170c100309020a1401020a03050d1d0313050405040804030b0a29090a 73
    0x592240d516103e850a012140c01d50300c1c4d000b00780c200c040c0b01440920f441140600e0107030202007806a0040c020031005400c0540c04e541140160840701101080024009a005815541030b10103504403170b00700f10101c0c0b030010304a101d650412490f0103100034002408241c1c242c1400c0c440e502581d01c410004020070944210044540a244c1c41394005000042c00b003440381e4040b50003a690129070041c101c0200c03040504032011203459900503085010250014201001540c908c0b100c01c1c401001810300c0d284008249061f54010b0345000d041005c42402c4180742000508003030341d00185150701d400d20082014008040e1810124019031072484002a42c2006000251000c07906070003030f01000d02e150b0740c12a1554040d01d45d0101c1301d81e4506221100402c0740380442e041008000066980d034a06104034010f0704415400079119505260070000010600810340d811a6441401c518082e101c040456010b4024408940351241141951420100c04520b45a20030f00013903600640307541792006e80406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 579327796 1250 579326546 579326551
    0x60306080102160f030e040c0f0914100c0f0b0f01030b06040e030d020a1b06021c18060b06091815040e0312040309090203010b0a121e0c03020d05040606080d08 70
    0xc3da403c002a081c0c000c0b440c00c2c685001040d10a150046018144900007001c4401100c1b200380000c0d20541481c10068100790090003400142400302030098644002440781c4074124100c008101e400b01c000c0c41002036010791004102d620420010140c40c00c0c4a407401800424407003900d00c103c0c20300201d4410b0405105508100b00c407203010f54901441d20a014010b03500201a204c10010345c00c0c01046c6196511f110719881522516000d640d528070005419141140340165504943c03501c20640080c110703440340800107940c03040b000703d4484d1281c0d0010f0098000e1045071070700b2040190b4101001d000d608039080c840c0840e0003070307100720703495150038030046640048000505038406c019800192481c80040741d0720038440c2c0381c40d91240fa1a4010b0f20240e0b0801e81c00044110400302e1942d0000b03070006400c1c0030420940000704030107622203c050405910040d074a18440d0350700c031540301201d03100340c0449051141d05101805142894940003000380f56503c00c030021802154402c1802e10300c5030003800d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 579329046 1250 579327796 579327817
    0x70905090402130e030f0c0a050705120d0c060f0c11060907030c050607020406030503180a1202031005060103020405060c0a060b0a0f06120212010e16020d12270804060306080102 78
    0x503020b180c8664250f00824039021880b04521091001503c00700c2e00e8002030815040e0b02014203041000f52800b0391510307a258201c03900c61428882c0f0b0030080741c40014840c0365032450740fa040c6940c00c030b1800c0a00c001d1402c462440816400c0007400c4070710640054008100100800c111581035039a24401d90700c560751804014039607080d1400400031468007401602c0081d00040001584950300e80c3c0d8146554051b01940b07249281e80104050f140c50001500c400400c84802c00390003000080e400030b9200c001000d0340e6180c043d50350001c00d425900c80d80c140c501401014040595504100710790070368400c82aa0300f164a1030078041320846078200703102800100d03490310740c0c840c9c0036508089098480104000120310b591b6400c0c08a0011941c481005034000c251000c401c040070305207102361074000c2852030010419984140700075840c050f0b00600e041003519500b840014440c2da442900c911500c5480216107034144010464005c5c8034040004108036803082d1010091140d4071503882c1c1c240e000c0d141e0002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 579330296 1250 579329046 579329059
    0x201050112080c0c0d0c090c0f0e09070216060201020706060801230c0d060f031a22020d0203100b0910060c030806131b0311040e010303050c0a0b010905070905090402 73
    0x200c0000e52108050b01000f4010070070340709454901404601040884241500c02d0b010109040105410721b00c9440172051032840e28500e5005942c4018080700910506a8054a074003030024080520034400460300701110413000d101555200740c000d01071b41001c04155007040c5014000203000c07405105124202500740000c0d180c03d402074130625071111004000d04171100b01041104811000c1d803044401402c180f800340715845042d810700010b03200368500c68040b011144c03c10302c070800400300300b01d030041102c2e906804a400120b00c00704e1f440b259100c20094051182c2019400c0d90b600719004040d5039407080d13605140aa880e419640d400ea01c2070310464000c11107050a07800828400c40740551301100c058014110316484018020445050b00395002d40c0003101c105404041d94180076001b190a100c011144c2424108032120b401000c0600c0300034203016002508905607034090140d0302402d60400402c00082da50313491510054402100c500c800501c4040c404583c80c80c001c86410f00858014080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 579331546 1250 579330296 579330329
    0x405090a03140c010501150e0f010806041109060c07092d0c091d091b1302090f0a03050a0218070f0e040605130b040608060702100207021f0e01020d02010501 69
    0x1038604625000c81002d11101c2000ba44032086024080e081c020050707111403140703071349950100401818417124040d1040b800170181c120305070f0340204081d4016400301d6000820720704000140c0028411100d50503001a4041207401c0a414080b500078200c40c420f40e1f0601c030050180f6038078090818020312203502c9000c3c088c2e52012800380c0754041d5408034000c0c00c1c03540e0910b80303440410200b400c0300340c620301d0710300c01e02c80401c0201c40091011708456241444c40e100c000ca05000003402c801c1406421040203a4003140d00e02c05540d940940094050300540185001d68990030b0148e1a0319600300d090f0300499920001340f1304840c041d041248184001d5507400e406985298080b6800c11804041c20317402512210042501d0ba05d10305040c1c404011a02e000a002c10100144015100750750311442c19134001400b080042a000f2417883c00e1510040d10050792182c2e40d200051040e000c0390b01d0301c6136022402072440250740d000070003550b03682001d8088508010034001304030300343d401c00d000340c10403000c94696 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 579332796 1250 579331546 579331553
    0xc080406180803010806070e090c04120f06020c0303100b03040809100207080d030c08100303020309012007090e1c022e020c0604200603010b030a09051f0b0405090a 72
    0x8507039000200c051103002254410340b40c80040740c200381c00a40c4a60002d03c00c2c00803c0c0c1d00100708200d1030809450158203444d00c030302c0350502400b4030310484400120904441d020001c04051011103103500c65000c6403038070000c0320032990700d4200f02e800c00c010000c0b0701c07001300308403041c0000c2c1c1e4400c0c3d40c02000241b030005100300b8031480442c4851043c00b580700746400842c801c2d90034008982d424009d5980051000030f5614014541c0d0000ba0030010003501101081c00420740c04000c03202240c00a08100f0075404101039048060080b0003c4401c1a009448001c2103011940c0c0201d51490381c2c0d08100d6a406c4203045542030744d964101d040c0b0026910510500b59969065800c40107018451011b030300c1c0d010550001c50042c4d9100350404c030120340002040000700300310012035002000d680c1101d018000402c001180181c801030003003402c81000440090030780321440e0059018a54046c09a80380d410201d405003200801340704159007050f041100c19201404c1074840c683c41544d1980c018004601c0f00d81307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 579334046 1250 579332796 579332801
    0x1202060d0f140a020307090501051606020c030f040f0f0e0f07110a0c031b0e010e06010c061b020d09051806060a0c0203060c0403030212040e340e0901090c080406 71
    0x214805441c40c2c89003140c11010103000c9855103c1d04803000701698038174040e5802400c0e01c03a41d4010310b040c42000c2c0202040700c2d59001c06c0640ac550720400051303480000c024010b1840c058842401000100080c5c0030030103050110741c05c011203d640344000c006a0315607003d240a200300321074481e40004900c00140d4507c0c46219606041c106030410750368030080c0c98882e4010b1001680013654102c05203102c450123251344090010003440031800b201000c0d4182080c2c440d004101504882c10000161500010b10400e40e00404140070180340070035003031160b000302a455080c055142e101190501324000303001d0401d90701c5400751034590038a0124607920b000030003100e500079162504c1041203040c041001620104503440c0215900c3c00e84689a6283d1716000786000ca0380301c20001e4415060000f00705640a11003c3c58100800c88004400c030360100c1c460b62a05034940c1c0d46a0102d428020104940f0b0390011501c40e001d01e41510a500143c0e01d034600c100a51704000c02d103a000407013120001d404141960b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 579335296 1250 579334046 579334061
    0x10c0504060e10050f0423060924040e150907051c1802060a11010b0d0c050f0103110a03020426060c0714060a1d0c010f11010e030c010b0a1202060d 65
    0x9007072185c2003080380108072045800035040860300c0e1031401c9070300324103e01000d1815030509044441624007440f12000c625945400c02002022188210380803841c004c400e01500c000d0b250a103102d03031851500c61061301900813125011030080d4540b50101c0d006034410001ca80794541d4409002d12902c84904000c002445007480c511041e24000c4418030042c0d442030300404d9210690303500d20030072840029003242192032407440c0c0c51242001c62b40810010340385c0301114048403000c944028040240400580150041c003040c90850540043d800c40c0b5503405038007031f1042d90300002608162004e0301071035006000ca004401c00300d80e8040300000303c102d00145d004100385881400b406441050705880030345001c80c00d1f5a021001a162074800b000844094155040202c0c1c420080440d051003c0003c0c0480402400804c2008058400c0d01c0c2c100c0d009401441d041198501269960100c0d59071540c000d1900c0e2800702d1245094542c00541e0038000d0f100605280d030001d01c4a031400c003150000344e0040812 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 579336546 1250 579335296 579335329
    0x3040b0d020412030203040f0f050a050f01110114090d08010e011403030f0d140619170102070512030a06060f090501120e06040b061003020a12091a070c05010c0504060e 74
    0x700300214100701c03201c140201e03c0b407203a0020343d2958100640c00481054981210364420048801000300f582e0b20003550381114400c1c2e46d07001d421188200104c88100007000e040180390b0a002d91591141e40c0c9505540c030880742201038481c3c0c80030428048a01280030302c5a070146080c1003005000410308100016200b0f60020116840c000a503501c003030741504504003220b00e440d40d400b000080745812811540e070065007112140ca0009003405280d030403403801d001e0000c014000000e2000464000d504030b50b01c2507000349c01c5481c10300f000c03d204007181d80121a4144182c0c14450b0000e8282e0094004048084903501d62052090500004560714a018440d080041d034079462003040c160000c0c00401d00030350081118190a1a0020a0109841400d80c90b041054410480400d1403075000c1400c2c20000092b034008151110729042c42c9160b000c4509040041141c140107002c0a1600107002d07142052151009200100c1c582c0d0b42960725018070700c501804a0140d030070400f503a00e440baa112100409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 579337796 1250 579336546 579336551
    0x4110307030203060103261603181a07020f010306050a030b07030f0c0e120d0f030513020a120606080118080307031e0f1b0c17041a1b06010803040b0d 66
    0x5880d00000e2806000786e00c150f40201c81040c0000f541341f000d40da80392800d40c42d07003691894200b05d24110568031200e00000383c00c200b0851881a295031400900034010098640300c801d881460b100385602d1613001c1e4000300e110382505502056554081c1c0222400c0b0351008100c0d04459143d6140c041000c00018545410036507581e540001e80c02c0780780b084d840d081580341d40f100240ca0f6001c003440b030941d85850a4401c55409280003850b9580d01c1012644040303ca0710300454151584501103054001c0c003c4c0080d0b1240c000d178408110380483d210f0709507006010728000e202150391142c040b4201c80381c1c3c0000c80c0f40f00da0900c9080011615610046030800d081e442d0010301c4503c01e034505000803100c181079828068441040d03080c0010540140348409180e00907403d80048030200140c044100300100409008050289000702030001c0161070007010300c442c1190485100d5505403466500200084e587c9141000340200320b40310028201c3d059031500802140750a0401d411011f5507003101a68481031034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 579339046 1250 579337796 579337799
    0x13140913030315140f12061b0405100203030f0a0219050703110a0503040906061b02040b0604181b05092107170f01050c1908040c0329070f0804110307 66
    0xf0410541c3c2000381503a50b240051590084100651880650765161180b050070710f150480e0300340800d02a401c0040102c40082101c0b007492120858015039000b2544142e41c403442e086440c1c0c010000790b2082d0032018450500b603461400c954105e02900480c4030301c0c04040c50b10700d407002d40184020802c240c002d0410620340c400c8400c800e864880c045000319865000802d017001454824025000902035a05182d4201d5981501001c140d45403000003134070458644002d01000c0d2a0403003200d002e02080a51822011106003500014245e40c0f0720000300d4402c05400030300840e01c03400c203440040b82c00030160440780a0b42840040d041c1c040022040c0700e4050520001030040d2148440404103c0c003030043d00d022025088030070300b1500000c1c154002c00d00d00300055902124680c5c048500c1c000e00381801038030b680b914180303040c0381c0c140341d00010041a00b1549441704002c1e0540c41303540d8000703080c500c001c040d91241c4c41103541200100341100402e40010100e00018180c21800c1824103002d421905150b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 579340296 1250 579339046 579339071
    0xf1710051305010e1507021b06130b03070f0905100c030e120d020606030708010506031203100510020312060a14060309011107080c01110f0715150902131409130303 72
    0x440d1400c060b00b02551060111445c1c40a01c8040982d10010740d001405290362451244c1e1700c88007500303c06a04ca032400162000105c1008000c500c00b03407001c1e41d9040d44928184001074400840c50004002080d4200c100143c245800990509902e840f0f075502c991662560b0303400c2d40c000000d070000030381c4140702c0303281051148010402d440e40c1004a9005115500384807092506081c03640d0030048050b4113040422505132170004e004440740400e140b01c41c0e41e0369143c0780c1100802000340c200e15032000d075001c00281d000d0b40c00409000b003c680d01e41d0302241c60301c83c1c40070000c91801c144110040c407030b02e0165240c41032030010061079205000c9800401c0490100b81c43c4110fa60004108035030440c004070341848002800d216010a0195440b444d526055000207025804d008080c0014505165a50884881350107500036452914604540c01040f41e1201240710107500000740001e01810b0401d00085c1003140c00f00030401b0120054008007440d100d041d03081d0b01501250304203806141d220308907450038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 579341546 1250 579340296 579340301
    0x10515040b0c21040f0b040605120705160b0103060509010e0c0d060204080a0c030c0611030d02030601230a181202010822060504020109050d110f0d0503040f0f171005130501 76
    0x464030f2400b82681d071418554003165001c601d41021042c000c00748414808160420708030f50b6000f2009082c2c0c2c08558a0000890b03081c8500c810f0300000a5004030120104180b0408182c140c3e84143e40030b201e16607480d130040e4225801c8000c2500700364010ac0d241c4400e818060001d010ba540160009481c01da02d807408186445416401101c00715189a020024001c80c20b050b54098442450680110f8401840e815070380e00603024510901a030000118030241c1c0164800c1c1c1e5407010f806140c0105041c500b0303002a864102c1146e02e004180045500840d1210310b0481d0000d550424801d1866214941c004403411040104820030b1601483d1807440400c0703060381e000c8101d91043c4070210b802c0c900340c0f0004000e84102e81c0214015030040d80c800001912841e22310703840400c00e8070004013403003440d00095030035a44408054128080010045481c140d580c2c2c0c104283c0302a003440d803d00c0e41c0d0f200c12900c9039608044019009402035100020f03102440d40205410124400d00c0d59200072007500c0b41401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 579342796 1250 579341546 579341593
    0x3030f021e240906010302060904020d0e011a0d080d020f130f0602070608060123040b070c0f050d020901150513060203071506120f02040f051608010515040b0c 70
    0x1072940103540c420010305280b00c4018101070054241a0035041c000043e940c2c40e44c060000034801e03200802c6001c02602e42e607055a040c03c80c80e50301402074001c1304c2c280c1802804195502a07901920307110213412424100c0700b04104075808038140313203050310f0044524000c1d0003041d0002c1c40d84500700020002064141001c0010704461101c05000c3c6140110203490401c2c194004414031081c5020001c16070381000100745840c03501e004e006001110402c1001ca6403040c0e0304a442c11501c0450b240c0b0501529900b07880a84120301c0003014515250410001146500000203501c451810014405460901c1d000d00c0003d03072a041181c1420005000055450015003004005a1011800fa8203214080f4a0030001e00e050300c000300280c605002c41600401078607200503050703040d09148581151201da20200f186500810304010707c1c14003c8900200307050840100c00000c1601e4008246460321404580300000000b45040c9014941035014074990000c441080031130251030701d0503000140d070200030314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 579344046 1250 579342796 579342853
    0x30305180d1205160c03180e070c050f0f0309011115070f02061b0a0f120504050c12060f010510020a060603030201050a1805100b150414040e03070b0103030f02 70
    0xc02c00d080c4444101203c0c1c0090841e002e450600741800c0d062504a082c1c0e01d840c54044c84d002c09038088004540f03116807516801001380b0284a010050f01d191710405005805228000ba10344410b02d4000d050707550210400e0480d500c0c0c00410040f01158040c000100071014400d0580385030490380300c0070302140d44017200c40502003403c00d5040c0c165154103103c000d40c410071100b10b8042918560064046034080c040301742e030620603064600542140036421490a541040000740081d2800c1e140041d12802180c0f0518011154003110369900040030442138270503042084452400e078a00070800003d6501840c2100c01c1d0b000c1c034481180810362a0103100007a5000f5000070809090044002040b102e04ca41400748a4161880c604005400452140740c548000c0c40e0115a01c180c200014050684040c0088080707400040e0000c2c01d5074143d099030040c0d25040740e04022812080d500c2a03240c1c03081802c01410441100c00500000740901c03154082440c40c2d00c1140d603820040e075441d110785c211100c16034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 579345296 1250 579344046 579344057
    0x30a0803090102090405010504051501110f07030501090c08030f070f290f01050d0201050304080309070b1209070b04120b0a020903010c18150906080604020d1a1305010f03030305180d 80
    0x25642805c060040c40c0c01408103840c1009545480f6010740088031640315006c3c10041d160403100c5144d041007040c210300d5000c00c8103441005540780b4010340201800002168821f00480700010341e01404403e840240e82444c410b20700e050307519660b00817503d43d03071002110714810300340401c914011521541d01d00c0c850380380d816401c0c50a02c190020070a10050f4001c03880f40030709007544001030340d108050700d8200e6405000c81c3d8580c0c80f43c6031281d0500c0d400c2d4100c40040c040114444500009208050740500b0418090340c52032903c4220801700c0b8031480c040c600c074665141c0c170f602000030302070b00103150301c400c44210041c0ce0040e1000000e082d42c410360154800500d00d114205030248061244100504609050055480d01e041000c1c041c0b84c664800e2000b4460104005100e940351601101c41000b900c4ad42003094407038070400783c1441d03220f00e425070f4003d0490110700d1030344c03515511034581a6150b449481580c2071860741d08030080c1000138001e441001103100c074000300303080400c07150090b8411610303403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 579346546 1250 579345296 579345307
    0xa0b0a03141501140405090c0f1912050604031d0f060307090f0909150209031e07050301060b03070318021507080904021306080a0506010f0516050d0203040f0905090601050f030a0803090102 83
    0x2c000581b040500081c22580100b0030701015980da0140415500c075003647d80112501c082c0c0841c4d542154198045004449128203803c208000440d441340b10341d20948801e500c00b0341c90050442100a10400103400000f616411102881c040010750391140c0d541c94110140c0b40c035400b00b01c2200500d0b0b8402201a505c50344404100070300395005ca58008148a411800d000c9a9400603a80d101041006140941200e42e0500300030018443c1c0740140038090020b005241d070b03416590304e65a00445800c00000d1900502ea07160701d4a800c0c00c5101c1305d80040100079290480b103034403903841c0c1c0454070071a5003003002c0019010035103039400a003842140541001d588213280c4100503041c6880146144007203454a82001034580e00580c5440c03c0714480c1c9866a204c0711690408090111003070009000d500c11800b504104550010081007500d4224801148280c0d031203600342c003511001e883c81d64450304150014080340c141806c0c0011406001800c44055404c180c5030804031354001c0d19140103603500001c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 579347796 1250 579346546 579346549
    0x6050d0609020906030c030709090c05090901050d03200313122a03110607080d0c12141b190302180a1d040302030c1e01050a0b0a0314150114 62
    0x344034001c00c00d0801c25860460744100040c058840141207408520340032010981e9184102d403000080c0017610400c1110603000e50001d4a0f07908494841f42c0f20300124030021401f41807507070219050750ba260b283c11103840100c64070380c0380120000d844a8a14070082c0050303456040380f500110300805a882e00d0701c0040050b070500141915000e03c047d80440b070101001020f08611405070340403a40c102004840c80d2041d400001d01c0b030320800c030740908400404981c500304001e2692280e002c1c0c403a251520060307020064041c200707586114101c00760528841d000100d80c4601101340c2180e8103141aa11032402500f081070b550320140030400000041d50105e0069400424241e010703104010031903c00809529040c590310088400703060822880c0350034404101054000c209032001000b440040e6404c1c0d05514200180741c07544401c60030300c19801e01000c01c030504100c1c480d04111800c00381520310101d0454452940300710303200010309128410740000720440001000c0950103400f2460146540940040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 579349046 1250 579347796 579347801
    0xf0f020910090606211d240c190c0c05150a030608011803110c060c1e070e070c060b03030c0a0203060f0601020d111002030a0506030d031104060c0606050405010608180c0102060a2406050d 82
    0x1810308041c001c0820200c5000c149d803683c088403056141c80e00404002540c03400c40f440008503400380340c000001c070319803c50184010000e481840702c9030744c081090707564440304182640ca81041840101d510b04a4510220780300e00700210000c1c4001c0d003110307012a25000800c0c100d603c103010702c04403904502000300c0c4844000340103002040100004045c107500b404070024006030b010382034009001e8500a000700700070a030742181e500c0d46001019130780c5510f01c03d44815201d9001c808201d21a00071980011144007008500c00d0050b40103900504c11507150441c1924500e016580e80801c40c481e101e03c2421984290004510078100308030040ba483c104842411b1901c2c00c41600001454105405a0b05c071000003003e50701100c606e40b03041001242d0300d0516000401c003540005d03400500b000000304205400440050040402b990006000c0740c02c5c40d0559107400581c10600d0060b0000701c089280250700740c100403041c0074501540820310302881c1c00040301e01c0e0154002408074002040c02c40c010003951 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 579350296 1250 579349046 579349051
    0x30619050d0327050109090e0109060e010c0201060f0b09060702180703090c2c071101050c04051518090408090316060f02010204050105070f0f020910090606211d24 72
    0x22411a6803c030f04000010300000c071070b4041c0703100250792405001031000c0f09400121800360001e07c00c000403844d040e0040c1c00b03004503620403000756003440c000081d810b00c841c075000c049520803440b050801645408004099011240999000103051a0000003c48040803540070380c00d2a00c0010300b00c10075150039901c100d09644001c030842d82eaa89804000d641c2c0040c100b03040803401c410740000e0366030f4030402d48207000e0326040c0204a41c80c1c00d007045a00e0848200620594604880e0020a00c0304140c1403480da203d00340342d044190158001184103424800340700c907005032107183d0040c100035140b40803a24260710407011140f0ba0325032403420041940c0140003c840100c007480258546410880080c0c004e120303a20006040c41840140c810501000d88031100c0325a90050600311541000495081910030b180203000300e55103070450020700980500168420508ca0a00c00c01801010b0720b0b0740320003021442001c41c8076101507803015444110134080049280749003004040c2c0d680d003200f6072518a0000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 579351546 1250 579350296 579350357
    0x7020f090a090b2d271b06250206162001050301210c090c0c050f03091005070f080d02070507090e1f0e060a0e06060301090206030619050d03 62
    0x21103c1240b13841814036413402c40c1002d182035145845076440d8248480c07a0220307820500400d00074840e0405008140303040c0000444018103000100d20707081001382e1203202098003949410f0319802c440fa000072554107691600081429041040c000308070120501c0010301142e0074030910f84d0b821003c9482401d001c504640030728040342158104140542410000482041d441d070f44400d503002003200d1a01c1d160044c3c81c040a041c0012404028042d04510b40c1480407103160046011021005a000040d2000d5420040002060300e0307400c241560302e0744c086041680c040003007415200106041d04001c00360685100e40042c0d81710007a0800c40e0a00c030040d00141c02a80c2046200000f00c0f10004090074621244918404e0038421102000c0003010242c1d0f40b404940100c0c07040290701c200da68060301690000009441055550104160890305910402035014400340042200b030f08180365038001c8020f0351122a0300c103030784440000c0e00c81140310404a00007035007111400520090789421420300202c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 579352796 1250 579351546 579351571
    0x16060c030603050c01030f1506020a030809151302060702092403011b110304150905010f05120406020a0306030b0103140106050603070e040c0c0f030810051002030f07020f090a090b 79
    0x1c0d950b0f1940c9400c4543c0d0114109070311203c00c0050410286e102040007050300c0e0000d00c100d5a210006511039001a4055000c20080c0000600780c1e00c1c00f01e601e1804011907002c40340a5941c1540001c0d000c90b5500c0241e8012206002110068490100450107010725035031201d264000c10058180c03481d850142540243d04000004802c00c05030003080c645204642007012070b2040e201203840c90b600490303100c142c0f41e010182840c10040e8009001b036080e44d40aa0740c545904240480583e441e2181c0d1400c1c0f81000741003000100820752540c0581a04641c5207804144545d4036103d001c10704101703030400e803203d02d14003105040b000401d1044000402090b00e0090544c503140002604442100fa41076000341d4403000c498255510820701045031590201508281044074140203001c2c2e41c4c104c0790510450030140c00405d0070311341320305001906601030307004500c0c04199405c02074041e00500e400720b07040039150504031078958905901905c1031140c3d1900098403100b904107100c032920003800c210795401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 579354046 1250 579352796 579352799
    0x41b14010509040c0e031203061903020d02090604020f1219051605070f080f070c050a0503030d110c03030405101a010e0607111e030f070b1207020309030316060c0306 73
    0x240c201c8140c51031074500301d03400110110f4910040e80c1c50341a85120607414001d00302c80f0800070316040080d40c014035003924443d150311440f90075004150070902001c0e5210b04d2440f442c200518042801a07404040900301505100c803007111480c0b43d40140d03038642101c030201c01c02c000d21f9614800061564210a070307014401418849140200c2c40741c80c040303907030401100150100c24440303542c80d0b02500c13a034080c11180e55511164801102c5401c0700108071159064210001214900507869105440006025501c1c202c0203900f40e4000b030081031081400c0500c00e2103800006082032020314030840c005c0002d880500503581d03840003184c0e07541901400c0340244100341102031764031003514107200c0c0d42030b81d070680d4038205030400c0280b1078035244600f0f901106034141031071440744001001d0305208059040303031141c00b5008600c1c0d40300c020b03130b01820764002014000901600746181011307070029500e005407880e16010f04007003419070b404021543d072072000c0c1f101200104442c6100b4614440c0c0149001c0110a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 579355296 1250 579354046 579354049
    0x120501170616170a110708030a0b0307030507060f020a020a03030806090108070e04120c020d0c090e010212040f031e020106060f0201051e06060f03090105070908120307080705070803041b14 83
    0x101c0c504007030203c00102040020b8070210fa26441229485680e091441d100c5202e86400180707548100c031801c00322800c207100c00d82ea506000a145065a0380702c4090f0464504241c001c5038044610907551701103101f0004080003585840c54514086c50080d66014040d180040034440b21140603440845198021102004030074a040301c40b0f80c00641c4100c1a5138004500d01d4100c440346003c16000e58410115075501d020000c01d141510104d42c07040c20144800d40c00821104d08074010f8107540700c0020b00c03001c0040c001940c8a2082c5003a107119061100580400c800016005c51150445c0c0c800f5039900e00d0144041c1e80c1101989440580310702c0248841d01c3c115030286181100e840b0201455104580841d5080d03903200d003500c450541c81402c0940300d00e020f80183d4043d0070162101c0012400058012510800200e00d94644010300c414207483c42d01c1c3c01d0300803100301e00000c00a0082020900030880091103e01c001c0d030085000c1d604032070f10041024a0b00800c1d2003070342c0c088580b55034810014000d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579356546 1250 579355296 579355307
    0xf0702180130150501090b0102030c0a0809030a2103050f01030305070213020c010e0106140d0816052d010b061c1812021b01030203040213020703120501170616 70
    0x70340c2d03580d401c0c8824898100c06900360700520084000c0000450f031290b04a20500c3e680414120340e020314007403146268401c016030301c81c8540c3e4503031491900f09810920100c5e00b03071402840c101602508443d186485034403050f080c00da419084a800c646980c100c2400c007a414003e1603082104400d0740740f059451a44c0241a0b44182c640007406400c42610601c00524640e040d02c640810b28002032224040d443e030071070f0003041345000d03800095000d2103c1c00040d044c05101400721550142041d40350000c0304404400b54034400000315007611a480503090001d03007071280d60002c0c0c0b00c1c0002e40d0121841e400091425154040100c602410080c03041d2510154050010701401b095440002401c00e5403c68001d41070203000c001401c0c104140c00440c030510b5000882c1c44500c110030015804942d440e0300110141d11003650060350180b0541450007207080158024100343d803103814864503101c444501a4160b480c02d0b408204030701700c110410181c141083c011a17902a0004645018080c2d1800000c1e05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 579357796 1250 579356546 579356579
    0x50402030c04030f0b10321216060801092f0c03070c150e10030902040b030a0305040f0f06020a022704050f0f16030b060607050303091c0c02010e10050d020f07021801 73
    0x81c7c07401d40209889003a12010341404041e074400060f507400b011411900350f00a0780f14070659001580c0c0000004410b0654810100e561058603290014460240c1426088c2103413262040c86607082082400c1190074100010401180f280c911209030a01d40441c0300b611a5080410000f88a041500c4400c6c0741e40d250301d981200c0070a4240011800c1c02d07400450700528928000d6501846a10260400d05420101500c2210440b102e80740d4019200d9501840681080c8180340160f0722801000005152894542070a0320381907034001d07001c4091703001c1c20503100780560301500c41c0e0304281e200c00801c60b01807100c08407a219540007461040c50325201103020340510301c0003400400889010804a642da901120700131904041100c0d1681028101951035544845140351801030080007a1215401241040100d940585442c420441080b00b44118410480c86a104102c020415007400a60f64400b40c101007130911f000546551640c410710840f9030b2425819109552840010060401d403100e0031503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 579359046 1250 579357796 579357869
    0x20a120213050301060b070c171203070e060a030c0905030d0e060d0b1f300f020d020c0708060705030f04290103050d080c0a09050402030c04030f0b10 66
    0x1a0364200030601c03180c1c1d031100ca4010562550800200040c181c204401400d5043d00030b880070303e40705581d12144203024442d2010054250000c0c03455202c40c001b443c010355130100c91030801030a400311880010780164040348010000c01c0e80d071070b038079108103a1120700c1e81c01a02c03003600107045011820700c0c0a0600000c014030701c1c1c4140703c00500000b0180150b040710b040000064404844d40030a07490601c0300c083c40c081070300001120106058040040001301c68403403603010400651403004100c3c44006404a1540e0748402902006181d01c001e119200600a8010345070203400d030b10741464000c0f402d004c00682204200401441070182c42c545500306036400c6503000f001c4141405100041c01c642502c0301200040c0104028000014003402042c0e040c2c443d0090794541d48107a0303502e81209024010445a080001c541d01c40500890504d03900450300144c10701d140d9810207a907582d401513500412002112103c5481c41031000034480150120b024015081401c40044907204906640c05142c0d4000c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579360296 1250 579359046 579359051
    0x30d020c030c010204030f21080a05060102150112060b0a150f020703020402030c2110090b01110105041101080114060d0f0e0601081b0102010b03301813020a12 70
    0x400c54030304108100d03034101c4680c00080d500e4540d00d0510583e0510481c9003a148103410142c424404a220f0810603030038a02512001a01d8445400e10f2009181c01003445055116941002c500c40c058042e0a80c000c0200b07030b800c894444250701d01034003a50038411099000d0604580188080c10800302005014004d501c0c0030345e01101004002ca01d800403d510280d0031500c004144603518100500810508100307508042d00c2c0650040460340168045030301d060350844142c000e03c050ba030360780c0000a0940051400e95400c20008120700d0841c0c100340c404482079186608815210750b000040c4500409280c4040414860b00402017000c41c460700600320381140e074070316440c0c1441202c0e6211184000a00081f070b0403541c0c503030311425034400100c55045101c4c40f410400d8152580705018402c1c1c0d094003d806414040c0040108950420200140d0003c2407a08521044010b5100e0003403c0058603140309102070039034034820311950405040914514034010840600000e4100c1300b440e00701040c44000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579361546 1250 579360296 579360307
    0x204050c161101080108030a08010312050c12090a080a050a0305031803130807050a030c05270f070f0c0b060909010f06060c0b010e040317040219080f010e070503030d02 74
    0x9001074460000311016400340d084a2409001110030142c41c040000e80318415103076200c5000f1552405200f81020014500c90014000140501c25018046c079850400608110800e04500c2c1480020309c9500300c0008041880d22152805445201c01002100042c2609281d16141d09407161900784025080c40000030125486400311b415420030b90300c50805494503240c0600c40c0b11005011403103002d005104034400420149801019001125481b18900000078580428414811501c4e000005041b190201004c410b5810355482c1e44221701c2c41d0a00a05803401140207040661012046020440710340300e00400a0217443c103054020204031121002580d0740411340b03015052444890303000e5030038002c00080c0c41c0d401550300d0881700c1c842e81400240742e0700c0303c11495480c6011103000c5c001652180c0c1507600301014220711a0058005404680342d030400c4500050340c0c2001d41c0c484481944001c00035007a1080c28402c40d10b608005801508156180100007a6a8003d40200100c0c0c1540000e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579362796 1250 579361546 579361561
    0xc0302030c0a0f02120a030c03050a0c020c0f030309150a03050a0506010f0c0c091b3906020702060f0306032514032119030903050706091104050406020a12060b07020405 74
    0x2017548203080d010120b40d01e0382114030040140c100c1c6181030002c43d0070000070452030304e150b02498440e00f8059008080c101c8840042041c0008910606034250004111842e150748484900ca4040c58030601000e0713a030140300c0002405c43d50010010403c441c80c18040c040c0c907a9100c65075021040c090700d0070b29000800340c14000720704c080071b900c4000c59910f010301d01c06881104001c004140101c98403800c00110000c1d9025801800102c900c030b20300741124a03041d082c890828000303c00b586c001e000040c10110030341c0c040781265012440f117520200003c800c04c032442c68100904484100e108a00480a540e002c0100a071034285001c2d40ba0f04801c9480012503c0d01c2c108240040c042c804c01507102d008011003920344080c2c0c000340400496008100c80c5010803402401a04180d03981907848610300032541d29020000e1004890468440c0ba004002c201c49036180d02406010714000d00e0010398600c640e04000c0c041d82d5440d103c140c0b449041000030401c041e14038094440054040e100803405507610319 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579364046 1250 579362796 579362803
    0x1203050403120c11060405210c06070f050c070807140414041e06091109060109030503030c0d0e010e0d0305060f0109030b0c070f0b06130b0f010c02012309040c0302030c0a0f02 77
    0x204c44000c0e40324403010003007413000c00a00b641e60701059001403502409180054030344c0c1e00c11403241441580c85800800c0c0001d10901d54103060301910724240307080c01c1840300e0f90307802c1611651103810a540140d2050000703200e60041010403034000c4030100050b441c1e00b0a040240f44000700091300c032041b008d000441c600d0012403007888c0c156120310100312030700303c0c0c0c50a1443e118003910b03017a00921f030303c0001a005501075400b00083e41e80050040d81140c2e00d9003c04000f5034000100024081e40750311200301e40715000d000c0c4482441400024290a100080004049800041400d0b200340491881624a030340c10401e071800f40c2c4d03080490754a6039920031215052074451094020490180c0c91021014003070680c0b80c6c2c0740078000403500301140580117a0700c00300b0340c0c80a140d2681c3c03020042d07411501640c0a007800500851040c10035110100000054004010f141503000007020700000380000c4903e000d00c9184040045400d003141542401c43d1101b216004110010b824008480b401c2d1700040d001b00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579365296 1250 579364046 579364067
    0x90309040f092001020a290a02090102010c02071413020f0a08010311010305011d0a061502030c190b130c0f0b0c0d030b030c01050a09080601060201091203050403120c 73
    0x1034000c1c005240241d0307000004000080064840b40400d806110260701d0400e034480c9990016402043c0019207500c0d100a4400d02411002c41c04aa48502c1c000500c101062184038000d0f0703400060312071142000290035070700d88032020021508a400d050040100030515800010804d440554070115940c0c1841c000380710f510552414a00c010604078440c0781d0001546060324440c1c0300c2d02d4480c5801788015801d42d00d0070b0161009488600904082082501e030030320b0741c059284100070400030355590301818200d10802d200030058000080701000040b0410014194202c0000c6003034000150752110492044041c22000030410303024000c03020b00140392524005415502ca81c68465541c0d00050341199118802408883c000c2d142200d209500038410401e24010140107082410a5840119510f03480a2000c40600240d45004541c40c102084070f1400380c45681c000040d100214201001c5000c2e0070907946040508140c100f10020b540003100010340004840041411801820181d8041c56007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579366546 1250 579365296 579365299
    0x3060408041716080a02100e09010303050a170f100b0f0313030203070816021c1115040807030f0c0e13020607020d05030d050105090a0c08180a08040f240c0b090309 72
    0xd0520200701c66a0219100d802c00f1b1007200e070550594503c500940d607002c0da115a20758480e040e440108040303400340d00148114800340c60035960300b0504090394108034405545086625990304200314854010f00f403041c0107010f6885c0707650b051140a4116102c240300040030b640b00b00b18903107030380300400d4000c10542c0c00850344980c03000c0d165007440c594150490940c0354140d115980000092045248610440c4050380d08482c1806140d0454030500c80340241c190b03c485d101c08808c00c00051000300521180c4c1c061403003481200140403c03030900300751016164004114002981e020300025440d40365080f016503a05560302510340109000060040241c0302d0007800a000010319501c200c184c0b688901c0c1610001ca83c0100700c1d88482c040c540032a00300100c004040f850b40800301310700c0394500e0091010b403104076048a002c00d040d5965800170390400ea00400040708194000e11000500781502d44006840e91000760300c00543c840003c001601403500030f4406c0840c2008a82011802c0c4200ca1352540f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579367796 1250 579366546 579366583
    0x1608150411010e0619020c04061d190e0303041704150f0c0605131419080c070306060b0d0c1b02040905010f0c09080f060705070b100509070806030c030604080417 71
    0x1305c586411491403c1d4540032005001c1d4036543c0a01d03161609c0350109031000d8a0404513210928820500080b00241c91265000ca4412045a012040c2c0c0600d10024441e500610b1b00d9003051f145c00700382c080301c182600360515824031041c0501e204028480143ca0380500d417000380102c82002c160b994155440010301001d0511040128002e001c24105901c07500c00c000002c4144015018941c0f20781031030701070700c20840c0f601c41d1581c0400d4440003e44014007a55083c4d0303002d90769994600c0110741740340d03009500300035002c1002100030310140700f07811342c50706c007414180c070f641d44074088075046c2d8154030070024407c5681d06030f003c041c80b109500489480e03403100c0c02000510741d154400780481c2c106215900d500c1c89516402c0d002d4100100340607014103180d48815007032440566900700100401048104ea00f1681400000e039a500c60304001e0107004261a0014141810001e25091001d01600d50f40280c1c820340038400001d0860084400315100380c840103120504180300c0074107000410522200c0d840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579369046 1250 579367796 579367807
    0x306060a2106051009030c06181d0f0f010605090409051603080408160e010501270b040e06010c03020d23070b010e070f020a03180509091608150411010e06 68
    0x14076a101905803601201c00c41201186200f0440c1e0403112070000400100d49164100040c2e801981141840300d1803141002940e80c03160030b07404091146c1402000c070500480e082c8050800c007040403a80103211506400d03120f41c1070480c082c20700c0c485d21100c80e000700e94820182c070a0010a101c200f400303400031000004010398a0400c004103170464062240c075405442480d400420a0b42170788411030703d400c64201e806030f1901d001582c1080c040d003c400444860b1400201021348101d03c4207002c4c200f144061500d4505241d80c030060217200a260324188210302002c00042030300003030700d44034800980c5440f640507512000d840440400344c00c01e100200758003050703c070100f20501041c103058410303900034501503035521034003250012100b45060000d40c010403030482c003003841a02d00c0228107041c00e0f070b0440300381c0d65400400c64030f4108a0b60a80243c201c0c1940e0380620210151000043c04c80b0310003000c0121b401d0070030141300c0d00003800041801400038041099a40256607007515050003c0c280394881 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579370296 1250 579369046 579369107
    0x30a03030f0c0302070b2208220902121519271b111515100206060f0607020f100f02190b041509050f030403031d060306060a 55
    0x401c2584004058241400d0002210390300c00d200303032200c19401540c0d0344220749401c1c1100655401204074071152940103603003100418440001402e42181841407003401803c003130320618030032402c0d401103031aa6004216a10000c8a6600c441d50485100c0514100c8070007038400140482a1000b80d814203411580c0c00001c0820b10304090807110704165021040440c130303282001e03048074800b860028a100d2a0b020b8090740034420707541d094081050030103c4a4070403041c400d10040c03101c01c49884000d4440d20f158074442e4240840304d18013401e0207000500306800e0a100140c801c01014828a0003820081210010355990364076888a409024217129540c5400f400000c00c0c40300403441d01005403103910400042c121880900c01031960300465030403095103c076961070740841300d1884081099a201c12020f401704000380b0213200b45604102c01140d4079865403902070701900c0c1030300812035145088200354a40d07480380c904580d40000100c5181d1f5442c42c00210644801c944040140c401034098541c58148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579371546 1250 579370296 579370301
    0x213180209010306090621050f0a2a0b09040f0b0604090204080706020604030e010503041103061f050406151107120503040515030601020c01030e2e0509120711040b030a0303 76
    0x24000c082e40c0034400e56440b80481c4042d00e000e44141c20440c14400c2c0300041038030761004050b6007d4480c030305a90f1078880c1e51045a1600e01c401009907528175201110340070141d5501c0040d0281800344150824440c07403c10703210700b94024070301c44030b0060b5110400d04100030280c0d4000a041079000300701c5510b03251101480c0000b034205015001c3c01e40b1594502081407400000d4051180d0b925542d5001c030030000100464141e0005031040381c1c40c0d42a07001500301c40c0c0c0d0078007140c0e00c01c0b54142c0c06441c40300e031800040564981154005070203140351500078400d030b018102d02c86249010340c2c1088203000418107201840d1070540d078001c017071400c5130b0012440fc10002000800440b00704440012040440803a140894402501c1322400350740003200404265000b50403c042074100301c0e00707803140400c00064039080207080c030b42481017443da5924000001060382c45015040440440100b04001028511070781500c01e00ea8090b00d10905007111407126640da802582c0c294038058150f581500e41460050301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579372796 1250 579371546 579371557
    0xa032304051b03012d0b15030705090607060207050109030909060305060609090c09070509400219031b02070e0a0e03071e0309051203040e04051c180f06050301050402131802 76
    0x618100804865a0301c0d07c00b400c0c03802d0035180c042c0c051071b40e19116016901a84102c00c02d0750800024401a00800c0051018000301c1d801200040b81d5815a45001015020150003400e084e515090040c00407a0001175025031141066440d01c2c49916205001d500e003a00031410540d20880140c108101076510401030007003e0819070300b03240070407803d40c099006408103118200d1130407003100e4000207080d1100c00c0d605d1108070700c00e401440e10a00c2030080340190f41da0041c0c0d50210747c40d20b455080c0c0b4065031f880950f0310142c910141c24030508040c40511007102c05044040c090381c4510801500300c00500c11940541e41c0054420a14600b41d101c01040c1d50040381c0960218511220000e030b6404c0000728440c2c0281210081d41c6031504000d034560410202134010388503842218107641005858040d5849001707810b465490184c200852541101e660581244040800c101e204002054214081d00c0c10b540c41100c0c00750315052014010b2038502d50503404800f4419190b101c04442c480907600510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579374046 1250 579372796 579372881
    0xa1502010609020909060d060b03012909060d030c0309080d0c05060702060702030d150f1e090e0601120809100302180f03030405010c14030a032304051b0301 69
    0x29682e440106004a0044e40c0400e604018510000307102441d0030001c1101e0203102e039000103514030310303140424211104884800724100409240000d01c2c000c00c0c04110a10100312010315441c5815000b05081c14500403000301400800700b6200d04160144000034058041582219008580c51400030904814494141e455024900200b610584041041072040c1495002503203804020012080203000e400d503030400140030300c60b01207283c1200407035000c0104024507400400d40d040144007c00940c0c5640714510141c0f40100c5490410800b040450440e01da44000b200c06c4280c40c1804607040c440d01041c3ca9004603c0700c0c1e920300b9644c0507405814a8516070905828119209092028890591102d694168401d00080180f50b10509d02c07806840d200c1c1504288507204105850310b15000005000003294607054440ca144030850341e00ea110725a10302901c165400d2a80300e1686071040588058610858000d50100795102500129542450308090003010080380c50350582c8400e0900354103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579375296 1250 579374046 579374051
    0x50c0907030c0806130618020a0311070c030f020112020d050901051e0a151d060f2209050c0a0f030506092109010c0206120f1008070302010302070602090a150201 71
    0x51030148a84070700310342550181c40b542020f40381c10040240700c02e0401c107500b40d11500d6003070214980801c2d080c094000c3d9010300c0096140c5820b0b00303010f0286d0f0000f07580c090040c8014098403011031107180c90300f01141d07000f9005846424040c00100d41c04482e8000410000d0700015004883c08015800071b0310985014000b004a6280c90303414203421211b903d04200300c1c0307803480c0c042119194150b01800601c104801756904841c6c0d10081d04d80c007503150381030214509050104124842c11310300c00f1401071103011140b441d899144035a40b0740f640c0d0101240095034550b80c041030390400108114100c001c1078000c02042d9055034510700e8030458003050008454600072030001c43c00144001625594411010901d40b41c864034402d00044280c10803900382d030402500d05120005a01c601000700900c19091107603605900e4100300c000348880b00684491092031045c9000c1000907008290341007034a90918001d80d94401c0750a101005e4090a09441d5000c00d810400107000111408034407685e48181e00203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579376546 1250 579375296 579375301
    0x121e040b160c06110a081b0d020303040b0109050103021011460c0303110a02090103060f05060a0302091504020d02030702010204061806020a021011060702071d010305100902130207050c09 82
    0x201c078410005113280350fa40d804850300380c00081041e005000c040b4140c403d0410640303402130301d151030030829003290300140c1c0002043c003080c4601300c1041c0e40035000d100c0c41030100b9451035001c00d0507000a007101d181008041804a04d140a00340115940c5001c84e001420ba0017030040c40d0300e046001640c1c100c040c0c0d6010100c0c0e00c804102c114a407000c1281d003000000c030101e490340d02c00f030302d000c82c0a0b6008112401089141c80050f034407803020501030f501860307001504c2560080c28500701c0c1d0029000500c1046080c000300010394407521496031245150350b01a000001e40d070f0126003c2c1c0030340313000130b41428004420409200d80c154050b00480b81141c3e19610184030303e0803420108183d0740203460050b00300e0158980075041c0790b44183c550703002602c3c00c101c02498000d8905d060680030f480207001600544420403040c180e041801c0320078641c0c0e0440c4c0105500d035585440da10003c01f02d10030100340c0c42c1c42ca203805550f1407002c40200514030f04015075442650340303003654441000c07419242c4a004100b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579377796 1250 579376546 579376559
    0x4110f09060a030204091a0906041202031201090b0607050f0c100813200409050a021003360203030403060603230c01030506280302030f121e040b160c 66
    0x101802200040c08034a030b010f09580901001c0c0c101c11340150b13250400d900c249209552088402417003041050090042030030039103002d19869001140b00780840d4014000f0385510302464071820f0444441c504009203c01b54000418910300984c0c43c0641107001382d100801c00198007007000d075007008080310740030034926035194241c9807030304c0070340741441e070101c240703441c400019440d41c0000070f40c9500740e540e1250702c00d002000900f56205100100c85540240d681c031011810038101c1840c41c420241020300120500584c840e40c00e40741c144d200c5003114492015403503d11803d4814001103600513094a6440b0340340e04224000e442c9511003154a24246407008000c09070b0003291640d03c480840151110400e03203401103014050160525a0041242105440c40b510480c3c6c00d245031903400c0300c080304041c514010035040c55185005071742c0c030303810458403503185d03410840031610b0215000050484440320f8440c0c1000b58013071604040400c1900184100c001c1c0c00904220108c248070310200103c0030349810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579379046 1250 579377796 579377809
    0xa05011b020a0f0b070219111302030c0a141204030f18050603010612060509070f030b030c03060c031906062106030b0601050c01090501091109070e03120f0c0604110f 73
    0x901c0902040c080d25103c50006060528244d00462a481101c10140135080c088075992100c14007101c128441d04040c041d030b414242c111003050303110240c0c11821403034168202660752048292046c100701d01d030444a40d52050600c2502c030a80910031142c525441c041c5005000d481c002c604800101d061100d9070b0090046800da407100b552001b519083c1035910709101510074404d001d68404000741c42d8940454a52500c0349258407031600c0d581d0f2140c602c0c05082000d02200e81b4003000c58060780141e010300f05036450024006070840c0d0310802c1550f81f6aa1845100d80804881010300125414904000754007540048240484512407400c1500401c0c24158101150300328840100785a00a0001448035805500030b0562035181070004070b1042d40320f03500e90342114015134088541c194a580100d186041180352542d00c030782c0604190130b4290103100000e58174104035422040c1c1500000340c40d4540d8029400f41d4404058103021900b01d4285480e0800c081d0258200880c0034001c0c542e000881c0d4500803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579380296 1250 579379046 579379063
    0x1b030103050a38010510051204030c1505160801120309050f010c1a07090b13050907270302090c09150903070f03081309021810110a05011b02 62
    0xa0020010b1034055038074a41c580000b03200d4103800298494040c8500c00c40d0b10003112850b0360054140400358140030400000055a83e04101044010700c1820081041d00400a4110743c042c14207903003100840c0303041d00c2041d4440040c841403500700014440d01c801703541d02d40c080b005a2911540940e0b0b1321488100d608040d1004090300180d0091001c001c030303041c0f2094940b0110b40600d000c94000c42c3c2c0e03490b0055000207a5007040311030113000c001c000d859684045150007510a00940e47d1500b880d80c610034020347e400c1d00a29100e01d0b00d82000c42d40490149401e040341895a29208414222071143d80e0103101c8103100690250040ca0000f82c800c2034803c1c116031540c040100308241e60103109040000030342103a80c02c96003610842ca00440d010301800c004000a51188446035941d1410101580301080e1070382c031105200e4014001c080790361804400481101009441e0740400e115411811154054911082d10b400e0041070000c0c400d000064100c001204503c244080d20002402c0049a40300b068 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579381546 1250 579380296 579380303
    0x35070206070f0c0902040b12071e0f03020702120a03110105091e030408030310030611030103020918011119081e1305150a0f24050609060d0507081b030103 68
    0x200310080004038044546035000c3d000d6032107041080e0719a009601268040c2e04a404000300108803854010001c0d02c501d82d0180c3d152412002d9110001140300b042041180681e09000074520b0171100706110341c1c10344c0c1500d80c0003003442c0c07441c01040e040e10752111003100c401d0b0000340340c1c030307191aa03c07080c1401201d0090b0580da00030004500070b030403090701140f600750301041180410040024800e001304042c501902504603802c29440c074524100d000c0300e0400b126a454550f00b0300c010000740c0c1e110784500e613106004000400600741184d020038010030010340300102e49140032400564a41404102c040c0180307541e2510030003900c44d03240800012081e0641c101d0503005401c000780c420580c0114003401e15110314200d51102c2c084040002010384200d90812406076100d0b968001c2604501801c401040412981411040340b0300421440749c00c00e0081c03034060200002e1216035034541500b2a04e59100c50102001507040c8028004e1455000303071110342002c01800c21307419100d16400c6c120b138102c0f07a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579382796 1250 579381546 579381559
    0x20102012301090b130203040b2e060e13060305010501090b090402090a23010311041406010806060c070504092102030a0e0f0f1807030e1f02070f350702 67
    0x3034003c0310b001030180c684089401485e525010155603250f80051070055121340680350b402c2ca01044020b800210001a0040501111441c550314902d01483c1c08259031640ca444685400703c04080350341b2000742031740c0b0b000c00c4d4680f00c800802c0c090190711081c148c428002041c0090018442044000141039a020750321464007004102e000e60381d80c0c0107a11807800c0d100100c4005101804c00102003100f644103441e1700036030b401459001d01d081c2c8228505560505400355143c100359000030080300e4010301050081000190740c42c10381404002d80b01c010f00c0300501c1032181d18211704c4e00d020700d03030f211008c00c030014078485008d266510300200981b03600d03140654403008a5400318041200082203241c2c0c0b1508000c080d60480c1c07084d180e50040c4180407168000408503030a2105004080307a8004002500541203c12680c8100c030042c2c900320b49401880341e000d40c0315149400c040c031840506102c01080f078130103c48042045a040f074250111089600d0030074150b1444580441d02910491000070752186 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579384046 1250 579382796 579382799
    0x1526060a1415120a0c031703040f0b0603010204091104080f150f04230a031e300204060c030206100e01050603040f120e041b021f09020d030507020102012301 69
    0x14208400e02c2c07803038480180080000b010849125040c03c130707000d00980711019800710038010700915404508080c409803106078507515082e12228002d694800d40200f0020300a404142190740075010b40e000303018030317860030032007002041840d2855030700c40e11440f80c0302d014454948941000203c3c3c94100b031101000b4229040d603400007051000d0b00020f200f10390341104580d0000c128940201c8001e07941440034010200d0401038140504100619040c095959504000d000405903202441c1c0342c0030070403508001000e172000c0c0004080203201e0340d85103882c1480424005515688428440030b054000d4098442a03202d43c012000210801e0190310080f00e00c2e08010415410050019070f0301a000b604821240101030307a0f0500c12594008101d000903265906109092901c3e20030350110b81c41c40c0344240f4142c461003001079254248643d0b6098010b45c03422909100d001d00703400561403a030340146030480110700b03440c0203420303a0495035003640150310300a003480e4110050a644100c4038502d0007181d855a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579385296 1250 579384046 579384061
    0x31204080319031b05040914070e0607060905190c090203010b0f070302030d050106030e0f0f060601030c090e070216082e090b18060619091526060a14 66
    0x1035024500b030008041c0c1e5843c12130f10b0808480681d4000078215601d103a561440c0c00c0107001903c004403e01d0155000410074400050b400c80d840b01d00d10b20080e6001901e50106040c03940090240d4000a00680141c08015101a085d00d03101c00000c0c1c8507070000b174056600c0301040d8040380824012141d0007001001602c00c90f41e100b20107403500a00c070b0b00c12246010402003000e41075072820303804280800d403294000c00c0d844c941403012603203c140d1500140110402070818a9440c64041c101506140e5200101e080080c07080c012080039220101820314a030500010081d0303912020000e2a01c2a8060030010841403c049100070800341e00000600d41031400c6602413101e084606074903a0001c2d81c0d50340f1140080c0f001da20607440b808500740f0318010b8801c14200701c0c1c28410001c0c1403501ca011036000a0004262045400c2e050310481580001e031440c0402687e41c0107007254100075104d2a070501c0c02c4800e504901c1110f1501d0700305006940c1c3e103407900a4600c043c0d410890112241031a84030001c0d110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579386546 1250 579385296 579385327
    0x90b0405090f0607141c05063c0607080c0a0b0703050105011e2a02090c090a140103020d0504050303060316050114031009021b0c0f0603010b03150901080c0312040803 73
    0x480c0d12a01c104d91070020700103078100d084500a1507411b0859202da0410869141003440d4034030030407000e04500b13145e1410303101411544103d40100d0350b4681842480c0d29941c0c645205a1321020b90003c400d030390711740f0001200c030799501c2c943e40c003141c042c400d00b800901c4048c03203030181d98102c80040e1030b110301c004a101e005c0e4442500500003041086207446003d20048803004600700c81c02600665100310036030f01e006004a1344001401d204411900300007504041d124000610110741c0c03031640780c03100d000c403030001200a4455601030801d05401d1409220501070080001d43c0a600110221400c016600d9190410080c0e10710500780881d00540700350603001580d100440d130284011040200701d9440d64021000c0f0f81060000c8200800c0c2c6076042d4038022400c01100e0122142110340500365481d03080060341d94407050040384104400131010542c00142108402c0740c520000301200115a11460440e83c0d940790038141038424451380c5c105140b8615074908840641e0030320409075140c60419074a5224 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579387796 1250 579386546 579386567
    0x100c030c0614011502011a0616050a0b0c040e060a15050c120c030301030311070302030709020f2701020106091b1107031506141801092301090b0405090f0607 69
    0x110140c41d5514441405031070880507010f403014250f803644016942c10000d0071500e103284440c030803c41540501650f42d80b104103840c050440a5000e2780a00564600740d0708014041390002c1c68104520103010b041d401080280094481210582c09241c0c1e4201c204040c0f441688100d249070851ba191075411a807085000303081c07048a03071003140c0d500c0c00c00a241c1d1b525540024100039280c2c0010005000b05580040c136542c00c4151603005014041c191780000b0b4507120716102d00209540d0004e050444d07108140107481504141c00f05102d404483c1210007011085010b40b4076006518080c0c012581409600c28800c2c0a034ad1a5900f003a140d030881000d1b17a9078400108105124814200b0010008030000890416880d10060129100303190120045c4d50010501c0f50603c80c901c0c20300310805c0c1118034583c490450754801c0740850000c80c000c5005892070781c0700d0080b40030701c200040042040444e0345c000e43c03203403641560200529038032502c07259140d600320000303051903070424004118080d00ca9040c002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579389046 1250 579387796 579387803
    0x50f030a0e100e0603270303040201030b03060f070f030e2407020d1407021c050d030501171c09050316150926100903020d0e03160501030509070e01060504090b100c030c 74
    0x182c0244110b242c40001b40d0804a10b041c06d54070020820046580c14018180114001e80007002c2078207003405005c000340802070a04d010012401848484240320340c202d0440240400150b40a14107400d40341228a203a60031106111840c010115070b030301d440041c002040c0768260780c0b070507222440d0040b811111f9010500581c1e000704010031910b1415480401c240219200300020f1540d884200340c040e083d614168800c0b44036502c17a00c803455a541003c214111000d400c0303450810803508044040da07030200140c101c290140f1400c20140d12174442c003508036066035060311800c0c1003c0c8501104880460450003000000010408400160340300303140c81c1590900341205030b89000004002c0075040307a9420b8401e80060b402494124003607900003440700d44036041a006018010310700f00701e03802100e200e4801c0504041d80e4200181106405100c1e81001e0224070100507515650b9140c020b14030380181c003403556400d207096034144040c070307182d840918420500c0d00c5144400d6002d440580b0000c502480a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579390296 1250 579389046 579389071
    0xf0c0f0f06050f0a0e0703020105032d011d010909020102120a050d29010f08060f06070503030117060a0c09090f020706050403020f1531050f030a0e100e0603 69
    0x1030300041c109010b090701c03403290200341c0480342c90414498030949030b03413120740300558008400600150343d01c28103e03540f00c80d4940c0710f0326054500c01c110b064001c0140000262041058002151030001c4090102d07048074510306c100e00c0d50f620f541e0007401b110716580c8002c0c09030b84100071802140e10303040094a42c000c114181140ad003602000e03828169034842c40c91141c0c142ca500c1288600b0410304102d80c0f80c0c954286071144a04680c0030000c1c102000140410f4452011702108500c2503403514112a0a164410f007529120f503911a01840012609034404032907014220000710000060b01c1103140c203000a940742410140340041c52001000500c100311101d82e001c200e818049050f5020342c5016503c640c0c01801c044074001c20340b0b8181810708500d03000c5403003c40144890705ca84608000310382803c46c9007088200080c0c0240141c1e80f540c5c07a00040443c010f22020b14603070103011001d440000d0480c0c482101041c0240100441a281e09206a002c640e000142020034144840a15408071481001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579391546 1250 579390296 579390323
    0x3040312140a05040e160903110a0b070c050a050d030804061a061305030c1207170309101e0833030102160c0801180f1110050c07060f0c0f 61
    0x41c11465025103030348000b00d040000c0c100482414a600a43e00850305403011500c0100d51030001c10f145418800038003810301d03c6803105481c0e51a00c401600520340c07040415a02c0c41c0525082d016285180b09003031191608010008041c201410000141c2e136040c1d0328417104e584c0da960781c00014484003045c212900f05401c101d08141d19100f0061a1203040329007407500c101c0c9041c003050b19086020203c2c5010b40c4015455042103000010408147c072034440080400718103d02c505c2d440c43c01000c601c181e01040c400d1061000383c6e0031043c41c42c064440040c0c014040b014116094070f910009561400e012031003c6850a40f004005c1c0b090300402c04031040c644400c00f92440007078266040300308440c010400a000308410007523107040900040002c0d2009000081c460104000003101c0300341d018100c4042c08540d0010441c03151010524400e0007007a080c00c0401c0c80c45e000740550080740c4100144c0c482c007040800d807940611002040369025a07221480c158603035407901c54040704a0300441301c104c0201ea8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579392796 1250 579391546 579391577
    0x30f07030201090c060804060605010f020a0206070f02220e03030c030f070e030609030d0b0409020d0209220f0614150105070309030510020712051207032a020d020f0c0303040312 78
    0x201c0b48003c5c040303a5201c242e5810581450003ca581c03581c452410b10040b44458a4140d0300801c0d449040d50301181d041d030b1200403904001e00c441d410480300942c44281d88480ca045035045c28106074080035500ca00f00130a40220007615a40d10003a1100c0113907240600c0000d04025000382c525612a901d458111541c030006004249442c0c3d090307407400304039000440e1a0103411020b200b840d00305a821202400f00d024240c0210701d4604044202078051074074074001603100902c01d00101140b01d03005902d02d91102c414103040000e84106041114011709280c0c09100e071100100920380030302e140c000c894000f102c0513001954650700c401021014000825000004202c085c00558070b1580000030242c2c2c0c803080da117440000012002c082d4400e01800340500d620300100402110750040c42802e00181b40d8005484564200074403d100c1040b001000c000c400300b80b40e000c41d07544d070b10008a400321100040340c00121612107016140443d0141d10502c41040810b41041c1030300860751460800c0b03440c1e0a1000d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579394046 1250 579392796 579392813
    0x3040204050c1c020a021204030b1807081207060f0218090615030406090b01060203180103111c0603030909062306091905270412031503060501050405010b030603030f0703020109 78
    0x3c1c441e40302075400f02c1d100c001e454042c000f442c2400220003140c0c1c80e081c116521080b100d003010304155182c0d4a107024281403090100702141c040c100900860301803c031810800038160b80401d0040700e6250802c501840d07075444034000e03103184201e20106083d0595a050034424148070007481d160f882554012400d4110204500650165016540209000c403039818624403c0b84181d1004d000c640c42003000f407183d50340b40b0f09090340e080024a00800da44a400607a51180d00a0300c3c40425400350b40b0b400343d4143c681e6603018008507846a01c0300d1030f000da503d81121003228214880d8100d103812902581e0702c0c2c2415180d6000580c0c1c0d005041d88d0074500080b001c5403092992051107030180c412080c2c00d208902d001502507000900401003040d042c541d440d041141204054002094601030715486010607001e0b40010b240311442080400c4107a65070b04010014050030b11400d405545072074001b0500040e00000c07240704807005801907180242c0b1180302d0016070721450b4141e045560340c0d1405000184c041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579395296 1250 579394046 579394087
    0x40506010201110715061e0905090705060d020d0e01020a0f0e1912140d0c030c050a050319030e0102090a030206130e18150402010905040f15080a0317060603040204050c 74
    0x4510790300d04035902e0b01ca104103c42e1b9580151a0b001c4894241144500c49a41c41c0c07000e940d0040720101381c0b6142d1180061405e80580c016560007000407405145d0a006507016080214004005000781c80180208030300301c0c459410304000084500d010710340158041d0008258a21000d0084650000d20120800407079440750452420500702c1c1caa80b50a1040700c0780400f07100e580080142890848501000d0001c0806180003400d011404070070344180071007400030500c410b8010382680d90300c0c4c4080d0b00c0d60f140801c4c00c807d0480480c2c80e044880903150014800d0303503c000806001001c1040c19034003040340c150040b404081c9a68880d0320040303520241408014061800c80001c412001c14ad285c0350307414419801e040c0c200b00300864041002607070b40551603908541c3c098400140909210a90801a00340a1030403002d200c5204000201c1d03101c00101000307c18081ea440c010741104c03044d5080b11001058900c598001c2e81800032030054038181d401030740c01c844051113461601d5900c54004200c904003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579396546 1250 579395296 579395303
    0x120e1006030317010b0f03070e01020f0d1e05040b0d020f04090c030911040c02060604020d020d0608030a23070201030b180a0b040b01230a0215090a1e110405060102011107 75
    0x804441c3c044103410004802d014000302001d890900c032003c99103000d14000200100100f040444801d000c6074002d01220308881c0c42070061710703e0000752901c05403458601c8802c1c080c010000d00c4c00300c20303d548910142d50a640920101c81d20b440c100644041c0690807c1309003500a40d8100700014440105108518018030b840c0c40c003207045221030404400366860305030304501860602c40074031a095400304d80598021401c580c0141c5903100c20094100901803089008000c9181850100c2c200d4400030190a03240000d55401041e004008840c824441340c0003040000c040c0e00f801894015070013a00804c240e048050b1803c0d00c0c0d2541d46202d01c0030302900b602c0c0360160960754842500303181840e0003030705e8510100382400ba0b40c944101d41e181c1c100c0364640101540100000c503001035000e10902070224800882ca10b04841800c0c6032100d56110031108100700e41c1c1c2c4103800e0000701010340c001092032042e9040f150003004141000280300241ca8000c0000d81195a07070f0f15420741c1c6025103006402020700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579397796 1250 579396546 579396557
    0x390a030302060603120406210e030c030301080606100f050708071203091103010b03071a0f0316030b0102150414070b040803040f050d020a03020d08040504021c1407120e10060303 78
    0x500606040c180b512110b11611740000030803060040795004080040f50015080c80620b48105c402d00d000010841189611a40c4c0000920004005400800303141030b01c13461400e661080d140c010402c00c80071070508031500850003080c40340620758014005419984c2c01400c66510b081e6203a0703146001545100d22150119035121000c205200030302c28021401c92080c3e00810443d1000000030381c1d50750703040c840d0079080c107000c01400d4941e1010406807084520400071068803402c101d801228a4030700300d03808400080c50001c201c0040d41c80013030b030304500c013408070140001d680300c0b070f11650850500d070003000c2001e03c40c1c01c40004410b00e01000034401440f680001d503844900700140f9818000b4198800e510402903aa1000003503a198150310044070750484401c0000811480c00004600950f0f20155119202003000d0024009846540380c000610100403c804002400c1c0e0702d2204009986070400603070700400102e004110b44c0d0000440820306412103151007119101c0c0001d231180354008800066 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579399046 1250 579397796 579397801
    0x60b040c08010806070305071e14030a2003010513110705060108070815101401091503090210110607080a090c0b0c07060807050703050d0f0906051008390a03030206 72
    0x20b206114080d040b05e540d00d4140301500b0650001400c44107180382c2c0711403008680f0b464284040c081d9801102c0d030010f10300507503207030f103030803640e69005107001200b040404840700c40c2c8400080c034020840c0e06039075009010382c6000b94940044002481ca641c00c6124947e420010100402c504024640c02452540300418589003442c16907401d1a90409a10160103844401e0104c5514140c0000c020345458203451000400e098004071071200c0b4135403064107a180c41c0545884543c0d850381184094500955820401c00351200003116044c1c0000b0f040c03240c2d60060b0740460000c1d4410f01031660020a5900007040800454071030140d02e43c0310342c2c0300c416510000240c006040b002444070100410072070908010320310b009140a407191281e00d00040400c40d00190200c0e0181e50388d80404c0036440855030030081d0003140c0c58000c0040c28152403225044c0d00c00c1c2e40004503120000703694044611860000410490703c0c076103101000c0484e4007201990400062100a10b44a078010540114021b80c018100350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579400296 1250 579399046 579399059
    0x10090c03060302030a1401090804140301180203030a0e13020d050f070e090406090c3c0b04090e100e03040906060824030f03040b12060a0e13060b040c0801 68
    0x6408405014051508140302000581e0f00401c03400da40d242c00000c080d144284030a452401000801e00040c000307040850302113a120714129a005000000350002c011142c2100008400e00300d910310000c0d4194010131480b0030702031040c01401c00549004e01021641c0040c540d2080c142d800c45445c40420311340c0c40041160100302d20590540005c01414000320041c0c140021a030245001030000d40290b88441c654402c205103180114014110320203c0070f8070144500080340e00300f600b54410107612b00301a00501c102e101211a0742c084407040241d0503e00f6161a1854010301403018407001140030344803410f5804440b034080c11020035202c002640d619414440b01c0812030351150401c2c01003004040821600d0f1002102c4242c5003081c00054240300444980068034140c032101b0303503400901000c02d00041c4c051110000d0586030342d9468042c1d00d56903404050001400d40c0b44a281c00c03100164000c22a90300c0f18000c010070a1340600d501151444402c404030b000c0e2070507448135074001080540100303c3d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579401546 1250 579400296 579400301
    0x9041509060605121e042307060906031506050301050d0503070501061215060e22020a0306020301080d020115061112030c1207020d081816030b060307060c1703100302091009 76
    0x8004540580240c0d00240103110861700c00820060170550400c443d51080c50b00040c5440d82c400120048131032594035000024130384946032280030042810903417209040508c2251400c142d5440b42d440d41c0c00c50b845c1404008882c811b61006a0b40e9000401811010a90038060b15016080c98400380640381c10610b0024010800410385110740780c51300d10144045082020550340102e42c40c8400f0003c0380c05078a1b803200d0f4204c1039000a621582d0302d5800010801290040d60407200190281c83c041400264264261901031040c0241c40b4604d02d424050300b8000ca0342c03500301d4407003001200c0042e25550a511506d034020b803030842c0c00301e8020a11904404501703110f0382c0d02c044584080c0401d014840c00140964801821031058801b4513a030822000320100142e06a903041a242524090360fa820050640c20095a485009015184000c95118003e0300c18a0546038030a02e040810301d100e501000c4550800b40541d96010500140000980c0e110044075005070306403542000d040e441c02a60004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579402796 1250 579401546 579401551
    0xd021908090304060c0218090a0506060a0303050313060212100503010b0f1309110607030e040e03030702120a031503050d08060111100b0409021c0b1b0904150906060512 74
    0x3005140410030540040102c2640c048034081e04004030800214030000b442003070341c64850344072904840d040001c0c00c4400240405100d0085003901c506407144801d02921342c0450101901065040010500c0d91002c44c0300101054000c0c0001170901490700d803810b103c190280d03100504002507040c240160301d03080c03141003c8508222a8660244a0f2501045400c0c0101110b01d10180d5918440b005004050034602c5117018001e1200d41d80e840e41c0d14015280c5018070640c03d0065242c02c640c011000f50000440f4012402600185030f410a1105107043c954011020b090405841c0d4654040400750340034520051032103400501f04004800b18000d00640c4020040c41c10041c481b02d40300e00e40c000110b100d0050000206001c5115441f01d00030501a00c4400c1d002074000c1c0c060160354140d17404010f80c00404c03503c900054001da4452080f444c00c24094206090341100042080e11007601c0c00d940075000c15a803da0f50528010745c1c482c0900b080395250790204010500c001038400e03220350b01c0780da03266 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579404046 1250 579402796 579402847
    0x20190b0a0c0801140f04022101050604121401110301031218150507170c01020c0d030504030e0906120f0d0306061716090b040303050a030b040504020907080a0609020d02 74
    0x1507080044001000703101e06114a00c2400110500500151201c1050b01a110000f90040d960f51b0001c031034a208200b2340c00300b0101500400030000c16103141040442d81250940c4600c41c0d1091400c0d01d40304050f414201210541d91769603098855800c41e2000914025401000e0703c0401044440c005043c25800d103586c882034020180081c41070a420300c403e000307c03c18034649035071500c0e40c518000c3e40e103048000e03030b4600140e40400d00003030410054000300b544c00e0b50f4034107030f910030020850180c00745e40301034800030045403080329882904d013020480540d01c0fa03001080c01d0389a5051035481c6083c0b000e41400f1400030741002e50310005035501030150700001c101c6403030407244104008034810070f8460091300c5014101810340c00d11360b4480c0304845102c0640300541919549030350780d18003e811644041e0008010a003851044140c51505205183c8900d80107401e10b90180c0d99524121341038440107080c0c074100e0f583d880c0c0c0490201610720181c103060743d54243c0140c0c2c03442c08019400e00240702d2130910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579405296 1250 579404046 579404051
    0x605030a0c092f090a05030d21090b04060b0102160b07110a080709020c0c09090a1106190305060f06040303021902040906020307020c0906030d0f20190b0a 68
    0x20034011150044851154001070020407076509551076681c000304401020410002810385440803030001e1201c0202110300e0104546d80d03505141c2c036150003000c59804038028120b81e241e102c0301e402c03950b4200315100b800094403502640c1c80240c1d200058a0075286a80d9511b6a10642d580421000101462007150b104007180380803a440e130140f0580304000c0105046511810140c3c4403a082c401c003410b850401d03100116254180d08000390000c111a014a10403070404400f43d060110752240140000700150820315456211401c6c0003070688012508201e0801400030740400d110f00c0e902c5030065559001c038a80c00c00b0000c020070401d07644400c0b0f108080c10002080065000503098004403500c0320450b000400500005008104010300035100d140000b00708491154041919a070468041303a5000d240e484c1c180034150b41e100f03401241ca002c20740d0910001d0030140900e4610350211a464080d40e841e0b602c3c040810700b4440451140240801407058450030001e1041030750b44e0003440b90350b08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579406546 1250 579405296 579405313
    0x323060604020f180a080f0a0c0603050402060a050901090306051e09030a0509010f02070302130b1e0f19080a0f02030d0201150608072006062b111201050415060503 72
    0x6402140f10b8804d0901005000d0704980d20152a46030070007008148482c259030b541802c515295850780b442c401300b141d4281c501500850283d000e8494030380515005000b00b0305041050b2f6094a55a0018942e1410310501000c0040000c04078050320384110300c07a00f18a001040c4030421a10b400c4030141284c00560010300010640e80c4d8400c0588520707a07001d1820040c6c41c00900c0050342050741c0703504040d403c05120b284045008c0519005051500700c1510110743c5170500c00000140691110070456002c400c1000360010751402241b124400250181e0142003140ea0b200191f161011495041359240a5901a542585414480c01804021a000034010f4584401c08004208820300030b44003480004008150090302c603c041d00a0001448448221080b000041a07500c070021100c09208500c440d1000c01410001c0540d12510303281120b07405c8c4140314542d140c1d40410b810780c4d0785640000f50003126500802007402078a0180380100c2c0350240062041c42000c003a12900c1d04864041d40c440c2e0070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579407796 1250 579406546 579406567
    0xc060219080d02090a12050c01110c0114090109080a06060905061503010506071505100e0a0213050d1e0b0f0114011d010e030d090807080f07090c0207032306060402 72
    0x48a505a048000050b900c0c1111800205e40c0d51031038011001110403c0c1c511b4040100005403802d1100c03003605e80704c840d8080c4445865a40d08100f040d0307800104801a01c035080c2140c0c001a00f00c00310305040180500e505c80c0e5115140c43e0044030182c80c05d60701e50408004404951080d90340008003680c0b12030140d0000000d00d15184410321405000b00340c0020301d0000c1c00300d141d20101040c80312910038003882c03c0c0503118a00d101c0003401491024984000402c04164545c400c40e60407044d4049078042051070901080204801c1076800d864103d504400d081c0c00d04c019035900e0f0035152040d000c070212401c080b100c640203020305030496808040c401d22009450b03a0815004048a002134000400740801880101c0b101c200e8a440e01c1d4040c070036001c0300700065801c0503000013a1030380d1004580440b03554a0f40c0c0c40d40d0708950b03151a11650841d030320074888180c1c29000400b41d132074117004460003140d481c1d54003a15158400d458014055400c5401a4101024032040340c0060040780c066007003508424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579409046 1250 579407796 579407813
    0xd1b0c0203030a05070f0f0b0907050402270f03070b0310270b0f0402030a0902040b030102040608040b0c0720030f011e0b1206070c0209091230040c060219 68
    0xf1454414403202103821001c10503070400d40820710b64801d82004010715289002c005804080d101d90010380941440401d96042504c00d5400070b00c04450000c19050103000000e10396000d03400b2103a080703990f03504601101e8400b002040c00402c11000d035690783c0d14080d98001c0d00701c0c03005d41102e044805a0745420030061000781c8042c1c2c49d03004084002540d400c1000008504454203c0100d40190012041000417010781e8031503d00140291001d04c240c445040403d800c134420383c014180401e00950100700071441c0d01003070a038000c083d00070003458050309407940380c40b460240034203440c0701140c15281c404a0400f8003040161406103030081c810b1101507040c071401d181030345c1038010300f135070b0340d11b51642c02c030327907030300350728482c6d091801c000e6078000c1c1080003004251080b144000c1e401805110049041c5800c0090b220f103401c0d112944440c00c0880400001440f00c040081ca40c00e80c01c0e18030504003070000b403021824001c1e0321071a410101c062512801a00300003c401200381403098907948a07000c24100f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579410296 1250 579409046 579409057
    0x70308010e2211010207210321050f0709411f11070f180204030210020a03020f010213050f031f0906060504050702150405120d1b0c020303 61
    0x150419850303952a808003a402842c02d40700c401c450348a85103224180110324070380040c80102039082e00d13070003a141c0300c14501c10101c0121041841107080c19010200340308a88411b680d1401410f0000900c560030b5030a41611020756030403031061000e2061190260304818020001c04240c0814080c0981c00303071103880700c010840c0c5034031414031049a440302d0403441c4003206483c41400403c03007441c2d203c03113a040400010101c00400d01080401c144030a11100015002084810050101e181c00741080c01d40c004041e080301c400e4109a40070f000120059aa42c1c00e001e0364280d80b0783c000c2134403821a060003840c1c00c12041d50030310b082c1d20401c17400c1c012070001c1c916403003990401c2e242150800c083e08003192a107264190119513071a001d0001c50801c0c15140c01105010b800b8100070301101d41c4401c104011181705035044c84c0507a2244800c0d50b8215120004a64800d004405882a400c07003000c603480c044c0d001c2c240d0500c00a5452000078092040e400c00110740c8042480d0071080302089a020984d44d1058 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579411546 1250 579410296 579410309
    0x30a1e080a0e0c041103090706050418150f030803150a120b100801060f08010b0a051008061f210501030308071809180201080a0902060f0d0f180c0b07030801 69
    0x81c0d48920368a0a0b080003080000c1101510070462240c2003600c0010f10340040c0c3e0210043d00480100041c02d6215070192003d550180350708a01d10317604416600010411310f80242e4112004000000b0918811001e000c011070180100982e43d00d407000060110590501000d031054410320001d200d800001501100384590141002c40d440d11061041c1a00ca031f159440b81000c0d6080c6140840c90001c096007040482d07071840002d014400e2800c041104070300860061641000b0040c2c1d020f012148240a90b40c0c0189003c3c020b80030094901000c1c0c000800f8840303040f404100085101142d0002030300c031140808407144010401ca50440da0001e101a0b0094002d004000b54001120b104e620001c3c4407000420325003001300100c00c0174400c1d0820b03520700d000c81030340450103c90014060402d14011440703c158004c04051912462110840450b040400060710045e500c0d00114000001c5210301034100c0364000b03000300d03213406510304040c00803520342003120388503000c0c081040001c1d0003142c2941501c08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579412796 1250 579411546 579411551
    0x10506121209030a02061803151504230a05180307050a02150c060915070503090c100203093723041b08040506060a030812071808030a1e080a 62
    0x402800030b1315080e4000c40103588104000703244611480c4072442e581004409030252160020303c5a00038410040c1124903142d40b43c014035600085113050f034028071b00c41c04000300074411249845001800503c0442d04801e41c140e03200c040c0050b22000070300004030a0070140c019417030510b40d961030613290301030194028042d010752020307000175040d07210680320481150002c81e9202d2030021401c030780d610400c5d880300703800011007000b0a80c080c4c810740460740310f110214020007641800342d00380999161140b65100440c0420310000d0925683d880e031030803595083c8022401e04000c80e41d810074658803280c003508412a140a030400040044a103425175400e0284081040c2001c003c1c0820082d20480281c21000c0a6400300b840c90250003011403400b4500820880d285a6216000e10241040900015041e044144008a40c1344802000d00ba03100c8035528000742c0f419202044100c031481d440d0403060658001240700c4101562001d20200380c1c0481720f0300c1000050204402400640700645490800da4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579414046 1250 579412796 579412807
    0x909031704111914152502030c01020613030302070503040b0304060c120522060b030106170d03020f030f06040e030f120f16050c0106050a0603020c0105061212 70
    0x140104030414501582049604040c5081d01c0c01c54240800800560b1103254900003890542003040b108074140c5103803801c1040040d455008100c291015280326490035003040019041c1c07031110220320f110048140e810601c941245204060a002500c2606811540820208600040340015600c0444d41500700140c1c0c03900107080040c00d620541d0040700070700d1000000d21003044080e90002498a400795910b24a640d0409281020707240d080d281403001c8405c5400c00c1c1400c0461003000704c0514840d103400500c0b0324002c404642512220341c81994440c80002400903214800d10072010002c25074034003185851a80c1d0034070b401303030301000d004500e0040b030400003e82151940c0d0711441c10258804100d81e10390640c1001e001d51940b02c018058032805200303022400c0d00559a1303400e07008084110981028401c41c5004580e16081100308903002d640321000003803240c80d00b05907030000e00b103580ea02580d28200301d041142580c80180440d400b400c8600262061004080741d440450f1b2556a040f80c1d942 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579415296 1250 579414046 579414053
    0x15040501181e17010504020604090f020904090c0e1f1406120f090f01090203060f2814130c03020f0310020310061b11211506090c0c070909 61
    0x307182a4000442c441603020039000d0300e06800d9141411601c0d24400700c2c000c062992029820780d001584c0094201030180000d0080300040d03003003804080c040c040d006042c8145080024181d030304c201000c1c0c1341e40000140034002c884c1710f03615940c1d03c0189010543c1c8803000040300d60800c400300744902c1d00c13801c0b5042e159080e5540d03410115492800b205a0250080c1030017440d42c0701002040d6811b405901c141f003104840d041c018003030360400301d4000340a4280c680d80d254440d503404000900582400c40600400e91001440342050003006082100018400300980d504003c40782010b0840104000e62501c20000600d940182d44c0681c0e50643e881d500c00105000420318004103e031640c0d4140e0b002004110780b81907541c21400848a00360754445030303600410070300c4490100f95080a0100d00c072200d00503815040011000075410302020320741840841c1480564200440408400c02c519080818841140307000c2d5003213038100e5152103000b490040c00d20500342d901c0401d84546696130b0b84034035464013072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579416546 1250 579415296 579415337
    0x11806320a0f020d060602010617030301120609050f0604020901050108040206070204150810090614060a030f020f041410060e011709100c050705010f050f0103030e0d06180201090515040501 83
    0x11030561002c00c1d501e441d1030460103009089030b405a00c00540c40e143e40002c01d90b41c503040300648031100c40007941c0b40d039023042101240207425000a940c0a0340302c030503103000110200f040c500708109100c0540603600b03240c8100008504107074041c0341000044014480503a443d081124032055040343e00140007003040d00448240e8030543d0051000d406004141c19040510340c010f02d0b03045104e0a01000301e000f0b820036040c0b9035401500e0080d04405042802d0001400f0041e2200b41e40340010700c80882c003490340c1c00103070548100706100300c4009001002d100443c0d000f41e05500285c200c604100c030000c0380401c0000d0405542403d030764040004480840c210020601c044212585401800d1004001d18035024060f41d00054003224590b280c0116131800501c5449001d0181408450032003203a4030f1500c02b2030358038441510076076101c2d206050510001e43e982c800c88211040c80a580d003002d190500003d081000d1a900c05409885066803861480c01004126403d4900900b490001c190100e40720041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579417796 1250 579416546 579416561
    0x12130b2118120a171b0d061208070510050103050d050d090f120807030203060105070303091514311b170303270a02041a03011806320a 59
    0x915014810b41c000001c10550020501440b8035110b800c2c0d66100e030386101088003011109840c1800ca038400201020400400400e00d2210007000802c2c002d4807810201c0000d0340303051040714104000240c3e07008100043c42120f5028000b89010812580b55840c2c0c030341c4071074480c83c84500704040020180f845400a0740030903501c941040020003001c0d078514261400c25035102c001d001040d200e00024002600c00c0c0200e82c421201030355407a0500c481a80c0a07000341411986c1203d03d64403450181450380da03a80710300d800140c000c22000071390741032242c0300c00c0d200300e120080c5801013006000300c5c4d4101116550052090b641c09a00c091004210540c601c10342902a0080d02135100e690141145d4a1b9000010b940a66210b6184c407011542d41e803000f042c4491480101c1c4a5a0000f1042001600d001d43c824084e40b0b41012440b041e0140700e00c0005d085504034840d5541152007540800e0030301c4850b2144222103002c400c01c0d03840c1e0002c0a22002054804071030f103070740d8013070300e80d40001d00700a0640c0201c103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579419046 1250 579417796 579417841
    0x406030e031305041e09060e0c22020a0e0d0f060f1401030b040203030405100c1e050a030f030e030c061005010e0d084e07050406080a060812130b21 65
    0x141b0301c18503240000d4201e0440c0e882c00c3d4810408006424582010380c0c00300c07010034040c0715031070886403c0520007035013200c0d00403010f000c0300713103124140341e12504868442184500801d864019142c60034038121808500e07080302c65850400003900c030810400c1606d0543c0c2e000100c4003855500c505c00a0315521498000b682c200704400c485d0f00c80d164222266009180c45642c900c5462007a003e00310002100700e69010744694009250140424000c1c600c25600088a18001c14030310703141021742e03242d42d101c81004601640000e0030443c08252241c036500c090102464001580300341b040004030856603141014240c10f00001e407555074083c1c08034054800070100c1903c41403c030303404400c0000c81c1036851400b030201d5204804c2c5442d0455108007051058404c0d413109410702d400e01208691584004101c001041e50700c000224164004021001588035110b10042c1c1c0c8000c0c0b040c00318690a82d607800a103010784144003101c422f01450154008818428017443c50035680c01042444510882c60400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579420296 1250 579419046 579419051
    0x20d0501060b2703060c07080d09020316060e0901050102120a05090a0e09190507120c050a0906050a0b04080d260703020c12070b07050304080c120406030e031305041e 73
    0x141c0710034841552201a02000f07850f0180d6101101d05264590004440b03d09203000304004107000150740320003074594040c440b0000140c2c42c1c515400b19141040c00071103641958000c031020060300750710404002c801542078071103517819454000041d54808200e41003480403040825402e08585c880c4017568000d0000601c03514840c0e5a89661011f114000c0d181500035010b600c480003488400c000ca140307140ca5020000b0080f4900d4525440fa226605a02c02ca4401340350000001d40c90fa25641c841c00a45010400081c4541c0740004010751110319074886035420005000401c015400814003915105103400d0400710203070496942d6143c6082502c103004003001c800240401c455066010b48a504985000c480402000c1c0310f100c0c1c418040d00e030703001b0400e141140010740843c4c4204003131a04070f446501980d09102910040038100255000c590081c9400440c0400c28254180200c001d81184035014501d8040012880e220b1880d107406100c4c015074640d00d1100c9a030008281440c0c0c0458204c008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579421546 1250 579420296 579420307
    0x18170a14041d0a090b010e1012060b03150f04060c050706140601180308091c0f0b150d080904150914010e060306070f110c09190c0908030403020d0501060b 68
    0x404010724042c1c030940300441010000342c0d155076503110304c55016401c80007102c000c2c0c3c0307811282d00740f1500040035030035162040180011714500da02843c1703545030702c00c440102c1e44080b5402890f00d4a0201c880800d605820350007403014070100507200c03581150f00258041000c0020010a4443d4807400600500503807a1401101c5903402055565008071401d80c0c58074206498000030590500b598000034041038420003024038146006009402240c030381c0c40c4030940e5101c50303032604d54290780020001e840483e01e0400300071101d25509a4000c41400c110f540e48151252900d840e0003a0180d20000c5000d9641c071503aa80c00703110101e441c0030013011144014840070007c0505260080300c00e200786200c5030341c06c102043c418a004500103124914942e140c5d000105010021100c03841482d0410a1078080c7c9201c514882d1284a4014420a502c80106082c006040702d07081c12903002c80b10000c00c12101c2c04c0709101508001c81124100d0350120344c100725600c20f80c203250703004200c140c1c44888901c500140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579422796 1250 579421546 579421559
    0x1b0304030315090e010e010209151c090510180804120c08010608010b0102010b030111070228090222030c06120609020415110706050a2006070201050a18170a1404 71
    0x11380420000740c0028040820210602c4e0300b80e000b004011365010343d210006121001d04440581200b0211400b480000326068103d03038220740c0403560544458003d03001046007450303140241d20f2804984c8071158003454a0351603105050045000d80c50280c0d402061a2041c81150300b0400c02602695008028032650b8289840c002d040c9943d80d64055403d04281440c00e15061040114403440c0e03901c4140b4100d0150f0802000000000f49009120708800c44401c020704108550b401402029200503610391200030400b209403102001820701c0b0200340003d200003a0780d280203508486240c2420000c8030040c0400c603014003050740082030b10300d1007c01e0011708a4409090b6210034086900e0700c00c980e14240050a80b12130190181101148042010382071891040026a0b0166881000e1054400122010604140c0305071007000060707469409001d140740c064850175568901e01c08840c0303c624010360358903500320070b2900d02415800c008502d079030056004031402d240310168030340e109035180c0d1201e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579424046 1250 579422796 579422801
    0x50a05100e12071706010e07031806020d090c0e150603180a0501090215040e0c070311100c200705040e16030305032502250803071103151b030403031509 67
    0x4616006208120070042e4004d0300030800758142c0d8103005640b000ba80d60003000340c0c06880703041801c1c0482403103c3c4610001c9042c4d80b002d4a003e1110550100c0e4603940e40c01c158500b00c6080c5c11840021020703609100405800100e8589007003820b860580d1039654002e095403450300c500d4403100c2c190185004c4c081c1041819401030446074805c942508030390106d508030b454a800b482c042d1080b4104408045540d14030740d50083c144041c0700b03241842489010f0400681002940c01c9050769094480241e030f80c240360403d407940f03945035114001401c0c19111004c440e544240c1449403901131661440c0e10403540005200341c010015135503024000a641d0303890014459807003152200880d130308180a441c14500d02e0f03001d142012240c0d038024402c508161150992a5840e4031032100d05000440c0b00042450341070018058481c0943c80080304021044207142c148020448903030355078011902004620f00c012236804002c07603001180303140c0303907621403405900600c421311140c5000c030048100060703100030a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579425296 1250 579424046 579424049
    0xf01030504050705060c01140c0306060301030314091806010f020309030a1b0302030a050d080c120f06010c0b010b2703280605040b06010e0a0803031306021201030822050a05100e1207 80
    0x4080d1035692a07a009d85503000554043e50312200800040012911030003800039840603c0c0d5540d40750000d800009100c0c5085940718102c29400d00c41045942c0d87c11100e4020000c01c0303070000d149411010400a0b0f04c03100c030b0140041040e41e00158000f0b4844405011401942e405402c540504429086c0240d0740c04241020600103a00b080004035030600303020503a44d911056010f41950341e1a5910030504051004001178108012003a19401180381c0700720f418003c205400c006550303204403014480c030302030f1403440040e2124600d59005d1a252800101c00007904a0003400c2000c0450024041d080c1000410018000c51306200034002032254004209020b50000d072146010030b0702000601170680c1c9680705041254109000189a01510b4454507020358420320005181a03046841074004400030f800a89802001080140504540750280581e00d500507442d54005843c00b0300261a200543c010079018495042c030001d401c1d40541590341c5007000c0188810301e80044107014030360f2800e05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579426546 1250 579425296 579425321
    0x304060806031213050f270702070b2d1902070504050f070905040c17040b04050d1103030c250f06050c04060c060203060315010617060109050f01030504050705060c01 73
    0x843e40b600000d44030303500480e41c08000c4220030301c101516102c2080080104510795039044452904080019401104009518a0340704000006810a080020710f81040c0360051858440d0800c4500c1d10a03121005c1c4002640c003000d052901c9841025a00c1001c0c05082e0033441844800c2921910f07464000c5028010764a064604110640d41e00d05181c0217104265054400304003c2ca805010505141c1c000034008459401c01c00e0105960f00c80000f00a4001c94041c1c1c0c01c4150305040c070080000511400d89840341901c5c00101100c01d021080d0307168030018003403200c03504000a698800d0401000d03c1d28002820030300e6002c600b2541c5c184118651001002242c2c10351400c00010003007080c0070141d6054990655841481c618560b0300c40000f0750000d09020f40c18400c82010000d846108410a4081c20459503000c1082d002104401c4001e40c019000a041c0680008240700a0b180c611400503002c800340780104198495080486c00c0142c41e42200b5000f0100003811000b0000540018291000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579427796 1250 579426546 579426553
    0x40b01211b17150105040510030f0e01050601021e120c0604060f020c070302040e0307060912030c03180b1503070617090a0f080310051309060c020c03100c0908030406080603 76
    0x10351000700c80300c0c0182c2c814205040c05000210b500900c1c0304000c10003446040c104075250503100c000140d00c020354080d03041c0010380c407404401401c910070b000d01580c0ca14420000e20140c12b00c0c2c0000703901c403a002c8100e050500071100c0c844200341403c205c9214851489040f660f51085404009030b01c0e80d41c119020b8403020304190503041c2c8048140308680040001d50050101d0a0959007008058072181050058912040c00b000001c20850302c41e02c80118491126548a1011010003a0550fa0005003503c1030500d005074110380740f040400103407040e5038005e054050980c1d0300244485610401444aa0940300386a000f05516070032442005480d032103010003485d281d0303d65603003544d200903c120040540c6e1401da030200015040f84042c1d03820500d0f0109500210380c0b9440071607030981103203c6003032880d500e03070800400707010b060b00c1600c0d50b040003440a00204220130001c40c0e500c5198141c1580540d9403105500a00b80c4205a40c102070110141506d682e95034800c0002d12084080d10018030901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579429046 1250 579427796 579427841
    0x4061706010c0503090d030504180204230a0302010e0d0c0803043f02130507081902070317060a05030601030807050c0a030c0608070309240c0e0f040b0121 68
    0x41c01007000740070b450360003802503281030040014003490800300e0714110240401404007042190900b04a20700d104415003005803231700d140c210300c04894081190a030000002c03250449070107840e004401015170760203003000d0340044803020116646079100540a001d40116800c003007a03c10f030120051040311441d00302d140d084010480e43c4103010305000340c10302c4246a11008002443c01c203d88981f0b0075400102103810144504070100203940044a0355030018100b00c3c10082030001c0100d1020051b00580821070030400d0ba5900904050401051446c488100d54001140c0380d5803120000c01400000c0c0c00c1d2074055030b48c0c2c5441e102070341003400700702c41d6030107405003040c4541810848082125000b4062003520391500400f55402c08020b000c020406403205540c502062200300d0320181c42c803042044d04450380d14610f50004031604a4480c00400044a4040f0a503540d80c2555500c42101141c000400040030700041e40c01c00f4044045501d950001200e00c003d542003a8804a80613494000100504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579430296 1250 579429046 579429049
    0x30102090a0e040303060b0301080105040c120321021b0102070506090109030503010b0703090f17060609010623070203010903081509060d1b030c0f140628120204061706 74
    0xd005040c22103401c041e141004000c40a01d00000382d40090081c20700054860f1588500010380e07000741c00810b01c036911035050200300440702c0e0f0004018a51001c8842d1b40780826600105240762400301c1c010308682d99521500281016812240307540307000361a00510000801c10ba074040c6d001804103031681d0080c080080d41c0c0b0b80e01806614074969060ba90145182c1c2001e0f01c484461304606000d400f00f180c85070011a94402108140024200600c0d900c00b071010141d0304980303010170050a5600034503c40b801008004c2d0400e00443d8005030490407500c6130403186400c0354650141e6580a9810741c24490307a202411703000700d05c2d1805110303140d0710a41c103c4161800d110303c0c000251440d82d00024024418000b00d15004400720310b05820300071155460382d681d11003000480080d000301c5c0b03000800d4682044022280c0b1a034003500c42c0c065627040e08049440070310811074400c180e0084d02003000503620002e241d00c0ba50036480c00c5201c0c04411905c41c3d07180d440040c040c0855015801c801c0c242c074008511207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579431546 1250 579430296 579430301
    0x6100302041a03060f040c030b0f010e1b0901140d05100305160503100b24040602010b0109080d03050402010203070b1e06041509110708030a050603060105061606020703270e060301 79
    0x2a0880034000b40005d490b440000e07200b4400c014000da928001c41007010001070a8015403600911584d201e070000c4d941080c503085248030018004050307015103448101061303078141d410780b0307100c0809003400030300c8641c0c5800b80c541d64440c040081c42194580800c120598141803501c5054a0207072b0101c400d070640161422000440350700074076626502115000f6030401e048e4004180c0d001c0050708000140c488410519421008040f840b190781030049018400594240f045540c01402440e121107103c3c50601c3c000d40f202e0b9000c0c408020144c9034400182075900030001c0b1490b20b684031016114524001000d1900000b03011090180e414860002c81d10500d068050214454902c03150034401c18a00364003d002807145424460900750240708000201e040c0380d0285100c1c88000ad4046450f140540400d4103210058201c01d105010900c110418440c00220808103c0e80c407820040e911401400d00341c034103004083c1c1940307040c200c030580805615034000d980c10480e00489501101615090105402d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579432796 1250 579431546 579431591
    0xf0c0d020c030a150b120d03050402030c0f0f040e07180603050105010608010e130623010e090708031c180609020112200708070b090604112704140610030204 69
    0x2002884c0000e11004180700d52040190000c01841d14100c201c8442c04a810004c250b41c500000c00e030740b03034204002d40c01c080c404441c1c1d08400302c400c0001d102d1541c001a00b07000c807003080e80e401540e0302d00b07119032080000c101d60030180910100c800380501c0604146406403045c0e002c00c403100d500700400042c155003e608124181c031545840805555100360325040084400d1000f5076080d6100c100d444940211311448622403c040d1881c05007035810319004400c8484090448040341d444010100041c64020096070b880403000c1125075012034400c000040a0840e480d8854940c2c0700201c501810400c82d584011080c078800e0300c94101001401780f12108995455a018030100300c09140d42c80005800002401e086208e0030590f0300b0501c03152142a900300c03046031034045a9010405100038001d002c01c590343e5100007105c1d144110284201d481c80400c43c1c00350001c0083e015403001c1000c000700b006040c1d840b10205812100035183c0292400c04101301481709a024520f40449040d200c070300c2c00b40159 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579434046 1250 579432796 579432803
    0x2090d020904120f050f09040905070506370516060b1c0b060f0a05060705120403060209130b0a0302040522050102190203040b09090c0c070608060924150f0c0d020c030a 74
    0x1f410070140f0001d01002d407402c110115240d005061000c03c1540e2144003519110415844d0100b119401d10003856400082d041c4c202542c017980c00b0187c4030f45030302c070007250b21003d00248140b085006520b080b40143c0880349410380d01c541001031180e03204000405020041d03006400e00c01480e2982014002c4ea40e5070008015005211100c043c04182410341c020980b89100d82c00b15282c40c040b1405c595800e40140c1c0003124190703000504c1d10014030b0900358030308540400000410003440d412002802610a40c070000703004a8a401c001030301004001450000041450300d002d101c5102440c1841c000e500c00340a40303c0d1008503100c0c940c007261001098a0540300703219007141c0307401761160401014540040927820030600800198100102c14031400e0010403407901e9001442c1040001c00150079801040b2840d00c1d428441c1e40116080c0045050420f24000e403401c50102d40340c0c0314003c0140c403803214940800140020203c06503100003030904100160b0794251988001030408050702d170507401d80060b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579435296 1250 579434046 579434077
    0x13050d050c12070906030507080105010e0c0d18050102130f080a03020604061805071d01061e030902120a0b010518010e010911130603021e160602090d020904120f05 72
    0x40c61814075801d400c80403030b0050112240c45a40c0c090714800e940e6150011582600125030401c1000c4d002d00980d40504103030900741c9690300d840701c0d48002500861045c950721a0f203880900c03606a0f541c040d00e2281c0b982080007503540300c080000c24400c44403030b03200d291055841e903000010000408560b5001003581580a08120340300d0b91684800f030424013000d0140ca08580030030500054040028200420b9010710746204800480181c1d0361079030059006170280814000302d5601341050160500c518503450900141044160000c1190411800380030395940c4a60707c17800044c0038000405a040300c1c0100c6190425220394041502201420b11941c03961804100c01840040b420342c100b5004001081501c0e401c0c1410902c6200108072a94060030100b90f001035501400c07060074030700c0c2400030b0080403142d282c011044203100c220701c08840050b212982c0071a07908055541c070311180510a40007440400203080508286203005003480c00800440d24030f00982d04000c0c01141600e417540e041a010707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579436546 1250 579435296 579435313
    0x1415180c21010620011407020610050109060f0f12110903071e051203070c17011505060a1808010606170907030c030f03030905010e0c0a06023d02030c13050d05 70
    0x604d8840c40103039034912415522042ca0010030a0304c1ca80303d43c46240039038020015414401c0d9001034030005908150704010150b0014003030590000250780c1049100e00e0045203501070031000f00d6401000300c200d0620356080515031150070030500b0103884030349021015510300355662041421401c02403164040080007100003088180781c02c240081502c0f4146054914054041d92400806d020310781180a500b180d58070320f5140218248549560490728050045056051800181031400342c0c100420030041c0c500e9440003001c1080c00100000d1403040003d00095884102c080c1042c072065525220040d80000001c02c011000100c1204030380e00620310440860468403031240c0ca050500041e800d050f11486c6000004600348070340c04040154002500f08900c140f42000b6600c2d1142e4008001c650200827504032420520b501c0e410749012001c080340268101020020005040354001c04d0300510101c1004280b02d0208000d04261602140c00c1820751340b41c00030003e002032a1400035050354096070031b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579437796 1250 579436546 579436577
    0x120a0f0b010e1804050a12020d0e0f210705030712110d3503090c0102060717010e040201021204060504030209010909150c0203040f0308040f08011415180c210106 71
    0xb0040c0c000e0b00030811b5900580c400d03124031604456003850340f0016800341c080c0703008480d845013260000c000304440b13640b0503048039070000e0f0f1911501400b03d0451540d442d80300040380f41c2084404003d000140966100070b644545201030300c00c26020640e405568001a1000c505e803921488030050780c0204c0c81040030b90700c28041040c10161a10b0700980c4507076031903c094681c074500081c5109045c48801000103010035000203060540c00340c8450140720400103840e5940d13050f25141c905560140040c10541e5032903000407890041010303118100c00c0000940822042c1e80b02000300309a0380266000c42c9a640d079001c0e00d2040b550500006089d031501c21604201010580d04504410703c00c07403040f2070404d80c507003216488404140c0d00c11a4055400201088a803910782071078401070582ca0020456202450b001e040001e100500c5805115211000441541c0c2c03600b0300c502510315400d505c3c8080e89800c10383e020480e4060b2486040074440000c88203006801c0103a564140d81c42d62f03035070456501d190388 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579439046 1250 579437796 579437839
    0x315060c2303310b03090d08370203010f0e06030d1409130e030702090907060f050c12030f22030e040f02091804020a0602210708120a0f0b010e 63
    0x202266183d03c029000c1400b140e085507001a001c284426075490400c2d4408a240005540300e24007808603407820040d503400ca003c100300d2110340741407806803082c80d0b6130201c0120000340c910420f09144040004205000c1c0506407030103540701c5140124050320b4031810140d403680001418800548034520b0140003151400c09030640c100040d141c0101203011914000c2034178030940510744294000f182903401d51900c0307034025402561072005403225034140300c0d000703200f100343c1340842c2c080c050300013440000700038200b100c0c2c2d000e4642c0c0b5810945030300300710b901c1c003280f98003d5600c45002d01c0c0701c0c450080b409510f81c2d040500254182c40d40c0040c2424501032001520413000e21554003a820b100750748050f22280d10710310300f854030058240d40c0c51800c0d204100d00031883e0340040003103610840500c0c10f400307101101c0100c000342501d161034440c4103507d8000f8052040c0c41444402c05914800d1001e074140d1030b04030b0038002e03003115003d02240d502c07100110b50216520752007652010140ca0141c24110050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579440296 1250 579439046 579439087
    0x10030605150408071a0903011a1305040c0e0c0f07060605210d0305070c080705011d0708030a120b100c0227041211150108010617060609070315060c2303 67
    0x240c503903600300808980060b00311102c4404c040001c0704007040c9c020030307481c001d02c1081d41908110380c1007003142059210b03c0c00281d0240aa0402e240c500000300b83c03032845000c1580d8580c0b2600304296039a10292800101038801403081c1402014045050090a40d000802204507100c2e030740286502405210210080c2001504010902071041e0800000c600c100000300f44c11030080b800814804111001403c000d4052081440e16401a581c01d01507040041b04590040034145010b0303004154240510000b8018502001e07406000c4980600700306e50088a03500140740200e031901c001c01002c0078588404031000000340c8034000f50100103000540310306c0341405002640c2c5400b0394500c80c0030803810302d0003d0310540d469826480000402900900340910005407441d0655032a10b0509001815030700c0902a101ca44555180400503000603c03d43c0070400d030035001901442525075600014120301510042902c1c500c010a0a122008030b8a2901c52421f00e034500c0114501103440c050018401c090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579441546 1250 579440296 579440339
    0x50d140307030c0908031b060105031f15050604181b091206092a060c020f24161406040c05100e130b01180608060402090f1003060515040807 62
    0x130070301c0201e115501000949926071111032900b07003050030382100318070b000c1051740500d00c29408130300a00c440d4481041041c90803a00e1040210b0400c10400c0c0c20305525030b0507001103801c10f40100340018a40c0c220b020030004480c400710308100b44030760300701182142000100c10030041801d042040040807801301c04490064040d1200244002081e92502d004030030b4107420791941d5040c0c0342c0b14241c030b1a02035031640043c00300d41030600b241242603010070f2040400362050780c4512040d0210820310801040100305c80910000d8060b940d048160003402c110414140c00d9a41c01880c8411410424000403100d01940c2c21002d01c01460303240c00100f115003000080c403002048000b01130142207440c0c50102a8100d45011004114608400c1c001000760f05504841240c400000780208015a04450303400c2d0401c00070f4030003598804414012030004c0d00c1d00440340c0c0e04803a50ba48030b11304450b4940d00c442c040d51001ca0f1080c40300e101ca140c0030b0001d4025030052129541002004102d01058070842a507001139 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579442796 1250 579441546 579441557
    0x60f0914130f0f050603241302060d0606020706091a160305040905010609060f050306010806100509090a02190c05060a0c090b0c0a0c09060305031b0106120f050d140307030c 76
    0x840300600b0654410101d03241a50f0340f100e0a0082d1840c041c08614403641d2103d91001040c9907030303c03202003030b44005407100381000c0c4031010000940d1103034002c6840a1401c10424070001e42c4d40c1100a5503002d4504c02d1308000780d0940008940c03211034040094081d24544406401c002e8444610141d00e227582c0c6044051100030003000a081c440c03400380600a180a0b00c1d2640725038940721003d011000150800d10030000204100072282e0b070070544454200f01c0a907403051002c8104941590984175000201ea0302010030020010700c9512900141827001508400d240001042c0c81c040d41c0d4064805001442074000f00c001420100d000e17131281d011041d44d4904141c0c015901c010f030001c00e5200080c42c0b4440e421120700c582c00d0007a0007035203000900c4a420204180e03031a40d12040d44902526a10072100c101070520701065810940100014104190840c61111000e00e00b14400e000699800c94041c05040d0a005071207008a0003c1e00c200065201d0515650b1084030450080c21b000c4842c206115 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579444046 1250 579442796 579442811
    0x11e09020a0c12030b0f0111060f0405102a020c0307060302090a050d05101d03070201031e0c020d08070c031b0203071a070c0b07020a0308130b0f0301060f091413 71
    0x58035516031082e44182070720f00090703020001e406d21042d00c080c1c03030005040c03001d4004501030400300010401da002040742a20b1001c1c1e10380b458005d0078440700749950b2952038200350700c8030211076404900f445104150020740440301118803081c0e03202c40e1307040850b0303506030003603803041040c41c0c040e400502000e107004000d4813001da2031348000741001091440a65541e44840c284011b46c03c0302d441002d004007032801e440c525010080054075528421080c000b030425488903040410b0f40640e00c844034841c2c110020601034529010002540c4440c0e8604a070005400d07080032442c014010b400c000100c40d0035a03501c101c40400400c201e1300c4030030300101c02c98043c891280002260b5800b11705078640146440111550386105003051040400030740c201030007107903081180c100140c0d03800d42c00404503a071146a49072180d4001c02e10380011491a408058480d000191800101c0896001036040e85e000d921a0080d0f407910341400c0f104089103018040d4042c1048060400520b8003410501c10003000d000c0114000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579445296 1250 579444046 579444053
    0xe0a0b090c09120a0203030d180f050a030f050c060a1a0a180605010302030c033403050a0c020f100506040b0a08060403020111070f1e020d03090e011e09020a0c 70
    0x344100c581610201d80418440c01c64640003181074107401c9070b04010305800703003141c0000340c4038031450f6061440541c0d10000c3c114840440200b40207400d401600c80d56075207100307091080d00c0e0789c110391084000501c1a14001c5800340039005031003c580d2000000d00d155601e078001d100007007610b4000700058142010680d80709940309451a000340003884010b48841d1009c4003840d0544849800643c18107006004000790007214406403540300d89059000d911558039043c191002d0039102e000c0000940c0c0b5444001c41c1c094240d084140109038a5100700145281001c007245c82d5000821100c020703030011101c6006445c1103400042e04680000c000040804007840001c0c500c55541c0c3c1300358a035030070a00800050640a100e00f0780841408018070345001507561b140ca04080e000a4010051007003910f110103e01803425809198650103007420b807181942d82809004402140704440c00040c42a0021801e4182c20343c0315480941c200c62031420007820a0a4000a508511044000c100300d00d441303031010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579446546 1250 579445296 579445309
    0x23181f03060c021e01060b031f0b040905090c010e011b0303020910030b040c2a080f070b0a0c0207052d04090807150b090711010902060408011d070803040e0a0b 70
    0x142842d81d0000e0030400c0c0b030383c82104903444000e6801038559142c4042000b45065001c22617910041c560203d5000c01c0514070000204540e540000900b00d01c049000716a02e141c650003240079044140481e82c0c00483da20044417070601d903000301070025050141e6003028000c2070004403017951117410050706180713840c0045a0f440c00c0c00c01803080020303200c0f0f40c030b0149802c103031048001c010301070310700102c0d20711070085007280c00c200c0300507500c880b0740448a1140500c401c21041e03414100401c0015603036803205060914620005071030b040c28181c0f9001d07599245a0002800100b11000070304890030381d40411402c050104013240e1500c0741c416400e01039004558840c8542c0321007504c82d801d420748404440c10000021414100c41031090341c58080920020f80d901751425500c035038540381c941414000e00240c180980800e400007900500085004075a50340190008002450b501d06076544a4056184e40e6981d00344070300c61081960030410003030050100300582c4690114090700c0126845100342c012611 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579447796 1250 579446546 579446561
    0xf061b0c0308090c010e010c0f02040f0207050d2f0a1502031b0403031709160b03011703090904060506060705070303030615020a11190f23181f0306 65
    0x810801561003015007000b480c980181c211402080408058000a0403440814409a05120400d1700c040200032003520004843c513405081480b244115419000c060b4010b1401204c40e03000b40c0c42c80f06455031044501c80250070fa9041c43d5804184180d01074042c0081d07544030390600c1d0003120740c01c07808200c4002419088104100300180e9a24181502152900e034070401a1501c400c1040100042640040a10140c0c0311180d101b10050700d888a445150010810078044c102469502c0041c8054cc0c00014504030b43d1514614400071542c02d50741601ca120b50310740603078030040c4000420045419030f4811340e070205010f003e02d844c018280d00d80524161995100301d0000b61900400d00100c54009210820754500d4001400c50f0200d550341d1040e482a01818680564111202200c2d07000e4001c1781100286001110070324415141c0d140760b0030303d1503480c0d000200000d10000014042c100a042d903000c0c1c0c030008a45507225254019004000c00d11a810000c06030010341d0088040b4896101d041d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579449046 1250 579447796 579447851
    0x30e120a1e0303050609040c051009150e0f0301060b0d020a030905030d020c0705120d23070c03050c0d0f03050703030f060e04050f0304060f080c0d060e0a0b0607030c0f06 75
    0x4030300007407516004041c2c0d01c00a22003030058814105020000e9001d00d011015a241141e16011302c0c400340c401140c50303665030307404461080840324244c1d4240345c0103200303c8828001a10404101e2503100281400d0340d42c02d02c10032000c8502000041c40310b81b400c0d80581500e00080c900828551051740365589103800c1400309a040f40e41c00a4076458a81081050000510042e180d6009508031100040c0e120b0240c030b03200009122441465034010042e0b8507500c0c00e80010307000c0b142e4888800341082120076079540011100c0f0f106081020380309140c14210854259880002d5000c040d40d6990102c1c1c251f0480203084042c944c5824040d844445140601c0001e03013058029102186000d05125140c11264a42610507400c100701c1840840c0e401440c44940a00a0428040c03544941007034501c180300c0c9401d8440302c907140c1030780801c2c00c1c03c29601c0c45001e0340d000002407020915140800802d1300c642040100810019040790001640031818100640e008540001c3c01004150751140c003521241400c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579450296 1250 579449046 579449093
    0xc0708031308010b0103180201031802060a0f09080606030c06071707120e0409030905040c111b0111120910110109050d1418061b191509030e120a 64
    0x40c004180d00b4030404212244c246000e001c104210554070a084c0c40c509400390425480350720780c0c1e0340011140f503200022540901015130340c20f50300800926008065000340700240001d03000007000240010701074060075004010300642190314040202030742c4809070869508000700d0041010040384005008001d010b8000403803440308200000b417005900062851090745045100004a5031100c0c420007944d00945000501030f41c0d107201a9031174100c210500320342d07120340c00020340d0042c0030704a9848810000c1e2115170381e11080001d115298000f80f400710440300402c3c003081c40f107864070701c0b09013190104900741002c458005030303402400d555242c48145c450340e001c60207568840c1d50100a0f02d241007000010a07040c42a8003200050000d410100c1e94860385006c00c144800144103030603004d1401d01f00044a04803418102c081076038114882d4169440891550781d01c1c4150658040d940619505666041d000b089150403c0003d507a07149204607107104e00423401000034000c125141946000c6100c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579451546 1250 579450296 579450299
    0x4050d0507091a040e1b0f040b030a12180303050a140c010e0a020906010311040902030c091008060306060103020a1b051c05030609100608010605030618040803071101061404020c07080313 82
    0x4d000a881104106180552110071026103500c001d15000320240800c49502100c0c01c00000000c0207050002941641340c00382d46004010030075441c52a4150012a48452150050000041c44c81403164440030780410010012006590302c100707064100035022240050804401c011f0f03480c00c40e51000e100390310551241d1b1000055140c15000603a1265090be428018500060900c0919000c2c0b4441d0301c0c600c40d00800890208009101a034801500c06440e048020b11107110081203c070040d25114001e000b03a201091440d4402e0084602c4101c080d1a5041231258008428a481000c0c080030742e0b1138000c5000040310500e000c206400403400554901c0d80300e0400b14100310640001074810460341c014070b2020010b041e004814681150554182144c407607035058080b80440c00c50032010940c2c004140704001c1081f901101a40c060003655803000b008515182c00c4500701e644a006200440213218000141c51615400030304900890f041078820159441450500d9038108583d00380080041440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579452796 1250 579451546 579451549
    0x310507030612200301020306030304030201032c070e01050f011709071701060612090c06050d02070f0c03110405060a290d32010b0702030316061b020c0604050d0507091a 74
    0xa20030840001310021407460030071b400041d40e41d00c40c92000034180354541d5905200082110800c2114007a4001c102302d02a0b00704103540d454941d14043d8081c51840080081801d040c0500108101035041c1c666440a4070a142803011071040101007400a2182d42804102d4003402c421a614030014400082001c43c24401d0141815001c8081041ca035490444c001000c00c146410315021143e2a0900700e66990b404003405d00039205140000d044030582018541c104488400300c1000c490081448843e1408a281040107480050b65680d50000080c0414000c54940811031b810300701040c02d40444920074a082581c6903082400d40c404541e5a880080c006482c0c69040c415015213005400d41c103060981020041c1c3e0b48042c02260000f00c0041382c0c80045480030021100b04411503240c0500518517468110041d01500461481c014401444441c20b68000101d01500001c002c00d942d00349802c1105200050000b0b40003940c061064000015504a8500c1041c3d6001120710101041e054420f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579454046 1250 579452796 579452843
    0x6060d0e010e0d0206040f110d0501110405040501090209150313020a030b0f0f0c0301150309020913140f031608130b28020d030903050c031305310507030612 69
    0x140f80d41550030072020000069040c2d14100c01040d40302e94810f0f41c83c1d4094010032030008401e82c00400540c41d01414481c040ba200020b0021108101c1e004d20281e80c0303600c02841680950840d5507008a85081501d420b80410360282d030340103200145d01001a0032503000500f04800c01d600940b075402000c0103001d44206040c1c0f4060303025009942c80c0580d41041c98943c2d0440c403051013401c1c583c0410b003c40f68506440385e0065107105400600401450500349940b941040c82e003407003254010303140c0d80304c2082c1c208041740114a900040c3c0185050220000f8001c02d140e01500c01120003d0007048a030200d481c3d02406034025111429071350b6250350840c00701962b00340044001c203818900a80017030000550004a00349c0040b00b61402103007800c0f0a150654141c0907800c06401a8080851080c1030b007144d0300c0d01d240440e141250582d9294100c152003200c0c0d601e0960100414401c2501d9010603c0090703048650001c0c01342c600016a00eaa4819904481169100449801188040d4400c1d91546170 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579455296 1250 579454046 579454063
    0x2070819030902060d0507021203010b0d0c1b06020d090602040609060e030601030f08131511010f06120308040f020306180f060c041e0e0c0405010206151806060d0e010e 74
    0x3420704029120b40760300092003901480c008040c1d46a01c6400040c2114820300000b101011405070803a240d5845420a1804c0c1e00f00307a0015192615003400000c400d80700d51555020f0710507000620f0188011a00c0d10700c06503108a4001d0030f1180c40b00b0100340000d10303e10040008025941da1118424100f40004102a04405140d0b12075071200e00140302203543e8404032000d4a0748502c0542e80d80b2010b08050380081c0d410303030009a004508881103000c26402810075846150075030000c114807a01c02c42c00310100e808501030b426501d48000c8180340000e00410040e41c10902510800000b810f0542c0082c1c81c05000321184940902444107180111a00300b1981800010107401b800b140d180c03017880c000380c90140e44100c2c954030740c90500001700702c03101901d8480a841c9400b0200a14900442180c2c1a54814840d00703005101d074500040c1512203850340743c0c400c0300c80248003075192124080c001388085c1e8060181caa021204100795001d0700502d104e206c83c01c107000b13030011840e02a0075110f207040034600d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579456546 1250 579455296 579455347
    0x603050d02030903151603050a090b01031112060c030114180106020102071104050402032d01140601180807050105130e07120b01050a0206131a1003050c01110d0c060f020708 76
    0x10305d0b080c425101e1010304003000b40604d5203800038865580e003004102900b010352010b040c400c0004004400d000300e100c01e941001d03c00741c03406540001c42d804d01b1581c2b420202e0346050702041c01d00c0103200280c06039000401c410b1004283c101c90240c01d164440054000380d01c0300c00580e5000610208000c900307184806900c10488040100d0315003030f001310b0784908a000c040c0c09900c05c4281030608034806650f80750943c0078140001c0210b540b071400501e4020400f5105a808204425400b000400512401c2030513500c01c40301624840d4500001034502e1b800404041040550303004000c02c0400702ca9003400c3c401d00c0e06585422030000d20020f40c4044a4424500718100a020011040410f80004040b0382040002d0603881c40501c46080c0354408080f8080b114800309a400180080010303000c1110040c0c1c1e0103130050b10380ca040c0c0e40005550f0315440e1844450103400c44404006013a000d108103200c428026540450744070501e250f18000c82e880b84034116800500450310881048140c5c0c1c1301c0c41d00e4601d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579457796 1250 579456546 579456583
    0x150705040311220c0203120f0103032307080c011e0b061803150c0d0c020607091203020c030105010b180303070f020d140610060e030c06040b0d0603050d02030903 71
    0x454550400700100c0707150650060a903003100003c54814103080700e40f0708281c010304202c0061540c1c0001c0d107962001001c03550569600012030302d50041c2030b245a0480e54075444903803401c118a9000c141d41d440421200c1c54a040170301000005c140d0748001032500203040400020304a00f400415540103403c4080e10300070318a04031611005846031403ca0b0071b140c201100340031a00c680200028640090045080c00712a41d040910210020030ba01902c131041d4164406d00814461440890362840c3c216a21000992080010894503200111010f4450b0092040d1464515804003080c00e5400a80c042d02000c800052040d01100340c0040c4074485500880266140810580b2060600c406600c2d002e0304c65880c4805074030402104035000140322036050103403822403601144d030400d0030800d072040c40c010864035030300e001103858080f44040e41541c004001908060a25103a580150000301803100030319034610000c400f00d50108200040d508990340107560304c101d000141801d00c040701d18078140022 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579459046 1250 579457796 579457799
    0x406200d1e020115050d02221413020a0501030506010509040c050a020f06010e011401120c0314060f1005181804031407050a08090f12012007030203071b0308040815070504 75
    0x1180c06540c4d070894004460020300a805400010074404180c0c002c84202d2411040706000c0d404a9001104010320b0401c03907c2c0d65980d030010100010120120003940b020284000707004079802640400e0b040141890064207000711880460100d80144c0020004101d0100e41c03c00c0c955810000c520401d08010044c241652401070003a443c1c06040c000c0c09000c1580a1000106901c2040e86441d046c0a242050050b01d81c07090014000f407011101d2401154808400550709050a802c4e041e1011f0002c1c000081620103d08201c909170420010752001c43c0500c0e120084640e512503a0414080840b106100c10b41464a8060401404074450b80b14940c2c0a01c101000300720013051600829400000c11030390b614400c00010581001c0346d0b2050391150001c0401411040c055100e40411034590030200304480c4203205caa0301d9409207110080040e4002c001c2c0c400007900005649581d003501803240340515407203039508000c6410607009032400340e1008021070703040310482e206541c01c0b00d01030030100d00c3c06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579460296 1250 579459046 579459071
    0x21b0f0f0a030e1212030705030a110403020d0204050c1303051509070305030a18090f1d0303150415050402030f1e10090218130906050a020f0406200d1e0201 69
    0x405020300041c8a130300c00340c0d440b0030000010710440ca00841d00000c00d65032842c2c080c601510303d07003080d10390402d414545400800201129001c8074140c07a001000003044103440d27800c00018000040c1942038941007800365421480b608540e0202551145001c0c0502401c40000800d40300c10060602c2000d52114100300003140000c0122442c19000749001c002013100465003030070f4281d040d403203c5040c6103016003016034501c0320b602c581e0902d00e080e02600f448441c050502d55490205540710780030701c1d080344400302092501d81c2c050305001c80040302e010303281551100024100e800c100c0e680c00840c01c4200c10480f20503107010621920902d500700781c0000b82840e40c1404002c110070302800700c0b45c40d4002905266070141e038003204814840141750001007221076501c80003420000030300701d640394180340225034a07003030038000c0e1920040301212140c107044c41e08c0011a107401e20b011400d00c0700c00343c010030082600c0d004e1104440c0d445590f100e90484c2042d09655841190f00b100c000710440e4174082103030064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 579461546 1250 579460296 579460307
    0x11060304030f12061a09190602030a110109080a030213060201050f15041b3f0903051e031918022107140f01091404050703021b0f0f0a03 60
    0x500e4051404861000d0f56844640042003070b0740021a080030b40c2d8080b00c0d889003070b82004105851041d1007555003800c01000910005895004020160b0418007400f41464800c0041c0814650900004910381c08252038085c51681f00c40400000203400141c0641c885586481103030040074240300070061481d000410030340c20000540250483c40205003d29103541d50340d0004400040304c000c2e18020548202d6000c0c25078800c42040c0d400d00e02280031090001c001d03004034410031040c0e240c00b1107002c804680c100401400c521608800340207060200941440c0407400d0a41c0255080c00704596a007451a45500e40d0043c405030000311a0819007448000b0380030b60000c0171255815101d1186003001c002c1543c06110700680c51004510540320f00103a082005441c00b04031030030940300c440604022400441c4c1ca07241a01551424480d00134030b0b81c03c18101a48040c0d8402250b180040c00d01030103000c5510340290a4107003000d00e510940b900031b42c01d1414440f0307540180e41c4200900340c0a0155501610 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 579462796 1250 579461546 579461567
    0x91f08041e050607030c0f020a02011b1403030a02040f0f0321020c030f030d0e060f04031407080408010902041104050a0501080603030f2101060c0c1401020a020301060b071106030403 80
    0xd00125440c9044207000038200060040d5002c002e4075803600d40780360020010000e5502c2c0d1b10024204070300c100c00690000c40c4515140790107070354a03195000d90745138030f82980ea46550125040c158a48055605a1050001d540150f0003009c002d69200d150a60803a0b12500780e411405001c06015004c00004800010140c2c0241c1003500c002c2e02e130360f007140c000d90a140b541880302d9014001c0240102d00b44002000802d140c80c050303d82040b1818039051050303030710801140e0300c2808200901c040703008680202c080d4102d014140201518003200f0b5500c0943c00c1d0411f03403101180e40e4440356408114505030088455203000503403102e00705440c250004002070501d10030303503060000c0d002c00316815850500842e080b9201d540c6000b41d6815240740c0c114410b0503101e06401e001e610301800440d03014842ea010002260308050030540003030030715011010308081d07100b2060541c0f0900a9041c0162020301a4000500700100d4281d00c07414941041e03034194102410052154134108200000203801c00d801c0c01d07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 579464046 1250 579462796 579462803
    0x1205120f0418060e13150203040206090d1e140c0f030c0607021908060610110a030f1e030501080706090806010306050402060c12030601030e030705070b0319060b091f0804 75
    0x7014070b8030802500050030180c12000045140b141042000401110b81c0c5400c14441d004002003014000c400c403040740019600258005c008011040a40c5000d200f18010b02c0c0c0240110f545c454a1510441017002a80c0800c68038011407039008100501c0501040b001c1541c1500c505903140c40c03c0d00001e40f02d405581546110350008a07010040d500c500900c800ca103000c008151303407003d45465115540ea40d084400c244075406c00e1071180d0320340d031080700e80034145105030b801411650440c0e42c0949109072105ca545013003241020306501080001226a4550342007a2400a0300d07505242c9039504105940c0c202909001040400704045c5500003a4541100d8000f1000140c5865074400103c40b0310440741820100d110304003000104100c2d800c0118000e030426241004400080a9041d4503405050030140007500700030b00400c1400520001503501042080c3c00554a041b001005401c885040d08682c0301c0860100d005101400c0a100461051881d1550001250f004004c02043c010700240b004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 579465296 1250 579464046 579464069
    0x7080a0e0c09180f0a0501051003081611090a050708010f03020306013812010e04020d0f0303020d0c031a041407110c04020703031e0e03040308160605011205120f04 72
    0x8014440f50580f061000300a03d0a13154a4141000100d40c3c4214484003603c095281002055581250303624100c21298804031481c03c010710000401488104803800f03440403007691185c05c006503221360b20f00b841040844130009260400000041008005810601c00b012401000b44050f030343c00100036046400e00c2550a90b0400301c866404041742101c02001e1413651200b56456a00070036401600d44d090301029040f42581c0e0b2850b100030108016940a9042101e08141e4008500100001540d0a0183c1800340c0b0700070081d6441000c541e40031183c032000a83d90280d0281171016502c0c1c00c0c5c9054811101031050b40700360640301c00a0a00a400340c02840304070581241e183c4001d100c3d0401801004004646641d890b04001c0c000d010100071442004000a0120a6920720b5125160340144040015402e180c11540d482d0031a0707000414464890311b0b06140c03003000801c01c2c09034074040c082c0300000c980c400c0c85929040b03240c205c560082070804070051207915001e01403241641c00300c03a03210201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 579466546 1250 579465296 579465301
    0x41101080606220f03050a140309060a05130f0906061b0305090d17070311251e09051005030616020d260108030c2a06031b0c0607080a0e0c09 62
    0x3d07500c46a1158458440702c0c034007140000502038003043d0003106e42e0003a41c0d0b00c00703c944030640c16900da01c28101002d500c45400d120319248a40f1600107400c5a00e071805c0505c100035207070081300011820700e50107074a404c1d41301c42d8140201640b001800407035961a550080c1385104680d005403581c0220342c110f45c001c089440302003007845021811a01c1c518170056100f550783d01d90f4103000307069003845201031249104181003002801400e010888030f40c10112a421000e50900745140030440c0e8400d80a116201d40c030318081441529889450301036280161102180351800e010f01d07040800c0184110200388403804d641a00765008203440103480c0091500c407100c1c52851000c240c511449d9180c0050640c081c1c000440c158100200801c4c441d51218100d45210004080500045010140100000c0d0140000d44030601b0040090740d00800c2c03042a03a504500d0085240c007003900f080741c3c0c02c40e8030390141c0c003804841c0780c001c04515004900d80f070041c080c041e5508215640c40790400a200c0c02545403200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 579467796 1250 579466546 579466597
    0xf0309020d1217040f0605130b0f0a02040306020408160608010f05010f11010c0807020727020309150c0d05060607050307110a051908010c0206010e2805070305041101080606 76
    0x40500f08000f5400d1994249800c210046200721401121003902d4040801c030460544410b0317201c8140d01940c0b606441c1c2d100e06503140c1596001c2c2c85810b240c1c3c2c090101200140d00b078005400038207410b0000703007440c1c0a83c1c0e00e010204072050303100209202e42c0a00610014030208221402e8910071300340007810060618086440f5204507000034425480c1c182e00c4804590302c599454007030f1080e50b00322021a0303100c2c2c550304c034034401d500400811000c1c1c0703100c0045041940e030051a032155645082d00e0b15030360364100c0c2d00c1d002d2000722060050b0764070018a142020049200e4642c01600a503045401d1081a507a087d41e06d11034502c000e40b0300f07030080300e031001e01d0741c0c52218060244c4400f504c0d01094200088007074070209801d0180440d10750800ea40200ca00d440015454100e5004103048207440d11600c9141c2c4000303510383c114a43d00c000c1c501c0c42c5545408680549805109503039000156880c1c2414801c8966090710116410012841c040c80403e86c0e90800f07556400352024008401040040c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 579469046 1250 579467796 579467807
    0xf0d0501050406030f11010516060507090e070c02040e03130b0a03052202130605040e0304090b0d03020c13021e0a0e1203030106050d1e090c09050c121816060f0309020d12 75
    0x105020a80380c820400000ac000298200302e0041003d6100e2345d0026031101e1410082c0e0900710794400008442030308910241c5400e8000c01606940354098030f29040703c0419103640c0b424103070000200100006021214142c1c0740c0b181aa010070321101d8950880980495000c0c400865980648030b40202d0b000300f100c1d0807042c3e019070b004100060040022100d40c2da0115126085840303059042131800c400c200c440c1c2012003007079003030301d0381980540681c0d0485005c000d01c0031007070310314400155400c1c80040960744441e4a001408030062011940302c1c801d00c2001032012000c10f000307501840110f220800e1805000050302c0c103481c070b1410155241c1c00c07101902030003004a030800c2001c2c020640c02c1040707a204168404501c45000b4035850900507120305140c2c041d61020b407050440f400c420400c02c401700750400d1107540c214509000002e54180440186c1d480c100200030b0070062907071503801c100300b4641c1000e1a801016071070b040c140311020030354002540918a040000e85003200c02154546018802c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 579470296 1250 579469046 579469057
    0x3060e030d090b01090606110a020d15150f081f0c141204111002120a090302100f0207140a181b05120c03221103030f0d0501050406030f110105 63
    0x1100d08020b80307005030a00401190080c071408500618041c0003003031661043c4e0b001100529184001c14000e41c895083c072544801c00d00c4207440c9916a1071400f5800d00541c0101c91a04480711058040c2a040014054824480e60301c07281c9258400e505120a20249507100b62a40c60b000d040081c0140c80c81c50180c480c0340400411603e0460002000303c410720b11460885c0c080e9020b0701003913203212a05428460f9019034000000d02607030013212540b422080d0715004103d41d035994907240c002c0c190b0b2540810040000c0e02c0f141c0c000301d5041c03403940c0041a41040080028000c1300c03810001c1c0c600040204101182d0b60151030b58031100241d883e911702e0800d41104412090950f2103121103118000014203d400c14005100000315400c08580200c1c0e210042d40d00560400c103100303524000324048000b005504134011900f0b070307002c103580f02d00075541032001c5c0c2080b4210390301c0c1e15070760310070b01c5041c90840b8816000709128520b0520140301164900041c60725039a403000540c04405003400c01a0741e0350054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 579471546 1250 579470296 579470317
    0x60305012a0e01120c050c070f0e1302010e040207030c02030c060a0c0807060608060f07030c03061d040f02040c110606310b03030415030c0e010813020a03080310080708060105090103060e03 83
    0x5000c0960b00740e0f98000e00a00846483d178040d144e5050725840c03811196883ca01c24110308a224500bc6451406581c41040e45544141000c00e0015144000328090707802c05401900820480000a0305500f0140180010700c1030443d01940f4000c4064800341c4085030030800a400ba0201086802c20030070a030713003c1c00c06800d451044500c03a20f4104103808004c041250035500007400c09081d0008a0b02901500d030594107101e204010b51003500321103603110000100180c0d68800b48801160140e00c5501c40d400705200d00c0e68840d440343c1074490b091480d040000e400303030340070364034605d018a001c041680541d0340406002d1302008012075200c06410180c0003150710345a060100242c0001c11850215415004804d641c074140f182c40d0554500b81d8810461100e01400b2810581c0010003107800040c46025881c401810144171640700c0d120110342e60811142e0040741060b030842440711110070890100103200c0c100042c9100e6043c10003280803104188001495030741c48450340a2890001e01c26a441c0145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 579472796 1250 579471546 579471551
    0xf02010e0a0c06110a2f0a0b030106090f080307020909150c0a030c0809060712060b04030c1a0a020c01050a0908152e031106040e010801060305012a0e0112 68
    0x212030902c07500300381d0b0b14412403000c5100502821030348500418560250350b08141040c1124909401c05c3c0ba41c24110150300d26820702c0381e500d24a40e50769100c0050046c00d02c000b40252250304001e000703070500080750080c0d903085600f00002c21201c0000400c80e110513034160f45104494851420151904104070b00400e8011900c2c01007007900320049000d0078807412079640520032003c14000682c0e001c0d5090783da41300c0c0b07500b0203070005550902600c1140c2d842c00c0800d000280c15680c80d2144080b5410941040303c1542ca00382c2c08000e00b074030030444c8011100c005041689000c840e0400a903551191106003810700c0004507051034594042c0fa15900100845c0087c1d8810000c0600c090380600001ca40f2160b6240109017801300f40600004c01c80302100140500740301c50350464a078001080b224003d8158402000c100100381d450341c3c07401d0f050081045c0f90022660a04500d444e50a640d155100617492582c040300d407852892102c018050905024188070301100241e00c0100c1d6182c800034032404845d0b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 579474046 1250 579472796 579472813
    0xe09010602030307080a0c0e12101d0c04020408070e09030d050c0d06090c0507201009080d0215040b06030106080d0914030a02030307330504120c120f02010e 69
    0xa03004001544104c040d5500c8018643d207a600d03010403595003080c08000038400420408007410040302c1131451000190440d12a00300c80904038065405107031510300001000741000f05690020004803104481c100c0d415401c0c0343c28011480e070b036000c075482802d01c0000c0c2d0703a0108502500c103208179000c0c1400300c042400180ba01d1a00e80301c5503404021031601c1c5500e40310380000c48051741d104a02c181003a980e2428a0034010703440f25402d0010744406801c282c0c203c000d6100710f542c1c1c1e0242c010000701098482d94243e5140071125401d050801d606001590010001e9844000c14000c900e540554004072104103a100c402c00720b8014580c0d90407030703401c0c0d100740c2c500d03205419000511402102e42c4140c1d24540c1c1701d01c1400341503c2d00741c940c2d0004d400d1343c014805440040c00c1d00c00c40e00e0103030b8141c1000310400103403943e289071203c1c0c01190340304400d07079910240400d02030184113200b031420300ca081c456020300d9030707035901d0a00d2246101c1d000104840342c4a180c403200c5c800e422040e19140c14004445400c13 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 579475296 1250 579474046 579474059
    0xc0123030c030f060904050601050d020303040909120f03050f040f03030e0706120b0102010612020402070f0b0415180c0608130b090706030b09041e0c0b030a050a0605060c0318010e0901 81
    0x991043d211400e41c000d1810000d001850715100252156500c8405001c45ea480c02c000d1001c03070050400d00b203078980420300012900b9050341c8a0007c415001c0c0b5030700780c41c03400741d1360000e00b0420402c3d0840e0f00705405c00e810030002e01801d0314a290800e42c054080c2651a2003410202c000344640030160705a800b4460700002d08581c4105030103002c115041d0704201da40d40400040e800c94540740b1904045441c0b60000c40b02614182d409040b400d4091a00304c2103a00a034cc0d641130700b030101120100c07280d56280c94030007030099440c0f26881480324129207407500e00400d1f4130f4441660350b10748112810803421000040841d00080801083c00350711020303a0403a0300780009210b0700e48099000710000645800502d4a8915010003e80e0140b074000d02d1003051304512100e01090096080b0041d43d81103012a0000341c44925003004610542d04020002600d003044d0541406072545035104038459042480024615840842207900b04841300541c0c000328203e01c0010f032000084544000d5003c7d04540000502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 579476546 1250 579475296 579475321
    0x20106060e030c0f120309060304031106010f060c02090a15090207110603010b0403080a0903351306121104080a0501050705040b0a03020901120f060302130e0c012303 73
    0x26220180c03a0111400000c0082c15079031507095882e2940640c00ca034501c1004d04040b002d014110300301d441500d01d401c101785c0c0855079940c015502200000c045103091481c402040c001c2501610f119090750600929110b00281075040c0110301030311a0440300041421003e8a0303000c82d80000b181d1520408003507548e14804029000b40100362441c880c000d24854561034110102c6e410b882c000704110b8106410340d2121a02034010070702d2142030000103200403010407901c0e9220303845020010f207108285444040014402c00c01940300c1d04e0094000d00443d03040920754156582038840d94074111600c1c100b90203645014108000d0002c05104001a02007860a40072890342c0059024100130b0120fa01e610100b00c45600c038500c00c441c100c100c02e00c800390009110b60005d00d41e62105140084201d420350000004039110039252074881da603070708820021811711440c8459507404c145410005081003009154a8441d02e01d41103041003105002111403c88240e8031206134401480d0b4940c4a01d4503020348100f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 579477796 1250 579476546 579476549
    0xf071202041d06190605131b020615010f0c080304120906090b07030503060d0b01080c100206090706030b221e0c170c120c0d05070216030f021f020106 66
    0x6509245641d000101d008a807200510403100041c02142c1d5003000201030b40d13a20414807020a5250540007030340d03644282410100e0980d400b00004d10924120040c1da07402d101d00030703200654004004100e01070071000740030558244207081029041c203000c1011104055441d80003400800c01106110900c1044031725108003440302d8a5585200d51202416541c01c80c0d0b5108030740222004003c0c00000911900c00365070400070190011213208100c2c1c0d500c6101c2c12703098002c0c641d80da0100180e896546020120498018228005003900c1e081514442c0d4030790180b80180810305480d00c1002850342c9500e0441c0008030320a03008c0902581e803440484028040c0741d11001040030550069542c0e1800c0c074460414007843c0740c1ca1701540c0340c41c0c0028a560200e002030260400500034016114501c50143ea8a0302c9543c40200341c60360f9120b4946510111a4040e0031901158032401490f00c400d00c2e101c0002d000d0b29000032040e62020410310008140541c3d40291601d603203803008101c24900c0c1c054203c01d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 579479046 1250 579477796 579477799
    0x50c1005010806071106010308031f05030a140601150e0402090a031506060f0806030615031c030f0501210f061e1a01050310180b030a0510060e0105060d020c0f071202 73
    0x10ba20117040744010358520b82804090310701d08080020690001c0c035400c011649004c40c00510200d5591140083d0400403203400c20b880d41410302d41c078a00c007048144100e0303015144942c04041d80d200011001800c1201c035903c0c1c40d01490380060280c0c15a620000030800071540f002208001c24407541c450405004a0f1080c00c0c01706001c002010300b428016903500e8070808000d0000d08191703441001d04100c100d009121290540a03c440903002d0f1141c0c14100903600015072804100c45010102d00e00403100140d0046800300000704410503500a05080c3c1c841482d04040d07880a401d0160411400810880c1c450500c0009100c64000480c07170f094100030380c04c02701000c4001010701c10800554551108840501d921000c04809105409205101c00020004020000380b0081389001080c5410707690903041e01c5540c04084040d1044005008550180620541100c0300d5494540481c207680a00160440000d8011401566140f001c002c0c2d610520721001c2110011a07645c01c0d14050680346c0c45080e0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 579480296 1250 579479046 579479057
    0xc0d050601050a211d010e06090309010c12021002130608090d0801120c030812010e010b07080702011409130c12020408060402060306030a201c050d050c100501080607 73
    0x200158094015103e0b0007001d42c882d400030344801c800c02c03c481d1500c00c00890015a94103942c1c2889070000140321403045255000090310f6401c00e10151130818024580c00305680100030855072a40e00a1020340301c241e00c0030181c00d0440000b030040e820030f20030400306010741e40702041a4070f10041c0841a074044800310b495007007031a211641c20700d4549a43d84d0015002c501e8020040085482c000300485000d400303610843d01c61a1a03a5408442d580500551020030003500c1c01402005141051180103140d0080c402d460001507545416543c06542c4010b41445441c038000c1018509000c00c50b580b98500610102407412040301e01c000503c00a20100e000603800d01110303022030001e100b01c6058501440050086603150303402c00ca0203910040c011070b0180505000c120014145038100340d042c80a410b0304100300342084091000c41108007082c5c0501034070f503035072038000b040c1c01280e1720020601c1813034402c0c0c2c3c44104100043c90300c8a00400440d4041c036182c000642248041402c078021903066464 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 579481546 1250 579480296 579480301
    0x40501061704140c060d2331060f0903081f0e090c090f0f0a06240207180614030c030601152d09150c110402040e0c0d05 53
    0x111060010490290046015100400c1c0825810808802032016400884e40d0b5040c203c80801d5003034024100c43c40c4110784500030391a0300d20110074201c40801001d4902030760352409400302d01d0300a89a0303240c0080000b804880710054080c0c101d540000d5900050144501e07107080381e520f00206031040e410740005d00100c0100303441e0704007860000c1c0020b400c681030120b1142844c840181020f40602b01c011944180d1440d9200c0307403612a102c5200312520030548040c0e00d03101a80c1480190010100908240391100922241030200d40c0282d50800041c01c089141c95103c600360301e00186c540040d18203040c81e0304115900c0c00c81d50803140a4031000300a040e00074407a070302416507540045e025544d054100c0001802600034489000c48520518640004402d101102a0f4000d100c50f14034a100d0566903a6144030040e0840c603148002e0200c03c6076418500e464600041c81014a03000013071224505540c82c01d1180e480d5015a4098080c184a112075810040c580c01e08581c004000b0600b45c9040000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 579482796 1250 579481546 579481559
    0x60708180f01020d1202041a04082b180b032e08060115090911040501020d080402090705070f05010f0b0310060b040b09060c070810240603090507080f0309040501 71
    0x9038000001d4180c00070300441350816810b45540e285175154010080c0d0a100020703403000a501203a515000c5c0c801c140d0ba0350b0781803600c001e090a421000650190381426901e400352598242c0f807180229051a0480c000072910b01c80c0340140110b94030441c03290f40084207000c480e4482c1c10468039003400c0758051300d00182840c0b011401d18181881344480365000f49004201c1c2c41d0100144120b21221460850201912000c1c004103c80601019008004020409100c81c8d60104890305078000141858011490698009203880200421000800001044034801c00008418820149034450300a0080007130380395006008181140d4520310910880ba94a21000064420f60050f1100c441d40e02d0f1800382020460101035000f404a940c0004041200b040000d03414016900500344407c0a0202621080c194201b40c03030543e1034041300e0400c10402a0070103c04049000100e441c941004584400e050800c0350a11203d644401414050000101c03080325020000b403804c0c050444081220746d80b20070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 579484046 1250 579482796 579482809
    0x414010902030d0e040e0a08220b04030f1a090703080a05130e0f07050304051005270106031415040615080d0504030b0106030e0615060409060f2301020a0b09070506070818 75
    0x200050f00c9520f0800c180166010526603400c440008498103a0020360780d40ea0301901d81d80944c1c0250380655466800004000019000d980c0c3b80e40c1512409145090142c0c85c07a442d94403600c401804e0900c000ad030800902c0c01407065850210b04070450300c220301d84d070360444151540d045503902c424211640000e03595038022002d49000320742100040c03015020812540c802400c0180054002d44810b82c02e98200151f1100c080540e002080c0002c0303941450b40c5050129803081e00401c00e003507006066021031141881c2c10596101e0742159009c00c8600c0204c440e55524a0b007600900118042c140c00481840e8000c030090045900ca10840000ca0f0f980710011401c444150b0640c1c1e1542d003000000c40e03645103030009c3d143d841c0c40f001040507141664031049081154950b92110070100340300301c2c0030800058652052104142890b0000124000e5000000d4131410008001002601040301113100349d13404002407006010041c01803a07860082c0d0074140c526410190051700da581081c41d4000c190f08045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 579485296 1250 579484046 579484063
    0x3040203070602150a050c090a140109090c0c0201080408070b010b03150f0d02010f170109090614100e0a020910080a1a0907030908130b040602070b120414010902030d0e040e 76
    0x4d4031034481d5a210215140080d21010b4020200e03e542409a040c20356105e1684100924040c0310721400100c000c4005000414240c2c00076202c2481c1650300018181c00c030042c4181e00d9824a840e04942c4e03601e2800c2d42050013683c001034801c041000011034501c481d00001d41c05010b8040c0c0c00086441d00c14200110f000307424546c079420031130400d075010055010303905e0001081a54104004080c60342010080d076054241d100b03da03200d4607100f0540c188000c51203210200d0922111044803464030807642c2c1ca258000f80f01e0380f401c1e204440e00107081004140e05560700c0c050000c2012121041a4034014845102601d1950607180782c1407003403490520100140c888003030094244611591203031000c3d07004110040c0261040402040107044850703c0344220030140c86600d0503191a40e00300200246807030910340000301c45c907204110201d00ca814290150740d100c1e500240ca200e44902030181240545071046000390903200780300310443e40c1c541100401074010420750b4100171500c058078081c1c0d0341d070200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 579486546 1250 579485296 579485323
    0x1d0a0b10030b0d0f03020105181b060a09080f0102070c0e04050607050904020d140a0c1713060603051608120a0e0906010306051f120c1e03110f03040203070602 70
    0x360100c0c5032618025085500761402c02040c050000c5003944504042542e070010840c0181d40d19800c0103422060a03e2017100506d0b904002d0018209000160641c0117034911801c0c130603040031030ba004c541c0d442846008094450801910703566240c0c065814040d421070741c0c045801c119840310201e540c40403007160502c225005001020140c6a41006507802c0c1e21852a09401603000c204180e024003072401140d596443d140c4a06405140c103103952411181d12005040421840c100a104440030607201c044c2c1210b025680f0600700e250703034030300710b40205450780c0300030054003a02c0703018000040d40707c10501c12131b01c0d1041a5003580451002242ea24403903118000040781e0307079005508140c100111090703413200060500042183d01d800002d103501c048010b98140008500d0000c3c241c00d54000c1401d214054002018030145180242c0605598200c28844840072806c4419a20241c42a00034924004800c2c0456940d0211041b0003941030f03004940590180c8201840056010f00c00620102d01e10203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 579487796 1250 579486546 579486559
    0xa060b150a020d0305040204410708150d30050f040e0405150c0c010c0f080c03073e03030402010e100c15050108010b010801060f0e03161d0a0b 63
    0x2110f0080d8001d01024000b43c0c1c0166482c0840d814258403a1000c1100c000302d810f1403840313039484d40d0100409006081d042c00742030700307014107202030150488c641b45c0d049905403c15130001141c0001080603080422401360002d400300c889000e0f0203814944400101c403884540c1008032502c00b60a80e010301c00c03805070242244080004100080c0c207007920a400902c00e0b0250340020140c606074040354201510424440640011028541d0302c00b4130400300fa005550525171a981c0d4240342c040c2007100028a0f09120010000005440c00d10445e107061611081d003165a141010740c01e50700d1200d9401800001c0f11681e50070078450088000030036a0f215544c141c1d40d1030030b05001c40f810301810407903001281c42442980040800040d0b00500350017040c0d0045003002031150300d814030550a4440204000e41440013003030040c441540d00000706480645203041480c03a407959000403030b1900741d080c04440341011401d600402c04041c000c0d194007039100900400032040c0c98030105881242e0030702044aa0004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 579489046 1250 579487796 579487813
    0x606020615040902040204080102090117070e060a1b0c08150606030705070c180b1e01020c010e01091a03100f080c0d1a040506090d05070807230a060b150a02 69
    0xc0360740d6440030301c058040e1021603000c505501040903604103030040540c607500440d0300303045540d0104212821100401c1c2e40a92402c0441000c0c0ca020400043e4070700030400000c02400b02d5004038044203510f00002314031803c00d5410b00301070410800c0d13406481e0884c01b5420400e80b0300b404c500c0384507000b03003001004075180da20ba2420a442e940d010303a900700c88624203284005040f40a05105d044503800304040410306000c44d9040084020a402d282d0441101250720066640d0780018050340740d100a00344906004002e00c0180c507a80310541c0302e07140940440703400ca0705600f0800042e50084000d2079810340a41d07110800100e6003a901c1c028840795901800e084000341c50300b900002e0209000704103407110a50714200b8408081002c80301035407136038825020300607a00720422032500340d0800d91500e0390905040365030311403051045c0700e03018001944001016038201c0b40c0c40b0046000b400308804682c111242131074070340003900218886520446040c1920f40c0b40302909012940c2c44600d99001c0c11140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 579490296 1250 579489046 579489061
    0x24120204081c11070b190f05030a09060f0c020c0a0812120c1201170c0a1a031905250c03170a1b090e01140901050d060f1803020c0406060206 62
    0x2c0089910100c1008001d51500029190500003c0e0240c00020120382d990f481400110340d52030f80350080704042000428082c1e01180e442800c1d81e820220b0001d000c99549a24241600548051040030018611313101c2c04003aa9900011002404002550644074669480303051036203855030308944162110703080000c5100050b500d481c2039400f00fa004103890900e000e007901c0018845c8260000758540082c0c040c103c00080d010800c0d1840e200007102e000030b0813428054032065034501134480009035040803000c0390080000f01162000c0401080c4104a64508180c42c41c000c00a4405c0c400c0e0030107645000d12801d588143c010b2502581c1584444038040b8041c04e00710741a400051075601c1d01d994403144074071440c50707000716070001c4803013640d51903006818402892810315041e4003c1c409500890721550941e26501e070103d0440c0c1085900c100020041d040c4035000e04404524040068540015070721540314101c502120580280d0031240300c2080142031000700c82c018022364015a02c100c0000e06032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 579491546 1250 579490296 579490333
    0x2406130e0a09061109030f010b010f030b0d0b0708011805040506070c0f0b01060f020c0f0f040905070f2c0601080414160b04050102010e030a050301031b2412020408 72
    0x4005441c00001d2040a030352250800c88090b41d43c1460101d0000403031038001c0c0340c20480b815802e100781000b0400c070140c05e0000b0b00200030000300b010915480c0d02c500c601940d20f200950f00d80603003001d8200700a160240d00108030390024092040071441412240034061800c1c4a900d00c074a074840c00070074150b1074420050f0b805542075041201c0d9050500070310030029040258807402010a601c034141c079403900100280c20701c0d4000b01028001d901c080e00c1c8000a942d500342d80e95401000351000a110b805d0313410140e0900d5016005a01e44140301c8600042c00e560040d1f10f0035100200103c031281d0441130a01d0380c002d045003600c2480c00280c0401c086004514104602000c08051200322403010b440444030a501e003401c0d87c0000a0900d02140c10030003940c0a000b14055280d0340c5005d1450303d0550b000c05451804107000c0540f031000706070780711210b02c012140c281016003255110071f04400d07400349080341d8601030080060002002110b544407020700c0307170003914262400700d00600004034811003040300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 579492796 1250 579491546 579491551
    0x603030d02030f1e01141c0f11040b0d020a09090c1509241e020c041a030d080403020d0e030a0c0806060f01091a0f09040e060114190e040201030902092406130e 70
    0x1b5160280003101d40000d80030380230840c80300d10a4070b0580d00340c443c0d841040100c8000c2a407190007001010038680060743c4141407141521826070000400b1802401c0554880106030004816001d04c90356148000c0c2e00000d405040f1015254003c0c0c510900a902024030603040c0c1101e408240444564100950714960801007208507104440c40c4c210f9001c002403ea52580c82d071564912400e4900c0d8609003800c0c0000c0341c06c41d084d810055081e0416071340095a441d82e0505031020000244105541740d6000e00c030502086811452800c101903d41400545404080c3d880511542c07032210200d405501a004148c100c441090b500c000c801c901d425400f40342d9208082c4d80074540070810911101e907482d8482e102480704203100402e0158102075020464400312400144200440c215498440300350124000c20394103c03040c50011516076200590250904100081d401480001000301c04203440d140c0d00351400542800f01c1c900c100c0d207004e2212074400c2e071000c04c44d884001030040c003246141c2007240e81c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 579494046 1250 579492796 579492829
    0xc050403081b03041e08030a02030f03041a040c080c010e060906090a032102060106020115031e061b0f0e10050313050102040b12060907090e0603030d02030f1e0114 72
    0x1038280c01c00b0514299400342e00004440645000f00340c0b00549084004005494084000c510b400412580a903070f038014903929403024980000020208a03803140720348500c0413481e0003402309003800c0c176100700e4100d001d020300035140c800e0402c3c0c60b0f8150300c5040c600d1110000a4a0f4600c0c05078618144200d0340c2c80301b21300304e8000e42403901c0040001d103051000c001d100c5051004500080c0310700002400c001045e40080c0440e07040101c00c800303010f4607241000840c0d03030045220085c0a0300c8500c42e0081039a00c0c07400f402c41d078502030301ca41c048810001c9000110240d80c3ea415100d40031818151110300d14541d810790000c0c0410a07002460380507030010b54214030b841500b00130000e01990384600760790080c0c101d0a0045008206c15143c8000f0303c240f50380018007191150401d1905c030200500403140c52090851203610500801c107292002d20807141612a9190300f9580c03854038407840444400140c0308800d01960307004540e0b8410f00c104004505032201e2400003100a45000100040c1107040540c24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 579495296 1250 579494046 579494077
    0x7033e010906122007050c1504210605100503012004140402040b0a020c01120513020906041b0c0215040312050307021203042307050d021e040c021e010c05040308 71
    0x10303020500751180400584d00785200710b951316001850a1420031040c0d50ba000d01031468142021484110700b0f00350f4007645c2d03016104058210300e0440d20607003004210400b40ca203601d00420b0110086404a419013512002e80007840303400c0c480030810916140d500e015400e62001827105210001840a0300d6022941c010000360905444c0e1260010f03603404038085101580c0b00300e40c0789900b560041d102444c665103c80c401c00c2203141c0004200c80341c04410030002d1160034003000044040d6119404610b03071070703c80d11901200005540c0b02501e00722840509a10411a6a561b0443e040308041141c0a581d80701c010a5810041c0100c00e4a1603007020b451042540101b500c0c1c8a0f07031900302070180d40314502640c8456802c8056219807003840c02c04400d10341894202c1c050610003603c0e0200410420395056918494407154070317442c5901c3c1d03009040ca480c0e21030708008654000b55400200310440d5074014007803005c107c0728000103900702e81c0900c143e04003042060008101041300c2d0400703007d0350000c88810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 579496402 1106 579495296 579495311
    0x90106060e06130b030115020616020309150d050f1f0b0a36031a010e04140f0f030a140913090507033e01090612 50
    0xd06000b10400501241d0190362854600010f00c12940b055850396105d40c01c410100c580d10340c40c600144260000b117010350001c550b0f40c0380c2c000011380080d850308054034240112004e1141002034085c4040c8a2b10800c1060307405650300c60300300300032100b0551a010380107000b590201816040c0415841005100d500703868000c0343c007003074201d051104260301d002c0800c9681d80403a50916160444080e1070820142e200041a0152882404910f1440030000c540d43c0300c0329000d01c02c11000ca031900c1c0c0424045680e800390740780c01c00701c0902502c00c0454030345039440c41e00c4090f142d0145260b000283da05020340c1d000c0713110b00703040c014124070034a001011400a200128510500c82205130f032035171803808011042101900a56002080c1e0b0549003000b98001e6411000500c10f00305501c1180206025210101096280c200143c680300c0f10b203401c0c8174007202c00c1500c903d44011840c0e03072100e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 579316546 579496402 := by
  have h0 := BRFrame.cov_init 579316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 579316546 ≤ n) (h2 : n < 579496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
