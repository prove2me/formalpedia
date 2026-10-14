-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3561
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:05.086252+00:00
-- url     : https://prove2.me/submissions/7ac75e13-a30f-4a30-bd88-b7c783cbaab4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 640287769 ≤ n < 640467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 640289019 1250 640287769 640287773
    0x1917030d1b120e0304091808030c04090605090c0403150e0d0c06050c090d03140702030a0f050c040b0f0d061b09080609010b030c062208031818070c020d 67
    0x5582070150720081c600e810070710000800ea80301e0782d45000c025a091080c015034030301180d107680300d2246008040015031688824950007240550741500e643d030114841d50b90b444c0505001001d03400074014405454103210340050103152203000c940c02694040c222901e010b1560396000700d10350001d5100500c0681300c6050b04e00c104414050107620240c0340d02d078449909028079126080300d400034010903051000b0f01109165807a8084c0d0a02129810b042040c00035107d1002400c5078055801d0080d8075100d030000080810085900c2820003501c51300442e0210245a000c01041d42d2004007003541001564180d02e07400e213000360b805032200717010340e0700084c400307004031140c501140198480602184118204010700ca03403c100003a03111184500030032501e114500000e0303c1c2c071580d0b180b01c2d200e9000070a1188401403d9002014028101040a50740d00d0341c50011540f030340c2001f00c1e502d00d49488900703084a9400c145109820703050b00c101403403000382d640703000a884002c034000040e40c01041400310100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 640290269 1250 640289019 640289021
    0x90f032f1e0f0a0f0e07020a05031323030c130f051302090f07091203031103040c03140102090a18022109070f06050a0e0f0a0e06040b1917030d 63
    0x60040101c96061034951421060094041c666071640c3d00440010904001c84500400c5500c180ea100103110402031702e4418003246050a550f602a005000000e60700800904100ca01c03002c80e003800100c0307040000950415500b03426410b000603056008460b40341810b00d06011f00148444401c180024102d00f801564800c450040755111036124524a10030705510b0301c20900ca0b8415103504000209141a482c0200503603610f10076005185030704d014000806000f1382286503000302d00840030380c0b0303442d160404c0b5425910a100c140c400000c090128800341406000301c1e0311084010f4114001c007454030b280c1c1c031038074114035505180903542071002140f6490030303507841c0480495220201e45076050100042c1d003040200d902841580752003544c01c20005800800b40c0d54100400e04103240b03145100e03c04104d4000b0041e880680c02000300d0004510f44041c000440d010301d4080d85c0410031042001c00344038401c02488078100d040034114104010010740c1220103808003000384207482c1061042c020045c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 640291519 1250 640290269 640290289
    0x3151309031d030715021b0d20010c020d030206100b1e0702030f031605070608070e1207031707030e04180b130c0b09100c022b140d090f032f 62
    0x50b001417402c7c402d4000e4480000d8910710301211201075110041d62035800180c507040d060320026030f05a484a040f80c0c0201c4200201d140c019140504984075450025112001260654500324110401045034218101500c0f02c201c481c0c02c048062520900403030f0001d800481e401c0fa450303c00e112510301600030500152503011068103900711040700c03d240440c10403100d80c0000c01004104010000c0065000c40310000c010010b64042640c02030307076420242490215003000d014403904440c0c80040b40c28400080420781e010742e44482e050031507141000151007003400c4104181034110584004140c14818480d00a85004005012094156200c802000082d8130000e5400000f05800d4a6400e0010250410f8602464040d0580785079500086804c0c0d4050340c85141c103403030204523210060460003e203107070345e0300024a00c002d0b40c040e012541d9035003a01241d500028030078181c00a501c801624805042e01e51083e64000d0280540c01000e13030b0340341c130000c2c0c4030103c418005410b00143c032202c21007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 640292769 1250 640291519 640291559
    0x108120d06090e07030c080303090607030e160b340308101701090210020102071a06010c0204020c0d0e090c030c0a2606030105060111030423030303151309031d0307 72
    0x9486013919601b000102c0b00c10590001809802c00c0003000410342003c540954040102d040002d010052615001d141505e020071115100070804000325850614901400d03d0005100201a6603960003c0b10b0b001c941200000b010012152442400000c2c0110719485d0300545504606c3d5080d5501d011199422440d1b003c0b0140c1e607503484500c141907003422003460040d0b41d501d000075880d280341640ca0039031031103294100c18607980d203000120b0320581c03141c0302402205400030002d5480d907008220007519441d00e8032000012402c0e0890b0000e40e82030414101d445a8a00c0d0050ba04590390844c10b1101944200d10b03e80c20012062034044030002c0750080446072006c10202072a50b4034021052508540c005400c0a05108004141e415007143c000f0485040d80d0407050206c003034802d114500c0380c400035000030003507240c00f0100801000c800441c1c1e6210700a40d00b1074402c080241515018822101a201c001c0e0004030882c0310407684034000c000380d51900c44040d04942c0c0d07440e5207907035a04c00c1055400304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 640294019 1250 640292769 640292773
    0x601030b31060b010e03010606050c061b07060911280e2707090912140a08012c011503150510080a0b0a030b1e0108120d06090e 56
    0x1480351103212055428007001c080481128245100350301c07000c1c001d0041d58014403054580d580036000d41d00c2003440d540c500801900030700000340c5403c030281c42c0c0c0d00401040701580c17003410000f6044001801e441c1c881006491805840d100d11500c0701006003c450702c007030b10103040f6102d0352034103500c1d4a1110ba088641c1d51080078801042c3c0045600c04050329800b18140300006801d000c2c1c1044020540300b007441c040340c041001890918440c5083c9201c542c03100503014035108000040c011800301c1c6650b1642d0035030302c0c00c140000645842c003d9000d10301e000000180c000c801800080c0410b031481d20700103290030340300800741c480030394030402d00c0c0003600040d200c04000b41e41001000d4042c054805ca040780ce0205a84450506020442d19009800000d081242080c041006034860f94081c1540d4100079007203000558490516030490181a900000000022020340034920f01c00c0852a05940f6510003a004146001c0e004030402c1d003069103e81462661440001a01005445403403114020400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 640295269 1250 640294019 640294021
    0x6030405072111030a02130905070f0303050901090b041a210403030b0319200a0801090c0612020c060604050601111c0212041a03130803101a090105030f07020a050601030b 75
    0x907000d8043c418854885000c4e510051480005940700416840545180b0344002403070005420400e20700080c50744543ca9685103054080141944003008000f01c04080e01c40c001c00c140c1d2286916440c4c4618400c107140c08144242018000503201c00925001034500000c1c500140f08241004080c8415101100440d0340c412291100781003d00401094a041c1503c0310445419074441c201c180c6508606800300c0803504486945a6592080800c00780002d0780003000440310928103414903e802d40145000316440e180b6038408100c403402125080b83d4280c011304100c0d2158003d000280001800050510000803030008010500b00101003000200d029031131b14144076030340081e04001c00b1800812808400f044180500a0a124048100126070b45910fa4956030b2000415104c1c031a40001001c2ea1070003c1441500c0c841e1021030001ea40608078010001e040c19070449107503224014809000c10310038000a01e4984205c2500b60340308001c2d006441001c02d050b5a8141800c500742c10403206142c0c110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 640296519 1250 640295269 640295273
    0x503120a060504090b0604020a0309050a081201171c090902121008010c020618030d0c0206070f0302190e210f0d09061d030a051b01020f0604080405060304050721 71
    0x4007800380248000d07603041254640c40d0b101c40000001c002c0200c0d0003039800103060403000d44213a01c00021280c01c403041d14a103944501e000d107400d9000340040b064042d4000e00100311018070401707100a0510450041182c80c560405241b0b0b4082030006400522211101c006452a800c0c0001c14880501103041c1030315190000e47e05880341d036560000101a03260298a101d602e800003615504800e076a2a540725020040701c0e020300e144903181c01c0c0c07000f071130814180405c00b40d000200f045c0a4100d80e264074007070b1003003c113048089005217000c2080c0f5402c00001c001e409401a0b0070009000380240c00c00c40492501449580510b10340b080c40211a440601c0b40c4800035000d02450501400f9403420404161034404014a4400203194504107080c903581ea40805550402403c504964004240c0782c2c144019151242401900010785025024161580308482c0d400b181c070318480e90f03201a005040500304007e104a5402c02801114684074581002c03508000000d080c410303428810302002400744182c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 640297769 1250 640296519 640296521
    0x201030501080c09010315020c100e0607140d1a211006140609030a0507090e07060c120503061801080c0109080a020f13140112030f0f2a0503120a 64
    0x160b002031800d81004180300001c0d074072443c049046981045201110700c14095142c4028070403010000fa40d840b41d806010300340400c80c2c00c000400d42010f01610f80542d9001c00035039003480540c40c0d01c4409141003110888903401c660081c0800c07107198000350382200d2100e010603d065000c40044407910701b5004500380c1c010b8208a60b000701100306006205880c030380301808c442c0070610040148240c10105011280d5141000305120854101d81221a025510f50021300204900141d0381098000c40c075000c22240e01400d40e8003d1f940d48203141010b0ae5003040030442c4d00350406402c0782c2d40004500103955148080d443d13194043d00034074002d0141c0c0c083c00b100150100b45c20394440081e0360050640c803400b6030b0b180c00d100068207105450706006540d0703280e02400206008078095a281c0c10400020400380c185004584400703120f505c900c0d151307680351b800542d10170801142440019043d140c40d50010340030f1440043c442020503e4640c62039000d036850500f03682100b16010700d17030f40581040055444403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 640299019 1250 640297769 640297771
    0x50a09050108120c0304050405041a0f060a0b250314040e060922020d03120f060503010b03010501030f030e03210c0d051908130605010605030403180e0105220e01020702010305 77
    0x80f000c014a801410b511044c1c903800740348201445141d55a001906010300003820032000030b1031001000040ca00043c02c0ca40c80a01613480b1409800781d14804a1034014000442d0503281a11054188000d003901d9240f4041d20361807001c4080002c44100110300741100d00103803028101d081c503110318a14003042400104d08001b044c001c1c002d0000b1071040300760790360041e01c507110a4040d00c0305501c0d045142000c2c0ca00c00004581101030920309001484051a190320010581d00c04900038017070b4482103401c040c00d9400a00000d170410104009003000a401070a41091044018080d03480f0b000d0455005510000b07250f40380d04407424005880b0044143c00e11080d05d81050320700b0301608000041851510308940b00d00b5100070b001800c001700c0d980c01c15110308070b24000e80c464000c0c8010b40c2c407414000e003580c200303540c100c012544421100120600c2110b4100c1611070038080780c0e1381a840c0104010345800a0071010384540c82c0e50381e0b20118030035140615001721071200009680c6006078400102141d40c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 640300269 1250 640299019 640299043
    0xf08071115031f080304140f040e1216020618090709240e060301081e010507050901140702041515031a061b0601120605010b09030d05030a06050a09050108 68
    0x28041c50207070718070740300c9030300b56500f02007942a00340c3c2d80101c003a840000d10b01d094020800c203100100300000e000302004960240200c058a40200005000d030074042079401c40e030760622182c0c22442130200c3e03001c801340c0540001e80340b00c0e154098000e555000309046500c85810003402081c008160261801d00c15540e070741007070040c50701520151520190030301c06900454108118880b2621901e0002c0c41a81d601d9102000144803d9507035940380000d6075034072000780d0407903a00c501c00ba002c41c80a4106203d40c91081d1040d40f60369240040030340044400340d0700f003071200c1840817050200d032015840b94410320300d558110f071120384a0f06003001c1113a01e241c40d142491034105070030643c6041389200765454085200000351000d5848000c000e0703480101c0164a078000703001d032003240e00000309065222403a41e0224020b0038104116602c495116a003445110040350300740d03000b00c07480e40089109100545d84007491364030020740d4030f8460340007030440d5035036a00901c0059140c00050001050030b03c407454000b9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 640301519 1250 640300269 640300279
    0x301090c0e09010303030b0a03021206010608010f060503071206081b0f030d14030601050c030c1c080c03070e06090402040b0c0d080403020d1110050106050a0314060109030611070f080711 82
    0x307552240040c00e074000c1400001c04158681d0340000341512551000f50140d540101000304040040070301e03c1d0349803003d01c240e4001500c20000000c04403032285000091300c0080c1d5815113503564040c01070b2030910302d072041c090501e40e56040c001060305090100660304440c00c200071110080110400ca044480740c0e00540c801e4000100ca01d040b1600080031030a45106a640c1949175903030755005945034024021090304500000130012240c0502144000e144030741134011110300d2108a13000c60303400784101c0d04001c0c200020400b150440340183c43e0110f20740c0c401891f06140c035040c00d02280c2680c01940c050011400081003014261400b809030624081c1c036071420004900e000e0700c0080d42c0b808011000c005102402d05000200c913400d1020850780c40d8485021300c080d5a64000041c12035006401d0880024603102e1105140c0100b01d052a0082c00c050b51214061030a548400e0018040000000d00000d0704000c1079000440390008904094024200107480324690706003d20784e05d00c4103005078030035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 640302769 1250 640301519 640301537
    0x204020a030b1e030a11030307050a05150a020a050d0e0c0301020d14090c030a0b090f010908040e0906101721030129030c1821010c02030c12032205030301090c 70
    0xc4d8600250035022541c11011340e400030080240841c0c1180b19031080a0000d000e02c81d00c800910000003040383c00d040a8400d00c205940e03650007043c080380101c1d44030800017070040201080b140004d820195a40d511001030307408084246000908980c0709208050300d642d1120780340d00c070109a0311219584500954042c10810b8030440000b070b1501c460f040024420101d8401050350380d00308102c2c011440309210700070403101c41941008a8103800900ca00641e990400700050250039001c00c520b8001d45000b184008041d060064400214042041e0750109201d82c04001c92449419004400601c000101c050780e29410120900440d0305140512030341980e181c81c01207640c03542541100c1d0300144115442c0c0c0c07541d180d60710a07102c903d00010425480070381903500c911111111254009a0b80706c10000708210010568241d032203024084001242d0b4000340341889000b0301e03500c02190301211744030752851101c00da4a81140c507070004c88001d442d20790001c4014000b541d1a4400c0400c21302c101c0c1000685 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 640304019 1250 640302769 640302829
    0xa090902030c15120103050309040e150c0a020a0803101a0c0c0f04060b07050d030c0207050a0302120c0a0603091703010308070f02012303060f1207030605090a0204020a030b 76
    0x1890340c00b254043c1c062007081840140c00c107000800c0d10501e086510304c000c403a503541d040481c0d03030ba0000e2443c54400da00d0504000512280000e002403201c6c60083c1c81196941c52482e18141900280710341d1095019283d540c40000c1d007010f00951041e192070b58400c0c151402e2400101e11140c1c0d40603c440c0c099020031900e106150b00146800304100100d8003058030703d0301a404600070340016071200c1a14000490200200540403c9001c03d081d003070b075030811400e48110030490755180346128217604a05091814405402c190402c0303142c0c00110340403226420783d003001140108045130b00071000665183c900c0320400c4205559125110102c0c000d160540d41141c503101010312640d2802046110422901e00440e40103c0100501036a880c902144040c5041504211a882203a51510600031105021112b16202c0300c1006140040740090020a056641312070040c000545100b01500c06c0000c0140103035618001805089141da801007410301c0c44405000d2444201001100d40200d120b040b200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 640305269 1250 640304019 640304023
    0x21308100c0503010902070c0f0308031f150513152d0807110f0d0e0f0306070e0904060e03271e0d081b010606020d0e03030702120c040c0e0a09090203 66
    0x105407052000c2c0161f0300c4005141c44500030702ca0780d005605540d00c0c1c3c4400000e01c00070340c0240d4825014034005100c1c8941c0f00c507c0b042d040c4054018500e803030b1010404421001e00c00c40203807a400d2182100c2c000700d29140c0443e0b14140e5905044500000d200d012011070342c10703180440502d040030400c0308008501e001300020b0603141004040c0e00404c01c03e0b041c00e51901d07a04108849c00b003035210041e14450202c00b40020314400307080c0901c501800213000c04600d5810002000e034072404080c2d5501045030001d50070402c00c0b400140c001d459a58550015075400241800180079a0440241e0441400035014000414050b15046248618428098030202c4103036298100c20180b001c40c0c4a030007180c900c1c68518418092110614100204818911880c2e841503100c0d40c140c650075000c451840e40d103160100c840c6e0055441003a015041400042c00604006554018000510b0300f80e4946041c0600480e084400e61104440000da10108040640c20217420b080041c2452010602504650750042a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 640306519 1250 640305269 640305271
    0x1c08060a12030c06111308061014120304090b090603010902100f090906030f1103062401030b040905010614010509010801210503160c0b030f04021002010f021308100c0503 75
    0x409010180c805074801c040c03040409408060703100f0002c01c0308510382072409025030021440c0c1075000b40b00380004100d826000a40910075512840c00d00d407040d04181000c4190b0385007052194214942a07245a1951003e1003c4d00290044440000740070006000304030b403800d4050400c50199240ca1350f0400580c451121106441845090000441c071110070704640d151802e45c02030540750300d028004402c101c003c04001d08070a0059140342648080309003056201d074415100300e041c2c00c1801500064281910a4040b071f82181410300040070400c10011a05488290108443c0c99540e004203108044001411040f02e40382840d003a414074a08000203405d0449c10b00401c41040004800c07221150110940300000c0380d400f40a882e21a03125a421501c10060b4800455070003441240220302c85c076002c41942e1085485c4140c030300c03040e20b80c0d80902106c0c02c50079201c03c00310754807054001038500d02030008240074001546a080c0d100d03d454000c504000d0395101c071081da00c2c20800484503c0e0350040c162 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 640307769 1250 640306519 640306529
    0x20a06050904050a06033f080405010c02010605012c09042102010218040f0908040e010305060c03040812040204060e0c0d0e1203041b0e19050a0606022d06091c08060a 73
    0x710307408410b0920880c00201d404401c41c0141c541d016a0310707070110792023a038050003544620000e01c180351458400780e00703070340041c0075190019454040e40714402a1410f0b1102d040d046032403aa50300443c244000c101c1c0010119402d8901050b92183c0c0703414140e0040d11095123080c203100840c1009030410608600c0b20b01a0751076031141e52602c00f241c1d1171120951004200aa2106a00750b0700d0b50b0320b950004511501b44070981381ca014100000d4408080c0d4411244a1076100c0d42e69480e103d203280c10040112409042660882c0e99190042241007040300e03194021030007c10700c1611000c490202070141c88200d90074402c241c01038000340c0403104005003941e030011740c0401400800f60710010b10b0400d50205512000e8464415414000003040314441100902405030b001c0c01940d84081c00a0141c601d1440b03071100582c0718800d03201940c000303c0901c2c0350610700c0b000c1c41c10010041401c0c141c5010301c280c03242c80032a00412142c60040c035449a009181070420705100700319240c0240010b4500d0380078071038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 640309019 1250 640307769 640307813
    0x1704020604091e0e0a0302071203020601030303021c0f0f0b03010b060409200f0a0f0513030b100308070b01050102070e0408190c140604150e06060f0d020a06050904050a0603 76
    0x3c60402c18a40140c18a10500c542100704100c00903074031103030360343c0002c0300007600580152800402e2001040b8240c1d80e0681d0150014402a480d40c0d4040b80250b0010301800c140310411506500176081601a040d03000c1c130b90080c0821000d0b01c5c890703003a045515000b0182e1107a0701d403549003841516600140c4048880c44140051600400c41d002783c40107841800400707100038001410400094188042c0036103502d1a0b0f560519045807030400d8a9912590078054165111a40d00b000000c003510b080d16404840360691401d815540d03500c01c141a00304076401c403502225040144203e590410080000f400305207889075490906403640d0000d0b100350784500ca81c00c410030b200004101c2c0a401c5448810f0740c00361018221880080907a916150180c400f21a440c030710024450450005003d80e42d0751015000141119484480c10809001ca581c00c150307401c900030080c00c0025949a400010061030183c4a06566022000400003211001081d909101d45042d6043c40801d1148801401003100600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 640310269 1250 640309019 640309031
    0x705300a1b0203011e090c06050c1009021908030403050c0f0d14010b060403050c01090501020616030b0d0206070803370b0a0b03010f05011d01080c03070309170a170402060409 77
    0x400d001d040384240d0b8040b680e941e0407107990496166031150b07256071f004400c48074030580c41e5a81120248101d0800c4410790344081d04903881d404035540300002540c4020000d0f6901802c0c10010129210140c0c4515690382002c02d00300b003804400d0201042d450400c403114103100303802200141840740140406001309800d180b14105101c401d50019015910050013582c445989140260351900c0074000d1a0000e98400b20000e030700e500000d0414000c0c0c0015881d02080c140101085008000c0000903035440b810150440016888010040c09024000c110381a43d928016a45520807145400e0031400d070800780380101600d403c02006e00c02c0c005060788d00070900070541c01c00501c05d00050b410030407459000000008030b0500040c08542100c1c020b0702d0f010303040302504007140c050100c01c64240b40415600c43c00506000b00900085500040606000510081544641f40b8100400c00340740d200c0e003000244600c0e001e4010b5542da020b0000703594814040d141c103a0214400c0e00481c49520500381c2c40d08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 640311519 1250 640310269 640310273
    0xf0a02030405041a040c020705010519023a050a0c20040e01060f060503150105030403140304051b1e040c020106090216021503090a02060d020705300a1b 67
    0x11003200c004082c024810300802030300403030083c440601c02c01041e04c82c5251030102e82d00d40c0d0010400300304980c0140c403024205002070500d901c03103884000f100e80844c014004804d080198410f4182c400c0940d182d803014800071344803030344c00c5104810806880ac2c40b50500000503103581c082c0741c640c6516070095217010800000701108410310f1042d254240c2c090308000b8008101c03c0151b1205040750484804285241d13540d81044c0d405201c01d0b00c03a080c4440340d0202080095001d4401150094440c0c40d1a5030b81d2030102d0541000c50300142d808940c9a00442d01d001100400c000141c8151141100e005041d02c101d203e07112140e00c50690031702d0069490b01c2c1021401070037136014100a120b541e00035540c0700e0208040940c29403844070102e1041e8464054101c4151500c030a0705d118943da607004080059640d000c00c21a60010410300c0c0d080c03a0200040740004e041030004282590403101c00e0000014509190480000d08102200750140140712010040d03501000304942003080f80200c2035551014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 640312769 1250 640311519 640311523
    0x20712031b050609161e09090f0c030501060303141603031a030a1a0c0c21130801050a0e010c021f090812040516060905010e030a140c091b0f0a02 64
    0x80d880103001401040100400182e002ca05925810741118000000c0f0f5210b05140703e051446580c2d41c06401003c0324144040010f6a01188e680741c05514003850140060356025904501500211000c5c0d44a8004000305034120b144100043c002000090900d0101d4a03041c1c3d000344d00c413502a00300350300d80c0d400c154101d440204800c561540030301900d4007407050b42020700b219114200f210384442902030004a02c14049401c0c1e810303000740d10016254080340079003000c2051001c0420f8200384c000422040320381c9000c2c100084001c201110001c80c030741c90f0501042c021a140c9140e4811580d0501054141207640401c1c20600300c40210007896202c10918542801801c0080c0002e1040000013001c9119006040c08140320b144140c0444034803982e001f9400e55200103c0c0b06a002181b00b22506000303c1d800f8003d2900c0800010b401c440d43e00e980c5868203400700d07607910882106508020701c501007900740800500d51004034113216100e00003518252815910402015150355800820481c0429100f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 640314019 1250 640312769 640312817
    0xa0b0f060a0903030212030105060a0f05090d0b0a0b0117160c0203060106023313020319061d0a11090601180605030a1416140904050408040f0602071203 67
    0x191105880d50361203007000c0c01c81903082c0410380c00341c131600c41b10000f82020501200e06807500508214100600e00360240c07808001103161400703100040c03004042c40c0c0c564481319078410f401002100e086040181c5000200e5294459a504122091500c4917001c841045000d800000c03140d501a2041c8400c407044030000602c4038000e5043c0180000082c005500040e00c00321194604444010003912420084c04002440b0400c0c581c089183c00042c00844031031079a10349940003400351001e180722500e90322010340e05040b007117914596541200544108180b80c080850300c0c04d400401c0c0981868445070603059410036501d200d002d1040010b515079100d20b02850140316010300034602d10361624070290003a0400c0711280c103a6071910034405c0903142444903060140030196208003034040e01800c00c849201c5811b519400d002e00800408256407100c4c03166a208a00814400342c449041140007051001d95500c42c80c219484001e0a10489801c03d0203e9007080c0e150420702e41c8040440d504041c4414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 640315269 1250 640314019 640314049
    0xa0b1009090f05010506120c1009030501020318010c0e01020619090f0602030f070512041b0f0b040801140601090b2d030f1021170301120308070302120a0b 68
    0x1c00e01c05144204580700a03400181c9104000911490b5100780c241f00b0035a5010240b514542d218011402e01400d040d14501c1c03c103841841c000b12030350b07140d450300c03800d990090750306400f078200180c05c01c5d0200a01380300b880c60a50b540d1401c502c4090124000031f5031400f001d401d04211645105031070000145a51042151585c040b101d59008145030408000039001211070301201616040002d60191088040b50400c003039801055000e61034640b035030036500c4041c001d94000d105a1403c0411904402d2155030010a0a00246548d6034201418030382520300c441c04040b0404100c00a01070140e03004100c43c4240c419105606480380034403108030706441350b514030810650700f118010004000b4a01c0083d4440c15401d42c4200903502e03288203c040110b031600c1140400781051640b17009000c19507071070501c01e9004c0c00c00448000b00ca0030b884241a4801e0f8007007500c4212910320102096001a031940c0d101e840c0d420211b0610040f08400c50f01400c00030040c0b81103c1ea07803400508a039450608540035130f0703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 640316519 1250 640315269 640315271
    0x906030515190f141309030c1e1e080a0c081c0507030506090903031f030b01080d14030702060105220f0617070b0901030506030a05160314010e0a0b1009 67
    0x360305101036900e209228000e030300d106041200c020a42a8000248220114000e8002207034500340d100c05100801b180c0e0380071400c00102034818004180a5524100d80151b003006440c500e807a18030345054500b0140d0f41c007000e00d651066140700400c1c039000a40302e619290341840c401810300c618222599107e42124410100102d4501e401a039210380d20480c8101c0603510100060745582d410003882c1c031821613418619520400000d00b10f084090600c0d6641c0c4507501c5201e51140c0c407551206035814098128001c1503201140103c54180d01c59209101d0300c040700e452600d1400c09031002501c40005000e04c6e0700401560b00500f031000540e610454480394580e1040000c58612284040503000603c10b0420481030544103007040c100c0407070040e08441c1d1400b500fa240404040056016002c010000ea0f410302405a020700410b0052145030319613034100500f441460300b1031501003a0b8104110b26400c1d503070316040c1c85070740440340050b00340400368201c003004075581e8030307110412908c9003180c00801100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 640317769 1250 640316519 640316539
    0x110d090203161412010911060d02040906121205070f1101112d03090319050c121c170403080411030321010e040b150301060b0a0c021f0906030515 64
    0x803c0d0b03d900100f4001030403600c2d4090208000c04c0d030750a07681c48900181c10100c01081d0303045a45000380080c050504d1034038002d8113140c0c0e0b440c2c50b0b80131550075900080a2a01c09185041081403004400e6200d00580c1046d038100203d0341c40d0035000b5031040e0b800034900648150380d40210703809191722221411085c4e086860f01c030704018807100b0400e81959001c10140143d0301100e250003010041c1c400c2200060014440c000003501c05079000300170104159580e0103100a104400c0d1110b00c8041c0c2e100b26190001d02c03900c66010910382884441501c414108240b441030b00c04406400700d001a0031a80500d0030341c1030f60f00c03903040003005a080c041c0d00507030511000030b80c1c0c0f0403d100c0c0d036140542c00c4020200c1c280540e81c2c0d82c4144c20300480459008000c0d000c50f400103002280342400c5010641c00290001400a458400d80e02c3c407507115205050100f40a13021850461904805c0e040c800790320b85000081c03948a001c0c0103401a04980034507414151504c1c0011441040791a040880700da0042c006d100c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 640319019 1250 640317769 640317779
    0x12030f0603031d0a140607020a0e040305071b0e040f0201020124060201050c0a0e1009031a09100b01140d0e0a03030501061e300504110a0504110d09020316 68
    0x1484415200c5100c10510603c1003100c03880d00c407502008403074104080362007010940d820468680e20030182203920000000c070120b0f940010807a414450b0744280c07503580e6030344118200100c2c0118a24003800180412041c284801191040702e15042503201c60f404003000e14910040c1d0140041c2101803803d5404406170110101580381400d0448030103030000c11041d141e090b12b240c814400c2115110100742040a001c0c564204800402049401d600d0455002c4d038503036a40300c01000c2d020108080c001000b000784164154203010385010302030b10040420070480c4580010b800c0000c00000200341c0e55010a00d10b504407044c0c0c019140740010b0b0b20940320000050714026008101c28003940380026126800300604103019842d039400c4514903107075103003828a001e4004001c51002c21210a0400c0c8444688404000c6401400c2c055480f42e000e822035014860280007540c25958070039840b9506054920031101c4c9d2a40484d071104a40c0c17200440c0e030b440c050011a152038040040400340c40031140001034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 640320269 1250 640319019 640319027
    0x3090b0a0204060f090f1203050409050108010b312003090a050f0703111302191d010f0903081b06040b0105150f270d03020313170a12030f060303 64
    0x205403052500c4000010032000405c43e01509140070b4106403902e041c20038400f540c01f001e0315060203482454000d242980705e810bd001900c4080c0d20000c416034484008014901c1c1200c3da0325480380b4642e5811003400301909154200b03228000c12020038681d10800c1c804c00c2d004075070031401d90610304461030f65241003000c0140d0351210024015030f05801081d110000341c2001080307800840e038216034800030100303071030040041d00b41d5454401500d2503820451070000b242c4e0740030b0a5101c850a0780702c02d2203070f60021103002c9103540c620b000181005041d2010002d40e1390005240800d0303d4201c11003c1e142c040300c4102c1000c0311203c10800c1451310507001040308102c01004664140c450958002c00008082690b40d030580c0564038850300e07030000511082010b44d015445814240904c0c010300034a070070020001c2084001c00190940051b00000f6162503d580480d0090000340b4602c024030030790f291400d40395900d903404d85078018003c03c0404100320600c0e20a40000d020603240c084104000740c0d9030310f07000d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 640321519 1250 640320269 640320277
    0x20408250807030b1b0d051f170304060c05071d10050f0f1c0206160b2202090901021c0903080702011b0c1a040c18020708041503090b0a02 61
    0x11200c144145012980d0600814a00d080303d41c03241054074a5102d003603401c5139440044000d504202414000c00001d035409018003030080e030b250514405100c0001c185041181d2483d085440301024000c005101d91a0000403a01103c1c510701c0c04c2d0340c1d040f04c2c51500d2824241668131070b40041d0002101b241200601c4070b002d500070006c2c00500100155038030140302004006040d1607034050f81c0c2a021445078100a20051941c2102408072101c4034140c0d170014020f5007000c4624500b00140030040380422810886041d040110a034031020345401010f94002d0410f0006002401107021002103968282d094040d201710700b0851488100f144803515101d0700800740740409400045000b130200d40010700610403140c08484000c05070241c0e081c030200907201401c20301e00803175030b0420605803240e1720201c05212a0007182300e0039050006900c0d20345600b103c00c0300d6201419010b40f0400681c1c0c0010410703030403141100c072140f1128a0a2005000680c020658030320042c0030540d10400300020411154020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 640322769 1250 640321519 640321573
    0x15191215020a0e1003090201020d05030c070501090503090a0602011107060c120603030201022104150506010507080f030f010803212226070b01030807140f01060317120f0703020408 79
    0x141041c0244d200044083c0e42c0b00c0300000c0d01680140d21540a4a4844d40065600c003014600e81c0385061055034540c0c1c2140c102d80000d031499017000c52100c68900c1c2848055001f45901d100920030415035940030110352140300c0005042a5131514080107a90080300c015043c0420400c042204544e01e0030003138040d40c0041d502184200050822106010710180418001c940100da2500010a0301c0c600030001e0801030300716414004181710744800200ca040c020080305000343d08160b141d0038429a0b502c6000010703004050350384c0040c4120703140b81001500201c445843e130107200c4823549031a0b003400c024400001c0d00020900001003004140f021851130601d401c0f4200d603074501d80803c1c3c5070aa0540d0b01488900030105200c2c0b000410105030b64401600c00c5502a00150211111040c0b590f440e02c0f025850741d15a90b51511004c10601001083d550030110342c002005240211942c5d003810031000045c03440c0c0c40c040348240429a4580310b0307810380d07015002c600204c42000d0225200b010000c61b102847c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 640324019 1250 640322769 640322779
    0xe061005011e0f0c051207060e0d0306060c030509041e1b08091f0f020c060411030102070b0106180b040f1e03030503040b0415060e15191215020a0e 65
    0x1e009030009054808510750b5075a80c110800c3c103201c0003181d45601161081d81c4510402010036900182c5c10f004094091051400207000824a0119130030a600164140d080c1890880c08014141d0080110300102c2ea051408a55981c601c10004004011807280c210025891200f0048444a19884200c242c080c0541000700204c0c2d20030202d0f00580d045030b1550045c0c01401d00d08898044035860342000d402c06a070045002c0701d1214050040303800001c1c022046600a00901041c400003806500c1c881c03105800070761421443e034941e1081e00b007061068500304a02c554a20310720107181103d041c040c01c00c155046a6855540003013a403000c6c001c0c0210041203004806101820079404000d00845c1c3e49610750a0860350b440d1075600202c00024016a80d8010800c1801e0500c107162041602034020480794050034140b80c4142d00ca001c60f03002d400e500416241c00703d01c1c404089400a1384c1107440c01c003100300c03d0712140c0c6041002007002040c40d085450000c03540301c0480303400018074190400c040c0c0d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 640325269 1250 640324019 640324037
    0xf0603110f030c1003091103010504030509011d180c160b0709060e030604110d0501020f07030306050405040c03060b030c0303030f0106110318040213080604150501050a0b1209010e06100501 83
    0x100b68580880d4410b0030b82c480c1d801c016458826000750800c4200034040d40c0303030052000c1c034540400e0030b40382c04a5049002820000c0c0d200c484c0d41c1c03c01c05410481c090051200d01e14896400450240c071654a41d8002e074641042c0040e041000c0c80e01154420b50142c0740f02d04ca50000340c50041d5400000352010350204066240110380c071842076041c8100c201c0020014082c5480399181c1d510f00c485a45035241d04010320081d0038002caa000d000400b0011039941006584c0c003000c0c20020100c4e031079034003d03600ca0340c28002030101240000110b0b0054a4001d48001603003140200041c0c07800c16410340090701408040708000409000c003120078101d5030700d41c985014003c488c0400903140d10914811052414000340541400d0070b2a9026100718040110310110060703c510009103020804c0701d0445132241c403d095450002440e00032980100350940303401840034140780d402c402c240500a100c0034030b451400c0000b038040b0400d412882e079210300c00382501c000c0d042000e14040d400105018650215680394 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 640326519 1250 640325269 640325299
    0x71401181205090603041103071511010c030204080c040e1f06180504150507020c040609051005040b01233f070f08280e010e030705060f0a0f060311 65
    0x1048602d103075001804546176903960745c1d03000310360700c81000755035094440e4850205400408440151a101094a49242d80f0383c1440102c2c2c00e650002880b58201170041c403041000e00d0000330307130541007001142e000c6803800e0b00803400c43ca007460b0704a8424808e00c02060b44541d40b61f4582c0441c0540e0270600210507040001c2245a06071003041d50010700820840312151604d444036404150400c2d12031040da01c0000c0800300007070940346641c0040f083c4555880501807403510314803661004000c151002d0241300d0041001030603920404006a00c4d15030203410301600104070004641540000c00f1020a00d2031612407404040301007010102c10b06240d00d021240c1401680769014840e481d9075440405201ca4403008a500c50f0014210840484c88034103050400d031510704118883d448524400100181603203603d50a44034120213a202d43e800821520000c164003240b4a94440d5a502e96403031300e91184034502e0300a140441801c40740d186002d10200c00c01c0901d403820000e118089810011a1142c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 640327769 1250 640326519 640326527
    0x10e01060b030c031b0d051e33062d1c0c112b080f010504090302030c011803090b1204030e040b1f02071a0301030303020714011812 58
    0x80c003882268034014400603000d81820f400440c1e222203801646205031411100b00c1c040c507000030003140940e43c2c40d03004000d041180c81e02250a10b00d0300103105c080c00c0c01e142e06a503209030718401000c0c004402408117038240c11a01c64045100c48000b0340300740e940d81c8803521800710300703a48245d06ca081000d03402c18481d070300b0b054002a42d8079604101d0103150382c6498400407800138601c3c100c05405010103500401081c2005002542807000c0d0210002609546c000540c40120040700040c0d0a0100c08400d01c1440a003410030b460544500303580000d1481c41505041e49180201455520310b076007407034034442e070303200201d4a2401880c1c400d480344007007a5151803801d02030f4094a81c800710519540c3c1e001030042449032041d5403803810050030000d0b002c0d00d00004152241040e50100c64960b4040005449869040255400500e16020060310050b01e118074091540710610020b41096004602c000c240301e103000350a0000350324032000300840d103600c1c0c1c4a000c078603500000580b03118000b03500b54200140a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 640329019 1250 640327769 640327781
    0x70b0705071a040e06040b04051512010903020c0d08070503040602030a08150d02090a0b0414060f03010e06011e17010f14010b0406110309040c17010801060312031a0402031602010e01 80
    0xb2004140d03060a041500400071400001d1542d9401601c0d104807401c203884600c141c50007400c501d050000c08840786428400009159088940307941e1400b45c00c0c9021030780c08100e00748100c208840c1510301400d1030030003050600440201070064040082e00041c0070b60004000c0c104020345465400707003582d503085007000325400c6040c06904800100629030040c41d0601c801a40815015000600b80741c5240c0400c4c00c8580c010903410441c00d8201c24840d141c9040102811140c904a000303000e071098600c650358403820b042c0728001a80c1c1d00d032000c590030361101c902400003070070050043c8000d140c02c00b41194042d00322401d28114862034200c02a14032021150392905a0300940780c114689860908201c03404122171b00c1010b02c0b0700060040240c55035a5000366503205003999500482e00003820307214501c80e40185e12000e00c0745c1c03400c4001c00004854a004201d23245403400d00040001e483d80151240303000d183c4c60360380c0c000d10010420000369412a1040c401280980c0200009a50070305098200c1d02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 640330269 1250 640329019 640329059
    0x1003030804060c020f1603051912050711040203043f050a1403040303050402130b0906150c0a0c090c08060306041b1208190507021f0c05070b070507 65
    0xc0034100007404038030b03541c001c15045240c1e441115071466582030340034100010483d8441c0d149a40e076000f0001c2c401d003007140c140030346583c0c540c900c021605039481c40c1c0f8685c51a5004818440003080340011701025040c802900072014205564030301d0b01380b50100741d4111320843c0d206d100040044c003040e48200b40360010404208842640e401c0d002d0520300356002e030041f402a80130001c00401d040402e4a10102450107148a600c0106031820980704010700d12141803c43c640302d51501e0030882c2070761f41c0c524100e50009003e60f004190400440781d0805d107031003003524100c07803880b95140d1882084040c1c184507080741c51900b010418a003810008588041060701c0030340d071540c040301c04500401c154804080c03031085080013508089540328241490750000f943c1c1501c10800115015030b6101e09441d00d05502102483c055241c0007495002444021561040310b10034001001c40341c5155000303a040e1240035800c030080300c0e8155951480c040d010b45c80740c1003c550501607000c0016014130320400c50351150f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 640331519 1250 640330269 640330277
    0x10050a0f050c032a04050d05010e1e0d1d0907020f010e03090d08130312050c070e0910050a060503120711180c0c030d091505060a0b0f030c0d23100303 66
    0x280301e03100e001844601c80e8980b51303c4010000020940e46010390964a284200000324011160400003400c2c11501c061181d4000803400c07400c52510404641b10403510405d041c0400d45c1c50440305050090034608030510b4000d28580c0601400760340020303c0d9462255140024805c14400540041d124026541d800781c01100700c40040d070001c0d80c0c0c0400fa2212155003004030f00700035039944030540c00444c811800004240005041040c80e201888004068213044980c2213003170401095550790f070003e0003903032109031f07a485020554100032030b08117000074940141160000c2c1c0003000c040d100b690008508503103804540c0c001c0c0d03080d41000c0040d1242d0b1a03c2e5021540307903a0314206500120f40c02110b0703c0855000800ca0003e80b04a14802c0d0b032100d0b07004041071106544da001c2c0200440304045e02c0d1905c80d00e45000e081200b8180340d070445604800400c1c1c6d1a032251100007110b080d600031403102100c1c6600340405940d9040844603c4125040460341c4022961116100141c8094103800090006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 640332769 1250 640331519 640331551
    0x60509160b040b0702181e070201140f0604090501240e010e07050307090e07091508010b090d050f250918030e182502030f0403020d0510050a0f050c03 66
    0x84240343e015002440c00074001e03402c0d07400f00460703c91500400310340b248a0281e0004010304580d40c2c42500c01c2d4082c116000802800e841161181400c8000412034055102c1640015095440302d8104030040b0358804020711003036070540c0b0052419a150420780f105000003250000b42d4001c10065a8101e40303000010000035100c10800320382d240c1c40241842c051140804001400f8012150000e22504003542e64030307402e07420010300d01d0440040880001c2001031401c01030008161030f108032074068030201da4000301825589012414900003a021035040d00800e104d000d038000c0d004c40c00e052200045c100154004e501c1e00041010ac4150b8021021010f284d440100c0c0040c3c000d49072014031202c001c18400114062a00070101504100c41e0710105440100380181e203804a100c3e5507072140310600140d4140300a0b00b0180e00e45004910010780700c0e2604018007010704c00107000c1250030542202d41400329241158801010b051840d0323a02c84100d141400040c00101c07560140d078010320880c40c04400c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 640334019 1250 640332769 640332779
    0x90e16030b0402060403050a05010603060b040c092d0905010302010e27040c09020a021c02120702090a1e150f0b090909031603020a0b010b090603040303020310030807060509160b04 79
    0x4444070040040380c2000c001c20010010460030440110f209104d640003140503402c5203040800d440d14852094040c50a1000300a54190014038181c10ba520500c1144504006c034104000060540e4813010010508008041410a09500105d0680b8004e8891440c0484d11100380158408a03041e0511048000301280764010b03100c0e16610b03005401500ca40c018640c41c0c4034000100c1e880401c1c2c00b00540e101d6409401d40e1200d200340100c90b205075001400035080c00304540d60440c0b250315070080c030035a0075400203518490154040101c50380039542c8001c1c182c0c2150f218900500c5e0204800c10b802031046000648071846079440380a0b03a907488911402e01c925282400b00810002e03003074081d0f5001c2442610b503002054800d01d04414041d1303004005034842428180d0300c030321068202010500080150307600d251100d8080700c1d081035242c40c0c01a03036640e80c14024406580c0e660002802540e001950714280691900618081e806510a4520b0100a5009001c2c0400d41c0d00c9007091080044c0b008003c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 640335269 1250 640334019 640334033
    0x150f1e0b12060105070204180605010b0415030e0102070b01080a06060902191b050d0c02150703020a02090a090f0b01140d0203191704030b010e010e0403090e0903070c0b0301090e1603 80
    0xe040b440605005003007085581c00981602d1070300d0104172416170301c5141e0f0818003d4602230f09004100e4100c2551819040c00c0c58001e03a003140200384801d05490301e268a00c2242c00754111114203800a00900143d6111003c0035150405e40d1810345000d03003031200201703040c0e0082c4216862807a44410703d051248500905480c0f14803070480080340c1c404c070300c200c04001c90001e014076060040641d4400ea100340f010f2040001070841d4040801d080803090145100107034002030340c082d084e90103e46021582c0d4a0310030f10400380c00103550040801c0071000130081000010900745042c2e41d01800408004550300050008940401401a500d907005449100d06a485200c840d06840e0080d0041b480c8000c2894182015901690084a00403076003001041910301c0b040d9614003400a95540925504041c3c070010110b40c03550140e50800300308440810162082001107580c4030382d0006d00c420403e5614803544800c2c0d0024414110740d40e0815407401e2450781c021455248c980c00003409400c800742191a458 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 640336519 1250 640335269 640335271
    0x3021e0906090628060f05160f0c0815040c0914010504020310050307080a2105030a0f0f0510061103040602120a0509030f0102091305012601150f1e0b12 67
    0x36082401da024010100c050310342400c551080002c8202c0420345006002031646c100401c00108004041c411000f1225441c0c00c2d15407100d40255614030b02c452141890b001c540415800009a132040f24802c0b60780c1d171600e190301071080d801444d040f070405959031404801e40395200c01da41e0748025198014000c500d070550107035800c5070008005030a0181c0303800109141c05a10b4201090f10b5102122000400c1000200b0004200b640505c000b0802c500c42000b401600001d046005115105c94040c039049409501041401501130000c0c0018104001c041c0f2b00107090340119000104481d504618100c070000464044500030f0740145101410325203412465000914020100030307003000204d940d0b5a04000c03200202c1e081c500010b030b942d0100c1080008810200344030b01c06560410004020381c3d40d50403503003481d03120f01c40c4130f5800e00d000290a0500401e00401c41c51658040c006010407880c2c80081c00e84c003130302c240400c0c01000d503411040820301070800d8443d48120041c204809221140040421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 640337769 1250 640336519 640336531
    0x30b04140c04150906140109150c2003070b0a020a0206070c0e10090f270c0512030d0b040216170424020d0c0308011e0504060801020403021e090609 65
    0x2070344904000e0301c001400d0300d0142c0360440c0c1c410000c001c2400101c0e09807040340002d000c0038559840e150001c10000c0c0c05480c992080800110031240034083c181d000e4241c59204903440121118182154465031184040c1786152a01a21402902041500c1484200c5480389010317001810030507201d40c200401584214003c54402e150076100050104174251050700510400360110a0141400c40c500200e60003500341c0607009040024081c1000202002400d0076800d20395803807002d001600385a0440c20850f03000c1604a1648c0000c0d110300030020001d440740c1d0308200710174451140d81204200c240d00400308410f520540103044000050b1034000d480340c074003074584501e03030601e42c0e50203070804409001e2000b5071030000c852609102e40c96050065005c004d82d1403c1000c04800c00da1801442d24805000307144203264919000003003805d4520021008200013001400080d07210909c1c80e02030340003440200d01a15056070301e608410102e2450803020580503101e10129a2100100f2070007120290203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 640339019 1250 640337769 640337773
    0xc0a0f0c021c241b1404030605041406100807050103060302090105040b15030c130b0a12020c0a020a143a080705011503020111010c021c05120403030b0f0a030b0414 72
    0x9085111500c014a8034441e0503c4000080c024203c200c0305480d01454040001003203284141442800710101c166810f4907044070002a46641d1403410401c5040b500740ba240f110322607a820448110144801c4000365000c860a441409a4a40040d07060340c02a000095001a01c81c006020038240b80c0d01c110304900d4010300b641e84a02402e9010301140d4401e0b80d04919101c0c00003a1401c43d070b4204100c50004160003440ca42c40c11051000041c1003c54107004804120780014000f0041042004000c0040e6001480c2a020940e1162503480c418000b11016006140d510920a060040851446c0f94012800c0b40d540300080715031040001c1c048102030885421409102ea00c0220703209100700c0380c5da000742c0c0c24108072050550001508001c045552030300c0742c3c0e061468000d201035001c22080c1c0d5100240d2425081e0b801e41c40c1099406002c1c015030448800311702010003080c15450f0700304030a840400d64030140c0c0d598032036062200c03031030040c00050641c4d04d0700d01c040b80c001015098010011095601 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 640340269 1250 640339019 640339043
    0x3041704030803010603020309010b0909060a0b01031b020f0d090302030a0f02012d0905060a1b020d0209070801090c0203070c0509070309140a02030c0f01020d080c0409050c0a0f0c021c 81
    0x18809940f900280c0040002070342c00700812210074800d00c14004d51041c21150902203140206015039a080010108098280c484e068184070381d020784c003c4032200d20901c02c194501080554020350b540d001640c3c100c0107106180201200901500c4c40f08140c039009000780c20140000c1c0c6400d41c6500a6100480c1000b2802d40242a55502c601c0c030b00c2041d148840203c2c0091641c0d82d4000c14035a255040988078a404108045000b40c1021300c008070840240303c03102e140d00184c0001220b464103100d000c0e4101c2c1c030790303020490450b070310a844d5030584107101c000b0803080c041000f040340e9030700440c003005005010159040c016850440d000c1d980c03052640c6004103865006598a80c14080b242004079030b164000050b40085140c14032202c46540741c10745641d0494500d802c0002c1d59522441c920b0300a201008011405402c40c0c5802c0380c02030040d80005100c20700f02522450760590090340d8020000b01308142c4c024a0074030035400c03000603a40051440d0300321004202100c41c03d40306c4040488890813100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 640341519 1250 640340269 640340273
    0x20613050607030e030d09060e0409062405030f07260c031b01030f1407050a0c0507080c1309110f2107240c1106070501090b1008120304170403 63
    0x1400424482d44690b40d11000680c078001414544040702c00c4400038080601814880142c0c0718080d400302d0700003250b01290401c240d081a0008014100381e542c0c03809680346480d100d43d10614151400c0303031001c1c0c00300e55030001040030b49902c444031402040c202d039070742504842e500b6141c01c401c2e00d200e068050a441c1401103500002e031500e40681e202030700c0101d10304524550703907030544514819038141400c03d104402c036480140c1c511100040000062180204201c54828412030400503010f520800300d0f280c15465018141c5e9920700c2c45515171280004d090340001c03c44050180c049010307400382c8410303280c098407401c0000c5030b11308860054200c140003559210031a2540381c0740f064070300008041c1c8005d606240e20304c00c0d440c96001124246901d51011040213540c842d0036000e442d07030800b40d02030f05400700e1000a1464800d010026190350701b41401002030111410070030340600e60a8030700c114100c0d500c400c0c940d12990055042e001d4454240005030210b602c19030038811000368494107a26064483d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 640342769 1250 640341519 640341529
    0x30706050d1d060a09060b04090f02040908070b18070611030304061d010c09050901090615030506010e0a03080a020d08070212210f01082e02072f04060e100302061305 73
    0x8031410301480c2d40b174051942c28070109100303480200c001a2010b01c0810310b0f940729200d540403881e000034010741d41c03000448240b01c550010303074070310300e40c468801c1e1100c2c1005d000000030210100207448560150500005e50180140b1603060607035403a0014604668039615110014201c6540c0103144c802a000b90440480c800e05c6203861805694070340010f4a401c080034041c1d0b401050b001003004034580301003800b00b80c1c0483c0c01c3c0b1200301014500450981d45090048070051084c03140c4030f401084184006c0200101c2001a00c00002203500715510803440d00d1088031210b00503268500541c000d08079003042c91403c20001d00b02e00084600c1d03605599070308110354515071002c40308410108001c4006000700704041c0406103100c0900a09600543c80c5e18075404854200f42c016404500c0d8001090820050510000d00f02289051920048a406501141c2000314003034402032095140c440041507418008000b90b0203041070b0030035071306164256030a11080f98000a4803548619150000258a5840c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 640344019 1250 640342769 640342771
    0x1f11030c03040e1806191e0204030501050f011427040303140708090d0e01031b020c01030b06040305071202060403050706090603060e0f1612020f0711030706050d1d06 73
    0x4454000c0d42d0340c0b49400030400b412000540703903945101940400130b41001c0000744164024981500038a0346d40e51390300807000108070180704208100d0300f0758039120350300295501800841c0c0c00344009010b1940c1b40d0060084000090050208030035040464080a0030046007208510100c3c165050307541c00ca1440e184507404007210110002503d4600c180c91507044d100400da003250f4a41440c03030107030070040c451613103d00d00c00c0081010400d013030715004510b81c4030b1f80200000c0c00c40c41c04485010451901c00070b4807140d00942e0340c0c3c0480c3c00e108009078182071000440d02104c1d040b0002c2c04200f41010080340c445103014500781e90000c01440040701044080c01000000d10f890b0f00c8000c01e01d403401c0700217401d446107640446071004040301049007103c08400c0540e0f00c64a001103450001c95100700568003010440c4008032440d01c00b240e81442c16540300d005201c2940524041a02502e2031810181e584190b401050001503081c400c0685150242d04210f0700d20514501c0c0d00b5494412820140c98028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 640345269 1250 640344019 640344037
    0xc030403020604030f060606020a0302210426070b040302150f0705061006021b0d150608030a0c0203010608010203071209080706052d130312140907080706030603021f1103 75
    0x21174121208105171807046800030b10007400540140e138041d8a0280d00c9528803d01d2040300d0900f01000b00e201500002220060204a2a10304654518060100940d609403082c1c40140c45884e002042508403141500e088070b42c01410b4503009260808401501d41100d081e40c01d680b5024030030580000c1d003c2c020f003071151030303041511200301d0b2510074000d1038030500141885000107030801681e61074440359808030b4800d1300066518000001c00035500020002170740b00201d180000b2a508241981c04000f06c5415070084000384202900c40b908030f401c070303c4144c441c0700208000401c0106028010f82114907180d02400c3da580c145489625400144e46003120081c1102c81c20b1460074040e800312510040c6002c03080008455540303012030041c21240280031014061200c4a02158041c0ea656081a6100040810864840e04141070240c1d1f0b0f8904c50701543c003241c0070300310020507454407a1145d00d08981d0010310300c02e5580c403400140c03000010f0001c0883c0400400043d4030070b03540d83c108000c02c0809 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 640346519 1250 640345269 640345283
    0x1020408030c0105010e011a0702120318010809060108061303050903010c050403151122170d0801080318060c1005070e15120a230103050703030305010e0712020c03040302060403 78
    0x40b0341d5960500311041600b200b07400801480060002000a4024403002d920051082d6502c140030f000141d00000403080c0211240300c0043d415010b621058001305d0013100a8850b100240c56906d032580d25007000b4007070750324580e03c510005110348540780001c54040d402030509d1498503a42c600407030b095840b4600c081e004207034002010403c02403c4924203d02200443c01040001d0140e00c1c030681038031852414140340582d0003200e0f0341da0704014071520300030508140001084403a2140003929080c2002c004400300320103e0000070481c0000c0219805a59260045104400d030308041040340e4000085c0500d2034030400900e01050300482c868140517000948910f00420f1441040040d090021607084102d41418000e0030030742940d1a40d130603001111034070042400c84425649021030f08211440d10039503c0d007900000103000001c82c103901901d0184d80d05101683e200d0360100b011100036204400054519102c03840201040d48c06004603400e05000e403031a141d0780341c00084998015801c159000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 640347769 1250 640346519 640346527
    0x1b0602190f020a03021209130e01051608070f05030c0d0213031104060b0708090f03060f070215070c0f060b061b0f01060b0301090c090315050a2a03021b0102040803 72
    0x1203034004020703034001600ca1004040550465030001c1d2203064425001007042d03000b241c04490b5030340f0a010401401440c840401c00040300211141c040c00096a1030182048501e03a005501e074854010244500c00503140c00c072a41d20184011921a40014540030030040180451035240c40140000c0052000103540026204d0942c10b146002d1013056007007520413031a05008000880740002a2046190480106d0341c890281c203000c14404200b280740c036031340b40c0604000c02c03070102c445829543c0034003100da00322031090464001a40554109650f80f50118603002c5040c0001440705840c07050030791143c60041940035051010035880d800c08003020720820301485061403d01400c02c1403078840fa0381503000384840380c23501c20040941d01c03043c003504000719255407849080c40d01944590008507481441000c0000031000d108004240035104001c40b941070460460147c0034944260028a40213103104540103000d40301a0000d40c414500380c44900400726101294000070301c090002400c8103400f8641d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 640349019 1250 640347769 640347817
    0x1a07020d1406070f0f0e0103050c090306070f08060a030201120518073b04030f0c02090403030b122d0c0307030c21080904020304110415150e060a1b0602 67
    0x144140071244c0c0010400b038050348641045d4800d0103101c1201c02030a002500e500d5400000c840c0b4880c02500c544c0510070901801f80c1143c1c0f00c9a182c2480c000c582e190680e07526242e00300107038400f2602c000303400140c511400c860300f000554001d82c2c0003041000c1007460481400b0742507041003400c0d840036480108039161085c45c0c049079510300540c00610020103407004450300048290303d9010344094100600c2c0d5240e0842140200300507251250010018201440c16240007000703041701e007600c14003500310003881601854000070410511746405030810004181c0e22490821560485000d201c0c1e480369400001890700c0c1880300740301450090040020741030a00e40081e800d0030343d14038058101c81107003040e040461078020596081d084100d07070140e5642c40e41d0500b00c075090079154000e030340a4a0a103400700c600b01c40f02281030882d82d000100b0b09103100f1a10702525003003d100d55294005100f00306581440c1c1c46105151000901c01c0307240d076010403054031003008981104190072400c2c010181120341d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 640350269 1250 640349019 640349027
    0xf0a020619182c010806011e030b0c041d060d03140d02030103050109110a03030207180b06131a09060301090c0318060204030614090a110301110f1804061a07020d140607 74
    0x552800d140c03c80c900551401c0e03102a035801051284880019401d400c031035120407880d003244010740c1c0000f141100c906142450719280d508c030b486041920b41c414580c10500d25401c010740352013410003c0c00c0342044441c80c0c905aa944c0100600300d40d807a07104000104030343e150b61010354080c0d40203000002e244052490303e120840144141544911040c0808100082d400188602a82c000b0b01303100a4486480344204098484030313000039442200030500821542d40b94100008640e070303450904980c1e00880e010701c1c100d07100e040e49543d0040b41c100014003a010705900300081060981c58001034200c04940150000d0a0003103003195450780004040080c048a030043c10182d0b00358802001c128100b00110319a51131069130000d005044014500745550ba0a6205805051720b4561203a540c100180c1c5034031060740b01900040b2207550010301c200007820036106990944054448210000d03980b003000e982d294014642c201d1307001a26600c0d140002c2d00d130036035803142040f0b40f0b0014281414480c2001d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 640351519 1250 640350269 640350329
    0x907090e1b03030304121214011811090102100e1009080c0655020c120405010509132a0215090601060e0a12050c01020f0a02061918 58
    0x25100c3d52043c014800428100c2c9004011224581442100350b01070710a1040508a12030f510402440745c60000540556428450249800f48540810003031a02c13030b1800b0240d001da6104603006902041d00703421030300c6040c0e010305408008941260442c1c00c1240c8072100382d450002c0115501600882d104100d280200482e94000c441109000f051340c41040c1291101900c8404000182d042d40601c68408803454000d4100f5640c0000c200160110f04254140658480544415944241070b610805609090152030036500b0503581d2034035202d06c403005c0000700845c095004651035681d07882c199554600c81f003107101d545020310302c2c9844200b50031000790a0120001080b5920103008041103d104800304085064601c682403400150401e040459880b040341c2d046140038101e108038080a101000885294844003603080301d044a80380d8548030785a60b0303945c030020340200c001c0c048a20085035144280b11f00c2c1c0107600d86042c85600c604000700c82580706501a034038824980c1140040c52000541e14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 640352769 1250 640351519 640351573
    0x180f0302030f0609030f1b060103050f1005041505180d030b09010e0402011202030a0b031609060611060f060d05010c0306060e0a03170a0c02060d05090723090907090e 73
    0x38040303900d4a000700c4c0361607220741040c2418882c030003c1c5520340314002d0100c40c1550070002d02210695030f1203140944d6100000356148100c3c3c072075a90012070380555070042910890707000100e60444403c071001c1c4000780070064062030240d810090f04d82e5071200100082d54840d105550041240c0300402c05000078183e0607000100c4001c041e00410001d40d8004144d60030f884442200183e0b00d9980c04441401000552240740d4140141640415010284214403096a81141003040f09a91341c160950701440c9480c0982401d0300f06900041010b40004030a680c000c2c0054003a0000c016156196401c41c0c1c204070301e01c030200703580380020300c03519511030080040d04030103480301d1000d6811600c454004800344140c0701c08141c00050290381d0188103504250a482d4040c1c40c00d5111003120500c0c20192204840280c400e200d800b000088910075806107008031003075544541401c4005400f032101030f83d00100a0300e070501c1400c1d000904074169102c0c02100c450010060284d04585100d800e00f038055101e85 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 640354019 1250 640352769 640352773
    0xf0b061221180d210e0616031112030a0b06030106120e011503030f110d0c020603060d1a0f0c120103060b0f090108010218030d170a0b03060a020d0f1416180f0302030f 73
    0x5c50011500c03028104c40001140020070101290741e85400c94801501c4059603465005640880c6029440c0740040e50007003a02032424400d170801d0300d0620160703010900ca110001010403101060380309040d4005041030301100008103440360114010407000d1300c540d0007240001c2507400411100303607100000b02806160b5001500f000c40c0d071400000c03c00007482074040d115110004c04035207a51f40d400749085c012540502503900d019841c156400000004031035401445444070300241028165008070380140a941065003040e90031a1941c100508082c0310b4130760024590b00810500c0c0d615507600d28001c0801c0c00026035924050001908203003005c0c4100c60007940907400750007225402c1100004c0c203150700c0c2e4035400700e0342e40e481e150b00140280184168045c002ca400703000901600c1e800034121081c030703035406002001d400d003030030320884444a03c0340c401d1600700400f280010a06c4250003042082600c1d0411007200c1085654207400740da5407050341200c0d6468400c0003103060a108044c0881c0c41400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 640355269 1250 640354019 640354037
    0x160302191203020c0f070303091706240d0f0803010801060b1204080c0a150204030209060d051506060d140115090b030a180f0b061221180d21 62
    0x941c00a000790403100240900d030b0046078075555040308020828001c00940122042e031503880c00d01400390140340c0288542c1c031183d0315030302c442801d0004903c2c1c000c111081c0c0016025441c81c0d06406881c010301000c540c0b0035a21009030003c01c00c1310f5100f038240c900690884d941d03545001c15003400c440880e03104050b6042c0c107120303406040c0400c2c2400c95002d9089054540d17a484940700c072030305120140e08010103004c1e850744c849207525071301d6014105070380c800e941040140c1c565100b00140c84850302401015a88a9040b1201810a544d50740f070300440302a02c03550918080d14110015241085805814000820010420901c1040003025a1040341c00d10880c0c050a211304080c5c50f20009114541040d200c0229041400c87c0401d128041034210241d51281c0420b898040f091210507284644a100e154400724640c1c40045a00c1d1042d02d5181070581800c02e820b10302c00d0b015000224039003802030f445a1868034540303550750245200c5114145040130031a84030241d195413800710100e40c0c10442c202d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 640356519 1250 640355269 640355273
    0x20a03140a09053703050406091a0d09061508160504020909040b2503020c0106080c010e04111b0601090e0a03090302010509040f150302120a020a0515090616030219 72
    0x49481801c440b101240a0b210b104c94400801c04001d0a1000745801c0d1100320301d540c14190b10102410507905250303900d00807140d9a01c0d203842014140c0b03007040142c0008010442000406a220300c09035481021301107034424130640c082003507183d2036004410395000044c0300400c0207180c154040c0a0401141c0071400c108200d0081601d00d00003c000400340d1b1101030225008441c0440c2100007a5002c95a0100711041200001c020350804010030115600f4003602151700940800c15007078802041c3c1d2400050300e1010200400341c40c2c11000c0a41062003002641c00c800c0c4010078104441100340c00a02444d490705446100311520a00d51030169001f0001034000a58001248000c880d024038025854210340030005005021416071a40c51619100741415101310b603044110031a8000c82c0c000818000308a6400d844080b08003000b075005142c420140312074505040b0071100d90002c1c0003c6404c0050a60100f062548802000244c0128081c400020941d040001e08052203038007a220b04020596 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 640357769 1250 640356519 640356523
    0x16080c03010e340f021b091902040b0703080402190509010501110f072d030b0606070c080111030402150a12020c161706071d0d0c09020a03140a0905 65
    0x40e0071403408890041c032414040b1030043c00c00402810790140102d40d40141c1c9006000031002c03070807000c0980100c3e0082d4001e10002d00750999150000780203001c6655401080c10014184100c0c4604416828880401c1d162980030140194912a480d0081c00342098010884454840320702d00c02c640d0321400051010ba280c010b03407a0304440080c240500003203101d1815074200b801204440c0c00c641703e050b100244d006c1002c100c0e0401c614008c0c1c4000140400c041c0380a402400f81c2c00068a60f18402e000314289050100040400c54040d0054022140d121700e505c5095480900848100c01000b0046c8429483c01d01844040700303801924051030304d00c00c041c0240c1010194088101ca641c0e001c107281850284c20710410f20410134102000c40d4041c6c40d5030103150240086456011a072081c1c1000510041c011100500003440c0d072a14021b008032107008205079201d080c082100c0349084000002020038150010340201502d035100802c01e4810141d40320800c4100070420103000303017020900c602180c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 640359019 1250 640357769 640357771
    0x4031109011d06010e130c1115010302092a04050906063c131e0f15052731050a060e1f0608010b1209070e16080c03010e 53
    0xc030b0001038401c0d540f1440181e80c484811801542c11003801d45440c00354040943c0444810035803a110010b01900841e00155207800c005055019481a80014005884c14440341075002c000c02034100e03c0c00491046c0d40d078a034103560445c00b820490200f41840607241441c895036000703000303855041c1011548465990ba400e80c0c00200304800c40380203501c0111301801c4126060480214035029075407a002e090444001c203d61084003080e401c00300342d0034200b40444000c04111a100061109040e061031901d40d10390440d00b41c2c09090110400040014010780c03003541581c00f46010303030b55003814142e00a101ca01079000f801c2c8040742030104a035500150031742d1020f041e045180e0000042c00d59800b12224020010354214a030514624000c011003015850440c40391581c1c3c0c02902400283e540c04143d6041c003081c040e0128036407080c84a6100c0c0d1800c0b848841d07004003000100d0304d4071556000070001d803880c252225019400124103002140d82c0004203903401a06d84d603881c928641c9044181e4010202c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640360269 1250 640359019 640359059
    0x403030509010605120304080c040504050c0907030b10090501020606010923031213061407030503070509011209031e094208040209060303030702060a02030a0905120403110901 77
    0x303a1040031a00c8290250721850203494040c024215001240810707a549400901c5151194400c1400c4000d40e801e05029040c00303240d2141c002d00e04100c11004000069000402d01e0040550b07807249901c2e02c0c0c0e43d00d0a0031062900745e40b40c10003150709140009080800c0103002c54103201c042401040f2028050500c2c19400c5480c1c83c00080102c8114006414140c0307a111003218140049000d05690080c0003a010840d4056215203210076944001c12440b40680130f030140106006000060600780180001e050302e21051400340030707006400d10201c3c21604244000d4000074002c4030500a12084181400310140d41d07810000092480c0107215228105802c544480e0841c08001c4540d04804000c0e051401c90410248040cd00d00102d400400e07400342210180d12031000000800ca01d0b060210071039016009550241c60b0607641e105000c0c01030b50002d0201c000c07040e521484140401c0081c4020049003064040c50340c1d84500d98100a1000d111021100d449181e902c07004014422842c941510703010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640361519 1250 640360269 640360271
    0x60903150711030c07050901060f020712020409020904060f0506042906190206100501050f0306041d0d080405060a18060f0f0516090605031005040f020c0111030106090e0f040303 78
    0x159489608864240d80000703400710b2484003059060391242c0201e041e05c2916801e0f80c1800440c0e80e21402200c200c0e110828a0000d84c008007410b00860600486404a842c00a080482d0a01c1c056010854200d0100c3c2c040d02c00640e10050b0380d00a411307500500f0b8022a048a0a1109181624035122070199801035048020065440e4414940310341059a8084018415010066429500281d1900001c6482c0d180004480301d001c10301d9030086098401040b030700300c0c0081c110703a0b601040c880200442c034942c01c5148001b070071940d88440104003072504442941d1301d44007141000d142c0b4034904a4007500503e042414640490308182454103a9080300b034105c1c0c408a5900000504040284401d4401c124003030300380303810040c1c011503e40d14103804914642c0c0c0c205005584210442d414002911001500306a0352401c00642c50150001e0000d854101070040c07400c101745401c1401c44241c00025140201c004c40100320941d042107101000700030039004450340d4a070035003000008000c000d000034141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640362769 1250 640361519 640361521
    0x11150415050403110606151903060308040f03021804050c09042a0e0a0e07090b060f0304030c05120408060a05071707030e0c030f121c02040308120606090315 69
    0x40809910952a6084205000c011a080a00b8020006031034904800c88620801000c202242081d4042d8940704050308111820408c1100c003030482c0c40580c0700288200354840c080030002c40c00040040c402000a08802c1081e1860761040c04020bd020f0a001e481c1e402101f4200004117101042c9540b564804440c1601650344515150b2080d8119401119420603e00070009445010059100c29540b015526250f150781f034040302010386402c105086116045884208030300b034469005160301110042c00341c1c4c2001400d4403607049980013250f040d000640c41c041101c040c04070500006600d428042d904518150500c152507070358200c094400c031b610b1643e0301c00085c1c8241c412001d0a1210452038080c01c1c1c00d0801110003005003004200c0c4144034040d0030406680703480d00055416400c01d112000e0409100e400000010343c2e08400004410b0a40d1540382814100242c8010000341d4401c01010381c0301e00000340403504200c00107150030b01840303040000110640e80003440304040e401d00102a211 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640364019 1250 640362769 640362773
    0x209060607020d0c0801050123032808131d0112030c142a0a061e0212040f09051b03060906130c050705010b010e22110a020c030706111504 61
    0xe200e001805002d00c0584000421751500640001c0d04943c041d1028200d01740d9003405900c864144080741d42c0d0700d07521503944a00c0340c1ea200091501c03060100561043c4002483c0c071101c21640c4618903007007006a030fa40c028001c01d1540008500c0d042001c161885042d8103282c0c03000e00c4252141c00c0a811306c00180f44440c10005429000102d694207142541e4540c40e0055041c0801d61145815280705800400070700b03254200000140200d0715950f179008803081b0f071384540c42e23040502001c0ba44114094481c0007003c0c880050000c0c00140954000a54500e29100c2c944045620103090101c3c440903149000e04208100f0040c1d0fa00120100c850701440c1d00c903100000e4401c011075a203c0510360801800d54059500040501002e0b40204c0003030043c6032003900111840f075605000a035101200ca6903c1041d418814802582001106400200b2001d101427140e00d0360046080e420059000c2003030380d100f81c00c09001c0700c0028a041e06003000702d105401d041c981c81716284440d6001c520411000101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640365269 1250 640364019 640364029
    0x30c090902060f0f090915010f1202090d14010e010501060c110f09070507021c050a1e05060a0c0e1e01111e0601060f0f020c0120060f01090612020906060702 69
    0x29000100e00982e9a182110f41c1d01c104e9004036041500c264a440c00181840310440c0504003c20f00594611000d0070f410340c400d80710f07280d0620b01500001d6090040ea98161240b1081068160040104a140d0080c850440b0b0035541e8101c040c1065134108401000010340045030205001e0b4003d0718051001c240c0400316050130064402e00d0340c031103e190148500c29400400406d02640203070f4200380060503401029002c9403141200510356400000440b001c40e039044000d5200283c1075a00c500500d595444891400905440c1010015038440080da101c0750080d1003041e45003401da452880382d130078000846640d0b21072600350724103104900400c006204802d200e55a020140171042d10700300a881901203607140424024100411071024151358041c0c01100034689610081d801020716003c0f64004640e50409514045842c0d007240f0301e2203540c10303403c5c03181c8c0e84916454510115150304d403403c41c40c180d9100381d00010301c00c1c500700c811074050386a0f682416404402038810310b40e21000b0703101080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640366519 1250 640365269 640365277
    0x9041a0c18091e0c0d0e0307050a170f120f01050316150e0a09020d0c08010f0b0703170a0506150a08010306022a06060307091404060c120c0225030c09090206 69
    0x500f01d85503c100300a218040000500600c4107100030400504030302140895581c440c8140141541e4010340c03a110000d403a005100180c0315012044900f0302c03400c94040182a0003040c1e11800503d40e403401c00c5a0300c0100c0a51500401007100101001c40010b41e0ba01524100f1b409070254030150402c200300071a01802260031180c401405200016030760341c0d03111000350000c0034082c0e034070360416034904405071040c16464144c88008558580345842c0840c88851540445400c80910502889011000645440031fa10400c00d44030003061038034092041103408141c2e5210011801002e0100950166201e56030a055035030003040160345d64003944a800281440303410720f40c0c40c1190002030004070032001c2261401180301703504842d031442d01ca050760390507907030301042041c80ca941081c00100070811503005140d06040a0400319010052611703140240d07a40e039429640564440a00340008840031508003003085003400d2250b9819003180c0c0c0728011200c01d0320aa020769a20b039161030781550f99001c111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640367769 1250 640366519 640366561
    0x1403030a0f05153010050106091a0c011b1806051c0e0703080c1507050403020f061303020406170c030d0c0308100806010e0108010e0d0e10030b09041a0c1809 69
    0x8080c0202c800c0340c0b0185d45401114070081030f02d04281c00001c1e82400b9040c01000e0301c0395404410045e007004c5080b03144035002540b0001c0150340390794160b8400320f0300040301c50b061041544c6410301003a2500c0100700743c0ca040e500440c100300701040200450003c2c60552403d562419501140c0148004000c61401c200303500090403103000060b0181c0c0468001a0609040910841050151b078440b1001d43c0c0350302452001a41007511501010500e103000c2c0010b08418509a81840d592510384d00410225016034010b000f000b02d00141000c0c490800300329000a03c10b0881c0101003001c2200001000d5200916004050000342d0011039640740000d09488040e10b040000c40d00c140d80d4950040d41e603080203116881040d480e2009600040c0c0d404104004400401d4072030304024003c54040c072680c100342103210b204041e62443c00c1c00c0340e5501c0c442124041c0303006515040011071040100845070002505010f0024420030807803044031844ca03420b00004408854000e03490391580d8810b07210745480425 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640369019 1250 640367769 640367839
    0x70b091f0507020118050109050904140f210f120c07080f09120a0302060f09010b1507020a0b07050c131e05100602030f04051302071403030a0f0515 65
    0x1200c52210340c0140940000340c003d99900c0150001041740781c3c4044054010380b4001a17080c001405541800380f00180c0103807040c82c2138900f01c0c030110081805c09001c41c840d0519a080490402001da04280d80040511120000e06281c45160030100402e4031a0f40640e584082100000800d014414070a032120150404041a540e0004412020f001c0e440b40203241c1c852020480c40000c12200003401c45825a4035400400c019202d142c0b686622901c0201030070305030340d01c42240300d005490704a104d405d20482a03401030b440d44882c1c810008078208641102c0426101400710310041400050b42c2c22001105480d85034107510a40008009041c12a100c544896180c1d08a49041d00d4140e000c5071040f295100820011921180e0807030300d81c0314600308090170303150501c000d0040d0b240103a0044140140810014640292a039803003114041200d03a80c030b00f40c1c20100800201540d14040c08a1000b1440c02c104000e01c1c08280c5020703d81c2012510f0b9006145000b11a044012000c09072408003544404c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640370269 1250 640369019 640369069
    0x703020307030c180225260714060603071203120e0a06050c18042408030a0201060b0f2217070314030304050607080907090204090614010e0102070b09 66
    0xf00034100ba5110310800045402030b007a040c6044406200791028410080d400c8980c9078000f07403468001407000c1d0003d864081d40e882c4400840c19001d401e038071003640c1e40000c694071904241014900e40f0300318415503035541c200e9010820103940114480080d10081c00e4038645101c45401c044074000010742c81340103403e01e0300c03802900300680001d1a0046e0b41c803600040c0055660702d14a01d0007401164250b00c1151560b0307141104500c1c2c640c11140005e00c2c9034103440840100800c04d41e0014010354401d034a260000902c0000780c41c0c0c28080c000c0075000380005240340c84515011034103148148070207040c034843c1c22144070f80d020075034040d21030003400e20301d001c80801c2c086030600d0740c3c0701c60843c402151071500848040d240c1560100590f031140b030300480036100b82c2c1d450100a5409a40c012301508090207500070100d040001407010f0805482d001c0800100745044c100f01603490710b0b101034034905009007400107000300da034000b40c000c00fa21030082c2100c2e21100c8510108821010081c141805088100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640371519 1250 640370269 640370273
    0x303040b0403020910050f150d051302091621091502041401080906072a030c02120319030c1407050c04060f0b0f032706041401020a090314070302030703 67
    0xe001d801541e0003100d01d500aa02c500f4031208000750a0300c06c8940000403000141c4440c605858a4107450b2140c0d00304d00e1a103084207110b002125800c0721742950f0050800481c900358100981d4544d80110b460011820300e0403e60746c098040d800c5007190312071080020480800410b20303500290203540e800003001180c2d100351030b2280080c0d0800d01821034a009420141000c941c465605203024400034006441e45840c0c100003123492200f03144e1801d5030003040043d40d50491080510b10400507001c0d0303480307400d40085441001440c0c4e440d0000210142d000340620b105229000c40300309450980d42c100081d50298400065941c1c0c40740d40341d503681c0c0b840301140450501c04041010b60240300704032004c000c55620303062072245d040391600030240603410510281401300e1003680115000301005001c0c1d41c8030010101eaa4482201b00740c4070304459007090090008000b0018800d03041c1c061440c00035810100c00000083c0b9400c1280b00c00380c00c0311410010510010700912a0902558002d410340e40c04907141c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640372769 1250 640371519 640371539
    0x15060b0a0306290913020f1b06180d03050619090b0f100206010902030c070f060c02010c0201020c0a03120f060620060105010516020a0504050a090c09090803010e090c030304 76
    0x50300c0348480c01e220000300e003004030780d0400c1108481c1d65035115032818044c2070414005410754184801310019401c00c40c3d1349071031400402801c071103410b4900d06a4010203032280c20f424981701414100c2d8081c15034030192540f0030045404aa00e82c00d614001804d65680710010703100310406140d542112384000e1010a8040603900110036440c001d0343c0c20b0340d00c8412002400f075441000c629140060300001d00504c0380020070740085d41c00004070180503003407440d10f845e83da50082c112541281e02a03503810b07050f4156602801010803104080c0021814901e581032031035165040024001c00b01b16088126480e4050350340d10001081e040c100e4100062921a20040c1440d8001c2016100c1c141c2c02424124003807400062040c1604c006075101828003240031744114481c2101c0e00100d92003040d1030000304103a110fa203d07003480340399181000303d032103501c0d418030b04c2d280b460507044441c2c0d09062000903030102e07030031000701c030b0441d0b09991190486641c2c0806d550b0030543c1e405019030b8075001c0058000740400d00c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640374019 1250 640372769 640372781
    0xb031c0336020d1b0905060f03030a050a02030d02040e061e1c0303020f0a090e161707120e030a03060b0f03070e060c15060909010c0e01050a02070302040908030919080715060b0a03 79
    0x45c0d40e804020325110f000401c01d201d6005031a03941c0c9030b40b01b04203a4021520400c060855400e1600460b41002a24040170060b6046a0001c104104854080201e42e03c0c0c003400241c91021240c03801c2e117094120901040c0290500005a248104842551070403d4440c6d8100c3d11484c2d80248001d444a03485c1c40300804c8610300348502c000c0c440c0020082406211607004200ca000c0791a11011111242ea000d074100340d081c010420302c00c2c0510900e80c209084160702458030000d165401031951074802c204080e048600641000d6a82001441070914440d404004c1700d4101d400d0f400c0010703d610209000605901c600c14840586000d40f83d203c4010030703256416140100f204503000482a9901341c182401c1b80d039410503c000080c0307040c1c07442d8180d5004a0062114402d18410769240c0c0380c403500414107450050304102c3d440344000041100d441e005100d11984102c4a0f4400031100c5625104d10404c0e000705c81e000f5050607420b0021503211042c0364003003002812151142510303001c66000140040c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640375269 1250 640374019 640374029
    0xb09060d1812080c09090c04090e0607033e04050a030506043e281508010f0618240305010e0603100f0b031c0336020d1b 53
    0xc2c24501c9031280610f030310a21131203168002c0ca0600c40031408000c400d46c0c0140040d000070004220200c4c4031500c0380140040b038226a0010709080c100300f00002c04650490961151810900824000c541032000c00c0760126078403402d03458144006190002d8a5100d02d40c4203580c481c655800000c01c03c000400c8082c0300300d028004007d001540034201003240700c8885055000c180c00340c09a6000000107100e811038000c409804404080d01c1440d0081c440115807106501070b9100c000b0400038000c006c032004261408500d4819081d514002005201304040d0003200d040c000031401c1805480320740301c1114024091440041c42c4004140010032200744200005030000e420440007003110036090407007601032407014008180e900408000f41e4010304200000502c2c59480e441c0414240d0740800161801c6035040564503022201e008001e0f044524480541101505000c9070601422a800d41030540407031038150040c01c00d034688000340121407650801049079892a1095000b4544604d040341966 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640376519 1250 640375269 640375283
    0x118050d08060d030c150f0b0a050d0b07121e020a17010302100c03030f0c021c030b0619030b091503010e03072102151f050f01090b09060d18 62
    0x4800440403101c081045540980205031041d1140000303101c0d1880c2c3c0300450003200c080d181181d100c101e440640340c03044400b1000b161910440c020b5450030084100040c1822582c811003844155102c08141b600209440c0c00d00001c0c00e80b128030290320f90452440c011181c17001141103030505a60758000d401113981e50300040c103c081c00b00303c517003080310540e4183ca800400740414411300341003c803194041400118209516800d4801d00741c2c1c08d9016207800502c0c3c5401414520000040040c10b941c0b00d40700110401d410a400300046840312021038416500c2d180e4200c400ba400300205401a00034801601d40005450742003220660a40c440007034803100c11002404802061480c19035203006407070740603101c102503110740d800c84101240242c40310a500e0045e6060f4114402140b0302d00c0c0c0301100c14019030324020420009088034100070001420381242c080c3c903120030440c0003d02d010254090000b4161000a5010150361071006541d0309008200061103000700080b41c1d51104103241004030f0700c034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640377769 1250 640376519 640376533
    0x1e090501080d080c130816150206040b04030507030c1e1401150e090c180609060a060e010f1b06020c0705040c05070b04030c120e0909031306030b0a08011805 69
    0x140102140a90340c2c5030b8070350303030f80c0d540d07500c40346014101644040300780c07480040f10140000b9240c0d000d10a03e04a60082131902c0e8030549003107020b00301d12105c600a441190080b03400c2000084060446c16007064051800740d0b1507000720b25055a100802000140c00410100f00368440c410034841c003014001d10070f031405080034541983c1107090314125281d01e0440916104103000c40c50121001c0b603070004950b41201e80401407140801c151950464548001042c1c64080010f107080002006401403c180e03852131689181010040000181c403023501d041090840711203480c5071103000c04030072400c002c103940450402c0070300e0040005e522404949980380903200b0005001c0c036043c80b500070364030b08a840c0d0070703e071840ca9614003840700001130044090004039050b800c0403c2840d911104d91120300e85030316086900d45420443c94074030041015500307a00c02c0012944102041d00c070a011210a0b08010a01c0d2800100050050860340c205011940c68082d02c610384085040c50000c1d5280900c0c190b07505 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640379019 1250 640377769 640377779
    0x3090a1109011424070804060908061509040323040302031005160c031106131104050405190303060b0d020a18120312091a06040b010e0a0e101e090501 66
    0x1081e1003407080243c181c1d540c210710400360034880550201030aa800445448558070240d1031426089400192084a00800d043c40600c1c0c00c12456000b4141040081030907190070b03a24042c08070903100d0024003842c0d400d00803404041c003c940110030425814140350800440310f83d000c406400611003a44039207d00c5001c1800108584142d9000b413408a83e44e8030f0b0072541071000e480c50440410105d040181c40140b00d014024180101c90141d0307010803042c50504900e01708401c80310741c0809407903c0385151009100000d50000b40c110100440f1a80800b00c071a418102500107240c280e0001821550008858000c41c04a40c010141500039844040740f4070a0300b12126000ca21901a000e151214a00c1c4038001c2805118561040d00c0a00004941e01d502e55844409400c04040160700940013901800403502c2c20340900e081035503080c0f801d0105002c1c078000051180c1060720803602031160030710100760b02501070340c2c404000d000c3e80c2c002d624a040328840d6816542006200701000c046c501000460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640380269 1250 640379019 640379029
    0x30406180507060815010315060809070e07020601180209032817030601080115020a0303020310171f0c0c0803040609080714010b0607031d01030b0a0924030812040201021203090a11 79
    0x40c200711880d01c0c8c94140b03040800036a0180340180c0700015a20501c140001c00140902e451403280007264098a441d5141c46021942000c0f0207100700c02090051025030131035100000c00c07035000c00605084254a03120000790500c1c0c50508400500038003401490040001c00300070040d40a070100780d84035101030385e894644000100c000341411006030025183c3c0c401280c40780e006147c00c03450f40d002030000c00d0b5403881502c55902e086441150142c0110764080d69406110300c6a4285202103141806841c1c1000c00c005d10b02000360b00000d0808401201180a10800313510000080fa4030041c640e0b0fa03481c1d1410081408408444400c95540c2030006a00e428100b540980e400c850b41615124140e101948000d083d104105c042d441c105030340d42805281d242c0ea04c40c0340c0340081c03035028400a08180081c0e1000780584950000060250800c1002c03c00a01444126620906004c4886006850380c0c030040341009a82136029081d40c4020040c01107514000c03503500d0059206554200341c10780c1c41010b01c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640381519 1250 640380269 640380281
    0x108060903070f150615020f060912071b0f15031119110d050c060a05061f020c060f180906010801051212070c0501090b0f0304061805070608150103 65
    0x803801c0c0c20910018000a042990b0000000d1184844000d21004000500d084901c6a031100c04410600a040c0410340e40607c20b03400015506409440c03140b8102c0002580c0301c14500c10002c54000004498003031010b20041d9514004110a0304402c46a41d520101c07410805805621000341c82c14844441ca00c1c040e1007102c0c03171740c0301c0e03100040c0c204010a802199040c8820000e1000d100f0300c403149144080f800d1090941ca40b006403142901ca405845505141440003400944030628020030310102e5524041150130703400300c1641244400c5410082242000d0b60751000c02d4001c40040342850090315828042c0a10528100c10340b0039068504080100003030f400e0312410301050001006010701d04141c1480c05003c85d1481c101d64446280008146003031b80100e1058800030411030091180f503034000169030050080d116440e0501305140301924283c0700c040c00003800310707581e06180351550b4144428035010381d40201c281c03000d540c0c0d0b80314047d00c46042100c0260b03a802149801101a42c007a03c240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640382769 1250 640381519 640381531
    0xf010e1e0615030a0203010e160f030b13080d060f03150203071e030204120503040f120b0c2b0b010311040e0a09030c0b091506120309010c140a1a010806 67
    0xc00c800c1d1551050300a98030002800b6035010b000d034103218009604c09014145412015500400e0f0600c503c4c0500103201c401504514407001000c40c0800224229201840d0020010780e50304600410b50301e002c8596214644174130852600340880081d001e04210880400c8901400364688103180719489801241700c22a07205022034042c00c80b0140d640070620710050500c0b03150400504d008d0b20b0307891203280c0d8103000c0d0302202c003540300003002c1c05500038000001000342003501c0b03564003241d02a03490110b100c10007828445013800200c0c0c0000702038003024840510f82d6025400c0c41512040d80d00b09406000f503031401c6800700b402c0c58002000508518200c030101c07104620b085245454070b18070103014110602c1c080e020801c0440c031080105058034441c500500d0b201004180041c0448110350500b000200f5130740c440c2c107400d401030b2174211012007241c0b0441e00c00d1074141c03200040d52404078030380c0301e00c08014005071103032000d820200021b41c202800c031122a65204030701a270340d07035054640c0c80c03100300c8203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640384019 1250 640382769 640382773
    0xa0303090504231b0c01060f090f060e041b030b0a050703050903031303110c0603010b070c05040b01090512100c09180902011e111f14010303090b0c01020c0f010e1e 72
    0x20b001e10341c4c950b9000101e0a10040d00070300c1c100e90004040e0a41d141c42e04820b48a1400764020007124407981300e0780c190f010209405012840ca09100e441d03020302c0c02403000d04a0201000014030b1600004181c101071980622001d41c50b04100969400400c011540400441e00d0b01c4007080141c0d00c0041070324030818501140c0d02c4001d0f100e64048691180440091700c8134400e80603000e2141d50307400c001d14082c11b92000d003103031208004d052021b50011690b0049024900c3e0018100c0710766489801c840584805850005007441008000391505a541001c541c80c0c91030003800d2007285600c0040c3e0003ca0303604400b500140034440d41003004803a10b09078024003140e40000c64404580c05c100320700350300609038100504406401e0707044c01e0508848200c1021285542024900b44402d18400c082e07c441c0410a0103178950306541c2c001c3d295059a0281d02d42d400350209503607140800c25011030784483c0d801000e03901004825681079020304022081071030a4002c078200445030410441850f80d560717100d180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640385269 1250 640384019 640384021
    0x81b0a0c140118050d090b03150d0f05010218150a030b210105040c090e1f0209031608070509040c12150207050a0308060f0102060a0f09020a030309050423 68
    0x816509039410840407100a404100356449480081c401c078540c1d40c500920b86a40301406280050401a1a4010070207004d00340b4000c1c0700c82d514510950703a020a00807000520103030188005110030340b11101c02006a80c0c221140c8080003019000350000c1100103080740e01c004402c1d0700f000000c00c02141603019240003070108a440902c25000030386800c10103056480941d07900c4038010b414407004048194161f4407003081c001007006801441006002004040007015040b180481e02c50445411106c000078200705103a0000080703504541811000404581c1021024592040411158461030080b0301030404001004d0501043c2580b040c0d506c100168080740c00c01e000d8200380c0e2202034058801005a040303990440380644014141a0301030740080902078424940149002001409180903584144110340d203070340c00103141a0480c112002c0400d000d60107407922401031120300c50296004a0b0f0f00c17400403c2c19004030114080c0d0701c0658040c0080c41c1c0d8440442c0000c0701d8482a1051594140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640386519 1250 640385269 640385287
    0x2310e0606061605071e121e0204110c010f2d0c0c06090b06030c031c03180503040b0a0e09041e020301060b03010f1706040b01031b0902031303081b 65
    0x100500428010010052410f01280c581c1442c04e542c640003055000e118420020048080070940c1009080c40740108072212001d42d1122360906a001842580444c02e050000455641350000300c000300c00c10300031640302c1d141e440c05540a80303080d0445400140c0750103102c010070708030035051600c5403ca01d031615603041002100e10008018840340c510420042c1419071000070003c1c0940703c42c00d4080c801640e2107003081c1c1c04050a00d01a0407030180700f6071244005100b96000c000c041d2014a00c14180007600918800b0141d035088030403500102103010005010411207881005071050140307543c1c0300408400400144242c02c074043e00e01038102c0c0c10041c3d1004807007451300360406101c0c0c07020f00007095196550f8803c4040c0d800c2a0896807500e020698240210300e901c01c1c4c081030890040c0d0040140b130815851f0900c0c00350043c00064145800a54142d00510b400c281c114000c00c0da04808644d0b91800b01024005103011038400ca0008140c00c000c10074078080c43d00b03d03c1a04001e043d1172842d2564030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640387769 1250 640386519 640386529
    0x6051e100509180103140601030b010b1303051203010e070329010c050105010f36020322060f110702010e060d0e15011d0f041e02310e0606 61
    0x480000810481c1c00c00c0703041e41075101d141c80d190603a507511081001d5941140f4148019041741c904a0000d64000c030300400202d6204902c0904440c40030410741d9607162981c4050842c0805034101074000c2c0700d40b04608a20313201200046048940c0042c41c82c0440c3c0b9103800c101c0540c0d45500c2c140d485c009445105607124002c811103054911014105046102c501c6e50b0b4460940d802684440c0d2001502c080400406182c1c24071360201074130322030a85a080d410710784405c000c18007481c0e07400100e550100c005200350382022568450035402c0402c000340c0d0580751034440c4c054030700352107d6403e0b181004641843c0001c082d09403110b45034142c441c20140d4035a9024404145c02900403110300d2074444c92200d036400d03001d210020550b0070b40694682c803581403000b61000d40701010345403c40504c2c003004100440420740d100c41d80281e40042d00d01c01c00005c0500074002111000c1c2c020754494941c141c001d00c4402402c0d5003030715590202d0040c5181c5510b914109040f15000038050946401c00c80c0000c0482c606 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640389019 1250 640387769 640387789
    0x3040b061009060f0306030b09010c0e0f061902150907050a1a0702041a04090c15050301051011031b0a15050603150a021908040b0619030201030507030b03030307020a030306051e 78
    0x61380c50000369282c0d498968498442c0c041e115461140d43d51188130710400e502095024134800192048026900b4510102e034851042035800030402e8050b01800058030b109201c124400141d5003003008031420000c00050301c8044034030030203220f001050f10010b4102151021004a4400c8000c090709052058090001900c00c1d56141e0000c1d22814402803201c0e5914814100d00c02d000351034009185040041d15205110803c041400707215044c40100032590714288100300408549c83e080b503204045204445c950300484c000c81c8072030f40214560715522036000540e80d034524080e4082c0350710702c1c500c03030350000883ea010384045070142c000040c0194106201d4201d10380000b02c2407401440d0022164881c0181da03845200c1c41d002131034040622040c03010a13040113810503001c44501c0700c42512020a00f80e00d203d203100080c141604d890004e80340c0c40c0241e011103501c100240c00d03265249082803001303480700040c00d01100424a0140d0100b11401d00000c601e242001c034034903010303100d0708800400c000c00f03007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640390269 1250 640389019 640389047
    0x41403070302122109030a20211e030307200303010905070801081f0c050d09030e0a0e100b1c0911090703090b220c030803040b06100906 60
    0x420200c0000060b01d4102c040b8414a2550300074100d80b804c100348002a0183d00188900b400b9000d0108140c40d03a00829400305542c0d0125148909401000da031484132002d2040c5d069100d4007070035145034045009404200b6800880c82501e001d4110b101c0c00083e90007103517629160a510500c001004030b4000d08114400100b14031032001035102400e0b91a04d554001d030404a2010b444d18140b22030f15800200f05801341040c90081c0000c0b0503c004110034040b00040320107141d03500c800e0381044c10760140c01110401806103000b807180c21030034100035040d644003103201d81c0501400400000c0080910021a0184805d004407a01301d83c60106480516044110150284215030a441c49a10b100b44a0b00d023034203100e40000c420214500c0200012400000e00f581c06150824031070a0000c0d0b404150b1991103000b48401301c8040010040c82c102c500e1004500406907944400003005201030140a5485640b2a40340940690b4072038042c006d05180e07141604000c40c00b20041441384074002c26402c11241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640391519 1250 640390269 640390273
    0xe0a12020705030105010305010f05060109080a06020d020904020313020306090a3207060c0c0e22050712050a2003030a11011b1806090b0f0318010207050d090608010605041403 77
    0x582c50303600183c2180c001303900860782c42c0e40d5440c204904410500449500103003d00b01401c86a280c11902620f6541d03400e0b0003054140c0c0042c0041c103034002035050703031031500020b00215201d190541400140e00844441a8442d03c11040080c9002c100092006119076000e183c50038a00d01100151410421641000c000701444280450003080104009401400d00703a40d400c1030415941400824001d082d000880e500002e80c04004820b5060b50084079044001d103802d888100190611038104681900540003c000300d400050034064002241070915010340e01c3c0301d10201f00000c01c5501880c5514a180c1c01d50010302c4a040c443d4051590402c07290116400443c000c000c4030044607004429103c020046030046802c40340540a04440c44050141414803c10260622408500900601010142803000000081c0403421705036a141d61541c03441000390b455078240c1c0780c0103448400d076002c200300061b0400c10000301b1b03521840415040b10317410340310030340340ca803c02d0000e01c0000380f07074100c0300c0d054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640392769 1250 640391519 640391533
    0xf040e0a0206070f0c08070f05011206090507030c120b0f090a02070204111902011406060711030601060306031a0112030503090c03060f09070608060319021804240e0a1202 75
    0x540c42d1000140a100e12401000c0b00740c5a0600d44408034021a400c440b40350b601a01c400d01100e00014090b206550007400c10b841003000102c1d980c40a080b4581000107000c0c20304041c048502c2d0560400030010181d038071483d101c04d500305207078401c40c1c40869419a1298058841c81c00c1410081e0348142c201e07400800161516415801090a403890384803410300181c0005000c40401c0d80e00042820104c40c20320007800800c581180c0d001103000050070300b6210b80c10028020040103081c80c000380c52410f0180c01e807000da41c0c3d02e01000d4000c141610043e1540d50f0b44e42c11582c05030001c0c01405042c2c0b074046040081d18041d684080f9101d4100030110f0806119501350070400b81c1d000c0144a204000c81d015520741c41c684440040d007010300990102c01404038003801e2001d50358010a40d443d02c280d140001c50082c848034000115615000c20410303d000030b0740e0b0140410311102518154202807041d12501103d070400c180e007030441d442901e0180c11604040d0070800024020240e6458a890910440f112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640394019 1250 640392769 640392773
    0x5090117040b221a0603030c190606120b010303051b010212060102071a0403020907090b04091b0503010b120c04081f0e0a020a0b0a05040906030b041a01050f040e0a 72
    0xc0242a201560400c0407076003005140c0c843e8441c10308500207100b100a0b004000d594505440d0500d56070318400115007540000d00300d0b1400c106a41086103100c080f903001080d04c00b24405450800d8400340c03180350800744046410140d45003440c55042e032141c07690f0f166a1a40e10b040742c403a00507120135404444c10990140c1400e0090001d03111009001da500c4c3c4013401c10720300183c686410341d4070000c0c01100019202140c5c5d80c0c41025103044940594217a040c680d900d150481d41c2d002030f50030030400071001041c041644510390f4040e1480d07452409071484844405001070b250341c0801d2240f041d00344020006500d40d001500001074006e07404a0342c150602d80c4940a807801e00d48a1090000d03089091102200c0e50a0a13020b807440103031142000d0301035004940c01203a6005000c0c0500551030b42d0010b2002d0300b051107182120014625071104010a40d02e0380740042044100307490944030355190808000a2810180700c0c0342c102d402c0186110a452041000d00000c0c1c504406014160701030710210b800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640395269 1250 640394019 640394057
    0x603070614121302091608060916050c0f0f070602010606020303012312010c0302220e0402100903020d030c060f0623011205040f030809030304230307020409050f190b0106050901 78
    0x1000c0d800401c214200c840c2c0c6c0d400c008103480c03c02041c6511456007171041c010150b10340340c6030031302041091800303c1e545c038607500c070040c502068080322200074031135455001d140e49000f15080058843c80c0d070080c004907070380d070303c04981c0e9000c20f02842d100040880c4182d104c83c031032942c02601e01d07480502040644000e0b50030342800c4400341c0103500040ba400041039046103200341c0b90005280b11207101e060300b207070501900c0d101415000300b00a008012000384144240c0c09014164000e65009041130f00580c62860018808491100c04845450502d00d840002802e0342c000c0e41e055461400f804600c40c810350400c801000c003450f25150500150240300075442800c0c1c0503291140d070041da50007a0250041c80c0050403540001c1122105410600a11002a4071402d0511012245440300403100c2c154101050440c03050340c034001d62203458548000200940410482540319400081e40d0001c3c03280700c0182c40d80b81580400500e425a004011b120181c041c20251540b030a06242c0002c0700030380c0741c004c0c034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640396519 1250 640395269 640395271
    0x80c0d15061806020a0809010804051009050d111f2c01020c0601050612130c090507090302010807020f12250606080c2e18030b060307061412130209 65
    0x440001c0403420119110b0084140710401000305100605010066444481e064016140c000741044170f450041014403200b009416289800b0080411410040d40f84c07443d03542e460340141c1c0000c9051b9400e841c109400109800d0409418440c00c40c5203258487c0e1410018003154000181120f002c4640c14640407440c040c0e4007010b11004001030707407214200d00c80d0f4502001640300c50304c03860082018501e0740301251030954000700c3c003420b02001045a8076084c803007a009a040204a107280808203d100340c0d1006100c0308890007070300e820070071b0f480360314080741c130341402c9100d400c202c0c0c3c040c02b02e003000030024100803c042c000004001c0d801450101801006216244003600c00e00e40366103040c029100240007080000b00200c408422108600801e0300014180100c05d40340c14100300f0b000c40c0752034024501124a0310001c83e003401030b280c0707a14001d03a49680035202c45000c1e00c1504004a001c0c0d00400000d9030b0704501150482c2030185d04d0242d006840001050032440041c001140e60068481440d0700d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640397769 1250 640396519 640396529
    0x250c051e0303180102161704210b0106020c06162603040b0f01140d050c090a0c140702011b150516020609011104090b150c0f0f03040501080c0d15 64
    0x65640c81c10700022144116207644820f81c1e4603481003004440c05036600e00782c02d40250f8441c845100a04d1503440034180e074011540200c0790342d46d03000283d2682c11489000c24109c94854600b42c021a40c8405c0304a07039034441d1a50540d0800000c0040c241c070703140034207100c5003450310500011184082c8000c1c0d0351901c1c09511b0100d40840000b000b071000b040392601540e42d028102584060140d0300d85454044814030500205000d803a40ca820300c4140035082c04103079909400606421410700b0941c0c1c4800c0207080700682a8001185281d203c104551007100705c1e607803c0d8050351850000c0602c03816242011124220031a0600c00c81207007001d06d8549402200d11841d84001c0401c0202c0040601a00b03080008040c403009902d01515030b040402c4120a031815100e18000c00129140400c0100d00c1514114162140706900401d040200744400106d041d455041e40046d40c0714070350300b0304269a0328003d60140c1408540080c00261101410078040c0c244a22484004a016125012040c144901c55004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640399019 1250 640397769 640397773
    0x2070812040c170d0507060e0714150301050f06210708041a1e07180e0403140f0301050d0204021902060105010206130c150c1e0308250c051e 62
    0x1008280802180b11a004085503c00900b1184180368443d0301c0300700b04184501442000300322001841030960044903e80c0c1c07c4021141c0050b20f4031050440300314200101845040c40003604610345640700e041e0380c103d60002d40b10100d194034200c10041c55400801214068200c01c0740049003005040307075914056451074880180606040c1044140c4501e806c003442400c120100c18042680300c424106c0c49940c1041c2030f0400c06480c3c4004c2101c40c0c94000e02108240c1d400d2203408684038018040301400756101ea21707010721511400340c4141c070324081d015030031454400a000400450408400260b540d5200410051070140301030643e9650341002202e210042e441007005004951301003081e280c2000030b070082d011605d0344036a21400ca800c142d00030702200041c1040d241c01441d002d00480004503a120580e00480d640d01100c21082801220042d0b001440e901c000c143ca003403100d10340680103111604590b401203003071941620192070079001143c003442510f44100f03203000380060312a0f1070129100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640400269 1250 640399019 640399021
    0x110c03160c0909050d030c031506020610080705100c06020f0f070605060f0f15040b04061205011a2203051605040b040b0d170c031603031d07090b030102070812 70
    0xc0019510500b038114030320043c904100d29011420000340c00c1e040b400d003840d0100e00c20485140840141000000d5050708550a48011038910f4012861078401c90880ca1103001942d44c8100030b50351b954562141980210201d021a10710354810811000716070b009401c090300e408032480c540c0740302b58032001110b404054042501807c00055009283e000324040300c0d2103450312110400a000344070711400692091130541c1040e44d606d1420000d40b8018401d400c1520f8565544050250400201000700c0c4021403600d000407626030b600440443d95811250080b90030820010356201d19080b03118074040100780078031000400101300300a00c8211107041100c42002300e20781002e0006070380d07110150741c1c440c500b8a42c030102035440b811080302d82c89401284c015004044000c003401188100001450680800140010714012807035580400b00d100307075800c10822905440070503003003120121803c19a0401031081152041c1c64000031504807005000600e4281c0b20344e5901003d50040c1a5603540c2e0903600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640401519 1250 640400269 640400273
    0x603090b06010807050418090b040c0f080f1507200309270a050c0c0f16090510090b060c0102030109150f0303080619090e0a0b100e01030204110c0316 66
    0xd000c0e640c01000a080040c114204004058a1741c081e42c0540c03400c1610744d0032440702c040d005801c40c1d000d44d900280c010000307080501340f440000d411405007a407800c46454000800d2400062121a071450a501529a82511400c00100d0140160500003000b8044c141519503504411340124180e4451000b19552420301082c402440240340000200c2c5141c0c0310404e0641e05a1014181d0008a5010000305039984e141c0d40c0d00c031400b52450007080e5200c0c100d500b0800c10b50018640c04071980c03620369506c1c1c551b070700ca004205440e82250713109002d90810100300280b0085410142c94140010300c01e43c1001c405d4441030b0300b240c009034000e003001a04d904000113064080900d00b0068420b8030308500c4000e04585014291210140403d1b0003076810803843c1304001402c1d40d440c000303031250030404d00c8210260000c43e41d0391002c4203801d5625440000100d100468089280300440382c160320400210380c69902040002c00c1c82c03248000c25450100301d9008410414001080785000800320556856164 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640402769 1250 640401519 640401533
    0x30601090b1923040902090102190614010b0711040506011103120105100207030503070809040605060c030d3e19080405070902091507050f030c01020924040303110c0307060309 77
    0x70040d0480f580c9580301c5880071041100e011503094500c0030f071000d17945103c0000100d15103620b00004d80107080004500208000080d0000304038402124120085079032601c00000d040e00c40e415000f820b2914034007040300345081a400c20b55001c40e050600240004020103140d056600c50210398040d03440807030040c00180b80c03000b0312a800390520700c02440701c1c03070955840310380e0b031310403030001801072603001c103ca61035681c0c1c0b0380003074010307200103400c1c141c80c4c416000809039280c12102c1c0a030303050303401c1c0f28480c0a0481c407000c43d0354420060403a041c01c44e07000380e80112900b90151130351000541d001c0194030740d01c2d10455145000c0c9822a62003c4003440c01307091180c2803406640240f1000b0b401040340c9011990b5015140d1040040d002240340c4e00c44c0d4502c1c089240c85003048050501d404081690703941c00c441980640256002501c410700c040d0410300c0440c0b04c01c1200c005100d0580310500c070900c00b0a00c100741b64140c800f60801103030070088030500041c1c60b18069a018000085e242c802801c100700c50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640404019 1250 640402769 640402787
    0x110a0509031b2805030106060f02010f1a12010207020607110a06080403050a050a0203270f030111180a0305010501082119140f03040b0f070c080f030601090b19 70
    0x502c1c03940c5540c0000b540000d01c2c3c910880d1443d0a250411004030b81c80f0212100740c0d00d00500005000300700403a50340c440030344050a02c445140c0036500c0d010400d01c0038803083c043c003540c03044000b031070340d03600e210610410000c1502c0b28144a02590f00340300300b10040c0c51b100c004000e030f0340c010850580e05030340800c10040e282d280d641048080180d41c106002c0000c0d0400140c406080701414010740b82c00c803010f4128a18004c1c00ca40c08960800a0344081c0652883d40360428003007019280e00031220320702d50616003039803044401e20b120500f041018003140c4031b051071480c880602c001c10030404186e4a44074542075980c06e8100c000207030840746103a04007000701203410090a03c40e000013402d00807100850b030702e8031801c540750034244000ea4041035a1494103204071103d6a4541c0022902c0f4145070401030950003003215000c40304501d07540030840490180103040303051588455020300d0b0030381c840e40d02e411940000d404031313050100c41580450140c030480d0142c03154a040308440c10340300614040003010828 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640405269 1250 640404019 640404043
    0x705030405040e0a11011b1a090c04060b030a0b0f0d060f150e07180810061508090706031a0604030302010e0706030b030703032d090e0702010c170a110a050903 70
    0x1115502d0742d00000c50170804524401e5090920f00075002c0e03100b50702031038207001800091200c68009401102c282030694200d028189080c11074002480d10010f10045400c14040c0303205501c1b00307000040d500180354000c441e0315200a88a4816040c118011400b4640c51880c100c8505880d000651002034103032195200d1340c0e40042d412081039103081e8040100300400360015040089212002030705038490b64150340200b4200717044640740405d801a0310000e00c60350089088001d04020030301206441215003070300507507080000e444094500202075001300201c840010564480040440980e6550005070000310700a400101e6003011004e0700318101120340e08007000b07040c0341c604030494644001960701e0170f49505003403842c2000f1416181c0004080002d000f402c3c82490034056003090b0b80d11040200071100c4104960165480d14001a0300780c5203402a0000021a090060340d815960141c916401ca03100910000c0c120254404007940fa0b0301101d04c036004100001030643c2c040c2410070168003460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640406519 1250 640405269 640405273
    0x603020d0f050c0603060901030210032909060a08030423030d0e010809010903141620030d030e101d06040b09120c1e0f0726030a090b18060705030405040e 68
    0x1141c000001015980180400b0b0b02a1140d8140081e5070380c000d0744680402111a00b040c0e28000d0102da04001000dd8103c510b4010a00390b80820124205003841b0016180e00ca80070710300f814100b010074000c83c03174940d01d44031101501305c4000800c1c3d1018844112401501d564944800307080d60009810001e000e040c03c001c9a14207000d21001c20340c4075880902040c14000718958030000309031116408005000090480c8150072903602c0f03003c910b4420b440340c8900640a2703501ca50b80480c000c0d000c8401c03920441c550380d0003000b480f03583c4070403e070310030b8049c00220080c5800c2c4624000e00d051508408680865003208014284102000c4c01c01c40c0c0d16586540c500c406192910f90030080f62160003826144181c0307100003101081c0e5150034000b6441c507007080c50845040c50350300d10a600201d200e21690505040d01d00ca8105c1c0001004005c90b19804040d8990800c4640341a0200010354051108407103160b0910b401242c1c0340d03a42500400a0b580100000e640b00c2d030901081104131241c54806009503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640407769 1250 640406519 640406521
    0x60306040e101e180f020613030b0c120601020a0b0f070306091514040e030d0203180a050d030b090424060503100f0c080103030c0f03020109060c02011a191403010603020d0f050c0603 80
    0x12006030917002d0065041e2034154440080c54000d44000300c181d000240619200000c10000c5a180303c0641003041c4a0480708000741c860380016038076031002c041c000c0d01030030503c40010b030b228958620340398200044d4500018002d9407140150100c4046491400070360045071403c01a1306c0c0b0091410521080843e001c204d2001c82801c035950b0f901c640d5040341111a000300000c0c00d1400404c5c11001d8860014085e0ba00000d59854100c2d2124801c24228000c81e18050180f0450b0812401a07071203581e011050302e050b804151a0400403480c00b0801404c46621040003240e142c4062100304c4207070001c0038002c00c4092040401d0000d849820702d500040203006c0e801080401d500c81d281c0c0524581000e03c400d11000141400c90151035400c5001c0d10060412903121082541540030036000c241c100745000510b403040d01001085071700c06000d6a4016441001131040c1d203038103c07611206140c0100002802592070340810148011080180c6503081407118203418808188101000d803603046540307504d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640409019 1250 640407769 640407773
    0x3060a060f02100f2a09090f1d0303070305010e040b010608130606080f060a0209010212130f180506030f0d0f0215011d070f020d050307020a150b03070e0402060306040e101e18 77
    0x6e4030199108985a0a484400010104480d0b50001050340b00e030740c4003880300d6031700c12000c0e80da254000d4660a0009240400000b224408400464007990b401104420705034648601191400805080010b020b2a003600800000c0c103d8480d2400030091040a882420b150b02009420200006c045890f510b00400c20303ca102c0c0e074045050507555101007a202c1c1c0f502d04440d0044c09945603030b0000390610510303100104010349000c92070401c01c16000b200b44020b070341d40414941c03914044071210b0000d03408003540d6a025805214546282101441142c203224145a03041c040820b00313901803401e4522904141e40c440d60880b031905c1d817111072070a12017403524040c0d000950701d60508545200700440030010980480c401d0060b90740281d04540c1c0200240301402007100200000021a4428803840e600080c490304a400103500c1540c0052086003107540c0c400500c4050412600c140040e80508031320300002c015940f15920b6202c5030300854004035000ca031030210466523066103070f20343c081c507112400e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640410269 1250 640409019 640409027
    0x1207150f021504021005042313090b1b0f04030f030905030d080106140c0604060e07091404150b130204030c05010c051b0f060a0c0b070503060a060f02100f2a 69
    0xd0081c1d4140c6280b1080d501010040381d56001f6a04480c041e950300d109008080c1e81106c4071f800d06040b00700c40ba80b4500c00e58a01c1401100c2d40d03a0801448907003090001004014003540c250051065188518903105104402c3c0c0701c99440740d0005c0316602081c0400f1010b143c0d204045c000500750a80c000e0047c0c1080010203415134205210f40800c01c50304044091100a640e01a07410501e0302608a42e40c074145850250b0261410600010722481000c1c0005440c000780d00950421800911001c0c0c41e0351203549800c10504001c1007a0f0105a40f1981080c0280e00e490b071076401040d000007001030300e56040d03180c49056481c1e01e6002904000007464440d000c54070200c1e1140700c9104881110a0501c403c0d00403031030b00424401d80706d038040b10102d61050a5a00000300404091117042e0070f81d80c0d03a540e0394041e50700b80800d0303401580241c0703007210034031416004a020024050f1103004071920000d44652840507945103001d24841d068443c00103c03e005c407040c1440c003a08458244070700c140e0884142c010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640411519 1250 640410269 640410271
    0x90e0304030803070302070b010b0904050f130212011427070b0d0c0309051f060b0406050423041503021e01022a090921090f040b1207150f0215 63
    0x10b0080d0100102052186000717a0407160b185510252071041ca6a445010707081a8000e0b110345801142010001002c2c5c8800d18a44d070702c10402e4410301102d45903190280b1404c1d2203800c10807041c0350758800101440c6103c2c1d0103540d2248a940a0002988104540b00410400c1002e6004241e0b4003c600911481e1401c0d400d540e15003607094800910441410001c038082e0503842001f0f002c0c0e00070760f0210011074075212982020b02c07030f400c00103000e00c0e81c3e00d202401a9204d948280400a181070006101c1c1224156400384c421085400c1724112080301400a021940301c3c9200280100781e80b5000c1007181007406904000b0840d01c250034040e802c06c0310010791908240304100c045040b04140c9510101b036400940140c10303501400e008070501d8000d19140e0b4032040e0b02c80307102c070f8120b5102c0001003204c06141214400c61014003030300080100c507001d11003d4162070b05e445034044843c000902c1a0142001040c0003061002002d5600303240100d07000c0e000780d8010b4500700445d0408079546004600c207900712 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640412769 1250 640411519 640411523
    0x40206090d0c0e06012a030c14010612020f030105040b0f061212091c150f020f0a0305010614040308120903210402010f17062b08030a06090e030403 65
    0x1596681150006a42001c24007402040030359160b80c08180318020b80856803080200f070720307440b01041000e1032805240807000c0000640d04400c0e004200040d10400744d00b5001071280914442d1030f81a40780303060075240c40360400400c40e0b0034400400158170b4030008400c803401041e4000c005c03e0400340c072501c2c0003d0740107000e45012094500415095200c0024003001440c138042a585444c802490860ba603520540f04184159100888642c2c105101d02c0140039180d4803050300e606140d0018047c0d80a841a07202c55490907500b4800031502440d030400501090411395000182036040540240441c0080710420800210600c41800011158001ca0704200400c0c980d0b0744c190381c0d802c03072806d18602c101344047c02503030209100700a44101120301c0c40e01640c0300762942c1c003401400080884410010750804020640e8003c0415058181038899107452403200e0200b0322811032104075182e843d516000103d070048400401c00a00320640d01c20507000d040320b420240007000e255086c46561340924000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640414019 1250 640412769 640412779
    0xa091d0717090a11030c040204060c060f0c1205040f1e06110c030703030b0f040e03070c1e0909110307140111010b030304180209130b01020c01090630140912070201080402 75
    0x42050395808000050046d138005005641d1503803031756401003ca0080301030888107581030a48001c29500d15001e540c00001059070342a50030a003030242d80003d403c0c00392007030301c2c0c0c03124400c20f0502081d000d0380e104031001900c905100415a05140941c1140d00071012954011414480e54540f19070110072a0220f58140c074000c18261090b00c0080c4010803100400c1c1d50180c030341845c080112401001800c641e501601507241d602c2e40d5074a001c1443c503000c12070340307440c0d00c01c0f40c0e014801405c0303039802200301c140a04d1500c007100c000207001c6481c003111908418624508810070465640e802074108034401100c8000348aa0240c034404030380c0c2da006d540210b0f00320402c0c99081000d080c800398140c0356800002082003c0741c409030001c500041ca421081c0a0050244060403106540101900301c2203076034540d64142d4200c0342e20307400e0b00800201c0885a80f40d207552801d41d0301610490064501003144c4c0864103426043c5464450b1070541245940420b01e1400c0c010180941e0304051000d900640540d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640415269 1250 640414019 640414043
    0x516020610091e2d02090a180f0e01021902030909040b0612070b13060302090906061b0313080c0d0c0603050711030726041a0a091d0717090a 62
    0x162400eaa5254840c50042451910b0340c43c5080d010301d030f10601d5120340c0e001c0313103014590410803040081c1c1c03107810241c54100c0c4d00001c2c10061012020b4000d2041c0b141c40000160580d81002c004003523500f00400e69070f0741d80d0003181c010085400207043c00802c02d103030700007145852000b0001c04c02c40200280040c1c802d000101c0000c03030315254198659240005c2809482c2141d1302c61140081e1038000708a6600d120068003070104070f0901134800c50300c1c0054024402215999451300308091688250b9078456890351020340542070140400203010b200c90b110f651a003c0908240410f0701d0030030301130036070751040021401d641c01240410382441d0540d12945400301350380d0756002d0162540c0c0c00e407440140c0b8510000a411003404003050faa10107242c011f620f000c0300340f401907541c95a42e02441c06481d041d128544500c14845885034014544a04030b41480070116548034540303491208080982c03a10705401100f00f03c48190b00c0035031a0081c00f049640d400142c24501e404540d28501c0c4080181196200d10b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640416519 1250 640415269 640415291
    0x260d0e0d0212160f24020c040b0112021204060513030f11030f0d1505030102040b04060302031003050d260f04111f032c0a02090a180303051602061009 66
    0x200900000482142c1c1c0d0000440c1d07980301100104001e845050781e00213840401c0a1704c0d80001603052100c1401d40e0041c91036812a07410000201004030465040c8410080404454106400540b0b14400084000d60082c50325091030b00c2561002085258032b0002608440006500040940c01800c50761034161442c800881340a0300d54821202240c16a210120302e0a28031103603600586140d042e400307844803d150769202818207074000e44c0503d011114091000740095071080c0d000d544e00006c04014013a040742c5e00e44815062041c1c0c0761f8050000b420328901d050180221b0f81c58149490450700e540348440c5001c05050050343c0c8041c100410b101100b183c0200980c1da200e8605000c1c541006402c0540c0c404144082c0041041100300100000001480510421608058005a0482400f0b40000c11050f42041341c2042d00918080d1813503928000450350354420207411021500c039403400196801c2040079000c9034040d41c4081011984030400b00200c060b02c0703080708821280340e600040f0708060781c2c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640417769 1250 640416519 640416523
    0xf1403040306090807020120031803070504020d0c0206071b0209060105120906180127030203040b0d020a031a210304050909061806071b0309260d0e0d0212 68
    0x168406442e00d4100102d6600b448421401060030f60300c00d0700c4240304040039006c4149041c1c0603a0081d40e054105108600103889100341926041000500381c420460712030300000d08a8000b01054031001d83c0c1d8500d00714505070104080c0e50040d81d5030800c003801d0020700202d0130b503088035000024001c10300d000110395164060810343c0c01d84040c00c907030285203281403071050303540700d00032914600c1d00d985d0b40d0080046a40d0601c26090300664540d0146910820614541100300003407074120118413041100003046001c520180400d0803501d031000d41d564815040007000d680890342a66500e0380030114040184d40c0704c180c03449900c0340d02040380348020700c40611181940200e5020680003800e04003089582c83c000b040c03840c4959115150300520000000b04150344010031034824000c9002840c0800c110a104c41c15460303038a1103440c24103900e070380300d5000001254403150303008c00c0d4545607521a10340d440140105401105140b400401048240d0000340c003600007014040d01034900d58604542c040d0007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640419019 1250 640417769 640417777
    0x20d150c05071110032a081506070f081b010209101d01081008010c02100c030608060c0d060b0a0806031c020712020f03030c060a0c081009020c2e05060307030f1403 72
    0x60720b102d5603450103251490007019030315400d01c3c00001d401000050040d00b078124248c0c05582c0240810f4141100340d030320516203081400c400c0c2c919072000c0c080664440103d045100c0306514080004d030b2034071a00014410078801c481498021302030300e1300b551034546460849600f200002440c1103440c40e02c92240210181e4480e40201c1da5a5080c2030700d03102e8041d0002034100b0100e070660350800c400301703c144089046031140c0c040c4052030340104c0c000c642014a494050003151180140009a2540c0d40713081c041c0c0d5620a44008001c18906000c200080c03070107001480c02c0161034400d001e071050942200a446050b14000d00c00c1c41420030801c1000e40d102c800040116001c060201d994481c6401605642e801d030440f41a503000f814200180302561281c04403034001c25021003803044075410f00c20718401940114001d2900c0b0f02c00c581c0140d4011060080c034801c013004828681150b0310f4020014025107000828075030184d40104801c00010301c80840c400d01076a00301c2c21042e440c010007500103040d841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640420269 1250 640419019 640419041
    0x6050a09060227090103020a1815060306061b0519030c060c0306030b01090603030e0108070302090d1113020c030a0c050a12030b0f030a051018020d150c0507111003 72
    0x100c0031905504031800c8000424107022810312611440e0f40100c10411800002d000003908440c062408111070a00d08010070401056154041803e403422980c82c480310140381d0201c00083c2e2100ca04000c003c1c1c00c2042c2d0808680c860b0b15442c0321054036103c1a9403021500c00c240b180103100180f040074103110301c075035107182c039400001804540f60503440103000d0b00782d50000b0740d18a08441d00005411005d0300c144003c90742d060300c400c140450f03080015144000002d20b0f460505408008100721139441d0101c9460681c03060040843c0c4454a4090000010540510903000c40c410054582d80442c00010749030000d58a1911401c102c04915042d0b040c580840402440c0840d41c10034041c200303070117030001ea104000c00c0d581242c0030004c1f4400c040e503d0100320409012034011458506140044d0f03000781e00e40c00744241c00810b42051607408a407148034009000c1d40e032100050080e040441c40d600502200351010310703040d03052200503120b00b01440c5111303020510805104950aa1040c0242c00c130603019a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640421519 1250 640420269 640420271
    0xd140405090c281413080a0c030308130f020f011815020c01030209090a0506040e1014010501140a0c060609091a010f0605070609020406031b0e010b0a050706050a0906 73
    0x4146480c5810054001042c00092640010b20b102c0400303c070280c0c40b00e11000c040e92409038888101c200303d011503001c0b81c0d010070150b020381700105134200100a610300d45403080ca408e44403e403840c00c009040b500c0141240041c81040011440419100300c000d034440c80d011a00e084441000303d00585215584072007450f80801c1c404400101d055807400c82500c4403034250250342c0501c07440d500440803072240b40300303182e1322100541c040f40b50488103034003ca0740040040d0000400183c8018101d00e801505801d4120700d0351a83d00b01e9440c01108001c0c54010301d800e007414410703401051500021030183d40083c5003044030710707000107050060980111002b0017000008201079240f504140e0048440f40601c942c0c002c459100010f1490030152a500131221150b446c036040401039501e040181100160a9a00a40b18203010020907404204998401e030311700c02e1700c6251441c145105401d00016408244245814041e0f0041c4507041070072100c1c100d40c01100010f0694414402e44020080184094043c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640422769 1250 640421519 640421521
    0x30901021207091a0f03010b1c020f040303090e040309060f090306091103060708100b090301110a05190c05060c22090f0b0a0b0d0203040c031a011404020c0d14040509 73
    0x42e400c03c5858050b00d04641c1c803002c11605104600d480c81c410100c3d00503000c20104010040c50520340050b041c0181118035600701c0c07214201c440c4003030382c110a00d03440b40c1600c00101007080540100003070005010700c03c050f003041d1030941c50282259134944541401d10150002e56044130b0b00c298006406954811010066401d50b400c0c651419421710709079034024456600407621b407500030000c0320301c142d50240400008a00b01030125500e81c006007101d0790590340301e6403d0b62402c01458043c0c10030032801d0b030b102034883c070464035051040241c403201c1c1d505000803511a1000b0030750104600358040503112143e55240d14041c0000111850000c0080ca41102440080781e030303a00c2034000c5c840c180c0c0750b0301c01172104034282010091008194840c5c0f0700200b40c1003100d0340001065070061948540103842d0100c03015030747e407503140c0700c112a00340c0004102c044200500041241c48071450344035000b5182103042641c500703011951000c01c9079011085c407aa0f55240134010903010101c90182002a00c9058a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640424019 1250 640422769 640422781
    0x51819060507080c1f0f0207021f171f05100c08030c0f0a0e0f3c030d05270d0b06120d0e041b0c03030b0d0f03050a02061803040501050309010212 64
    0x1088514900b43e154a080120405484403d03000741d40e2156001081c04902892b10f170a00e030b020419a0800e40140f0609403550840c0c0f084106000703105001000b0550804034080241c034000e1907158210303922070f03081082c1000038291311030040031707101d0740c008941540da440d00c032220900e50107582000402c461380056842455548800072915000042d660b884c4040c14003006c00c003180301030784440106c1c60302c00b04602e082800020b02d4071102030310140d094445641d02d280860304100410561304081078001910840b0704582042c08a0304201c81c0c1521400702c0b42c580000707581c071a82050f010304021180d00108021f9500c2000155070118843c04407020769000c20f1019080351103100240d48254605003c001390503901c080398405000480c1d481c1101c04060396401e900400d5442102e94006083d9080440018080c00700300c624070380640c50f032030b403508100740c1d0080c40d007840241803910f0700021a4a104140c0400421364050303580c04d00b0166241c0c0e84043d0500c0c0280640d00e83c2c995000501d42c14008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640425269 1250 640424019 640424053
    0x1a0102061b03070e060a0e1207060e01030221090d1d01051605100f14010e010312051305030d03020c0609010608071205010b04050a15080a020603060909030c0d051819060507080c 78
    0x48400301503c8214840452008e029120045489140c0210f41118400c00803584a81e00502103080611400c4510020612400c05401c0341241e26034881d03031101c01409149a048a81859681000100118500e0b65076000074030902540018424003011056101c0c10070405004107a061240c41c081004559880240e203800f030901e9910008196079a400041075852000715000c0c10f880d009261000c0e14000d4845c120750541c090440d0b40d1000f14140700c0032503995402d000e00312070981155409610358040a05060030050050110440c5a2411204204c45403010a11108544100e01e20340500c901c14204980075080c1c22007001e61161034101000001202903000c83c1c81c0c00024041c078421191908030071580c1d0800b000c0003960060b000e00014245c0c0c54228000b0744d0088101042e00c2c200024400040d10302404c480c011008503c8c00f0500d21009403104032000d407030600464a0030f2440124400018907070035140103000400000003a400240054181180c03800d240c4002281c60041030128400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640426519 1250 640425269 640425287
    0x901110111030115090b030408071b14012a080d0f020c1e070311091302190812041802162003150405030316140c011a0102061b03070e060a 61
    0x840494400c61003092010321803e09802541d0307640f038009186440702d841740000ad0f004501308407820312141101180c801c5c0e04d013201500506100c1c0e1003079240c900c80c43c005490803082c0f400c00260321043d40d0b442500794a1981d01042d003660814281a030300e291130201c03000904021191616000d00000d14200c501070006001e1903004d5100c000a410040100d041030b0301d80249120190038242c20a5580b0320500d40b007410765800001c203d0307030307410300c41580da020481d01c207401c0000450b0314440c4102044080014400261280318101101c0c0c9401c1c14481d442c008641080010710f200365020455030302e8510342c210b1400d216500080003035814210134031b001c0d075000c801740c80b610b000380106042000d081c2a0401d2050040350701c50b002d1419503a80d9840562844141c48160b001c103d20000d40307200c5c00c0d0880000784400281040080344001c3d65103420700480a500d0040740c115840b020030800d04010030100d030072ba150749030452603580307440342c3d10110740d0f0700400c1c100154050f200043c0c0b0085180c010030341d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640427769 1250 640426519 640426529
    0x51606020f0f0c2b020d060b030c04022a2401080d0504030305040302040b01090504060f030201030b030303130209090a12050315100e2103070f0203120301081209011101110301 77
    0x1114680c40c10880350b0785900c01072000d0307500500c0c04000111201c07036203400b40e421035a212081c0c1801c40c2903a0000703209403080d1b840a5607602d5454403045100d04081c020ba00240c0f00c183c07030546c0381c0642940052884147ca441c0000880b01c82407180304c0c8210240301d000300c1c1503064110b030003003451700000298030440203204810080c4110810500207902034000d940c1140d4054868070f0900c0d2564080c00042d000c5412000e0402c88520b0001c0307101e070f647c0e00c0f50b58050520980c4c201019815480054115002c21502c603110360310030700422074044507250082003100e5041d252078000c0d4603a12281440e10704140001425104408aa44207240d4828069803140c1c42c00003c1c00c200300c1d604000c0c00881c0300344501040024149002d0351465041010350f10b030f40041c030f4213084c481d00e07a0050041402d503004540106e601c803110703c00400551400b040940352000140b00618510f514000c2295500c0c188039100702170141c400308a8801c0b41c4c0c004d0311b440040b480520000d2007158020256400194024014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640429019 1250 640427769 640427773
    0x10170d081f030602181f02060606030403030b0301051f060302070b0a020a0207120b0708132a1a120714030105010309060b12010510061d090907080312010303030f0207020f010c051606020f 82
    0x81d0300c1c103c5208102006c8010340c000d4802c2d5140c0005000255100074000e030103050300c8502036140354509201d048c0c070032032032040400c881c2400100d410018010650046042500501070b59010421501201e508200e40d9480141d0310004110181d0410700c0c07552080e503031405182400414442c00810081c428031241d40c1c0c1111554843c0c4040044480803100600320f0030351845862044820074081881d011b03002c1405a0070180c0d210401d400c1c404030141889004070012460b140d42480d108107054101031507003003030007088004184204450205101701410140c48520700428054560300080074954080d016004d404820581d441c080e142c1501e01d64000b0030401c200041c0703203104600403a1009180807042c4134000180040098080c800340070365015001c0c12000003021442003005027101c5081d15070101c41580b542c00c0c0601210320306e1030158a8503004000f1040160f81c1c070101000318010900700403031031082c00c0c2800b91501d0610182c08600c40b54282012a00a400048001480020302c1c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640430269 1250 640429019 640429039
    0x31e0b0609070804110f030a03050c0c010206061e061204060504031d031e10060f0816060509041d03030c0d050618070c06110310170d081f03060218 65
    0x205124004400315200c00c00210460085000651341c02c2855010a40007030100a180f05094001f07810080b0411044020420029040283c942c09008205080c0d0003400608040e180507400301d014444600f2000d0300b10042211030001aa40720009d031001c0000006000301d1901c3d10345400001070800b602d00350003044104414005012184029040c3c40030301034080c2c41004c988c50003000d060707a81e104508000c0e02550802040601d03c40c4210001003240c1040ca1342901d2030040090304002021001800fa10b141400501030281c05c00220b4071210001c0d01e00007102140135854480309011055542418003001003400114030840c4058150400c808608008585400003040803510030311900040d4032007070400241d103c41c00b804000c003046001c1c84001ca0030028144c1c000c005540700300d800c00317101c4410003030511100c0580c410303441c607d4280070000d244400d0494009011440c0081c00381807403d11840c844002c0341004440c00d402103601030010f41d225103403a580271a0365504110101d0040104c80c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640431519 1250 640430269 640430281
    0x100504230703260403080a180807271805010e0c011704020f030a0c09050103032c0907020309090c030106030e03130306020306040e1905070b270a031e0b 67
    0x4920841140ea0050385001143c0d070340b10705032154500010b10b00440800500000021513400b0340200048070700f903070303403c10542c3c0d0004040d210300e03086401c00a529844008280040b842c0208490060750032a41d10007500030744802070401820350f140960326807688003402c1178200101508952205516503003074a0565070b01c60011141e01c203504c03116440c040c40c1c040c0070a01604000c010401800800f07415200c600a41c2e4441c01102c1a0983c40b2501960340c0e02c2c0100f050660095501c1074050030128099500b0360f8518910407030b02e148512051060010030041601640200100c0b0403102020303100703d00a180044810200b50001d1081c180031908102ca05107542c80e0200885003119900c7e08801c402a0071925040002c4d000207040c0d40d04565121480301e0080800c02c2919044014030048590714007003850890300f4021651b208000145092184c40950114014851101e140803030400403e90080000140501819400584410000c5445a6248003007000071181036000318400d0140761a44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640432769 1250 640431519 640431523
    0x25081b0a05040e0a11030103050c0901120503031f0504110433122009040b10020a0308130b0c0304060608160315060506030a020705060f011203080910050423 69
    0x36540ca440061002c000500181e02c5001000750801165480011110300010804280f6882138000307480592183c0d02522031450824040d0380900001d401d0b0403900c444030740d5141c0da40d00000d070101d85e031070008082e0b441d42d000c5172a801030003c010040090000b081c10180007000c9502c2400f03180040c042443c01200309e40d0403591380000e114040c9aa18050040d00e160480b90055050000960961229120700c005924480ca8240c0d50f0307210f500560381c40800108101c1240c0b1002d540e5030181e04104d031281942a00811915a00e54042c204038041ea40c0d8000445082c026400c3c009101007040e009202c94041103030081c611892107890100621520341c010f180c0c0d503100120001c003400455a106000080b860800200081422100414080d8036800042c02e00d0b04201e03001322407642d0215031101400400c1001c01d400ca03011404c490410f504010b506c03400c800301b491000e000d1280d540c000c1503081d40b00f00140b8140c00c4501000700500d0030316140c001006400740d120040d500003400300d456515500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640434019 1250 640432769 640432777
    0xd0b0a05091803070c0f05030d030920010c05070f030218040b011a090d05030a1d0d060518070605040e09010506010e1002030702041103010e100b090925081b 69
    0x200801129840d03440601c40200d030102d101003014580024440700c1c00040c6404071020103094503030011012581000e043c5032400035940845000c05080c1405000861a4400f402101c41011036081d1303a220300e079074010f030f9200141c00c8004005205209001841140e00700d00039050300c1c803c8441d0341b0b007030990041c0761008003000d960141002d0f8481e001000582400400c0103013101c140b00f182d41c100050300c1e00040685140101c01e40711030f0400540600c14992061380444515008044c1c504200c490f00c0100d040030001c2c84000303140680d9900400c42c00e03940329890031040c200c428205c807a4a40c44080c014202e81091054004804481000c180c031004180071b203d11601040c0e407203045214802d0200620f603400d07500b6403401e6000400418000d0317120340c02610f27410129810925565450240c00c1355a00400420b402e10184180c1e9041c0320019010f0101c55042c0e004454149140d04ea110381500c4904c9906d0b0554a09900040c161203481d4008014520884103449102d41201c0b22030113184251003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640435269 1250 640434019 640434029
    0x1401060809030d2309060106121401050d060209030307080a140c0d0e190905090c060922140708060102060610051b0708010504051c020c090a0f09080f0d0b0a 69
    0xa1003025515182540406544d61200d03410014a04015050000076a8160349001180d00070200500c41d1075080741294500e070040c80c0c2c00700300c0c2c2c0d419480160040d64060007054810030a10230802e0522484d6019507503001c2e0001d058942d2844035241041141d80f0031403014000ca124070115000c0c035030110003504c800d20341c07076000341440b000703001c00850b00c0e14611513840354080d400c01070025004a115400c000900803600c000244c81c1040d0f82c0d064600f0361003e8005218603030401580415403690800d40800510400b81c1e220704c20103c0940034050804007030b00c0c04003a030100041000e502d60055000740240301c00e07001d580c583d4440c80140180c0e200d201c3c0002e000b15a0401072005205180040b8118a8417580142c03194940c4640d50075082d140e06031010b1303c1c0b680c0800404114544215002c0d018802103000074000481c02401107104107000818510760b0302d58030340c0003034032005a94208001240e07020f800341d5900c0e1031401101d00d15030412204130509602d8900f886125013446480403081e25 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640436519 1250 640435269 640435273
    0x8040c05060f0706020318030a090f080f0c2e12150506191b080c240601030e0102090918151510140c010621031e020717011401060809 59
    0x1289610390340082d600240118684c10100c0740780c0c00b12090188040d009d500407503036401e460a440c0212040041625403c00c04054001a040207425400041c198840035420f48d80c03400000d081d0044407030844100020001022890300b2001c0810782e101c01d00e0103000c00440c02c01c209480c00416503504443c181d001d1603403c00020030941d03c0c10b2a00085030f641c590408e1030058a0708100e04185480d524480104440310100401e24461008013489541502c2c02014400503020f40342c020074041c00310014150030705041d5600602c01c0010400e404807000c0803009859018103080841d980079489082c4120f164071406228424080c42d81c80301c001d613009805c0002c03141080007601007040207001c0c03100742d050b045c00480c00a00400028400240a2042d4080f000190680c40c0c000075505002070551101040040200240c00294100e054206c0b02140441081020000b0581c140d14200d015000a030407120140b88040f100d0105400c145141d03803880d0392243ca80d903a80c540c00c0d0b072602c0c41981c4c85811a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640437769 1250 640436519 640436527
    0x7030e030702150f0702030a0b0f0606070f0f02012c030706050c030d020f04081504060c0c020325090e01021305060f0409181a15030d090e0c04050a0608040c05060f 72
    0x841c3c1000070340003410f90701c42030500d48030f050f60000740760143c030743c42c01c8420101d2041007107461100a0100c607401002911154a814519600d20542c1010329030010078024440010000356440345007241211100080f00c1d0b82c0500242d824010b081c410141a00d10910540c8800704003584140b00351148040600015800c00300505545c602075000a0b1010101010510002803001810480d013184c03030541c82c02c84462802d02d81080030685281b02014001c2c881070380031950040c0c0300000c000c81e401030300c4000100c1d109620402201d00e00150b07803119101c40c3c28800d440b26400410340c0100780b4040c82000030000315640e1014491107001e048449030646a0600040028018a03003103d18200c198040081e0720341c0b00c41e515805810f030344140a04414044000f0004484c4045280250b0604101c1c02004141002c61000708a524503000740d83c6029490b00100b0024200802940c001e8040104039184450b122103004045107004c40e8150307111120000001b61509240c1c044408030303c00c01c0c24032850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640439019 1250 640437769 640437799
    0x3030408030d1805070617150d060504020a080105091006210807030903080d0608010b0108090d03020703020a0b04121403060f040222030c081e250e0106030507030e030702 75
    0x40400101000544101c003c5440c0080c1c0d007488030303801500c01ca03104c4030030100c4941e0345400e14090003405074000c1418601008200e5507402e820000e4141e0216001c90f042d82e071440440d4110000d9130104000f903081c0018051982000300324070760300ca0240081000320507600d018400c000e01207090583e902464414104010400c000001d100140c0030341000031425603a5030380d00c0c00644c044841c0003c04d81d0358030018404101d00303024094181c0e00c00d2030b000c0c03194106209201c3d1198213903140003090540c0001c0030340405000b481440e50040d001021601c0030700e081d0801880000c00d69042c000022401c0154141a08401c42903d000c0d41001c0c08841044403000c00340b000070340c0714040d82110301c40c01c1d1205848400c00021001c004d98410004001c60610f0000c015251114940070090400c5000e4a4003681030000600c0304110f100d10005419031000030601c80e0b1600c00182c110040d500f2040300007154003901034222a00070a000c0d0307000c0000078156001c00d52203001e1084025032040151040c511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640440269 1250 640439019 640439021
    0x120709021809310b0c04090b060315090a060515030601090824040611162d02090a061205011b0507082b0603030905040606090b0a030c02120d1a03030408030d 69
    0x1448200f804901c10440700343d180e9070f28400302260084081c0b20001814400700545000307003e04000d00f40c130072500354100031001c005803000d1007006602850105c400140c20b41ca1035000300d0000d1801424121025403800714000b210b83c02140e9181c04105441c80000b901100041e204100040c480d0030320040e4030003040c10140c2500054800e860036a141c50107414400030450040a81110107001408030003114645942da4050040f45044c1000d030801d41c0b0205a20018800c4406603412a803001c02c582d81d550200009280d40d030001c2c60410303c05904102001815071104208030381402c011030045550f10000c0741d161140d000020076a40051120300686482002107010506190f00c0060901c010030304000d08491642e482900081c40c41c4100b0061030a0034851a405804c0c18500200d03100e040c0300c1c040d2454440c2600b03d41c105a90350f440d04803450701c00d001e0602200d0f2403040f2a40c2d83c40340c130782546020b4111410823100b400440c0e55002850716002046900315030020000d14100b08030401544 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640441519 1250 640440269 640440331
    0x2030316030e0a061e021b060d020f030106080f16050a0e040603170d0b03030c12210411030607030504030909091505010f150504061d120709021809 65
    0x50600c045101c0c0855507955081d107580290842d541c500340c1451031050108030845492031003501355000f00201f0b40107032810070000c90703002005942955403403404055040092041c04500158440c3c04000418031a034450001d0b070017880c443e40003403101d84503241c1c9400c0d100140086000410020492400c2c0e0500800740c0e003000d400028400510181d4984640159030b158002d510041400090840360001141c8511b00c01d108007980218101190600b01c56583e40d81128210f19003003000c107142036041c541084070301d400404c4120030751007070404d450030080400c080082ea0b4070a025910000700014442d100701840b03030750580d51340b40c0d56620781400344000702151201551101e04412a85007098418003c0328002d2500b401d40c4141d0340c0c0f030031208040142c20601c5100030400100400c00c49198401c04856540c0340b224a14200f40850744000344040c9060424040329010312840050003256941c0540180644510940f0404013a081004645c000480305400a080000803034043e10352a95000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640442769 1250 640441519 640441523
    0x10b070312020c0109080d1a1507050f030c031305040203060d0b07020a0519020108010f0803030c0a0309200a050a0e13060905031305182205030d09030309110a0302030316 75
    0x18504000c40c6461801d42d02070202c00d1b02d0f82c3d14001071000d00500303140300b412140585010451b018807480c00004011030528814118038a401040da4410712809000c00800da050113022299202a458962516500102d049002e4640300c40300026940c286402100c2c071480c402441980b159501c1e5841c42c026a03c0601201c0841c829101c401d80005c20420800e000d01844030049d0060414501c001010404d0503044549644003101041110000000a0b00c0e00724003081c2d46540c07170380b440c010218000e01c00d500d40540f00b5680014041c0000018031400101c0c00810b940ca5040350b03465600380405001d5034892110400e240c0c40000d084203450090070401144221404110340400751640c601d035401c075081826800c02082000c012070303c3c146828048492214091064070b180401204100028100e0040c28210011b06981c0400105100720382030007812400c10041c221060800038010301d0420821900c840b498540d8403801c2c0742412030b070f800300e95006000f180360040d00b828000740140003c0302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640444019 1250 640442769 640442771
    0x815010b0c030d0c05160c2c070c0201020c091e0105010914090408070204320c0301030b0402030703061a09370207150b010f080609060d0503040902030708011d010b070312 75
    0x2121400a44990001040500949501c0047c0e030800301081c8811164245100c9018141c00149280d07402d0104c0e41c0d070f4082102e05180c008601c1c0b600042c2d0603c01d0029000e41d00c41c808000304020700c588024280c1802a031440c5041c256070f03d46c4019a4504500d02400b010180204145180391900701200c0e40d2051203602e40604114843e800b1a05580346448038144001102c00f2031806400307424405074981504050000c41800d02468614081c4018000542420403000000c0c042d503d04200f088002d40d44964200803c005225a090110785001612841160a00e000c550410b100e040e101e5507151410021001c0710700402e00480348550406210f000d150b40900000d004500c16045001d0700c181503540c0481e1a8490000040490703145000080c03c1c01711100900800781c540c4500c55500810640700e0800c056094108545103003d01c1c2d011109290001041005081e84400900c2c126403015400303608200804100f0201c2c0c800c2405501e41a0a0078407014012030300c540e00300c8154541c40c41c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640445269 1250 640444019 640444027
    0x604051b0d0f02040603060602160f0306050a140903030a110715020306030a0c08010917070f0201050d0f1a091311040914060703290a0905090c0a0815010b0c030d0c05 73
    0x58460b003a80c00a41c00000840e40c0c4500800510b42c0500407402142407905041040d1810325001c05000c030801c0c00090300350303076850300014450741107944034444010039010b00074900d251160107242d0340c0d4012203507401154203180c0c4040018650303200f600c0c982588802004002076010000780001d41000340f4641e41403240440c004080b807141c40c030744006003418200100d2a40c1c050700300f030003126582d0f8507507040000d01005140c0101d5400742c44180941d609107049540c88075a00d09150280c01d40750070244400f4580030301004800c05182d1000044081901c00940650318100c0108902c0340c62a8050040300040140c0c20702440c00d039008801c0c06104050703100309011541d8603140703844400c60f401c801003a52081c04000f00480c6003500b8074050000100d45282e8401100424944e05141c46507807100398403400070130034486040c8003601d1644005025051025a40e2074040c0c0d40d803e1600204c620481c05200201d104100c101c115481c0440071801546040000d03101c0c00c0080401a03400c40402c0341c244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640446519 1250 640445269 640445291
    0x302070506161a010320060d140f070503040503031f03060c02030c0f2a0a0909030503040308090102070209010b07020312041401021501060801170c0310090303050604051b0d 76
    0x2d441003540d01800160340c0b5055250045224000da5003400001c107400b00100002040f0000c00e00c0c07048000040071601414000200f8090b014000362400c0c400d0921078007220045d040011b941c450070000f040c941082d152640161102d200907600503005400c20000529080e052410000410416000c41c04205549072607100403118420701c1280160000036110095030010041840c5c907582d05405880c202c2c03401c0001000b250040c1051900c0000e514181c054a03a6031a52501c2c0102034226003400741103190701d03004100f50f204403030031008107060301d002c41c014031014801d40c1c184a5000e000440c580e403c01c206885540c00c0070600300d0f811303c00c1040014190b0b03e8080540014a15483e041e4030750504440064100401d909410108a48a00040000e250300c07032007503030454010001c500208180c071600c150a10315100c01881d01440307840e6014003030b10103d034003e0011f81c2c0241c1d020403a80d15024200300c00e4502c1a02d82811001e1345861400c5c41c07200c0c8400510101030700300d8002a0000b03000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640447769 1250 640446519 640446529
    0x180308160f0b0f060910050603072304030c05010f030e0a0816060623040510060810030f03080f09010207050c06090d05010905030c060c1c15030605040c050a0b091c03020705 76
    0x300c500c0f109400c0e803101445983d003040301c0320b160002031036022460b896080101281d60381c08010a10402c201031032a040e02429542000704003011172a40c0c41c40c0d40c0320b0b00da092030074080e107040c811140080c00c1c802d0b00e01c1256209204000c101e060000c0034041c41810b0742c0341d600307060b0002c420100300c40c0034245c0450700040301442004010f101c028119508810f2100b803148040381586050742c0128140020449898065800c2c0c0007070700c0744c40c00c0a43c0c907610784004034000701015170001420760000034000020305401004480c400c5d420383c6071803402661410100c1d800d0b4080c2d910010882e9100c80030f200c0070b514107140540800c0310050101d17803900c0d429403521401d41c2e0048c10159619040021000c5144009008040d44041c01618240c6490204104d03c110b41950720708400e11190350f03542c20b240b04454440403100540d009070082c0320310300b0182000105580380b0300c0f60300d10880c181800086c1c4140b0000035282180001060341c603881f445070710240b01d40c0d0035032203086045000c0c2000100d40da03507032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640449019 1250 640447769 640447771
    0x50603040f02101805040c1806050324061204080d090605040506070930061a040e0705130b0303190f03200327061501180308160f0b 58
    0xe401d1500c02482a00500440e403030042c90403001c116084060f265160040d080c603908507a005c0e500000c02c610b00300070490708641d900034031701c04607004094002002d6a000d005503008030a0005641000c40d880c0d4a003180d00d4a24181f215048001406095408844030701140d9020340111300091030704080814030012602920300443d680c507501d00c240b0003070200c02c102d01035000c07815041541c002402d156481c2c081d01e01078582000704c1e600d0340482100380d03002002c2c469803c590151003449045110780010b840070040480542c01540b500290550705600001c070b9a048542c0541445100c41030081ca01028060280d4000c1e010700c4200300081038116201c030075101c2c10450b582c1c1d03031100008a0000800791200c20000240303580e1030025040750045040116900a4104060000c4014500003148000d80400303007501c8282c01810200300c400141d01c44080c80450003685c5200a00c0301352900e07040b030f141c0300340000340400f0b03c20300102c2100c481118103494040e00481898680440c035944010134490 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640450269 1250 640449019 640449023
    0x3150803040f090905121605010207030807080a0c120216170318010b0102120703020c041b090b180d390801051509060f09010f1a1606110405060304 65
    0xc80080c040010100c040581006401d0701d100c1030080848684510f59510140301104580314000200401420a0030000d01c8281d5402002551074609904002d802e41104a4500e004070f40070100150200c0c3c00c601c619601140162143c2001c0c5c1000234146009401c4500300c00f5580340c0034007040010410310841d2030064417140c0751599403803401c2c60505203400c135180c44400d041da04200c100d01d426a00811506a450f9421045640702d95890034101e00e03181c40304910365003040c541609a60549610182c40c01c1c9200ea94482110103580d031940f03108184909003101d100f0781c1080c04484050701e8044001c13400785001d05000d441140000920006035841803255105161025a0390a50101000031050040030303030318002c0049203410b905003021401555038040c490305002000801c00e60750070014500c0030101401403100342d80c48050020381003449001c1ea40280b02030461340d40c1c0141c02c510171580001d0310003015503074105e46a039134034014252040e424442040180800319840d1070754000313140b00398 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640451519 1250 640450269 640450273
    0x1e1a0103060632040909120e031209091005130603060b0f0d080a110f061f0e0403080603100207050a0b060a030309360c030c0306050d02060306030a082d0301050a0e0601031508 77
    0x4140910701a1112800e123007958000d030484000e842020318203500741c54415400323031516905039480c2c048080c42c603900c98200591240350250b0901c9500883d43c0319501352841060f081007007800000c201304002600650165128010801d10000111800003500d5004010f003000f9160a0206080c48e050564680c0180900e910032402c2000e40f0218440d1000c1d611454010815043d00704001007900487c010405418080d40d000450741d03503141008070b00e024914405085440701c4151810781c0d100e040c002002c2d03562260100c041082032030030004130412281d15450322144185001c01c0c21001e042c068400320040300116819811810f01000044243d4030300143c0002d1004001501800303c81c0170310030301020149000320502094a881d0a6058015012101c0b1030b2265524000030f4074000711100020f21032640410014000041c074107240750102c00800c070020305540c0704195050140000d2060301e610a42c500070400c5080e0b07500107460740148041c580811b1041e09101d16002c0408030354070840e800c2e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640452769 1250 640451519 640451543
    0x5040b040e0123010609230a03020303040f060908010c0e090c3009010522020f03150417190c060b0a03120e03010515041e1a0103060632040909 63
    0x80e0700c14010f1805000542811920a41404c003281044107641002c8844174124225408040d5107100c020001107600508680c2c1c0c1c1c5844560074808c1007014071400300840d05003100400d01807418014020340b1341d4265075090f01c0c0610081046515540900307050103442c0100018410b00b01c0706202940600b00d4003426a542d0b103003c1d00310780c0d01b882c00144032611a034500701c144424800b42e0b010001c07410f0842d00140c280f131032280c0000b50101e0030300042180e142c07154103401080ba02d00b0700c0300a40306070300035003806004895201c140e13074a9215981d0b00e0b00100c0200c58000d01c0180c0a0700341c40c1440b5008003400252003584802003583e41585810a442c100300d030391007a00f02143c0c460440c2c8181101a8000d01440c02c0192500d014444016191072046031641d070595051101400c0e0a107455080301c00c1400b00c02c0404104003030041c1403110090000782807103000f1070382d18040c031204800c00c1030300c4542d08880200c0d50b01946003800c3c01c2e07803200101d050410001841c004203008044445000348494200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640454019 1250 640452769 640452821
    0x17060d020a090906140c0702030c21060a0c030608150a020f0c030a20010e06060d1e060b0a0905040201051611150d1404030503010314070914060103061e05040b040e01 73
    0x482d038010400903062404006560042c0c0740824204ae42001c20f84030040034031000703240c00046110b40030080c01c0b944101020014280800d0708041c08c1c10303000392005c1220a0319402c0d1540c03140186034034101024091404139482042c0c6034010300c00102004041d034202402d8059641c00c66004480c400c0005d406000071445584880e110b1500c2c88105e24020080e4449850f105074481100800c9284034041311400c81c0c0034003000c04030803001d080b9580303802c509480503450610000d020001c1203d00900b5172480119500d005403044900440e01615001c0c103024000451041f10a89040201c8901641042c036076000d031207001541440c41076a202582e103408041041c042150041d810381031001c201c038000c0c8004281c014013180d043d00d4000d165210030808000700c061404c0703200d81c0400101d07450207008041e184003041c00f05d805900e00b60703401d02460703541d070f00c4425034503a24421001491f881d181d4100403034506644054400c580c09040411841e920001d214212007403030204009000942c000c03140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640455269 1250 640454019 640454051
    0x406050a2319030605130210020a1214030a0207050a08040b1206060a0503180109050a03030915060f05010509031906020403021003050c03010909021f0e03070617060d020a090906 78
    0x852000c02c1c0c4001e03405038030341031002100100c0783c400601001e98900c0401e240e41c0044c40344c0801d0340e4024007001162100c08000a5071070042020980d005440350301c1e29450760307200da503030903010700342e080400350641d00ca592503000250311110b400c4030140326104502d0002004100504010544120102c2d00d40400c69032510001c0741c010f012911640007002100890394000042d2508910442401034401d094581040d00400110310041c00501c071300340703103c404c166041d00240b840394802c4a070126171078480d04601e015600140034500c41c00819100c28001544243d000d00000e4400804498140e036032184108087c10480d5002e40d8007640000b410301c25810310301e0034400c965101d0300d800c0203246401d849580070350206006120781144c50384156419551562824001b40b80b001801041c803402036607001d00410700e040c500c03c1c000d000d5444005012800740e80885e0b0107074002c400f1140280e441504204580001c4282268000a944004140d101036840340441f07680c454400050700c5519080101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640456519 1250 640455269 640455329
    0xc010e1c020703050307030804020d05060108010903030b0108060d0623090a0209010510051614030d05060915031b061c02043003030e1c020a11040507090b03060406050a 74
    0x8040d0b6204000400025000004131890300c0d805290401d02a1a03078800613000e02d44108001c1c1162040c0700012946040640c480048144a62802c0010700c40074401135070112802c9403080c0e406010b4842d02c1012851070b4100c401500304115a100400300001c4039110a05401e842d1610a50300200800f0114202442c00501400048441141006003504020024800c1c82c00410640144110f01801c00c10030f4129a1580340060003034030f0300c841c400c44041d03004080c1121400e100d245000c002c6048000030607808195410094003600c91042144d200d0216030400500c241e8001100b00500640c4445030310781004014007280015960f5468040820011b1304180010a00c1403940442c41e28402611580c03c2031456050602040b0350b50342002d4a4240607101d5040c4090000340c40e00f5a00080c0d0101e85522250f01c40e00c6448031141c07102c0140012100101d48030070200f03042010a111b0151240d02135075008130000c002241c42d0341c603000130400ca0681940000580301880c100c105032030b05400040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640457769 1250 640456519 640456573
    0x6040528080c0312070309050d030c170a14220305030304030e01211509021b150405060f13062a020a03020309010c030513080d170609011503020c010e 66
    0x203190740c00031031002a48800240003003c00044e00040c0100403d80200007d0000300002000018101e1607401d01510b05001c1010841d00001103400d030201810802040c0d8800951a5485443c1100c4c45200d0203c3c66000c24000300b82c00c0c00c40044481c14071854075401e00035510880141da164242850050001c0070a4000c160501c030300b044a01c0b05506901c4c600000e4021840750220302c0050035101c0d10204d00d00741d08030008003030000564801c0d001307030030445008000000044413044190072051040300c20003554010040e4004901041c030301050030342e0b000c0c4c0040a40030092500211595824110780b620b826016a40340502031480d181e000e040c2da00c0054103940d00190900490582c0c009440f1f200340814281030010000103042414401d9080c4c440c0c0d8115808282001c98030b030400070369681e203800ea001c40006c242c0d00c0316418205032010380c070340602405049040386034240042ca02503241580c403503008140d828811080e4a0900340281310f035400c000b03006031512a421261001d444a010100307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640459019 1250 640457769 640457773
    0x20708210906010617041103010c2601030803040803040302100f050411010e03070611010603080c030405030d050c0d0e011209030f0e0a080c040906020c030d05240108040b060604052808 81
    0x4028098015081c2c6018603090102e4401540e998503181d00142c1f00589001e425603c2e0046840c03845070400d13108041c1c42c100f030320030908608480302050b103000000d0000038001c1405001080003e140c0c403000c1c6130441c0c1b081c01582d5030381a010303840e00e04540001542d1050300b038482091105014100304882c0c1800301c03c2c0b07008115982e6280200b42c0d2110284204001c01c903d504606d141e1190a502c03200140d98800c1803642c3d41d4004400180c0d594106005042c0300307009060062100f107000e0700c119011440c0300e0b0040d00c08144180343c00c0d119410346901490520159140c0403455044a02c503070b280f07d81c82500c132801c5c00144400c00402d1030303084001207401006130480a214151000446510501e400c031808103c40c2c8242c60b014002e400780c0c3c817414010784000b00c0c06440d03026468110921460940811b202c1c03565440700700c85045040020040e012601e10801b103004a04c240b10310311340c848005040540f070705503141c002c202d10440c0740d03042800c0407442112a104448000640708018404c0c500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640460269 1250 640459019 640459021
    0x1207090e061e0d063902010506280e04050f06010e100326040609230603040204051e0a1d030421060e030f0405030c100905040e01020708210906 63
    0x40014660001c2030710b0b507100d05401012841046016082410400c00c901d500d4248004080f02080300140640055181e00f0b80669072045418414030035144226002002c022100c2c21583c05100d80c8102103c5004c0c0c9a0054180441d00301e402da1031541c09544904020805112950505404d0403010f0700701d03102c100e0787c02041c088201400008001501c1e0030001180054128100000c4a9003090422084104000c140052402e8211580000311681d140c03044040c20035029554074030721414448144d01003c14070101c1c0248c1030aa001071b51003805800030481048a0f80cbc145560440f0807554a4216030701c4403031300c84081c2c06031b41c8119180c12065004608060500e1280c40d20f000a20300000340841030314608109110040e04591240c022000551303907110380113142c0143c582e005005950207807044404060b80c60270f0001114040544035a00c1c040043d0500b0104400f0309020200e400866409016200c04902100300400810070510a4501d000310b0403940781302c6100300106580681c0c0c210070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 640461519 1250 640460269 640460299
    0x30c05030606040533040504050d020d05090a0b25060c090906030507092007061a01020307050d1404030512030f0f010303080f0606070b1303080108030a020c0d081207090e06 76
    0x6a18240c0d001d51411028042104407117180680080f12201c8581c040d05200a0009120000c2101040c4a000782d0994802c0f0843e000b080c2c54600c1800c140503008a403103882048040c0044020340100c0e03420400d4182c2e030851608142d40c200003001829140182d40700300d0084069048a001340c010002260705001e401e15546410742c8945851060656050302c4440030222014401d0300c002558107200410303501d60a42d400d011000303181c8000080381d07100002940342000c7d0300010640300510740c400c00900c0f0038a1014011511040020500a9034030400d00010000440034800340001e49200e210721030b01c1c0e1901c9001501d008001810060811009000600210f42d10800d0954800c80c084031816460f111100400c02e64890041e014040e000b40c0c90034807510044082280600318001e556240345a40c03200034072500da1107100c081d4030160b48500c2401c0c200c1e08160440660190050003003070309100c01c1160700105402c048611100191703d0013424402c10400e4841290404416500e020385010a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 640462769 1250 640461519 640461541
    0x50112051002030403020c060c0705030c09191d0d0201150519060302030705071e02120d2a0804080d0201060803180909070801110a0210140708090c0406030c050306060405 75
    0x500d103001d00580010003d4141402046240d000341005043c071641c44054000454842c002400b07114801d00441004030b040d071404a000502440d16055800301301c030580c40c5203100400400300d810038402e5074009001c10f012024022562007550940010030382c1e030a240c000b02d544154030703084a84a980042400504200080d61400036148142001030740d81d110304500362114018040001c0c05034046003040306088400071134282096100351401c1e0320119000740441d48031010380c0c12200c00941a60064135041d0a060444c4010b5405a010032800b101c0c0c41d1203101c455881500b160f18035602021901c4200341d82441036000410001c0003450410440c0950300f0710400000d92468841c10b005400f19208843c1030120074010040b801c002c00130180c200441203980d4211980d82c00250051002c4500519114065140e91400005030750700c082d645d02e00c0654070141c010b410b1505a204002d041840d5449038031568000c0c0d40036100d0104214038000416140100c001c01090180f810141400301003444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 640464019 1250 640462769 640462783
    0xe060a09060f0c0203120a030c08010302031b011e080103030f0305010312080402010219110103060b0322050a0b0106020a0204061509050f010329090f04110f040b03060a0f05011205 79
    0x2985400c085125642c141114400894900a90701d0300412052100c020791450080c0320403c215242400180081c070f0098551190900c006501a0045500b01064204501d08400e58600504000e450f6801c100400041101e100d101e0001096451005105060b0055410000c02c0c146103010f0100d0340c1140d407041201001912000180582c1d40c010500f1613000b4403a404d03080c1c40312042c10b0000d03c4141840c40844500c44240c5020928004010800002c0d11048a04c1031501c549a1070101e840580d01300c0d1510003030801079030680608007080000424030100c543c02007181c0c0d802021181601e0040008555160384070841082500d2101100c05411000a100b03c5900b04e600c413000c0b6541c000140d0103011703a01d40140ea120745802d01030402041c08111003c8514080d16881c075140d40d500d034003400780b401c103072406000303004480c8101d6428941403180025004000e0004240d0f200302c40003080c85c0000540e11028070b00d458116842a030700c080d01c10a401403102b08055115006c07a504d0300c548903c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 640465269 1250 640464019 640464029
    0x5040b130e130f1101090e09060613021204020f01030605060c0c100e01172502030c150105150d060e010e091501290427050106030204030b0a0b0f03060c0a0e060a09 72
    0x101130158100680c0100d02450003041d80b400701d13640c0c0f072400301f0350700c0e84805040b01c643e4821141d0030380c004a2920140300342c90200d0700c041c2d400072680c1c98a07004c101c1c100104880303290416455400114813511000090210018404c00030191030600c6001c2051840c0103941c01c10820800300c48501d07843c1ea000120404640030084044038070384a9000103020f0a01100c00309086052030502007046950000040c11101000c10a032200455070b079050701c00001081c03080c940e100b292484a138600d20504001010041d1050b880091503994036018820103c509074020043c0310a04800c100d02c540c41803045404540300b100e0341062542c1040d01d403440c0100840010280030000c420030803514a110000c4030050300710b07220740384c044040c3c0311402c04210303411039500296682020000075441c0d0013402540c007525880f4034600d69603519502c0210040038402d0010f6848501c04100c0070b0140c4082c005580103a010056803a0384075510310700038002c5054240114013842c0c04103e15048258040650000c0d24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 640466519 1250 640465269 640465283
    0x90c0d02030a0f180c0b18060a0302070c060c14120409090203030c12040501020f070f03020607050a0c0923010302090403030b0a17210a120b0105040b130e130f 70
    0x18a41d802c2c240001c20402014010031458200d00a000072200780014000600c110700005880e07450b03a10300b80403030082030340c18030300c2003400005c52041d0b2800201902a810f0342c0d1900509001850b21000c04c110004e48c018004102c000c4a12000d110011007981c0090b0034203402405c070fa041c0176020a0807481144145020a50703146440d8086640c2482215800303c4000126020490302411400469200c0d2103201d02520038040600401c041c041285801c940072001d90840441c42d6030240310f030b0b0740c1c0300304001c540364042d0446140c0007442912010019009548000820000c144002e07202e20095100780e01e85107a55100400c01a038420542590143c0d05150214450f5200400300341001d100b50804d80c00300d01100d0342c40c1d101000c0040c0c00a118510740d0020940301200080200140c450b50340070744000b0f2400101d01d1004180368105415001040c5049031915a5070340b205040c58100311f00404840080c1030080201e07901c0040310940001e0840642d0a400080d991100c041a44141c0d0080800c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 640467625 1106 640466519 640466521
    0x140102060123042a02010e01060b091201020c030d0f0f060302211009060e0d020d050d051003210914060403141212070e090c0d0203 58
    0xc0318110210070040b1a14018084240404028a40c0058890356000c1c0c0c894200e000c00040400c81034008864003220800003825034400d030741c0c00203c0760304203401440340540b08421603c0c0f43d0700443d91040901e05081641d40a0300270907554040f030340030104000010052030341080c8818500e0355400c0150841c1e445c50401228020b00010303410400c0d01d542809d01d03034250b074100c100c1121400e0071105100a4a4582429201c4200041340c445071202c4507100c040c0c10800061300c2ca04d0075400604031062800c1401403070b0b0302482c0c00450001d03864501103030000d10b810200130043e503003280c0300c01012001c07020100081401e40780349000003401800000b9102d0360345094103800309402091180f07440d1443e1504180c0500c0d8042c204018040c42c09403e980c0d02d0135200614820312081c15407602c1d442e200c040686401102509240281c03019010400316410500850b6181c801102d401616 = true := by decide +kernel

theorem cover : BRFrame.Cov 640287769 640467625 := by
  have h0 := BRFrame.cov_init 640287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 640287769 ≤ n) (h2 : n < 640467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
