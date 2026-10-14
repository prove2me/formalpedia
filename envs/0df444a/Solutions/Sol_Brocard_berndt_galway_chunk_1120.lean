-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:19:38.133344+00:00
-- url     : https://prove2.me/submissions/14d8297f-4798-498e-844c-35ae35b350ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201258992 ≤ n < 201438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201260242 1250 201258992 201258997
    0x103051905100908070624230d110910080601063f090c21032a061415030f0c0108090c12030a110c060d0e1e010603060f090807081e0f 59
    0x203415070800c5001c005992054034200c481141c0c010341441c49021342103070800003100907501090b144ad02d011801804103444895006000e441800c220441e55407414400d98130b0000140c103c1030411009445180207101600d160582c0242c0c0c6a00400e541c5081551014540d4030701c88018000905251200c4140172030709a1207810364806520075200c901c48004c07a1522481038140040000e40140907443c400c81c0d2860741d000300d440e100352081e0301200c00c0d80c0b0740105403421464450941903460b403c0c0400100c80440d0b1207480b01d0268080d211010281586a4450070240501c9051003c00720004200c80028004034000e90710080c05040e00c1d8030300c80a03003540c03a040070300c140380812184842c102e0054000100003110010081075a0b142111030b044540181c4071511207040a8841c23032010b03c0c3d04000d0f4920201108031f941000044561941c1400c40581e20511541c2c410249801415000b00b00c5507400c45150a4010f2102d41c2d4544100402d048401c0e094200061604000b09103047c0300c1034880300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201261492 1250 201260242 201260291
    0x92301050609040f080a0e061206010806030f031b0708030309070f08160303140d0905030d060f1a0a210f0f021603030c030e030d0501030519051009080706 68
    0x2084a90340304020b02c01c0d0004260360260254240030503803c009980b06009006640941c0b0b48494050940b00104003c1d400500320800759510200c01c2001659101f240c00d41d00c10403c400400b120309040324000d481e40f040d100b00c0300001400d0784168441800402c000c10090510400b1244d8914150700c0041e06e42c0ca0900aa405d031002c01a40051907800000d04070280c00000356400c2c02071440c5550130744d150b002c800c181200c034003007c1c88a03000d032034968400d02041c0c501400255503280581d8186a00312403564100d807000c48051581030041c0076820411461440010604544e030b081820401d4802134100300144d00b00140c40c1c44200c1041070755402844034544480b20511401d600c0c0c41480c0241c0c01030301100780c6980d10680c603460109110f034005900344510317400c00047c0da03904440ba19003594050f2400c40340c059200c074010420043c0400c0303504a0000c40420511010126039201615456007500d00c0140544440344581402000004c42d02102e074040800c125003a07441d4061011640e0540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201262742 1250 201261492 201261563
    0x3201212060406170d0503070306080d0906080601110601030b0702031e0d1d030a0e062109060f04052a060313050f01020906040e0c1b0604170a140d09 66
    0x210001903030501d43c48643c072064408001740ca10000298022580398000910040816885a200140c400e000b8000e00c50042d4082c0e076000c0c101c9060030f001402800003d03100c9810001c880c4000c1c0c5d9035480110700d41c2d065952222108103261161802207203580034103400c1d049603040c400000000c0380c0402c002000788081001d8148284240300125505106292182e0041d5030010846c00b2002d600ca6802c2605a0030000c1c112810002c09284038101c5012014413500f010b01000c060020901c000c1000e25402800860443d0f0b0b640707896510785440d054071201c2c0144107a0702e10020890584801e021894204020340b1090b01e03450b2900005054008405080c0d4481c042c01c42c0046410806001312040104007414052426140100d0450207160007095528408010301c00c1c100c51584c0000c0c86403010922500034089802c285c1401c0b90119039800340e000700d04030108502c40a1903040102551501c003081000c0c1d0700d60f1490001c8501800a42da001400c5100341c0004c2588404d0307250b03003240c030000d03400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201263992 1250 201262742 201262751
    0x916060216050909150115110a03020c150405030604030c0605150a060e03010207060501030615090b01140703030e1006080c1507060207020a030b01080601180504032012120604 77
    0x1018203036254281d1009220100c500c090090080d03081500c00035820140003401c986054040301c3c0b5501c0c0444007a0811881e0001d4074142d440ca00f5804081540c40c0e03026100503111350015039030041e5840c202448924000d2441c00f0f5050890b0050206917402040301034107440440ca041e1400500900100c0c008880c400d14141c0440e40164a803610095145000f0b4134411b201303410480d003a140002d0180000e58199020016503001903202c0c0a4a40218880e540200e03800c08000400000c0c8000340d0081c10700d8500c0d000c99400711b03a84c40f0160010142e41010800d5480400782012000382c40d80d504c43c000b040c4036842d040e01800c0b036151310003c1212018400d079000c540605080050158030707032102c181c90070020721110020407142c0d8010301d5242c3c80148000d800796580c0c0d50741003250909034404500d5421900040107800c0484409040e58034204900300824549942c02504c003800566002440c06000480c2840d240c4003081507014000420104548039042c030141508600c0c821a4101d0045050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201265242 1250 201263992 201263999
    0x504120f0221071a0f1611010206040503030a050402061b150601091202060d0e1609050c090d060504170c1b030718050601021204060203090108100b07031b05060916 72
    0x4103049001107492040a05401807070903516038480300402c100110f1450080041c10170204040e0004c01d9001060080c2021926690501190601c00c5c0e43d813a50654200c40c0420002030300120031254007103030780306000403070703413a00e001169880c0201441114001b00b440b4480c4072034440010309004103042801000741664030354004440c070021603c20901d09084000360f410061801c100031b00241c00300c6110000c0e0766001c40944a10f0145c0c00111000c40c6202000148000b00241c0909988040386042081c5020480380c00b0405070849100003410060b1740354081010401c29141d501300c3c90340c4582045c0c1c2c07200e40d080c41d4a501c66002c883d20040048102004c2811418007050500c2201c01d0021809000c00c0218003c2c0d001d0080100183d0441c062007069054070703c3c0c8900540080d00035a8001c0d6114600b46002500300100500b20f410440036406040001d186404225450164035150071030120004100c019404000100010841d000b154200158180c0000e1580078804120b00f200402c0f954 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201266492 1250 201265242 201265279
    0xc0b09070815040f060c0801030501061406040b0d0615030204260309090a1e0207150603080901050705031308010b1c0206160f020a06030b01020706030b0603040b04030504120f02 78
    0x21a8070034810203412a003155958a2403600e031456100f80a43c030512101c40340f0780d54020440390700340a01800300d8200c01c014401c0c450309200320005404041e242290000007900001c4550041c1d11a43c080c00500090006150490f508401c00410300c07560001403e1591405c054043d40040c013440130894816481d017108003000c4445419501d00ca203000e1450180c0c81d00611140326001460350b22502e8640b404802001c4036805a07080d442c19000c4010388656540c94412418448492145011400c0110600c0494104000c80b00600000d0070820b81d54040d07480c0082c1076002c0c2c00c4c2841807826581400140100301900840c8a1040071220b0a00c1c900e108110149000d8844501940106085c0490018240c40302444920706003d049180c000000b19800241044140d4000e540040e4440490310030650701001801d010b85100e041c240301c001c4602010484500000340050000c0d030950001c0f80a15005004850141025200c040c284d402d035810118401010400c080380204042c0462840440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201267742 1250 201266492 201266503
    0x807090c0201020f071e080301030b160f02070504050a0b060414030f0d090302090601111009020901050105090312030a1b0203040305061b03062101020a080603060105030f06071b0609030c0b09 84
    0x3003407041030170b003880c0964480000081600400c2c00403160149a1400810216000f460081d841644081268138080d0ba039900b4170307080400c031501072000121003010910340220b86041503d8082e030300000e203079442e0300082c400382001c7d80c02c5c40e411200000d000f0510810400f20009001000d804607070081d0a0250382c0c99a91710990701c2c04002504414042c4014602419215013090703051505c0c42001d0100c0c1e155508020008200300c0d8074039600d1820200b14141070340a980104000d0070614180702d00440482d840d050602245204100008001091420310ba03000403044609000e6400003401625406541d03540207010075503c40c492500095a00c0c00c584503524030107940310454900390f8a40c4804e1284804403c1c5541100104c2000125450740092000e00402c0300341350348412160a00d0320a0605180040e00202c2c0650400404030076001c80008034150020284d1a0807030745090020204819406690320080405061500500c141607003e143c1c0c5404902805d03030709140743c852214880d03999 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201268992 1250 201267742 201267757
    0x100207050109030f08090618040c050f0f0c0f070308120a05040f060e01141906080d02030915130b041502010603051b060702040903080117161701150807090c020102 72
    0x82c02e4803500780000742441c0c40c4103c1d0795105180075400c00c1c00350f00004609800c1041908040c1868500c610300da4917181c003a00e4004000341c1003442c0740401d1258428043e02c6101c04004c411040003501c0c15520300104150700c2c1540c90841170f2403100352285010001d59201d0104604000d02e00d401103030780c0d08180e00c14107000d140d20500900c0032803120b81d1904090301c0c1c0525003001c00c0d5620b006407103640000310005d40c4079040d00249407409003842c01e554800c64070107412001c2c499206802001446030000211010641e0444092000760700702c0b02d002c0d001d40f042d0703113003050200c695036800140341814001420544070360316242728180807815012400c0b0b8140e84000f074007a80c084c42c0d513a81c88410b00401c58070480f0000d029289004010740100f0142d89100314202c0015407000c0c010003c0c1c845a80c0340c50700c40c0c180788010340000b40c40c400300745030b120009010b541044084120403110501c8250b0101c1c0c449800f01440c43e602c6561001c1e45900d9202611401d0340d442c1c10300c0d488a1102d441032003112942c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201270242 1250 201268992 201268997
    0x30402031c080109110c0708010f110f070b060604090e070603180c0e13050304120209130503040b180909010b0a05040c1407030201090b0f01051503040201020a02011812111002070501 80
    0x40e40e103400480300240101c0120041d14103410031006c01081c0080c00078001416150002041e951000e041d4503048034100141002000c100744004070160070428100c906045c5c00480c9881581c90342c500040e0301d485903a01000c11640f03042c1c1d81001c01140845c00e41d013100c2441e1001c00c00d55075080c5c0c485020f038a007204010600003038110240040001c904001e500a00d00b201c2d00d03511240b0766900c3c00e1455210b604149e05109807444283c08600d00a0809036015080c000580e03022030683e956556680114011174407012800304004142c00b60507078000041a80040100d00b0500308201103900030003d1001c01400360114020101c1d1605103401751502d00803041c0d40e103a80328841103134000c00641001c5c1085045540b16990040810344210381d0030b0090100300540300b00703945481c0c200840300c1070441c00f060354642c05000700300260b0317004505004000d40a00f0841140385205000303c035180c841d60000324044502492076170070700c1281040d40d40607550549100324090b07002441641d07900313000e1285c90300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201271492 1250 201270242 201270257
    0x3030403271206241712040602122b0902030c12030403030c02190303200703080702060a0905130b0103050c0301030b06011b05030a0507050c0d080a03110f04060302030402031c 77
    0x1d081c1380d02c040c0d40300d88284042e42e0400040403e189080c4107030b070f0000b02d50300c6992412040d0f2035030900101c030203011130406d0145010324101c0065154081003400c112600e002080da060b180c00c6a051102894801c1c0109150a400982c0703800010000b0a000b07901030b03c103d00300d010041c14803402e001324805809005604092550364101e0380e6103118070b03080360044400c116020115203148400d90266100b0f4441c0816200390003905070400c188032507446425032003841d00304007080808048821090301550100d0b610400c0c140d064a410340683e11403504035416072035801d213030300c00ba81c8035401010099800b88129241d1069600c1e80f408203010141c250781e5040e01003400b81d80100f40f2071034400090507003262842e020342c59003800c41d04200195804113100084100400009006481c41e984040b40d44d001030304126104ca003818041e20f60700701d0505546440d1800b022496905850800060103041640d80307480d030f0b0008001c1d410580e0200e001c0e109000307200d50348a81101d4202d2684084e86d84800c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201272742 1250 201271492 201271529
    0x70c08090616050a03020c1c02130b2403060a0e0610081f0807030b0c190e030a050601090902090112080d110702040c11060a060e01030f0203030c0303040327 69
    0xe569070060140790b1003520b2900000000407402e1003901a0503010350003400c0300b00c80b42800e11040c0b81c40141d507403000101c1d070850600140d4a4196003280242e08c1400043c501c0c3d50480030a0b510280140d804000c0340300c070036400c01800c280000445c411003060321141d91060b990702440340562170903580c1c50b40c800c540b1450f140d0540e03c6801307400d5020f281001b0380114070701240314010010721142c1003045290003040040c001d10494040c25030700112062405403400350010f02003800110400da0b00401c01805032144105540c00700301c55440180c1210a4a200d540c0d6100020020801c10f10700b240034004a000018034600d5181e078444101d07403c007500740d19000c00d05000c8002491400000c030340c0200e091000300d002d42c0b114460600c10a4543d1940d03419898908115440c1c40d200502c460251810070200703001940325020041d0440394050f02c8046640d505100107400d500170000d071260284004020081859413008009500400c203510f0500603c0c10503a0104040f5028011000091220396100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201273992 1250 201272742 201272749
    0x11100e1b060d020a05040b0f03070206010b0a0206040219081204090506041e0b0a0e0a0504060b0a30080a081e04022b060f0e0105060a03020306070f020f0604030302040e070c0809 78
    0x10684c1040500e1302601c0c0c241c58040d00250340e004065002e040800101c200030046804109031401f40c8802c0c01c9181c20a280303444002c2d81d136000100000d020f2130070268641c5180f502c2c0012180a8181001520001040b54000c0a0190018401c046070740d03017000041042d5090600c1100c3c46200c1d42182d420b110b03d9803000301c102030134804480f42d40002881100003400688007075954040d1a0003400810203060900302203050fa020121200d2090140362800c10044040301486202070b105da402810101040c000424010a001140503000c008006485600303603600048142c8110060880981c5045d20a1611005500c08a8009402585105140307406c808074484c0e0b4404c0c4100c1c030003c042002650303074420b800c1d03031406600707940d220b81c8130074905031000340070700480798880400e8650b14085446c5400195541c10040e0000060043d2911821440352007403151800c0f80394100100e030010308040c079005000307501520030094413410410200740b4988c80740c0255190684c01a041904009042082 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201275242 1250 201273992 201273997
    0x70501240608072706030b19051c060c0f020d08010e0a0203040f020d0c05040e0102070c03060e0708150a050903090a0b0a05130b073f11100e1b060d02 66
    0x61000344804000442c00030140b41013880c524010060700b441034607251240c040e003620340e02101c0900c02c0513210310a114001c400390031801154800c07078a50340902003c2d001d072203180030900750250101342007142030785040790002803c4c1141c5a5580c21510781520150301110310840a0180107042c008a0006c00c03100c07589500035507001030147c940f5411440e010750008851403586402183d03130b210940d0003000180f41c24480c51000e000716100079890032025559203002082c60707000040650380d0343e001c0a0241c2c0d0040107400301a01081c13080b035805400001003003146074001c03206003950909100014400500c08415a00c0c803481c080d099520749400c000020b4501c1e00610109000c0003c184000c03500d0240041c0c844000f003040da22480d03030787c0c403090034881c0d80c1b200044000302004811081840c805021450307001034004090b03a08a460803030107602142d46800e11082030b80c0c1c07403082e0500c3c00e80319001617200745599401403007103840140094a01c40051015801c0c2182c0c466010302103025040040d400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201276492 1250 201275242 201275251
    0xe06010e040f0c09060906020a020d06110a02030d050a02071e210507020a060302031911162906010f030f0f05090304060807020604020d1e060203070203070501240608 73
    0x1031240540c00c0d20008101142c1c000c00120102c60303121604080c2d510340082e8410098021490034090f51810b000c03000c0c0d1b450604141c028092200780841c101440103d500c0720250000310303192030742d407592420310096032070b0800d9441c09a068074110124004c1d00300345c03088500c9680d1110154070051400172240c14030f803465020944040f0340310650111100c01c2032510095003034107529010f03241d01c2ca0380180b040d11410350300b10034241841003081c0a41207554200040d030a18805101188901d4180c901a030a4010f0b17060394010f0f403488043c54810005200d0b03e003d46d801041010700c0003000010f40d041200d400070b45115000c1644891061212031007504005003100c02c1d260085880d0310340c821444103c030022106040d09800c04141407104640c881c80c041e030805c1c07180c8004c05007400c081d00041c45000704044e0050101d030b00303090441c403480002240c0011198200104540b2450000b5000c1d4499202020480382d40d4604000001041b0141d02a00b000701d0031040d618805504180054800c07010140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201277742 1250 201276492 201276497
    0x114060901090f1e0603050708030f120a1e02030403081605030c090316080a050f010b0102070b09130f020405030c0103020c0606012601030503070b160215130b010e100515040e0601 79
    0x1485840f0604404ea0300c01000c901940c0c000403510b00c2c60a0450600030309406c2901c150f00204421200c3c0343e50f540940b00c03050002c00307162130951206155a801808100f003e0741485040e030401e098034050541c040c51155009442d007121607a81c43d2443c0701c480c00085a040c000c924180086045041d81c000546485070029044804400b05603a428000c41c104c0c9d404040c16a001441d80c90403c030090201c0b140e10440702000307000c80ca20703510010f5261000f030302800f0321041020485282c103070f454403000782020005400400c283c0302c011810710003175849405140c2c0a403103003500300e18241d4840d03c221842244c0241c00303045244c0b02c8600455140d01e00354203424052034805151541c00c4407084800c2e0080d80703d80c0065035201018540030000c2c0c400146024000d41c0c0719040c0c25406600459240d040403c002c5000840ba0f592004180c038050bc0c00c50040c004400c201c0002c2044500b95026030300411030601500c03511642ea10422901954110203031507140c00c14401080b04040382c403001d41e0000c5050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201278992 1250 201277742 201277751
    0x18040b090a150807080318180103020f060d020a081f1d0a060806070c05010b011b060c02071e0e091917040e04110f030c010f080a0b060c0706020114060901090f 70
    0x43c58030343d00d07210860b0006251904001450900e05201c0c01c542e0080c850f082d600d5290131000302c0c02c00c5495000520010b402000f64000a607015514402201da488112800031500c48002480007040c0c0c01040310721341e0010301c50020460101c100c050400040300e05102c010060300718242c0e82c038203400c140070342007400007074480c800410b59490034042c880c412800c540c1d0303984041a007030034203909607543e200354541489a440b800c0d00c4500307481505034080c9504a200801d045880c1c01d4124070b0070041c1c0d80105110781c0c2030748007080341c40300108000c0d044503841c0262a07808d459240109444021300003541070000c0280c2c1c802400200030f200000c981c00f50010480e07082c1030f9111400f8005a44c103d5044903030203050009000c4924040c5c000600ca07030407d80040c40c6148004002a10741c02000f20080305006207500010001e0840d0f41103201c030144081c00d41a10b440780b03050120f42d45c04090152101550910200c03101401901804510a10008110a200780d04c4d104070701008220038000c4036413840e00e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201280242 1250 201278992 201278999
    0x1021519180222060b040f050904020d140c090c040501092105190b13030203180a0308040905040c080c0a090507180e01051206060603071b1718040b090a15 68
    0x20031412450b00c0c03c0f0489841211035000e070514040320081c1c0c10540c00d0440500c0140280507945800c482aa41c0a0311000d6207503c40d4000a449c4094107000104440400c083c0480b0642000c00c0c0c01400c05016120300060b525840380040e80741c017490042d5400150426410003401510451203440104204844220300d0381c02c1d10f5043c2400c0380a000312011114103504101004501000d03558000c1601c5400c66070440182e400946a1146104c1441d001c040340910030026511180c00800850f40611300540d0f8a60b03031403286000d08421201545e0a13901d0946c0001d400001250100d500c01c4010070745001c0c40d061680c181d00034000504540100502010a96001102ca130340c440054941d06245407403a42c540420401440900503c0c0748642d0040e0302801029112482500c0c0c100c1c00908101d25940001030b1810b080c3d010882020703040e01c015040b50400c44100c10300814010070b00c219503000d00e40107002804140d0300d94000d00ba4000c1702c9400000c2d00c09400343d200040120744004640c144603607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 201281492 1250 201280242 201280249
    0x20a1209110f0a170a0201090803070201120209060906030f060f19052e11010c0302070c030209040807050a0b04020f090405060f09070b12150409050a0308190f0902010215191802 78
    0x407000280880d1710a4440b6070656800c111803100030154034000b50303c0c0840c030750b0008114980c200d4100c14000d0700030500c048241d5680b0290303003119401401003907d0b4a80042d80188081c02962403c1c0100c900c04803e81c0705091030111030301c0b05030400e525200014a81001e00001100c0350946007a400c0e0740d01030303007118242200c00c814485d440c5c550f9039401601c80500440e0865410085403020326204000c21400100107003148002c80303804891000013079440c0d0900b54858452600018140c1c0107882c50882040303846001c20707000ea40251407900000c2e00035000d00c103c180303003580d000c4c0559002800064220a06440040d8000c20070000e59000c00da44101718500b9410081e1305901c2520483d0420070388032400c003e10b6480b004101c41c14002150700340c40310358440c00c82840103010025640001500c08203610010f1103c02640d40d8100705810b05820004000e009440c012401030182e4442840f0b820007034900d55000d070410049103c00c078418909850300a05142116204061107034240c0c0002d6178 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 201282742 1250 201281492 201281519
    0x3070204061d07030c090603020702043909030b0411012703111e010f050909040f0302150f070c031803060519020f07110112050109020a1209110f0a 65
    0x4014120b40c0d103902002800502c500c0006000b4001c051804004c3c070030181d44000c440044400c541001a030b101090f0011070050072800081c0c281141c81440040d42c8442c103044002c51038140364504010f02c0040300411100c10440340b002404c41d40c541c40104010814a00f81c80030945c505042800d210004100028810003e03548481840140c2e618100280094030f1101b000d02c180884902440740c0300c0e040e11189d240ca0013a0034904200540807070526140c082c40440c4d060a030028010a01883c00e031038510400000c1c0c0c00100c0041c01003201d2000b400d088540d107180500200ca090344000e9a80000845507180c60920650030041198042500d403903500300c2d810040e40c05100c0224492070607240b419451050344150401c842e10411035203052036004429980341c60303485001c440c101c800c2000102e42d00c4042c0351051000c0c510f0f040000420340c4261380103211003d100d0310386482103290310550030100d0380741d414060251400860f2290140c0b4120350286e4505000520040c4c60b5500e8035907042c00d0304c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 201283992 1250 201282742 201282749
    0x319050105060a06020606060d0c20210306090103020f060715020c0f0303010305120d0605030f010506012003030408070609050a0f1104020a0e0d0312020703050306040b03070308070f03020307020406 87
    0x6956603414408542024504280a4407480c001410103082c07d0300843c096109504e6488076060340c9000e1042d41610070f01540b5141c80c400c2040b110030102c030103000c90729111119254810703041080803520b1040c0c83d032001c1e41d100d54030040c07111b007413613203144c0900c03074404000e41c40b02e40d1043c1c00b04142000070b0704007074401da020361100100580342e00e44140802e1801c500180740007480e038024001000022000103040c0036a003500e4005170386940e5038601010260585410aa42c5402410300034405d041d41584550b1040000f640c07400b41c009441c42e10382d802050400400010b03900b0800000700441e560388000c00038a0310510b000903800c4059200c02d41001080d600807140890000c8011080c000200250300c1c2c0d4001c00c940440c50841e0b1a40c01500740c801d0150313810300a010b00c5445009060080071b89040c1c0d60248036082d9a00c012515008129a00407907003144528644003a002c803c7c140000e044d816030798020301c11450003040d03031500c14900400600032802c51000f0400e600040e1107501444005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 201285242 1250 201283992 201284003
    0x16151d0f030106090203060906090105060a030e010b0904060e010b01050a1b0f17030703050105040b0109030308040309050a06020f1e060c030c09031009062a11030d0c0504030302190b0f060319 84
    0x200e0a00e035080020722380303000d03209600c5800424010b02c05030350f070380701292140501410b0000b04031019420141c0940300c0f00490036030065803c4100400d104564000900040c403410080205481800054030240148001103001400202e10742100c1c66440c0e034a22000c90040d40300a441420703d5841d83d6444480c0c036000303242c8520110a03c00c8a42c0c0602685001d4401220140991600c0d4000240840402d00c006401c10a4034000302d800d05020308075580103054060080c2131815241d01c00690b5803501d0306249910341c0f04010300108084010003003000d92490800191110713440f00c4880460303036000500340340d01c8804200940f21065808010f016000110780340041240d040a08201085907103c0250a40200010f0500305501d44141543c421051581c14100480812b503501c4d54030310b01a050074212040d00d001d01d1000c01d1500072010b001124404d030b0071605248582000b66000c186182001040d0080035804140400300c00c008590f805003014080b1550180528560409040441801c8e9038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 201286492 1250 201285242 201285247
    0xc1502030d061d09010b150315090411010905030a020307090b060f0d050703110c0c012118050d0c0c1a0c011503020103060f0806011202010507020d0516151d0f0301060902 75
    0x41c0c0c03d81c02140e6224003910020002c001340f0710003140030f00c280030304524144080040081c4000c0000c4030724800b000d401904484c1a4134180c41d1000e60742e1007010f00c441c0400c0080340c00040324580040c9601300140d0180140046a01d41440c400c0a001c50710074040d4406030600525540c0102100645076841c0d640c080031440781018a0301070100e40c120b00c01c001d0700321401c000b034041040c00041d00c0210000203180051401e81030000402c1582e0200304105291030510700381c4880b5105550800d1074040c058019038481d0355100100b1b55940001060044c10400c40ca0ba04202000b040700742c41da0395211120b203c600c0c024441c0c0d503081c212079408106a4600c4003005c014829947d0500c1094060100c3c00b6000b42500e04000740c40740d8410341446000003c80d111310100c0116440f035030075100354a90161007501c9503215807038201c0e100c6110140410003420240000103102d0004401d00d180710f141a2610f0100011408124002d05007070b07040590800290606001903460034851316006000c04000141c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 201287742 1250 201286492 201286529
    0x50f010606020a0b22061407030e03070b06031e010501032d03080402060d0623060c070e060a03020909060f0f041a07030608030408030903010605060c0304181107150b010c0c1502030d06 81
    0x600c7c00402038101401c040c90b0000c0c405040e40000102c45034680c01c00b03506006580c80c003000902c1c2c401440d40b20500064010003d070107401c415000a07050301d00c80c04141580c41070284040f04010081642005a02c0c10424000003190240d4030041d08035001920092900116014260558441d03a1181c0c509a803640105400d01071100f032001e80d0404100c501e01e00d4440b41381100d60303440845015130031005a0480114086658072203011000b954090001211841c16561854643e04115180e00c00b440d15a4005603c0352800b007030301c0c5c0c8101c5d4484030f22084102405003031808030720024100010715945410125482000f0800340008041e050000c40d07558500c00203140c20740b400b03640040d00170042404100b41032940802a201036a480240341c0203903000c071440c140d014100340003202290450001d518014003540080300c07000078425180500107005103c0c0111040482c0c4a070180015140310350070300203080403009204181c095441102d0622110030032003c01c68400307502007d50b1141961221 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 201288992 1250 201287742 201287771
    0x70c02010201140408030a110c0114010509010e010b120a0e0f07210b01090e030d0608010603031b1a060d1704090e06010b04060e1c0f050f010606020a0b2206 69
    0x44910400c0d400311020f2420182c2ea241c3c44ca00001d022116203684684040e220981301700259149421644024031513101203081c1210158820b0040c240201041c00010035010740544a007412101c074071750582e10b8005254a440c1c1b20050207030000071104e8503035483c098080c80800c000a601c0060101425010703103401c05110070043c541800501620401c83c20501048e90002d2041c1140d40b540360114180720300704d80050841c0f0941284141482c030b401c0e40491808015844501030b1b0b48240c85500045d1941064181e8408620074010706c1d45500c038515a00600100802a42103003002d0301c0220100142d0b0307100c840040b10401451280e0802040404c03d07101ca9005115802580d10b0203050381c3d5051800350f50281c41503002d8441030004420103900e25803100746182032a1311039002000039004041c40c100700c1fa0880300c00c082e00c42d4494840c0d10640c0a030184100c03400c4440d02d400401c03c43d40c49698441380420002c0101c0086000b80c001c429100010a1101584520807440001c0c0001c260118 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 201290242 1250 201288992 201289001
    0x13270b03012703050f0f090307050d050c01030b01110a11090a02040e0c07020312030a0c0207061d12100507110105011d010303050705010605060c010209090a0b1503040c050603070c02010201 83
    0x115109a060103441d0b40086501010b1a4035900e0745582860451040d08003528180329001c0d003802d0401c0006000e03244601c0310340290482400c1102550310703032a640e508120310b0380420000038010b600100c0070078078170b58001d80c00b4005d10101810080c02c3c81608402d00d5080000e0000295140030210f40204510328200f488030f54044080c100450a060501c030000c2100100184810211100040c9075419541c0c1080784192943d50b001525590b850100d00c0c40d03002d0b182e601d41446c0540f00c0d00354080356050007500d1a03006108a1010381d43c0d015071003003c00070031404c00040c501480c043c42565039207010040c0110303840303180c0c0303511000400c000ca0503565003190b03c140c0c07040c5080d41c04c8180860301494902202411260585030003a154040ca003030003801007103c0c1d48003e03801180000c0280b402d0350103402071300c0e100e50700303c0d00e6962543d94261901e040c0d071001104280d215654440c42c0e0040e546450103980c00a02400703c030108113840d8004203590340c4c8295041c0010030780c650150800c42d070742400b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 201291492 1250 201290242 201290261
    0x250215120c0f07031419030905160803030a020a090902031006090e040b040f03050c010c0207053d3006090e0a020105030721090b0106140706021327 65
    0x10020320b0980d0b041401e541030700860000608102030034550103e000003007000c1e40c20032102412149070700c0c089107901600404014400315083e01800a040700040c440328511000c54100f44007451641e075030440e54500a60005548900b1300401d001d01181900c0c80344003661007450f52030005c00003c0c0c1442e40261040180754061110400c07104108800030f00801181c40c0c00c0b41e80400c0f0088100c0441c5006d4403180035114229041e1b40c43d05610801c02130740014084102c0380151620301c4000d0481000c901e001007201c0b45480742110081499039a05016050340320320811f10302d0524800c03a1807401c03001c038109856052180010800300d1030ba0042ca060311903200248031650707080094a41c8050311640729034401d1000b9052090100010380801e0050070b00c603d800d0300c280110740454040d0101a401040743d00e070305940b8002641c0011500a0040352a188401300c40c0b00941d00f4034910f84d6542020750b110030880c1804a822030000604610030050110440401070102c014141d400144502110829a0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 201292742 1250 201291492 201291511
    0xb090105030d14070f020d0f060506040b0f090c040f0906090b010f0c0b092e0501060f0206130302031611040f02040f09020906090612011707060525021512 68
    0x3084541a181c100c4038200001010009960f180d110b541171620110303c0030200a5084400116290304100f0240840060030780720760008c100c242c840e031080c80300300c4444090580e0040010307042c41d9098a040362545502890a028107460f1030b07100e8123080000301007603100340c0c0103640304c0e03c041c001c2625900a110501c0001c1ca044410044122030080c444011940098a075480250220301c0520040c0030300c101020110140203100021140c54807100540020080300d242d01d00800801c0c024498160500060000d0b801401d80e601e50281742603c007640030340c0071820752000b000303440104204a11340c5103445026200d2042410031450600090703c04940103a0341040c410001886503000006045041d00c0c0c050200680300d061900200740f040c811181d403154480c00c040b030f000203da00d171104030307606071004400c50b400c0c1c079400210f18598601c0a0300819001c12003d06c92800d0400d440b4003040e401c9000c44458034440d41181d00414519880303080007109000d0002003420000c007101003110f4101c5e01a8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 201293992 1250 201292742 201292753
    0xe0706110708062214010e100e0c0603010501050c101104080d0e0603071103040f1e08010203060f01050a0201090209100611030304050a0f0c031506050a060c0c0501110f060a0b09010503 81
    0x3080c80482000d0055048280444988010240b04000e06410700e0705d080f6038000c02c03c2d88110000c2a64038507058900d2016541011040b401104011403607038284213028101c1415a42080015516a041162200d070b040c45040c1e0305000d82603443c000c06000b900380000c9143c1d5682040ea0031418901200c030034405000141d0081c0141c2d4881c1c0c800c8961000c0c0c2850450035005070612850304502c110f03400402002488c80020645c01450301c0003e8003235022140c042c2810381d0301c0030310900342d0108039203c560040ac0f500950b05654004d00007400301002602c00010080003680c0010a082c9054545811f945007445c0c007801786035080f0040c4000d880616009509502c0c065907510f41e696031200b001060f9003800d9550b102006440001800555404400b00d1000703900f609940c1c000781424407800c0d10402c00004000380c3c00f40a00da240c41210b4015928a92842c10031005461540300d9007401e60f114821402c1c1141e0154080c010b581c081d480128011441c00c80c0b0790300304500540f0607003007a0704c02d8002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 201295242 1250 201293992 201294001
    0x70f0c14040510061b20031504030504030f0206040e07020c030f070b071203021b010e060105040c0e10020c0303160506100501050301150504230103111305010c060e070611070806 78
    0x521544044604070301c0c09400c04100e45d070403c51540c1d80b01100400949000d2400211500b13444001d600101095040703802c01040c180d01000c0741002034a001e40440c100304000d2001c641c09440040740a40003401042c41c007a912003003044004800c86542e4010703004080000e08915040c8000b0004180d00c400401d03401f41050036205603440f505400815030604400d01c150b510303001c0c0c2c040c0d0310740c04454a058084441c1e01210640030b40885211000c080c0520000410b00d490144910701030102c3c40c0e900c000032042518140309113452108040030551050b46500c0515a90800040038200c6403003d00901d008403602d44685010400341c01c080c0024000d890911551743c6c080e05803811950401c0c00c0525200100e00151414465074000c0850900c1c800c3d00c01c19440303400c404a00c1619820381e0300300629600e000c89002c042c00b5528204050036000f0108002c03a43c41040c5000940d4083c0e1070008101070581d01d1903240100960003040842e04502801b010780c134040c803508c40109103d0010703001900d170 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 201296492 1250 201295242 201295261
    0x21308010218010e12160807080706080c0903011413020f060a0f0f0c170c06090604080a03020a0201020f07050109050f1b0411130801050a06050f060f030606070f0c140405 75
    0x5454403810400c5501c4884c50958a8420b2003000302055015140c10300182e0203e81400304441c080c25101c0c1c41001d0002880d49000500c00c4210f44041d070b245091a1626204141c02d6844020603640c1592039103005050516200c40b00d500900ca14282c041442c106032050040000d00420901d2003103000780001030080d03401002c000d07480c0c50545030203ca0b0055416044d645100c0a40c0c010300b80014640d05112426500c85c010107480c0d0084040302c096030342d600e032516070315101103500401c400b07400c1c00b4649041e4043e402800305d504250001505148000c0044482504104001d64040c1e440c1c40c038134401c1c40400d11001400c4103d1001900620f00103a594164440400c004075001e00c0c0e41d10302c1108641954415504c140704105070402c112681c03551414080c260517221101c4851800200042d40d241003c6c0000c0e08000140440341000300303150145120390402001c05403c04010002c07540061b241103003410f10f461052458500c12400c16000901d4000001d80c0240102d01e030000b4004c0418 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 201297742 1250 201296492 201296527
    0x402100503040f050f0303040c090b0f06130503010e011508030406051e040503060702070e0c0913020d0908040b0a0e09190b030f1501290301170a080d0213080102 71
    0x100181012503030382c0c9662805100d040d03007801028200d4010f15465000c11140440198091130140b0312440c00541c56490f444100c80300d1015060713000200c0491404075082000241071340c001c01039049550107560b100401d007514010700c2103a2140c1d565800e81c00d28820145502d20103401030100a5051508244024100e07100d05001c2d40402404001c40c00030024207602254041d0001a050300c0703250a000801035924842170240d90440503040f00050900c1046800341d8541c1a40101101141c0b04821680d5001350b00007122034142945030400140420b80100042000303103002da41d1640c2c3e400429400030a4a2440004144190480424404c01624682c4502c09a4681a10008203002e9000011345800400800b00c0ca0301c0c018610000000e03180000841c3c1210802c404000c1d0320304060503454000c081004861049510a100600c9031154902c2d04002014a01c800c582c08551039484424007074210005101c41e072600001d0b0488909010341c0c6039001014224025070800a41240001390107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 201298992 1250 201297742 201297769
    0x50301030c09112b020f0304020a0602030a0e06070c05031c0806030a0c0501110c040609020a090b280210020f0301080c040b06041512060603020304170901140306130c05031e0402 78
    0x70030b00400c031300c4452501001490828040c5040c21585c40c3d40010207507515030800c8809a210320041c80001444500201c1240c0301b0002d1669134500c0c0b80100410010303660031612041d600408440d40206050b00c041100d8010040801d40b101861514084002c140c588010b104038001d40007840c8081c0025107000030107040d00d00c2420207490199030310f80e25600d4510a28507495105042010000d00303000c10f980141000526551a4003a6a0300c480c5c90100c01e210300091034403071840b40d041496591200640b501e80d44e044d0340c07058400c80c1082524a0b020780e000683c05e11400d40c80000100640070b0100440b000e5072006550a01010140c8030004003e4007a502c00c1c25024410181071400c143e01c9000180506051030f80300700f05a40d1034200040003904110b0b400c5030310640100181c190f00301c041e8207552240405a56203500e40600034640000f903000540800d400100411411000c40c1c0e0724002c0e220809001da5401c3d8891034100100e050441c0034105c4034907103942407800d10000d40c0342ca08049890 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 201300242 1250 201298992 201299017
    0x610060c0201120b0d03030b040f06120b13080d1407020f100c050405030f0708012711060904051602060106180e0709050d062028020f0d050301030c0911 67
    0x103084461141c080a01380d20740100c1d5019100010f1034040503015845200c0c02002581d040059110034020401200c0d490700401d440500140c3c4070304001800c01a42650245416001d64511003c42d46c464590340c2200030b03909200c0d5100d50301d941d10003842000d40ca03803107030651000b0101407407001a81501c50950001d5690919150150440d09030b0060080b14003d1102800301c601e0080c2c2094060744800c00e034013505c2421b50820344280f03000c60b0b451155445244012a0041d5404480d41e1201804084d101c1032a4000b1418003610510781c4d80c0c0d1117414450210b2040c603412645000038002d0918105800800a104401c1043e070103644400031410203690f9401850070007525400815103003041507034004c560006a44c9010800c1080d2900040405c50300702c020708120080e0505881014012443c3c0240103504a20410542c031710490944500002c1500586015a010004081c20010304696610210708000010400c201c034010380700c8010410042e041086004108c0031044a100b80d5114052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 201301492 1250 201300242 201300257
    0x60d02010207080709050a18020a0605070f02042a18050906060f0a02030d0615050d050a0b1f080603070302030c0918030d090210020703020a05120c03100207050610060c0201 76
    0x1164000c02c680c9000d44545000c032055079a0351080000601030403201c2140441c00d01a45400c2c41c0210f040c00c0b000319030b00901c42e43c0340e20f0400c0b404a6550308195011380c0d018001215040150b103030b1744140d0794040083c0001c1e440c16030081142500001449071218104000d04d100f030304035440e4000c150020351750201c891103202c0d203c00c0005010740c00b0302e0840d018030003c0000c002014980001c024207101300941d00900000b980c52040440800640c1e03038a0b408a6402c2002c81d020041551240d42e04c0009200005036001c00c241c0840c0102a104200d608580c1d542008500c22030341041600e5442401240181242415540440c2c1c903140000500c9010f5040c07407000c500d400c55440f44d0903004070105001c0b20340752509603c5420213002801410390188014aa125104034404100c4c0000d803038010300b10400036840d0805002894070f90385008040c03030040c05c00b51032903aa030170b10880901c0d4284040268503003e2070300b4460308018004e030101c41d59081d500f0f002c101254000c110300c0401502400c0940 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 201302742 1250 201301492 201301519
    0x19030c09020d0905031207080f06010815041b050315040e100c050c0d020109150e0c150f030c040609051801030204020313050109230f0601090b040b0306010b07021e010806 75
    0xb4090072810800400740d02002c15003184003448640003d2040805036030704030140d100c5240c0400321920940340d0178000b50f075038070004500010507020181c9042024000080403c01c403001d40010001e0020308200041e00001030041c881a440501140e001d4215003c128001204000d5036841c20115040010252102030384050319000c0d900383da8144415000742d500704200448028024020100c3c22104549910007055071010300b4801c41e030350b00c84103500810418032200c04101c052055581c052001034000c0002c5403440e00808051806003020003080c54031a420500003070701d1601250040c40c003401c1c81d5100610440034608a0705d045a40688005035240c8400900b4070050540c540c02504541c20100d0003410002c0f032880c0c7d11090f040491012040034000b0000075100c52404001c140c095000c280103010900f00ca600c0f40010400c02400081e801f1009800319041400076807160fa441c500c0454072905600f0121113502c1a01000003008508065030b90003c0c1c9844d0014201c0ca007d01e82000d141d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 201303992 1250 201302742 201302767
    0xc10031d16090507020307060b031905072c0109022208030a0f0809070e0a0905070f03030306142110020d0b180105010f11030d0c0e19030c0902 63
    0x425a8210481402289400168645981e03a4034409400192500514000b031502c00521890b80a007809a000e14503209580d114440900101c1c0d141c00da050184401346089803c104115010b854494409040c144c0c4c03810a01e00e140d0091607428005c1c20001d00f0752500700000c11191181550641c9030f005860399001c0d4030040310140d1152280401010034000840e0f0f800d40003020300186480f59513a0340410400c01004c55005105a4400017240c0c4604800e0010a582808940e803040321a0000218480240c48492130110958403c842c0120080010b009044d45402010042d029618100e11003c00002c08104000320010344034800094024000640d1902408417941c0580307206001d40d1150500d201c050001c0031f4000303c040c480d01c030801043c4014614541d215040b248161281c0b0b40700321541c40142c0c0d00c200614603041c401c1c002007180402d029224403550a42145070303552644103400c0b00061090340c20f00b41c0b04862851041e130000f000041e01071040307241954541d0902584075410012031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 201305242 1250 201303992 201304001
    0x28031d0606180a060f03060506030c0111030301090e1c0f11030a020303010e0402010c12030c0e030718020304080705070f05041109090a020c0f150f01170c060307170a0518010e0c1003 80
    0x28a05c41807801c0c2c400424000756420240c002d440882c2541c0307040301440300640307071502440619806508184010459811698400840d020700101690414511600c40001003019401904c0c0070070300380180c50480a034040c26812803000c258004619040d03203030802a59901052080c00402c2d49048001021a4400ca1240010342c0c2c0c00303a12980814207040000c0d021b054001d00810000d41c0d100a00f1401d40350005c0c03030b10b0884181c2d80b103002d2028030140156010f544024416600340d4410010784001450400455004051710202c10301c0340d43c100f0003040141c800050b00780d800e1001c14800c185040d600c0c0d550042d0000280c150045ea01c924103041039027881040000214540150080052000c46c50b406240c0700307085000520400b0380e2200c10f1041c20b001013200800e5164066000c024141c20100d005540200990800360720344e007049a4a00c01100d022145002510b441d2424403400403c0c2c1ba502c02103000a5a0091203100960390710941c2d03444845107014401d9406528220315035001313502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 201306492 1250 201305242 201305249
    0xc0d0804080616030b060403020a03110114120106030b0d031b060f020c0f07060f020a0b04020a09050a2c030906030a0209040e1608010b060f28031d0606180a06 70
    0x10769002e4a0048070b081c10711007401d9080c402007818588117206a260002c2120240e0345e00030854203ca40c216200d11030314999526030b090600a03a030b0000c8066030042d0002c4d080d0084081e41c0d64920b503052050040a0702c0c100c408182c0a10014100580084c0e04410319120015000303000c3d010007100c9040c03d00191814020a551003840091002000040030031201440c1482c881180d000c2c031340d181c0d0b08070748002540e8a80e80c010380108000f04000b400200b002c5802ca40000c0005407070340c4c0c071402d1003070444e072065850815055440c005a11020540c5050000d817102d030705032000690075200c0c610742d01c0307105100285110f00301c0040090281501c990581d01c0300311003e0410003d03d402d0742000c036a81c698440803083d4010070002c0c001184001401181503400002d40b0305070400409400c1c03801c8980081294820b015004040c5d24411820f00d040341011148a950110700c85644621404051805c080864400c1e00004100040d64541645415844c0500003c9a484e40e0300c507204040148091781 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 201307742 1250 201306492 201306509
    0x1809010f0509060925093f020906040915110306011103090a09020d18030e0a090501080a08090102120a02100e010b150c031303060c090509090c0d0804 66
    0x500104a11002049010696005541a00300794848004000c040707038080b60250f03000f550704101c00542e100c0580042d0025400c5040c502112030311200050510006c03000200e40d4420342ca044840c0204078107400901c21240340c0500000800c454002c00c0a40c80001d01c154095a200daa42c981001b0003a481500b103441c05840c1000690494030803c3c1c0154802c1d0b403020b0000c0c044660803040884080300729404024014002401c0d2072500301c440d03019420110003100c000703039201e103100c99044900801c51007a504ca5910403e10143c400b04000d905129500101c1c2240d103070100500c035031030001402050b840e400110150b224030b0340030f00403448c3c8030800319045c0309040042041a4601d400080c114a1462007402c140103540215901e14200c2d01607a0a50b60b210941810240258800e01e00802b1102515816070f407800d0004020400200d8483e1f01c00c848140d5114000b5211300d0b4003029450290400300c9008031070741061945c1c10350b039200085c11a40b2540445030305d241089040c604640c010401c18 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 201308992 1250 201307742 201307759
    0x206090a0e15090f0f06010e0409080d0f0c0302070321060f080606030d080c0a0f03061a09030105010801180b06010507020d50030c1203090d030603080f18 68
    0x10b41c054690182400160740c0074a80840204440342d6101800c0c6105451420100c0f005039104e4004440d11050790801c19001542c0d80d0034017001c150b80e07000624000f005070038085101b0203070603280f00c00ca1303102008000c10548140302c008006a031120404030865150607260205601c0c681c0014001c2c880c580c4100c40400101c00d000600701404290144691422401e803039490303480c5041600c2020080360701102154003000f00e00051381c01812116071b00290782c5000201c50f9211103001013030703026681e00850409004200301c081840c0900400b4003400400b4000c1c021034058400b140d07000c00b0341120080000f1010000601c0c26403041050b118030383e800a00f120042e640906029607000e03807000c85032080b040d85446500f064030040c8d9001c0c04040ca8a17000000c0380e80c0c6543c0002c14000000d071601b555000822003032051040030444500403600c0b821016540c0e05168901c60b1a25584012170f00506052117403c1000c50102d000781c440070280c800c43d0030b070381e000c2c200c0b40080030103000c0030456441030300c1c2d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 201310242 1250 201308992 201309001
    0x9060212040e181c080a020301050a0b0a02100501060c140c0a0302011b0506070c14010603020f04090203010e0a12020616020d140904060b0d0c05130302010c081306030b210a0206090a0e 81
    0x582d13442c004c40c419200c0c0b03041e6846401d000750991009000301a004104000100302c8604c0305002040042c0ca18419605403003c102181400e48000707900070000118050002014481482a0429030003d0300004007400300750500890094002c91001a040c080c00484054082d4100d18800d80140c1d48042640c006107098040505030001703019080d60101040030520450410501c41e840940360014100b41c8a000840100005130185a0003207805549904021540d2581017050818103032040302d10050f180f980542c000c0c5003510041c08440001c0c20991400b440d5500410f028012005601e811020b050020350068494424400c0d0355030064a040d600107541009000a0042c00c42c1c1c4e00c43c140030545001000312518010171400311000305c45042d04000540c09624446103440c480c0c0441801e1601c0d1404207402c411266000901190319164080810715101e800c0f48982e180d2410b1103418919070320406540c680c10740704028005d010000f0080c04d01d41e145403140c0000c00035502c0342e6505240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 201311492 1250 201310242 201310273
    0x503040e070f0306050f0d2307091a0a1203120e0607110c0d0c09200f0703020d11150c040929040203091906140103110109060212040e18 60
    0x38100b110100080c44e010000c191032415510001001030018540061041252120304022032500c8210100081d03000000094882c180982300040403400070001e00081403a8640c100e903e0158056881000000c0c0d003404a1316504420500da150103140c2000b1005148920304024808880515181d201e03070800c00c0b0006038800e41803a09140070b841030300ca0000110003800b51014080000030301e01c074007843c018002100070340e0103019904038120005c1e4071008510450340f40e540c00300b0072000405100213030003401d0640400490004411500d420307080000641d0740036440d01410006170b01c4042004001c182e9143c554000c0d28054045018108507884021031901e480d00307221340c800d031702002c054442e409a074a464401d6900c922080400b174048407401c04140d00044110001c11124940e86155001c0300203c104522400780d485454082a0740340034030005015680e45070300003021940300d0303e5142c8103409060f0503a4101e6850715050b149544545a1103401d060305000d49042910400c040a0070412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 201312742 1250 201311492 201311507
    0xd11070b1303120213050411070f2015030601030902010315091505090103020114030a021309020301061722051203042d170a030e0105040506160c120c0503040e07 71
    0x80c403070344401c03d8880310809640b00340c2c0a040014804a44c01090811042c00c0c15000380c0ca64550300c0040c18901a0b543e95003d40c5190b12000545d4416402500c40e6044400c00b43c0b5401904401c036101900e9143d0600402034602c0010601070402d80c035601c4040440e4000c0e08010021254144d55854503500d4000100040c11404140ea03862085200001030a007003183c0201d0580741c0694500c91881c0c441c24a1102d40d60000e0044100503600304810075001003405001c0c000740c9200000540c0e03079403400800905400e14040003402c041d801409000d114907401c00c0000344102460040c0407004541e083c0325040019040d203603c1088800002c010401010703443c02c00d052010980300c0d000300340707120804410003001240010007411103603080c4e071030011030324001d82208141440c0100d903072130100e181070382522400e44d000c80c0c0381d85c48242405142c151840128074610050b00e846160201c480d01c8102d820100c1c2c0304040140a030082c010720a210051003114080d011b10b00081c0400d007481140146041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 201313992 1250 201312742 201312781
    0x120a0e0f0a060e0d0e03060402091f030c031403034c0302011103120c091201140403020c06090f04050604090f0b01080601050a2607090e0a060e060603030d11070b 71
    0x44c002c2c8129198000d0040b000f03d41d003104094020700e0540c3e556800d0105083d005000810725404821501d170300b40c1c0191031201c001d9407198503114031044c51032620000390400c940580c9010f4000340100888030f090800c4c481e025204c0680440c0e45040c0e04110900105224110030000940300085501c01501603000c5e14100c0c0e201b0303600ea000140040c45280d8590040710a80c041545141c0d0104190780c210001034885000000d09980ca0702440240d09401c4512080c0654006031000302000140364040c040760411000030303154285441030701e0001924171b514918000b0301c610340d100f01180b41500c03680d0041e0103c9900c101210340100d0f003400d00040d076038002d1061305818801d00b400031172207040003015034044510700d41c03a9980b512a115206007041041c158484210302c43c00744001400141e070701800010071a80c00103000501c05509100e81912a441c14403850740e4009030901c0b840c0d80b00001284d032402941000003504d419130001c0c1d50200d205030031003d0003075441034050181d541d8075044131035040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 201315242 1250 201313992 201314021
    0xf0f0c1101140a1e0509090a05090111031e0703020c0a03180e0c03010f14060301091a030d050c010623010f0c0605040804091521050a0b010602010204050a0b120a0e0f0a06 75
    0x1a1340074640115418800c0e0b80c80d15400800b0000840d0040d14503401241d0401070443c00440c0b00640460320305040d8001311100d151258440001c84c0d003104a05c48100c0d0080a103180661a18034046842582d4410f168001000c220038001918482e03440401d5940140102c080c0e1000182442540c94620350000e00070900c0c0324001200000d000780c008200e008005101030841400c41e86428400c500410079152240500411040c003030303c16660601c01c020000600b034940c00e8444401d03982e680d0860386260841d101105282c90b1404002c07c40e403100e55003c01307007403811288404000c0310441d4000d03e90b180c0100000c0c04d117004c3c0801c11031b00c0c07400740003a078103400310402100408004405c081e100c1c0340300d03510701c4194981c010a050012407404664003402003088a01d0350800340d483c5007158100f42d10440c0140d41c003050a01c00c510701704c65504c0041640c1407a250822003405040e0203094006401400b40c1c5035600c0040440d000140301b1102523000d6007003644c3c40310701c2e90304040c0060a807480e541c0301d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 201316492 1250 201315242 201315287
    0x405060a021e030c10060f12020d060c020609010c090b0d0c140a020d081e01030201050c03130305060411010807050f1305040c090915030503040506210c0a0f0f0c1101140a 75
    0x1055285d52055030304668240d04071142c1d21f0f150100e03198244180d410140d821036105100c0001148860184c0784504075198014100c43c0740040c4800d00f11180d0030034a00c104114034400b000000280c00c20341e40c108085076000203115084000c01d648100507405001314007040407503018080c50300803071001c006040a4450101039524220b0483c0b41035540401e01000149043c01400503502c0b030009003111202c44000c43e407510744c40c0c442000c25040141d10445059000e50300f00010480900b90102000b4404e083c6209641490074001e0aa805015590002c440010420f800384019400744c0c4d03002450042c2c010001c803004035070024110f40325409903520780345c01c0c80c00914441184007403a10840e900040510309180c1803c0412045a00507441c8181001c040785040d110b07144107000c070a000e00503040019070303541c2885201a0080d80010b42c00c2040c03202d587d10020000360008151a200c6a1082c0b0114445607041c0042e01d10ba640016070030f084200104804070141d400c030042880a13032180017102c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 201317742 1250 201316492 201316513
    0x40615120507030e0a0308072a060c02370209040308150f0d0f020609030d020307030e0105091005160803070e0a0e0c04050d1509030c0204050a050c0405060a021e030c 73
    0x4040d54070b013050b1080198444162040840c0c401c00000b6004111454680c2401e0003403514061550b10342d1190032822682c014400c0c0400c9068481c5081d44102c1d80003600345070108898a10039080c00e03604d440750603002d42c5d240c440d1440304409250322060f4003c09003c0f0600b0f280c02d0007840d0390411035580043c43c0c0e0303400500100f440c0064424141810040100300031804680d1444907a174030f00c02e03040b6040001403207101002d035018007880c80355140342e900071911803c090400400b02d0480c01500c9043c0b100800c0b00840d40c0c1c84440c10410714100a0400302e90341e407c2c01503411158110804044c00e8604007009103d0340c1e9901c620300031180201141c070b01d85419203c8100e03001d80d030310a0300c400d030391600100001c009a041c4807044c0751782d10f07000e105243d80d052400c1d01c0034003d8902280301200041d15200c284030443c41e05109150704003041d01b200300300c02c1c50082c100e00028400d07409928401c610115824600e20b1080110000041500349100044100710786229500c0e0482002600d0500940d582807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 201318992 1250 201317742 201317747
    0xa02100503070f092709081801120b1305041416060909050f070e0109030c0e04031103070b180304031b080715050301120819080907081f0b040615120507 67
    0x2801903440340c600c2d078070102805d444545103d8001011380881d1a803620600302c0030403118005028082450000542c3d1800c2ca40c000400f00d0341c103260800c04982c58444215215210b940382c8103c4001d040000090ba51110304101c00400701e00040c0b9280b52090104800a001e95071951004031182910386050494849080e071050b10005c80b1131310102a64080002d0010344202d0b10000c5400c418144000c02546a4861903030640064004403104246031051004169003ea200e07001c0c02d402c50040c0d82050b07855075452a8280003d0100d00d1a0b0309442032404a40d44140122030045500c8410423120040e51820521104144d1103140d246000391640012604645003288006131a140e4070740f4a10381c01d080c0107812200c0f09900c281c2d0340d11810321402c541e0100c41c09003240610301d50b0b200d405492404100182c40d001e0660412246a0880310300a100c1c0c0c2d40c036120031600c461081c1c0010448500e0140031070001c1c40203910008814661620b58801d445d006807501800092010f002c0c440342d56000e006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 201320242 1250 201318992 201319007
    0x4020d0f06170a080313110d060b01120920040204090f0b12070303020a1704090c1d010219020909151306061d0601050304051203070203042d0b030403020a02100503070f 74
    0x26040c03c0781040002d146000080c441002188640015841e291f0018080f504a1121072400c850035540c13030169280e01d40c0c1040034902103421401c0240f000503403a540d41c0703550849901301c030802c13101a00e104c14810b03070712501600c0250407900401c001c11822034204c2d402500c4501c240034042d5142101c4540c0c0786d24085080d005694041e0001e1a08000a40e1450744c150b40d41501c00400d09410302000c500746c00b840c024140d40810903920600c0b542d0140798208050348003185034906661042e01102c0c08094446458030b50f01d03404440c127071041d582e036006c450300300350458403610321b658400f00c01c00100080311040c00d9950b5002d40d80130859140c958810700300d4081c00c44001c48200c48244000f410175841440150303800f501c68415210f0003c0c0110074401903400648034a005a080400c0500254268041c0004143d1442c400605200350a200d1065001c015004400c8161000800101458000c10584c1d2045a01904544502402007802003c61f00f044d04c0000014010038181c40c14140705186 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 201321492 1250 201320242 201320263
    0x110a08061203090d081204030c0b060108010e0a02070206040519180507020a0204090501020903010504120f050405060406032a0305040c150212030a0b09010305060a0509030f1804020d0f0617 83
    0x5520b0f080d02a810804d07150414007003185d0a100810a00d4081418040c6040c0203038403070b4035521007120321840c12282c6190020310990420150f5001000045003040c0311541040c0e60100041e03840d8641e0010501c50304c00d60700300a4018580761203025a410b80100380e1b800311180c0103055400d101c1405da1440990b10251056030069001800380800b502d000d50259950354410400180360103a80300101e425100100c6080c0e40001c41e6040c003000c4150400c4d0113a0401d8000d1603e2842c2c41c2c10580003074110b010b11702489007015500c83c1e0b03010002825901820172003021404048000d020403100034060482110102d03039407035031150005000d43e90b40c009003680482640241080a50628083e80203800091200c0c100a480d4130345500151100a04c0c140a0360244001d4a21031504c071380200150b840240011903154001c000c484110840c40041d01c085810041900c02c2c0c0c400d000b40054007900071916000501c82c505000f0348040a032591012007141c03041a046480040f07600d40c00c45c1c60380030410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 201322742 1250 201321492 201321529
    0x109060507110f121f0507030b1507020105040803191407050d03270f061401050603070f0509150a03050606090112021b1f05130c2304110a0806 63
    0xc4040c1201d18201d007207403c1d5000b000c1e001100c291400541c0070716003212000040280141c100ca40000d480403806515801100c2e404c040c4501c100600118480c40c0b410070202e200318070081341d0b61045a00c200c08840080c080035044a81350030104da100e080c00c101d40078040700415000d40b015204180202c054900854201015113100329500000b0b60107407203c002103074030701c520000c1408030310038800c08840840d0340141c0912851009c54a0031038220b03260750b80c95121030240340004110700d98a040450340c0c081c55600e0b02c641c4017515048182c80b01c1c043c3c1c012065110021481004421503440702900781080c03280c0d4148107980314201800f000e88211003910303002504804882c4c0d4550010b800034400c440c0d4001c00001e17088600c0100c42e00b0400f4480608030629030b004512100010103000d0240c10280c0c0e017080100145040d50f80d1800c080e541d105030059050304407000c0c1000a00200846060000500700707118002c02c0c0300c241d9009601c80c007150004510301c174005c640e250510b0004020f080d800c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 201323992 1250 201322742 201322763
    0x150301060e07081003080d1d01050126030d09030807030f050108031e040b0d0923060a180c03060c0909060f030201181205070518040201020a020405091204030804050109060507 77
    0x700b0100d6420800a1004264400b40704001000503000700040c08225004440020070b00714440f21504d1100d4080168500740e81044010302680400480000501d10441c0b0580c0005040000042c25800b40c000215402450003454100f41900005a140310f22495601004082546030800086403400c0c00383c02d02c150f10034000d00300c031180494a0038429000301481c040c02e040e9100c1000e40e2542c81406c05100240d141c1c039040702008118182d44618008420b40b0100f00030102000595450005114a00c0b60ba00c0c0c8000280c00194a86c1c0c420541341c00c07001c0c4480c52601c9007028800307095414110f0000900c50b000004018489120354130540300c2585038041d10500d1a001110f040210b21041f1000c000d4a89001a0388000c08560303088151145002d0114585001d0401600042c0620904011a4030302c00304030040c0e0380481c200130601c1d8111400a465190a02040d1038a940e4128070211075400040c040140801000a44210b900076664a03074425201c900c02c58a600a001d40204160303040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 201325242 1250 201323992 201324001
    0x70201020703171905090a031709030901050d09060903111618090303020c061501080f0f0604050403050405150706150803040303120213150e1f03020d180b150301060e 73
    0x1d02c0780d9003002a0392080844c4198445030001191000ea40c401050f0380240b04502c1010b800464624800105213031049661030b25180243c0c60f8800d0840840c100100001d003045008041d50029202e1a000201081110b80383d183c00381c001d000b041c08601d010312428841901600d20384400c41c090341c1483d852003941041c2c20500e2009171540d1581241456020b00c222100c002080000c24414001c0c0b10303404c060008080300141840c60082c080c04e100322204c504004001c1c041031a00c90700a1010303180066996201e00b002c0380c590003150000f0394022050020703400a4400b0380050615180560010001c600c520761140c108225103215002c02c42d007051000b0008030340a10900f00d00881c10140240c50406140c81481151100c0c1e080154650080c800c54940039501000d5500052010b0f21803100c1a25190900e103202401600740108150b000543c02141105c10b810078454003105042c0c40808000f189016441001c04407501241d041050404034080d19050007001c080381c526481b8035009864 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 201326492 1250 201325242 201325277
    0x3010503071e050315010e0a0506010801030f02180c091201051b0703090506070b0411030d21060506040e090607030216060902030c0a0803090f010c08030c0a0c06060801020d05070201020703 83
    0x70200801080c0588940303002843d5282400756081c42402400b41901c50344c140740c150804840058a000c0c031807841d1008029a90f41c0140d440c50640b80c021030a841c403501e1f54400618400701081d003181c00d82007054140034440504030080c0c0050300c41115544c3c0e003a40c8a841480c03c980040b2216010382e0160700210503c14440c40040007100c0c064600a8211034940011461680c440a001c458180c42c00c400c0005100070900385a484441c22006051a0704040e600180050040041c400301c2080c0d0800c2c81205402030790200c0000c0002030f2147d0344683d9920600d000c000c00480c0c50107000d0003002c0002e03000c10f20910880d00d00031000080402001815119039000b004912808c82e0035100340d00c07440540340c0e030700708401d001020410000c568405108043c081c2c194120007409050000e269005800900c19a09417984168000d0340c07582c0702c40f00e02c801202d0348040340d000030340344a107460701c080741802064008242900c10214240031a444d44e100403801c0744a800ca001d070006520805040e900314 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 201327742 1250 201326492 201326519
    0x501020a0515130b01030b04060e0d0807030c050c0703080c010506030d09031101200c100e0307290c0601080106140f090a291003050912090d15051b0301050307 70
    0x640340c00701250f050815903074906141ea401c3e041910013041d40d404000410605020380341ca01400078001d07068204015a01505240000c0d141380d040c141c8600c1c80e00f160703a20440c1556090048c4030301f1580c41030707501d082003052984800e0101200c0e5080800048081c2000140f91034002d07059500c0d6885030f8070715210403001c1090300b07100034108548c0441c80c443d40003182980c0600421070030050580b0540500401c03a04c1d00390195220140010207841e041596004140c280c00c5507000403804203401e0380b0300c41c035160031030314030300340114500b80072070301440180000030031034140e6083c40c00800651342c80d80c26040340561144401540046070b001000c040e800c0151549030480002d020105081c0e154441d5402d002c4c100c0c0b519403400b120482d5419085260825084100700d105090400113414041003860322807660202c0a41d220034001b80320761140c2c0305c5004420020b84c101c28050400c40c1c6003161034004c1d0a040d2400c02c607510000c0c1c00c8000c0940040c0450b8101d9100a0040002078600481c246084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 201328992 1250 201327742 201327751
    0x120c0f0301060c0503191805030f100e150705030709060315060c0f0b0a0b03060f0c1608120a0f0c030b010806010e0109030c1508090a1707080d06060e0a0501020a0515 73
    0x90205011124609140310016611007606884141e03a207003001c0a10a0403a4070380e445527110b540030300e544924841020030070302d180085541c00410440d08404140c2c1c0780c48981126590690100c03c204008598000d01550080985544e2200443e40d038010440c00d884c00903003500c015003100c8000300f100c07e00907007464408a2040907100311140d0b15483c3d580000c1411200340300c1264540f0f801c5180c601e400d029055000c03800c007450115504151440c0c1e43c050141c20803900508690340d0031071050110b5201501c0c0c0401d038004903001280307440d405880140c0700300c04002000c40d08100d04c0300301e00360107405483d40d191f5060b55040115920a001104d2000c5c51880c168140054844044041041c1110314000340c2a100c107800304000c10303840010a4110300600480ca541c000101070000200e440d048007003d00041052a5140e44490034139510324402c0d240d0b0403030440d00d011400034556030403080c801ca016208541951615030ba070001682c03a0540603d005089070810040443c0d0b40001500d80c6401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 201330242 1250 201328992 201329003
    0x501050306010e190507030e0c0603040809100210050405010c11030306010c1b0308040e06030601270903030b06120105030f03040807090f0b0901080a1b060509120120120c0f0301060c 80
    0x40c20a0791190008640d001d403558030002e072302c400c000b000350401009109110001554550325510702915021341074022001014401c00f019410403045510800c4865824480140c040010341000d2070402e00030310b2511120170105502c5070203203030103403c0842580d22440060319450200b8a840c0c2c2c409002e021083c5000c1d042400442c030100110700d098002d0405000301900e28982802c0a0080610b05003050340303c000c0f41e038180140a8910070042c0c0d0088040c80c99080c000c555400e1a01c2d050740503180102e00160088d07400f00e980c1328902041800c0904860054041d18101640c20380581d8a903c10f41c01900219400100300700128029980400c01543c92203d000898001080c0098410341080e4045021580402010b01c01e00c001c187d0310320074200628410100b6145007440c050034030302403482a20301ca00030213000c02c1c41000c2c0a41081d0350030f04024010641d00000748a040c0b0642d003010400c20380301086480091007144050049a103541c2d09014000d08583ca0803204441040101208948 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 201331492 1250 201330242 201330271
    0x190201061203050304111c030503190f02070201090b13030b040f05030703050c0c0a0e01051c060e030d0b03010603050604081c11090f0a15031503080f1306030501050306010e 76
    0x3200c800001c040740c101c0c0e01c680c1d18540e40c4e04050800610740c0046070304185c840c041d00f282c94541c0b200c7c2c0102d00e031056540f6090690704c03541c55448000f0722404c0d55511821187c200b02c2d400700c0503000c0e9401000c0b15803003600c6440c046500d030a000c003920300030307000c1ca8034180329590b43c1400411400d9280d254014030565110b10328800f40d546035406c682021034120081100490b58902c00f00d000d0001241e480011381c0c0d2250114600360445402040c1032243c94092681d0030600c0c0316070050003250403101c80d003000013403005440786000c25940394000100c0e030901030328284142102307103018001d040480350000c009211544032603c3c1c0320742c2030340016224141041410b280d1055982c1e10700408000c1c181401d1040d0f1541c94010070f000100766151042880780d01d100c40140024291180d500d0429080c0c1d1a00280c950f444800002c40e045403034001070b090000100c0c014860504050081500c1c40f0302181c803090707440e51214158182c030400e01600d0350603088000144000d15400c044141e00c01c1c140608000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 201332742 1250 201331492 201331499
    0x903110d171504091506050901060507020102030316271802070209011a1b010c111f0f02040909121e0801120f120e0907020f100b0406050907030501030b060a080319020106 75
    0x81c00e030403103505e0701c0703013512000104046d180002c01c15004141d40c3c1005480c04c901d65000035241c0c44000d0101c0009002400c130030300858410b000da44025001c1c00150000160107100d102550b40c1d44e88128034080400c18050280d00b8400d0098481940c0c0c060a20000ea03401e01801003098500444014403c0409203c1e41c012800016010181510b99000019800c542180002c00c0e503400d40078866965401441300030701c020803280141071036210304117002443c2d21071200380c0c0b0068815030b48000e039400d041c5490341c001d2000b962a18460542d09454a0b11524041000040c1c466840303031081000c40c5801004210036140c03050480e5610384140003c00060015664100104611040c00000103445419043c0300341010725103180c201265000070016482040d032200d40c1c2d6009122850002a01d811402e040c1b6262504403402409004101c04a40e240c1480000d0003007000344401e44401c00701c10080784850500d514801d00b030311980e00c09940b0345241902c0704c40456640c1c481344d05c11517580317000c0007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 201333992 1250 201332742 201332753
    0x30a02030912240103120c02031902010e06040305030310091506030209010504051807080c090307260d081b040e06042004080115080c2808010903110d17150409 70
    0x1403009543c1c03000c68250703035411402c0c200d01c0d1408135558070040c08000d09254000d40e0300040c45488600030312201c103180a4291004035003051200c10015003000300413030007008020020003d18810305107000240013541d03441781c00d074095411103040002c0c10420700c03809100985c4260002d2401c540d0604140e4501b5a0341d001081c0c10004580e55141500c1c1c0c40d200340440d050b403200c606a08100d401683d50704200da10340000b0f85412081c80340c070b07664450612481c5c071200500520030004090210659a5120358004060301040c1c04840f6403409140401e09451800901001d42d000d45442001544481c1d40314400d0100030300c0340000142151200560f281040040b0500520241031550004100907507030054980d0305003201c1d084504660410401d01a058035800c0c204422080c60382c044100d45041500c13009400010f6411429065003048240700c10b1540180454030040c040b0070445c0d0000b11400c0044036503000c000c29a141401048002c10340002c0040c109610800005000065200c0280e42d072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 201335242 1250 201333992 201334033
    0x1401060b0409060503150903040b09271e2203120e0d030e03160605220c0510030e0705100203210901200706091707030804060509030a02030912 63
    0x94103110b0b140d03c010701440c1018406100345403003007000320781c3c14244a681c094032800b60307000c0c1005202c00490b1001c45942c92902807140c1c00145400414038020341c880500d40c510301222500b44815082c071100d032081c020032800612030300900c42e00041940380882d00100103030904c2425002c04c041c3c40c6c0950035501c0e84c0e218009200e400385004003207030002980e0280969441c80c200c20001e800620122401c402c06842041e06903030710030400107456440c820490343e08801400112100c98442c2601000c22042c02d0a00d016a4000c40c2c03042d214407c281412400c6d00c009000c0326007503810a1808112508051b180380c440200c0340c1c01640d003026103080249601900346041489801c1d5124103100f20b2010a229400d40f6500c000d00d03000e080b1341c06203400e500354072814030010f0006a4452868040c00724521a00b18030a1402c21480e590310305505006146150643d81074407014274010201e0303c07100c80002240e400c44155000f031810040384008000039a0400c00c150849801102e8030400f20a03201103c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 201336492 1250 201335242 201335249
    0x6140f0d090f0515070210060803070605060d08030f0601122a031d01060312030c020307031b060207080d0525030e0c03010e0d030c020c06040b09040608030c10180f1401060b04 77
    0x38540c3d038520304005c00911708258000d004070038a01d0260240704489021045410b2960460408607a42e10b80d4400314114298280001c1c000308008810301428450ba2a100e0303005140903650f400095046454400c00c59010300e03110310b8074100300e0a20014000040e0814003400040e42400030b854006941000384000c58200d040f40c4c60f0350748000600800c80d195218406042c003d01c6c0c10804a01c18040c00380d500c0c4078070040a81403150011111141e4a0f00d241c040010300e502100a6440302110701d48429140c021f0000e008907141050000707402070fa0581d58804c3c80d0f0719080b00c605c5a01e49a110164024240408658114003620980103d01c6e1424000c44c003041c1c010300000c04a003900044000c08139030410200c507003150401e00190a950b52100c056609030340c0d05062469685081c940007c00800c3c160744081c2036030001041d6903880d090042421880307450f80520a0110f01454074002c5029810004e000f041500f25001c00c8020650103d0306800002c10b0320b00001f905521080b5488503504940d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 201337742 1250 201336492 201336523
    0x2040f180209010803040303090b0309101118030a030504060507020d02030607261b090103090f0303020c0d02031603050c0a0c03061a1e040b131506140f0d090f05 71
    0x14200421818480210350050401d03001450400d03040d90f50044c0701008510034962b80480100200714180c43c10701901109141030a8200081c405039900030100703401000705140582040341d042c0c04039040120711442c00c11741c1955442c0c5401c0c1040f80071344490304403240981c3c00c425445181c4005850410400b4052040740d1100c041c0a1030b0341140b2016000c0c004e1840c59032400007030910040708908903134541410a81102a601c0385044030049000f003e05800240206000e80f03001414103400d94000c00c0403c0c1140107590003000205016603603441114050300240c1e20423900311000ca8400c00c0548101170100080c0d03002e1010640b1001510240c6400c141c9445036240c1d100008803204042c4e2120500f0155104043e01d80c99614000349401040c100c01c0c0038942303403242c0300c069540c1c4500c1101c0365461110208800f41c4002c509040008550042c0d80200350300740c18240e42400280151000040c030000554603050a004c1d402c0007816902c0001ca880901d070101c1c000018a007030010060112410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 201338992 1250 201337742 201337781
    0x120b041404201e030105130f0f020d050d0f020c10020a14010e1b01020d0e010c02040e01020906041712040f120201090b0706150b160809030705030a0308010311091003020d02040f 78
    0x100105801c465002e04242a0020404400c00012321500c003046c1c0d01e03a800c0f6a440d16403006078008640c007011110401403440c0542d2800900c3d0035041403204ac1d03d45415070841d21403032a140c00303000c42d40d83c18070490000360b444010580c0000d0349031482c40fa9110192800401c2d10440700c8016481d1054061840d40c1c611108550144596410810703184608001e10300080c4030143c01700040c010010049000c4d0046ea1203002241c1c5c0f4450035011924113010181507a40c1c0d407030350340b90a042c080841c00d01500a6004425030000451302c450b0070750f004c0d5804101c404081d079103400c001402c1c010301d040d0200d06100c401e03040024030a4812014107042c0d8050708007c180180305c540701d200036414580180d030411105001400c06811551540d024065002d80f00c1d42c1c0d500600c13000603290003120303400242d040c81848000d0f420940c0c00b060040c102c0f48180c04100c0d049030b5510811841c1c600442d018200500098400c102614220384140b040b2800580002441100060060140e50070326200480300c0c03544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 201340242 1250 201338992 201339049
    0x303030b03010506090f0a0902120c1809120a03060902030a06090b01020604150f0605060301060906020609060103050c1c0f05071505190e06040801020a120b04140420 73
    0x6008616100c1001c4000b04154a05000024020302d03018116080450341000050b03901300d1907510601c500ca4000f020f200558120501d20b0784c0d522524481907020b02c08028403204c044403002e184a00601d61480600703414080b105d4a03030340300c1d08440662010181c4640c0f000a00d12424030086000c2c04e403212021404031b040c0346907802034a00b42c4c07180c181150b01c8101004007081c602c100c00c600c14445210089003035020303418000b011f8038030341e000039501c80300000001030502e4111851004a0b102a000c1e280c0f01da4a8081307035070321082d00b484098070b20f03000301500034140d1502207002c01c01ca50011140820b00352141d2240302040c541200d04079070503800303840d003405209240c0140740900c00c400e1134454a0f0441448151202442e641c40f81d2007440810342c0c64a8881d0307100b03810b490240503000002c64031850b407c0c00080900714224000c00909140c8044100b02d401c00d0300071b00b807068030340c81c8100e01c990f20795582c3c10000c040000104807807031415a95284003940c498030000078804480d402c1001c030b15032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 201341492 1250 201340242 201340247
    0xc0b010e0412111f0204030c090b1f0c0803180123240d020607080a09030605061c150b041416111c1404031a06150409110f0301060503010303 62
    0x7801208909200030070fa45890034203030000d24541108807500280d5813080f05040014040d0040d0b810051001d0310310480030440110b01c1d4001414068200c6007003810500d6094181103106200f1038860019064030300300d070f0200b0403160080d038200100364451095152103024040c216000010b002c200c15070301c44002599038001020054108a001c00728040f02d0000d030076501344807035903140300038000c60f5985801c03810f5542e02d06c280d554030b0790003040540c0d4134458520002e0038820140021a100761801c804520300e8204034043c03005010038081e0b40891404940c5a41c04642c1d141440070400c1e07030319000c450b0000c6d01c590091121045c4108500001d03030601411041d400d0145080200c02c01c540701100f54541007000a1070001d0501700007000341c1e02040700108541d800f084483c600d81c80440042c00000b000413045444800c08200e035041e4020740c54070801c001c0c1c1d101d005062111401d00c11b003c1032004440603801248140c540f0040301d8684890864036554941090703000b0804140084010800d058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 201342742 1250 201341492 201341513
    0x7032106120212010501080307060e0c061b0714010f05030928060f02031015020c0d0c08011a0a140f1e0909240a020c010e030306100302030f070c030c0b010e04 70
    0x25200900c403c3d8140001c0a50328082d03050040c01035505c8840c2c8200005d070334860140280c602510242d078030700e19180b480c1c000c84803880040c607540c07107003880004141c0c580c6c2c1c0c5203421240059448808180f40340740100c441e82c0014011110310f00a004d0144462180b80d09540404403500c1c030303c54410a000d0070241d0858000002411181d401042003049600340860794806440303503054107120314010792030224a854070a10109030408807008080d814441c2c1103942c00b0844880000a020503414030980588400020003e69048404208140500d0440440c0041e650401900d00041d8a543d20001080c0704111a0307421600102c4110040d124200700f00100c1d0f116540780020234844143c1611403a8140e03c03600360040e0b4071011008181c94200c1c5030111103a00300184001d03c207015481307421a0b100c3e402070390300c103109048519502519074064025280b1130259445482da05a450440644101d40c21400403010081281000302c00200e10480260180041e00c002c20700c5e501e0945002d03807081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 201343992 1250 201342742 201342769
    0xe0607090503010e0606190902030702010609470913021503010303050a03020901111609060f0e0109230106030603051002040803161103010906230c070321061202 71
    0x1c0e41030031084002a4000503400d034001100340d800c7d4403041c1c1164440c880840440d0815410940004280141190305401150035120304440170000c048031402080c0b60020391100d1080d0108624403980e14104611002142440508907680100ca101c00300050010004468240712003401d1000c5406504024415000025a07060441e1455055850242150040180a20401d900091080c031030340d02c20100c680b00c1c1690017007141c40e400d0141c0c200030444070050242c1400103250140000c1c1e40100301141c0c5080301c2da03401e01205180d080208410182c000f050300e50803080d200342040a400e42d2903861f06030080a569400080490440c9080b41c14400440805a8035a006010600c440200801140c81c440704003111707280030010318601101807030b0401d0349095055190180c0c0109015440e00480d820321100442580c04001ea081c0101500000b9104030540e00c0062080c8000240201c01c0e08041d03440011014408281000a030001e8600541100c0030000c180c051080c1141400041e41450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 201345242 1250 201343992 201343999
    0xe2e05010e13060203130c080102031803090f01030b04180c03030f140901081e0109022d040308030406110f070b0f040b060d26090111010c14070203010b040e06070905 73
    0x101d0401d10381c035510595035800043c021507800000b10f9285d00c4001504003005505c00f6211907132541d2200114003d400855029150700000303811240c0e0144080100d89190740700404d409415126880111b00510184010b02e400c140e0b948040130f03034400f16848000d004c1e480f40b4000c01c41d050851400800e024410400c060500644021030344040d442041520802182842c183c030782c603a501240107541101a880c08040703000781500108130301c080c5400038001031480751041526200c80c40c044080c481c3d40c201c2d20084080c8240000d200180307140f8006c54005006200101e440c104009002c8003540c8000fa110700c09040000d8514100040c0705007199109102000418803481c00c2c0d101c2d581c00d40c4006000d80e124205104015081040340c28820100898282401105201203a0301d00480c1e440a04490b011641c0101d1100310080c1c14005c190481c07006c1d684140c2095031100b83c422094108440c101d90654840719140c4a60310f8a03c075122a40201200400250420380e002600041998014902 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 201346492 1250 201345242 201345269
    0x3270512031308070f0b0c0c090a06140316090b060c0706020a02130b15090613030b04020906030604050d050a09050301050405070e16081b120108210a0e01030e2e0501 73
    0x25030a50203644004655400840035610280040300904100c000a8034550011103a01402b10304031560740001d00765049075200c2d603902c6d0070100805545088102811151041386c0300d0900510b102a0040010200c5c00b9014509184951311040e08040340d03a005900142c4c40b01d40010254540f0303180c85008030304201c400b00b200c03560300e0002c50100c001d0f0841d00c00006000041c800c04c0790f01d4039000c8500701101d524103051401d0300c901e4031205c0c01c0303001e83d403ea104000d0000420360070b15010403000d010300d90050040c182c00b46010400c0d9100d402080c558028803540d80c81c00500c1e62805c0c051a48124443c001074500e0741d040440c101b142c10009000c00220041101d0000c05090308008800e81080c580700341400c151005551064079442014159200101c1e85c400005000c2c100040c80f82ca1031010140d8204002c0000390701078501d02400d40040006007040d0040442075002c1e0344104054001d01c0140c4542c0c0c605000e0700400c3c00c0d1845005426078103844106c3e80407004a1268502500a108600a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 201347742 1250 201346492 201346499
    0x1c05090609100905120619020c03030406050613020406081b04060f030207080702030d08070e01051215040906020f0703120213030215070b01150e04090327051203130807 74
    0x81840c000d40125a00510540b6584030301a801010072070010a0014400c103100c0005c1d000b6503485a00a403001e55901849400c49516141c4500950311007150940046003142d40703944401001e0240601904d030400303a111a400445222400288054602c0741c60b0015103007040d0944090540740a03a031012400720034030091001640c49100078418142e94503000d0b07110659414000f500b8452080c00a40c50700c150401032242681200c0007901c12100740e151590800031020064415200e8000c1204d01500d00c0e00014003008008200310450780c0303000c1c0c40016048103982d039030822a07202c441340d095101e1011425404040c1c0c41411540000c040306000d41c180003c8070305021710b400381400000e103d5074018020700c10f03034001c0c8020b42310142d030000d0003090f541d6518080090001c2045421100280560300944400d052a0281d02c0c502079241d0758484500581d4004101c4861100c201111140e500100006071036030740103015003540840401a5a80705034001c5215980c070001d80c0015800c2d0441841003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 201348992 1250 201347742 201347749
    0x110f0604170904060801020d1e0501030b01090c021005240303040f0504051e04060207020f1804080309030c01060e01080706080f1501030207060207200409110d03020a050304081c0509 80
    0x1041290003001420b440b292490009005841c0a4205081e07a620216803010301e00c81903003113200ea80d60900343c0782079040e501d50559400c0d41e809001c007801030052100100b04003c0c4a52107a0f940e07500610554051543c41c585020035250305440106208402a039070b4252450010b440041d00c0204400a501d49032408500f03c602c4420713481a01e1046507918005960f004000c40b1700403070009881c001382c5036031406142100081d0058542a4050f070000340c031b03903c03040c10041c44106c0d449000581001855036280e403076145907400100702c0e920303d010070b00030461503103000d01448024004c601c50012443d03061621040c684281c0350301c03000030001144c042c0302d01881e2003021942c10800c00070b009548015207000580181c800c1010080c8480d100281302e00900154001300d2602081982c0d000301c05031000b004020585030303d26400303015540c03000d04158040c44c00842c3c95044504ca0700540c0d00011b02a207400e82960025405120385411004c004082c8504410502d0f07540030640c1001c078100b05816011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 201350242 1250 201348992 201349013
    0x171906050d0b1311060a050c01050606040506070f1509060603020906010e01170a020f03070201150e0903091909020f030a061e0b1b01050c0a0e090402010e10030209040903110f0604 79
    0x2022403800c0003c002600707000e0181c00c1d24185010103090165100c841c444014019840040c228000e0751030b00d030201d1024070f4800216801c58000425090400105480714110240c1c1c12204480807158146150111032503070107021100c6005d0000000d4192540c01800b800c03d000410290410003c0b802c0c181d450781e000410445080112901c40c0703915900c00303103060f00a20808204800706c10001c000c01000c00e80c1504008501a803211010b0040c1c2d540f0f82004040c24002e5800581641084c440082241859036900040d4038000b000c0c00609551200302e00100e9001e00500c6004020000c10000054014041e0a008110380081e03810b5040100e40c281143c0556402801e00200e400940d500c43d4062034000100b54041141c0204418144000c04c442160711a500c058042249201d0021440c60b1040d1150700c640d030180c4075036210301c00c0b0800700003ea10080c445481813f81c24000e03100680c0b00ca11480300910322a482c3e0540c452012001c0510304000f04a100c25554090810480000c602c100c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 201351492 1250 201350242 201350251
    0x905060a0806010e070212040f1508150f040603060203040609140613020f1f090602070f05090a090305040905010e060f040902010e0405070306030203030708190207080a12171906050d0b 81
    0xd601300562103110049040c000301108500c0b10039400f0801185805000d100389045442a0403880200c414620007601c03550000c0b96003415680c401c3e074290003035041c51500d0040c002801031000817184d032079941e100c1c126001500c054582d01d50320300c2e0203010003041d038000413034440040004110038500141c030413a4998001c1802070044816641d500c5c0181c8408001c442902c0700d074001c41e1185076240000500e11540e074482c8900520801200150407100a00d607507040d1200948140d100c1d0340c490405202400300c82c6c000b202041300401002820fa2568429940030b0a401d0620b184241001010080d4010b581500140b0503480c3c4946200182e070071290324500448152400f04480c1c0d0340c0c41c001d0700104403551000e90180030010345a0708010b5503000a081050098403101d0444a210204a9503036000d4002d444180c0e20a944d910085401c8030710304071465000d0b00d410164a461002e5040582c0001e40d00180e9003403040c03408443c07640315030040740e02902c421303900003141c051030740c032220f1880c030000d071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 201352742 1250 201351492 201351509
    0x20307050712140d03051f03020120030f0a121d06070c080417060a050a060303050a03021e0403080706050702030f070809040207050a0309170706120b0a030c08070905060a080601 78
    0x81240d0070007070102241c801c0c1881e010144c8030040000e041c040d010f00f6048824855150020742000088110b414038003044d40e030117940b54504444030700004241e00c8200c40f040070561106014a941203040c2c0002010f140c0c4a550b9411452002c290200080c0c07007082940407001d900d00070084448120001d0010340c410ba80345400c80c1c44501900385200e0611490708000100e55012805004200e000102c16000c0c40e5506020071007507542c84100400c80342e4600004000a400b0041002058440d402400744048005080d05040303101d016080507551150348100c510300d4003c035154050081034801e05910a1aa00142d0b29100340c03248440d510b4843c05000400c0c80303002092204198556506480c260355100c4200c848114160a01500d00c4d401403003400c030700d40130900084010a00c0400c1314030854203d034591031840100d4400d4000507007010340016410003c4404004040b42d80018900f00411111001d00809400d01b600c0314207555000388003d0003200802420050500c000821a04550021 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 201353992 1250 201352742 201352769
    0xb010b03151011010204080102120117251520120301091802030102180901060915050705190b0a060618050405190609050f07030b030703020906150d14070203070507 72
    0x80006490b030882c00d50f5000c0056102080c0441c1c403d0056000300300b002d002c11600015030380d0740c080d50f220b4414012409041c0c1d80100c408007200410b1120410900100d003c0d100c1d030340035218544038030075a6001c101000020f4402c402c0010b0200c50700d140b6100c0d8036070715000e8420070324540d040040c544018860700c58a650b4401c110261072510000c0d092817030307500030001c1d560b4280306040e503440041da51707481c188144010000052968007460000c8101c0700c11440382022080b00301001e4030b642d0400d81c402d43c1c1c64010303209800c044003400c00e24981907500c103980041d0075082541c041d404a40181c0c120b0804e0003000034014050034800300d0043e04440c0100c80101d101c1d07075464400c940d85e910740c150010000d0708240001c201d130000ca41160307100d40029000058140d81d210740071030560701c0002070540c15820069040c005410002455940220054030180051685045c42c00041e0b11204005240c00c2c0c0d80d00c003092020f40d04081c603607040300c01880198145480c2e41c6400341c0781e446034410603034280e024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 201355242 1250 201353992 201354019
    0x50114070e0a060e040e010e010506040c1707050715021903050a0c02070e0901060f170d03020301050603040f0c0512100e070e240a12030201060504051314030904090f0b010b0315 78
    0x4036080b846e00c00c69510300138840c54548402c0c00b406003605640807445642410b601c0c0c20424800e03d04201406001d0080405035210100c0983c2d099106850a940c4003030944100711200829000500075552503010f001642a120b00d030080c02c03154060b0a0038122810710903c00d88480d4002a85002d8070307030b0781000140c183c4409128a0042c015903004114030420f454001605020314441c42c00d0041d086401d03995005100a011400c0784000d0154aa004400b0310100e00413a41c400a0801d02700d1160500d00b03242611070000030301e44030302e0220540480c0c5c8416201001523841d40650304440300c0e220000c01c1e805040a40d0f160070b030704009140c0c6c0c641d007044007060320341c024102c0112070a1440c09042e4407040c0307889082403074100f4100901500903600306600000d040c2498460b40c0c1c0720300a403030289000c00100d9550115411071903164086d0074401400155004d54952051840a030302c0742c41054074141036843c1041d20404164402c100c9814140700f001003602c074007529205c000000f1201103058220 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 201356492 1250 201355242 201355249
    0x3070905041d070803040609210809010201090507090b041a0d03081b070b09010b0a0b0a0c030c06051810020c0c010e0d140d021618020a0c050604050114070e0a060e 72
    0x20440303420070240c0324550002540300800b0005209491f039941c0d07503d0000c1d0303d0b04a400d80c12800f9040510300003042005200111316001c0180246100502c00403554180d5611a40c1ca00a02500403070382c4c1a41e2500074192a1502e0710030b0818000954490460003490040002c0086204003c00703001e001c000c0c000900008814a402803d4a42001545071101070301e08015001003000c03200076601d58a802e00c10345807480c002038902c003200e40d88250180b42c4416024105e642c5500881d08600740804c6090003c0001d0340c41c09001d00c181000040d400005480042d0380b49000c0c1e108220170303000c6104002e144071081b408194491642428249407090001d400d0100b15500010354000e4841d864035400c0014051000c40c003606d00420301e03802c0b80c2c120303200c01c410711051500c1d03413145482e0340c10740090196030625650064040042c0b03a080540d070022407529514240041120102c49695442096401096002c03040e1500050149480108078a0f00c6012450b408013a001e4031092100c81c4400fa0420b55 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 201357742 1250 201356492 201356531
    0xc0706050115080106081006030f11040b0a1e05031f051c0c060e1e01030908071a0a020405090a051b04060309050601050301020a050406030b030109080f070209010b0307090504 77
    0x1a40040200165a901c1a07128050324800c1010400100c14800021791180318011031802100170480e16118549001400e8004005140c00300c5c000c103445280d00161044c018000d0310081c0500c2a0080c6d403524001c000810b5000840361222403014020151400254001c007900d60102d00b0001c00c03080d0360b0302052540c09101e541da00544e030244400e0964070840700d500070040074480c828000000e82a49414040c0e40c5480015000c5410805614145a0f45901494451501c0106040002d02c0781d403c0e4488203141c0d4084001628030030f444141c407048802d9152000743d80540010011030070310f4103020001d810f2810180035010341300c1e241c4020400400140842d650340150005000342e48940c2c0f0440500a030443c1c440a503120f006c1da1000003404d040c103000300c0313103000107079a1110b01e03040c2010350950060448070320300b540640d0f0b10814070f400140143c00400b244e030b001050194940040b40704002142405800204014800f0300c24170004642112109040e00c3c0b0890340170504030114807041c000720 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 201358992 1250 201357742 201357757
    0x3030f180809030d0905011b06090506102d090e0c0a082d1e12120f09070303091a0f030c031915050d0812090706030b01030504020f06030c 61
    0x94000304003000c001d514001450b0400c1c1c19001d85010010402e03040d600907209224150200d0b00001c07203101d01602a404000b92944281800981c1c080d1036100c0b41d29156017102d200c1d00d55064103100b440352280c202c03901e5000d24407001d0068645e068520003090000303828070446001d00c6c0c40d680d007c0480c803018030a0400a45003d00003000c01c07a51420482d5845541c861407a40d1030002071584800d000000d081c0b41e030600420700062042043d04030300a298504200b00a11840c042c001d035494168040ba0001c00c00070121080400d40c50500d11141310008a01511030911395000f00010400a40c118040004030f6030040c1a02d40031000a90516149104201c040b1078104000803c01640740c5556002d14010413250f080030445510035100401150b03109000c004046c0f542d200d080080d80341003043c3d5071540e403041203450704155004408440003042900c0c1d18a10b40c000d200248030495141c41209400802481e09121a06054000ca20700881385d41840b40184c200000040094081c1421038251 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201360242 1250 201358992 201359021
    0x1003020d0c0509040c0207120212030f07030503040b060d0f0b0714070506100b130308030c070f05070312020102120f0702070e10031106040308220f060e10020d020a03030f 75
    0x10103210100030265405440c1a900c84ca14109900c42d580b40f00160200c16510920940e680da001550200581c001c030315180140c10b03210030880d402003801d040c005820b04501c01e0301c94a0302ca040074a051001c000b0000c0c801e50244959444803000b10340000c1007824556004450444030743c640b588112501c407a070500b00f100c100d800080510411000060703091182c46a184213814007502ca06000341e4a10903482c40c034144011001c82403001c00e074000025600031403102e01a030700e0030a43d96620f80100010140542d120b80003a0000c00c1802401b05440707052200a01c02185009100b02c00c041e01d02d20041d104068091030140000d48143c002c20200d80900a6880c8441d0245000010b20031000301a02044517020604091088903003003a4007914152907000d0f998a00749441c52824010b00e40b40320014000030204244000b50003410001900090b207181d6460700014045042844002240341c1001801c41d4400b11b410310102c1d80c00b18617140300c01d82c140341c00304241c1c80040301d10000c0e16445880402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201361492 1250 201360242 201360251
    0x61703031303020c0a17010e030408030f0c0a140c0108160f0e0a0308040e0106110102120f1b0a02010b090f04050a0b040312020d020406120b010801090f1b030509061b091003020d 78
    0x40d501c4881b0707942034401305034000070300082a0181615840307008a10590780285d01c140580402801c40c08007401c440c640c9441120a40c81460320385640c3c0c4030100764211000c3d00400f01003482564041d4407a80e02039400d24022200b041c1540004100310500c803010303010003050b513100250540d140d5941070002d64118a0307040e140c0c1d40b200704000560000f032040001081e56040c11001c81d00d01802a220b03038801d003c00a92948e0755250380b854002100038140d615600c08040c010b40a20f600502400b01e811a541c00015031011000900c4523a4201070403003141018400c082000150300003600c08000340d800a00e071605600e892074107684a60203a02d11146007400803600c00410348441e405001110850707644c2008403084201c801045a0100c180309000601c000010f10407482503030804142000f0926000070342c1c0383c4040c401030b1700c094013000c2d0500194851050080d0603108000c1d1303641100d2494440d00e807489100c3d40081c064850b07805002d01840800340c0d075001e0b90340207506495085031844802d10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201362742 1250 201361492 201361499
    0x20a091508070f03051506121e0c010e030c0111030705010212040213091203020306030c0a0e010f0b040e041203061706040203010501060215060f061c020904061703031303020c0a 78
    0x4196105900500d1920b11907018005007081e041c000340c00499420201800395100480000084003100620301c0380c200200c0c4d14100d083d14410044800700d03444d8510003006054541114600304401c0c0140300d03040148182c420703081503a000c02c0c488100342d07007400c0c40390340300c111b01054a00350b0081d0303040900154408140c5045843c00044803501c00c9208644030b80700100b49010281c01c0b206d403540040c0c00221009030f0890414001c0e80159005440142151860b42c040d00000e000c82e801a007144501c3d81029004001804104041002511070094860700b0182840c000442003100108040c050071a04400d01039914001d6109030007410785134080b040b2107503540394155600d4205480c100c0c0250b00c1c02c8000a225403003c00c80c00c40c10b090401007000c803a1101c1d000c00c1811402e1101a42c0d10690030807101200403096404d126091010980258441c180384003003100b260625444001c40590400100b03580030310110032684d1111042969030803030748030340c01c0c124541015802c895401c00380407030b0b021 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201363992 1250 201362742 201362771
    0x1119030b091305010c08070206070c140111040503010c0e030a060f060b0d0e0c010e010c0311010e06010807060e06070206160c0312110106090c17071e0c0515060f0d020a09 75
    0x7041030901a60081c04840d05c81c4c0004c4a40020449803540160007000c0480d001c40e100e00305000209002c0c4100441022082c500107085952852030016070740c00c00141007043d81000e0044030210412070910010020480740401c2e21960610001400b80795100b800303040841c150340c401006440310806041d210300030040003000615481103c00d04500c10b4101a00d490340c0308070301d00f01328100180e64081d003402c075590302030300c1c180c0b80039804036425501d4048040030703000204500d5009012a0006002070361600d200500641800816203003d2102040003030b0141e01c0c1c540407220f440002460940c0d4008c03141c2042c0d044213045800051401200056060201d548401004045484103008100b150780d6071090000b2241101d44d008003103410a40c80c440f00b24141002d03603901504508044480340c50502c40103408100d40c102e204003281401c8040307024091700300981ca5020404150080c124100200041e542c5400e50000394402c0e800b440e890411500c41d50310500003006e014506000880001485 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201365242 1250 201363992 201364021
    0x121050a0809011206211a0f0f0c041a030406290a0905010807050d031707020307140c0f041d1608150103080f070c03080d090302060603011119030b09 66
    0x1a0000d00c026004180c184e001c0d00c01d90701100c40c00100031102110411405003c6001840c00341c03207002940b1101c207000004920010312607030415096040c1d80c078222a001030600d02c0a003031400040402e0105000c41c0e42c00e0303003261807040901e2004940703e0f41c0c3d510340400079200011800e121482031004880840030f0300c120b0070000320b02c1200ca508405895071040c0080360b100b40714101d0315a0207100208030505041c1132250715580a454241c0190840091b19100007006030743c41c1c40141d02c00518003090021114184804550082c0980068648a00001c1100303808551380c500c41d694a20040e0442d800640002017800c0548059843e40714035000c40c400303044410f03c14240d19000d40d00d83c0015040d0070301d0b10395060340e0380f0041c801d0500c009442005556007082c0e0084880a414aa010000c6038905014080c021704c8c62101194502191800900307043d00500004d0007a81401245116070214206659204900410880715250b45140807409046407617092a00801c0c51b0051205411003004d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201366492 1250 201365242 201365257
    0x30d020c091305070b030a0209060a0f030b121e030d0c09080f0f030f07020f06040905191a01051c0501080708070605030c040b070507051e010315030503030121050a08 73
    0x109800720780d41d151000c00902d04100001800e90308005001d0101209203c090350b00041202e600609259001c070114103142c0c0400000310115410014200203c0e5050040714200e44003034403a1f21080040c40750311540c42d0140008110214942c20070007402c21010400d40d550020950002d22017100801005449504a030040e125140030702400100c1e480380c0040c103401c0705000103000358500101071a002d001a00316038022039001c1e0007150000116602c11000c0c001030042900005818100502500034030310040031207000d29802d002001003a100044000d8222110a08005a0300e082e102081d40984c0701c0c5502d40c0e403c42d4030b0300c000482d812074001045000c0c0d900040440e41c1c0c003901d84005441500045030901100d08041000748071040010010300034a520880484030140d848030001102c2d00340500160308040d620706d48a03c2c843d03900d0b018200340d51000211b0b8180c801d06588a41d5101d10050291320314001e0041da0048181c03001802028a154228099940d020348034035014441d58170809 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201367742 1250 201366492 201366499
    0x203011a090115090e0702010902060301030606090e06060102060601030c0302091f08010b0315040f0e0105010e0907051206070c0302120a0801140603130b070903060e030d0606110a020f0a05030d020c 87
    0x50011803032044001080a9545598440c841303604e20b003041c4410303045ca0046c115001c55407207600c0200181c90b104040e50181d441040c01040d080d0400322610100d0340d0051280d10b142d03004209003c656600492440d81081c000e180120312110006c03003c0d0040e110300144550000c11903001c00c8284441180c4840e0f4031031080c1c0c0d0303010703446c0da03580c1080d14180019036011928055550221206207482c1d840000c0d6020b1b02c0d00040703904203100b24100d007100d60980c8240ca0411303401c030420800c428240040005440c040300c0c0b00807403010440d00035548a00c024510781c103000c0301d01c001c2c1c4180350080042400c000b20364240e196658688000080501c04284188090321020302841042880c1900a5074451034280d40e00b020114032503120f603100b13450090301d028180000c20001102240c198050070150b200010025591407140c519424210740b41a0b1000041180445280e0fa4100c0c0210310340070030799012651042180e8022001600d000300c25808280d06102e58414403070030319000702e0040e0082c0000c0307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201368992 1250 201367742 201367759
    0x1082703030c1902150105240c01151a1b0c060406020d0905180402040c0905060c0c090c04121b090509010507110607020a0314041509031104090b0105090402030a0203011a 75
    0x2030303820317640d60401500115448005c100180706505207090002c1c00c03d6030500b0340071040710100c004002d8640c130280c046000e03651510b100d030190012110020001705884151042140030703810461505016400c110b6141c050308880e1a0001d81d0200448140280020121a9103e41e0781102070b47c0e90014800358000300d0341c50b1400013002d1404074503480b9032451b04c0b803180c440ca0703a42e98204001040045180300038444012808a441d03119000075000030000c0100402c40b4405080c104003c4520003030541c0803281c020071040c0441e101e0400d000d9a580c0c1d108801e0721995031000f491540442c0c1c1500505480f900d0035003085125501504074600404194840b09221514032107210740b00c0004986d550090b9100da030403c0c00107840b400c0c4481c1c0c9604079401042c02c082d110000900b1802c0210401e20004002400500278840e8580519546e4042141c04201100f03003680c3d00d8103038410511030603100d019402c000a00350348003817001c40c001a600070300810007500d1a104001201c600120001c4c001c0010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201370242 1250 201368992 201369037
    0x82505030c210f0615180d0c08030901030e01020c1e010209041107060b041407051612030903020d2627010621020303120408070b010801021c090201082703030c 70
    0x100c0c5c070701d0207503101e009014541410001c0c40300e0844c10361284160003d10202c48103000c204c10303808180103480350401441e03484004c40001001d5440660055003140d1042100042e2100c0c0041c00b1400d1440194580d840d45890342186070090081b2812150400d0400180c200780001100040c070080d0701c80c2208005203030800381400101d48884800c4d1070000d0b51580810307400781c06032010b401154040c1d500505201c840d0742d50065540d840070903c0011a40700c03001c4008054041c44598500011840c0002c0d10710382d041c1000b0a800300140c83c0100010070040401c030b45561050084091a6135115038480401965114078000c04103031041d144c0984504804104903406001203103c6181c0044c011401c115990200107001c40020b0b0040311000001c05c0303a0350005510801c03540c0240301c1c00d8001a110b80f0402045403550b07001e54010f4460724640100c7c00c005070f8025182c150000b19500d0f844051140c0456040509022010400300d40c1c0f0011042101400c910802040d94009903407518040044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201371492 1250 201370242 201370249
    0x90d14040305012c0c090a0f06030510020711010f02060103080a0e0303030411010f0201150b0a111006030605060d03120e01060803070c031205030f15060706020d0c082505030c210f06 80
    0x1100000b640c07104849007c80c445030400c3e080020003012041000640c0c40ea00e9070707020f180c4a2160443c1c41010780200e45601031141403a40111804d01c2800c1052407841d15403002525480b050100402e156808241201d1040c8100009440048003804807580d90030700b03080000310a000c0d480c0c4c00d800510100441020b092060164100713201600d00030101136070a100e40c46482e178103c08a51010071480b4400e003075401c5400c01c82c3c0a403c0206180c009081030079800c00700c080d10b4004001070b0049410405000c0080d604c440110f00106140d6000100b40c10f01d80421400340c0000d5000c0749180c40701085c0401800003144a40c2c0c03c99100c0c0c1164880390030107120a8a00b4042103d580c0500d6104100048c060140c40f0071003141444010131007450400c00347e0b81e040c00c0f1381080304040e410554509012040719000004103800c420083c1100c00055100e100c501048540c42290030b08108001c004121b01c0003265083e14201c46000049030030141c00d80007104d541c0030f001c0350001d484c08414400300d0500d04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201372742 1250 201371492 201371503
    0x7090f290a09020f0703120b09041a0a0204060509190b0309100b040911090405030403080315100e030607030b0102120c031c060f060e0d0203060106030e0c0306090d14040305012c 78
    0x44c1ca4404141c1800401d48050316004144180ca03001035480d450304119656608401c00d106078820050b00940e0301480c0003042040c94020100b030300c11441003100340a80307600304083c2c13020070804499140c0700300310800540c8079102c1c0d42e80c07040124100c040144070b40c3e24004101c11185800390300c010484074125000b00b0046d9071000002500d82040007008068070f041c0058959031140c0208226441c15030b6aa40f00081648101c8aa100c1411000c484100e6864040c0c14680703003d20520703118056900c140300090f2220400b1700070b0001e048cbc3e42d40f070040c5e259000340203610007140e41031700d1507444440c01c0b01c2c0103031280c0c0142036030b044418112020b0414000d461040c101503c203880c003d22151810024240c880745000b03505a07a03c0200800301c40700507501044014081d010550300810b5060a000c0301c140f40142c0055040c1c80b0ba0094810400f01c100005046000a5411316042c8000b0642d141c01e0841c521580d0400b6140703500b13007101c482d003440e038000c40240052034925205030228003502c881e40c3c540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201373992 1250 201372742 201372757
    0x30604200d080703050a2d030605030312060906010c050f010c020105130812061c0615050f15030601180602060405070f2108040b180f06030907090f290a0902 69
    0x89006108400100f485400070700b443c5e03803080c01c010940404400d61000c7c0318903018030408640c1051180e418030968140119802040305400035801c0a507800610010480c00811190181c540200003075696031169400c4c00c00140c00a041d60003085404540b02d001c0e00c00ea105d400c0241d800d10001c03803800341c10102c1e00c1c070700c0d00d030490303203190a000c2680980c0c03011050180007a603100f0310184400710bc05540307001a24100c1d100e00c1000402008000854200d070046038403851161084900c05506074640c2180d04441c1c134025099160341c7e6407003e00603150109109034141400074109400301d50310b0780028034580150b00641c101c4070481d66801d0314550340c3c204c1303000754141c2e8172111151030140c4a02030090000c032841160340c00d080c1902c0ba00060301982084400d01c4138019480c0d0040560300303000e00d030007003c2e00c0140c0e03245140d0f10300b0301c01aa43c0c5041e0380c42080d10171682d0308401d090b00412076000c0521a21207400110742d8004500c1c01c4009452102c201c130b841001502000030f03000c4464800c4a581 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201375242 1250 201373992 201374003
    0x30b0f010506072006030a05090c01020616030e19080a08011a0d091713050406051e061b03070b01060f03060303091205120f03011a040302091311030604200d 69
    0x400440f9a604c2c1100c86000f8103074072211001e600c1c01d9440341d03a0000907520038405401c00240d00e2410041d01d070300d05590f030b100840c15508540f040c003440700c12000b9801d43c2000c0d03604002c240141c411000c146408001420100081500480340c0c04016502000300110225607899101c1ea980703030165a00a070640e030800001c0400104900d11959596400440c1403500031a44141201d00a10b4400203650280d4415903250646c0541032081d0316240c850100540000d48400c2d094800e81c1041458007400c42080c0d6203c1c01c7c021800d07442c1e804001c903100241d43c05400943c0c0e1204503503d000c2403501d0307003802180c0125225040302d00d0090301c6403080600b181d8241c0d903081407042c40c0c115056620301c204030060720240140180c800f5a481c50400402c0c2904411a6451b41da40c500742592a088030000755441b4100c4041000f000075985407550325402c5084e4207410189c09506c1c0c0b60440030b508821780e0a0f505406114100000c0c0035100f005030401402c0d0b001d00103500541c1c1c1c1c082000b10181e04000500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201376492 1250 201375242 201375247
    0x90f0218071209050309090a020c1203091b0316060e01090501170402041e020403050c01020d0809030405010503070536030316080307050714060106030f0614041509021201030b0f010506 81
    0x3003000040d00180c8000c2d0040040d0b1b8030300684140824042d100883d1003500719500091750a5150004201000c035185004041c40d05604081410130740b1903901c0c204e04103510380f8115000313003540c0d070500549010a1481c080344d04291341e203840c00362a0710390a1862074003084400100107003950160310300c2d48112503070000f1000d50359280c0e0700f0000200750781081002ea44008250030141c0710744c5840204007460180340109624030401c000240351010308083d80080103031010034007a400c03100200ba10b0550b002400e01a469949a040032515401104101f2421540c016064070404a403010341c10415030700044d0080407100c0c0030042c15500e10412021084da58004022000402d82c20409190030100c0c42c0341c0503180c01001d499885c200d81601d0300340380c200d400c41e0004201098040c400d04004c070018100c14014145005d0400604171020b501e070034041d907255816008961800e400301809440c15000c1151a180c58150701c0c4103002090204442c10301030a030104070040c411040302c904a5800030310b00341c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201377742 1250 201376492 201376517
    0x1180f0204050c09040906020d0e01020a1706061e0a0e04020a021005100f0605180103330b0a030e07080a050706110f0d0f120c0e0d050f01090f021807 66
    0x402e0020128022031000b03100103c42c0b070b03030780d40240a0201d000300c4026845644800400040301c204194118041e0700c10014a04241e070081c0b4070b840d030140e492440c1441070765480e011418502c111151f0f0544444042080045540004058102040c0300e41d9014994240007003032000728400c95100c0c0c000b682c4015100000074a541d04450307488041003203600d42c000d40c2d4a03480c2c621200640c1150006c584007040031000b84402040780000d0300000d107400c0c00039512070145941401c50481002e0b00d20703c11910781102d08151048240004c003486610580d03180c4100000900800140025032094000c001c4009804817001036540440d0341c001001c0d048407413408106440500f070404c0c644c0c11038011640654401d100a00c900806d017881500c0b00590560030100c0100b0b40804e00c489014006d160408840310b4680c0003098500000381074411003400521400e100d403a00042c65a20841c6600300176144007000284803954403068400d5070a40c400641c41d4605040b000c0049030f030540001e000b4182d11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201378992 1250 201377742 201377749
    0x405042906011218051006031203050f0103030807020f0a0c0f0803031b0703090306060b0a140c0607110f06160305071e051602060d0b0a090603050a060902040e06070c0501180f02 78
    0x200d9001600f01c9044c100040035035070303d604024505100040c440d54841081044c40304512030121502c4440c50108010318202049250071130060002808001841000850240c0200043c0c030818540400301e8084131041c1c80e00f106070090394007906103400060354000803801c2000099900030040c3c00114080740340420388810309500143c0f02507041007440c10000010460303520819000e449100c01d0990350320141c0341c02800307020341542c480400b0a403c0000e00d0f20090b01040c0c840c0c211040b45408001104003e1006182c400d4140104545005140a221005800841c00c0040102c03c0c0c0b014005a590034409440c4c0350700082182c0810044c84403501c94942c414801003040c5041c500c001e0307000c107150390003003607454010351000304640c2d40d954400921440e1880c0d01000401441106020042c1540d8902c0e403206c150420061982d52074902200456031548c211010802018084508a00c0c1c03400008109040904066a05528240501480c40d0f00c3c0c074081031640f5045078001d500c47d174646e42070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201380242 1250 201378992 201379001
    0x3093305041502010209100f02060f0a1506080a110304240f020a020a060b0a050a18090203060403020607030c0804020f01050d0b090c0a020105060604260a0204050429060112 76
    0x104000302000045203642e5420904072400c80c090740011707183c90a050510940402d0130020303c05208008070f011002a60002d1201c3d0b1213104404503500e01c3e00d6241908000d01281c1d0703200703507184d544004003051856103c0a210303c01d6484007002c2c03042c100e20000d02c101521081e140907100104204591a10506601000c41c0c40b0b40710080024012203e2080316040703170007240400c3d005030811008807040c0403040c01081406035080f0703030301c070480d51400000440c0160030748140d08208503881d505982500c3d4070703071003e401203402500b650324074606445e0003515860202c5964000c43d1034050820140c41c0b00c1c2c1c21052203981d01070041c110401e00c01005480036007281a0010703004d6104e488141e86500d4008000d8061400380480036116580c80c0d4000e400d66000420040c0242402e01c410803680c2c0640207644180c82000c030350b6892895601c04e4840c10b044c60803001075080b030306100c18441004903014021045d03403803100743c06c80b11b41482070f15080c1e884802e440d11400a01c4604031190000b425500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201381492 1250 201380242 201380339
    0x80c0105180a030b010303020606031501090e010f050901051e0105010e090901021b0c01091e0b0702030708120414120d2f01090b07020d0c080a03060b13030309 70
    0xa1aa410141c00c500140260840390070448403007100c58010820107030100b10080d04118100e019040f8401c504104140040c01440340381c86140d116414040710120039803143d80d41071051170062183e03190145065002c2c1000340c038030400c1003410744040034402246183c0d0605031801650380380000c2415200300a402d800142c0400e103655820007910b092480ca407030140840c1076501c006001c130440c5030400500500110344c80500c0d40c039040700d4150f540840720168507003601ca4204032252500c0700c600100c1d00c0c08445812102c26441500c1692919654900181048606070301003001c08601b018180014280415a141d1565000c1c00c0521052802001100703a11100d01d003034007d0220b01416503004851044601c01016591085620300307000c00100d0555001c02a80010500b0300090b030b01c01848902440310141c02c0c000c01055080f0494800d400c42d200030604514800e48030714805829030f00100781407004502144000900050a001c0c0d203500050944485605002070102ca80d400400c501c0c4a48 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201382742 1250 201381492 201381517
    0x7140d110c01140a1a01140a0203070804090515010f020d0309060b040f050a0e0c131509020304030215010f0f03060b0f0303070b011d1303050d1b03020a02060f01080c0105 75
    0x205940000003445043d0074402a03582c0350342d43d81849682c8108945a51003101c910007880314071010f00b030b41c2282585444428080f4a150381d440c04c0c510890840c00341d004010823094001400150507842900400c1c0100340311306c1615000c0b40d490005440d00d6114841410160300b0045620059600941c0202e90a034002c201c0440c03490501c4e4001000c40f1200400da840080c0d4850911010441510030505003200c0000100260022200028080c190041c840181a51146038000f4007600c1c44403954001c15030403105545a0415141c040d48a0812215001c09103034954000104055040c4040f82142c070001c2e40e8516040c00c41e00d5080103402c0c100b040d40d400c003210413000201520108010300316a0f018902c459025410041003000f550380005114400c20808400d20455126201084c5030b00c40d030604140f0380d1402c50a2602000c0e00a000010102100502400d4040c1d60103400414200f8031a80c00d4403a07a0741d90381d12700110a0000c0c00b40610035488100c8060955000e800207000c40742001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201383992 1250 201382742 201382747
    0xd0809012307270620030f0a0e1c1a01051311070812091614010509040902100302030a0e03030103170702010c0602030a0b100807020c190305150f07140d11 68
    0xaa0340020a602ca0f0541803030701908069003041070303a80c000b848000400c5401c2d076800355206a40106680c900403007a95108802c40090081d1901c1d01441c4a9100e4101c042c0103c6c01303409240000110980358444156416110082c1e2600c000c0d01e0009071034180d510060041d04031000680304600104103c0d015030488810422101d0040390320500036045400202030540030901d13003403562500300300910555240c4030300c40b20024040b8000034110394a0461081c41c0075503e13443e5620000d4050259110081e401584a041c0c01c815998107400441c410000000240709040281843e01c2e1f40344424880608941007245401c0f0500e202d040041c584240141340902c0200860b840b140102c5c0d205807143d10809544402188160030030f4185100c00340407500706202645441600a522540d880c95243d00c60f180b0030381c1d118400c0c410780e5030a50245401c00101d07500c10161042c461441c00c1c0a0301c40c540091807481c0002c0d222445000a4940307008505465800c2003d4002010060034000342c0c1c14030382c80c04c103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201385242 1250 201383992 201384017
    0x1c020703061a010f0f0905151b0c011e020c0d050c030f010b040b040b09060d150e0105040209060d15020f0702120604060c0504050a06050705031207020d0809012307 72
    0x9070b0240e00c5030032614840d5202d2011406001420b20000341508100340940c0000400030300c0d40100d80c08044607402d481041c4884644914038615114410300950b01c05980080b03c0300042d400940802c2110003a01e8100f00b640c0d45400300d0a5204002159a006a00a0300c901c0328908101580500e154420811a0000080035000131300303003850000605200e0303544040502451078940180c0300011000c3e202000f50200c480b01007000340c0402012a4003030140c84d484001006038503098001c42409107101000300507448003503e40a0b00050314264452075043d0082410ba103090660785400315841200242040f444100007000b07508488211a800e640c2404440d01507145c3c041d140d11b4076181030001e060140b520740780130030440d540210747c0070400a00b4001032100740c5a020041d0191230447c18400d4544041e450060720f94804d9036a110203844401c0c0c14000c141c1d4000918400c48500c43d03e940ba85560b5002000b42201d0240304007207200c0028146c016590404082d00365000300707441c50501c40444c0e6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201386492 1250 201385242 201385253
    0x80708120d1b08090d081605130506131706010602061807030c0902030117010507050a120b1203040303090909080d05060105070b010f08070902040b07060b060c070306050106030506040903021c020703 87
    0x7520b21041000c07550744010040050020f1102d400001818181100d207400e19a44071840b030301007401d0001c28044001010f0f0744411808405100410000300555600c0544003100c02646c80f0300c0c410070740d440303400a50b08100190081401c138180c0324a90300405071607642c01e402d030940308000c1210b0701d01400303004004808202c0c501d20010140c5540f900250707907545003110b0044070034481404d030145a40341a0070300102c198000308030b8064200b14a4440c0c5041061050070000380240107040b940400d007803928031014040400944201c0e030080c2c59030320a560b41c0798003000c1230301c24504000f45103820400604468000c0e42c0d00141d00300d1018540341c3c2c1051016528111051000c0e00402008805201c1c200304820041083c0006030403c54130941c1028600b1060108500071844001c001e87d40f62890f5241d41d4076075a0a44200c1c18182c81201d81003681c03801c2180040100703000351310000c3c1c01c0400081e02401c245c050520081c1d80746c1c1c001e0a0640e030030180c4200c1c2d00308289000c421400b411800002094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201387742 1250 201386492 201386531
    0x219021c06050c0304140a03170a020d06080d0f0206040305030f040c080a05060f0106170c03070507080f0a1805030d0e0f03011d0d030903140901030603080c0c0406080708120d 77
    0x1001c1d40c4007940c2d05e080c5814584690500141c40318841c2d8080c010480002c0e91018131f00c0d05640802c0480401c1d52079243c1114064060343c8442d240d0719150100004136800c00042c007034074061682d2201610004691400c07030301c4e1201160701501103001040440d400c03c02c00440a544603000b842900003054a8a01e9141000b02c0081c06840d1039200380e0a1190786503100c004180100210308086108001d2a0302c0c2500e509801072100000304000b2000a0020b8090307000c485826a01002c059580d00100c5c0c3d014055400c811070b03c2000981001d241d043c4108008410015610000d0043c8503c1c4401001280c841d0240c50b05203801c8988038079a002a03840c2400b5072400ca46840f01a070008102c032000440c600902e0213100c0b400c142c148690b9002103500180c00080222403c3e0030f05984883c5480141c014100c2a4030040021200044009800c10003154210500c0001c98091100303030381d01d10b0f4140e40c4002c01d01500009400c800919040034030300c500185030081d501000441c02d8420055542c00c1d26 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201388992 1250 201387742 201387751
    0x4080901020a0f0b040b0109050714031005030706050403060b0402090619030b0909031803031303030f0c0c14010206060a0f05040207061506050a020607090e07260c0c0d0219021c0605 80
    0x620304003061004004044603a1405041c2c0023408120301d1400c11030080084600c50b0b4200164440080801d64841d810000c043c06001c01030110703540c2a56038000107000d80e009120940f8801d01d485143c00303191030103000300c6592480040c0054207060300501c070100b0004407064403006042d070324200c40d8015210400039911030107102e0301942e01c84002c10007141065070b000b400d142c0b094004000100c00ca8501c048040705032501880e00718941100d08405945241c3c072140054041d200710794000503002c40f4a10404017240c0c0030317803d4503ca62070781c9080c49420442c1d80100112066004028041c80c1083c1d0b018001c4240940c2d80410340a000c1004c42c01c101200d900301c0c500107030002039119107076501000782076000100c61501c8000c89152584282502002800410800102d0711501c100d500e03140340c01c0d0000123081c010b03101c281d0038072105803101640104010680c9016107610700740f403070b800414844920001020002c031306a280d5800c102d51094005400c0101c1782d1490190008100d06228240c4034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201390242 1250 201388992 201389003
    0x60f09071e030f0f0b130c0210020f09010e0f131104091b0311031504020703120c0804050f010e0309190b1201061209080a080702030d0908070c060f0804080901020a0f 73
    0x8003c1e2003142c00540b1014a040d040c5079003007108142d05030b11030500c5168040200c403000901c000341110101c1c01c1c006070000c440e196500110303160081d0041c80d0020111a80240c0712201c1c4041c3e41018040d620200100c02d40d40084109800d41e440c0040390001a041075603019502e103444e8035501d040d004c5a410604030281500c0740c6c1000180305030940b180182c19201a0000c1c0c0c15454824020700b07800d01d80b8090300780034035004100403081500850301c0842d6502c540e0003d01a00403039410007042518100ca040d201846903003c1d56801d8001841154102d0034058040c0d450140403205004205107010380c41c5807410280c90740001c0c503400310030207003084031105100c00145502d0580c1c004e102441895076400b030a80fa021003a0002280d082c00c0710304c20003003801c083c0c4c21a035641100ba13045014698190000d9820f00340400100410b1034000e054062090020000c259101c230400c88548400e100c020300802e80c440041000b1450b2034000d8000003105104840145007541e851754130850810204480c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201391492 1250 201390242 201390251
    0x111190519170f040e04060c0815060909090a0614090c03070b04030201030506010905270a090302060106050f0f1803010c030b031e0a020301020703080601080906060f09071e03 77
    0x400030207215090503903050941111448246446030b0740d502100310661240b500c0c0010301c1036003810b40101a540240805c900040081c945424903002134001e0f0780400000410820001d0360079064034a100c0307100070313015081c50700b410070780d206100701c03110098a141c4481c440e0301d040e030700059401d00405483c036040480142c41c2d41021040c1a10f0000300440091080e040080d062000e00389c0b05054900f1250246008504c58a5000c0140c4620310150080c0b500818020140c500343c030400505403042220f051018440c903907803034001c00200c58038200001c0040c0c01500040051030b1195010709140200003804c00d1030080d8030317019045660b00c4025003606900e680100002e441c41e0030f00c1030124131155802c082c0440e00540e0002520f50404c0c0341901d504d5241e03207000e46840b5000b08420403d081c3c1c080c00031540e07140b144c140942140411100075002424482c00a100c0210209031103006840c090308900e6810050001c000d10344800800400400c2091410a0030b0490901c4081d00c151215440018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201392742 1250 201391492 201391543
    0x3090306010e0108030a0f030b030708060615090f0402032e2d05011101060b0d0f06120510180b27150103020d0c03020d110906010f05070209060111 65
    0x14240301059010607410480d010040006000103c112000030303100349843d40703c2a4440c0402e600500030140500e425101d01040854000c500003109802000b089482c009510b403000d400d032030300b07128500200350130290a0a000410707042c50b402950700041c00d540d020300d20060701c3c41c0301d00c20680c1c40d000c61070382c003500070a0800c20b40218951004000c401c00401041030a41030340c5042c1c1c40039213842100e04209020f014072400e120294050740c09450040c60440c0e0701d024186203c80582800001800d00c14502000050101182910b440050780d10002504901306800b44000060011210b2020002c100074081d40c0099100ca100c10321404980c4031030142c031000d000000c01098403252280c45d5651180003510b00814035043c0a07411039504503080341c1083c02d41d1a01e249100015032000750000c1c0e400001c0c13000c00c25485960301c036090081d10441c140d95503400c01103564030715500040012640400105000d402c0c10407200d0340c4130074107040c2001100c0e000c41c62907261200091110680545182850b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201393992 1250 201392742 201392749
    0x507080c0a081f08030403030207210b160504050a030f0b07030506010c14030d02030126010b090106030902040617100f051608040302070911040e06012a020f03030c0309 74
    0xa401150300100c26041100d540006480c2d0403003c1e0010302100070044219001c42c6426002c0b03070207442044280c9448079600e1030301130f54801c102d00a5442c0412140010206901c000458801064215034403007800c3d21a210f0f0210040d641c00d29071001c004080101041903140c604081d030003107100345400c485031016810b0603264508040e01c05030825040c5418404a070782e100114131640350700900c1030185030012000c010320351b124103404000e074540040000140490040d424408456a50645418140840341244d08903982080620ba0003210b100051020074481d074800300074244080c10001c1e100d91119500001c10310680b104800640c8001070342d1062507030b24026050082031070b2078180200d041212289055000390486c120030400c018000a02b410b2003004030318001c05504070100103c078200720742c14016a2003400307905ca00d507110001007540b5506c03d1908140d040e80820888814001c078000684060030070351030980c2d10a0f288201c004569400f40001e1040705420030042d40e0352685501031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201395242 1250 201393992 201394007
    0x3040303091509030b0a0225050a1203050f070302030a090f060203060103150b030a050c070605010b1908090c0f0d08040f0801060b030112020409020117040b221a04051905010507 78
    0x2c800401164803403c000040f50401c1480e0008910b000140e26030810103e1a8010180994150303400d51800e4103503400c0c00700104104141c0750095000341800100000c0035026510185d03002000700c0801c600060003548680e01460300905046000300310103000380c44241500c82c10344415a41540c0c004140100341d81c0501c40c80010603410a040304036507160440309866400000e100120003078640e0001800c1503400b0b0115003086501c440100900d58440c00030030384640010310120700c03000c0360240c070b880202d00414160f48541039600092443d108090140860302800001007508010050044000590090701410150443d840c00d212524034040005003075603940d034010002818200010f10109106110940c10030750181e802090902e86440101d4410400c02c005000104000d02400100042c03542c01c5070050462203d0300d50103001c00d030600e4060914918004041e507400b5801741c00c0e040076048032030307074018024001d072250582c251030f507001c415031700801c11101a5940c604006125401124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201396492 1250 201395242 201395279
    0x11091e040b030f1213080625030209030a0311010e030a11150615070f060203070810171914010603050f06070e012f19020306090606010504060f020f0304030309 70
    0x1041c41d400d00f00e00494980083d0066404a040002a00e90840013901d2005000b40640b03403c40d0b03da4a821200a030002001c980354803008001c441c070801209109000703803074001800030003400c0100c0700e5980c160760414201030303440210754071a40c100304500e805201801c2040c2e459210481214052010ba900b00840380e0072005012411034284103c980380c810b003030034078480d001e90380c5982d6100f2810008420f0803403050003400705000100300415150310220300342c0201c50a848207c4100e489001606c0c0b1080100030840755903002007080031540d040d21100c188154060140e0500c0290a001024292180e5402c00c2c1c659610103007520000d00410007a0941c03208480c908003c1c49900f940000300b0f02e010801d0010800f017140c0d074810322800040e4003a0b8861010b18001c075500002201d000e1201c0d44100340d0164440d0081600188001c200411700c0c901c030300416541c0500c1d141c2400760548003204035050300702c114410b151076010854802c1000308003450081c1c80307c0f156240340c0010484150340284 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201397742 1250 201396492 201396499
    0xf151e0e0906010b18030304031a13020919140c030105011d220e0105070806040c0516081b0a050109110f01092c100306062711091e040b 60
    0x10400080e40c0001c20b0340360549829407003903079aa0031156000c07100b1a0700205401d6142c0000240001003103400f403440300d00d4000d08d480c0c0e58040d540321011620700320240c400184d001640704000441c01008515046444069010002600c1da01c0805180d20741070119240c001441c0008010b01c49c668222100e44c8010080105040c108001007010503080019040b0110031408082c03490030390444260044440b10075403100800c0740e441c01e8034008085030390079a000b50040b0f180c038600c00d20f80f500c10320442d04403901550342c14480103001d54807051a070b4002600e034504200441e107030b840340007802c1c130090b45924040c038004511000030341050244281c02d0308540e807203103c4601d5440d00381c0c0d81102c80c0f8000c8880c039986070300120110340b1403800c5072401c00d00442064250401007201d942119190003041d80d01518040044907252926440f542c00c2000401040c0003040c0380340c00803044503821a40500229855883c00c0002c1c0074040340c400c000002c80131102100a081c0e256a07400e1030700c1058540d00007103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201398992 1250 201397742 201397769
    0x30b09010f030210031e06030303060f03030203030606090d0c17010c0f08040b040c09020d0f0f021204080307020106090c0e01020c03061006140c12071b14040f151e 72
    0xc9800c1d18040311480020f00030b44040c40213103281402079001c504440f1404c1d882c000901e83c1410058010320450000f1070102c1d192800100740034001c01c0000055030b0380341d0015807171a00d60380b0030070109801141d2a140d0003140d14480a0015108040300341c001c1c400148101060410000045d0a50380141c550408019114451522050740b2000d5281c0203500078900428549540c00e20004040180d04804c070b120340005140840c24900e64800e0181041c0b254007001a417440002d000240c0c0304a01c050441c001400001c1808103604000079500b284042c0000911241e85419800580c0c50045020000c290312201d412240d58040c0841545841c00f1406000140340003444511013205a001301001c02945901e100310b518004003c507001a080141100d9140021403c401090341c40070408503000135900c41c00b01c0001c443c0304a20019120510400c2e40c200384030800b4400144903451aa5003440e450f480d0801c401101200080c0c0503240c14014400c4071b54070030110920b4149503620010440158 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201400242 1250 201398992 201398999
    0x31b0e060f06040e0403110d090303021005060f1c06050a0b0f040e0607110a0b0103060603051203040201090504180b150f0d0c050f12060915090309030615040212090102040303030b0901 81
    0x1000101c500313541419040724102d4503142000c0b0b0700c1008106072401e252141c2d420425510b07400641c000c0840c0d02c660300710703060805110700060550f03805032080c2d0b4100e1224200c1010a29040c0e085000d8091403000c0f200e8100202e840388000c0e24000e032113081f000c07903580410710554103200d40e428a2440e801d031800c4c00f4402540c0c290b5170340c1e05001001c1900b007094400000355801802c2c4446122586c00c050401c002c1d503181e05000d80102100d10040301c4c68820414900d03408561306042d20320a82d01610b5440304189850705100c05071480041d040000290b45c00c5401c0010503940079580074072940c1e4043c10203582040244031040000540b082d100d50f140b03505036000100e4443e034a03000e40301e003034070003940f1f0b60040804600186411070441c45140540c0d02041109600000c181440c04003a04480c25940c03030304511251207120340e200e5603030517802000014807064802498681c141700302402c011310f0301c405030085400070b01d03080d2801f08040e50006400c20915916004a282d12401120482d1442d40f5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201401492 1250 201400242 201400249
    0x7080105041b020705190509090d08130308190b09250c1121030f090109050111031b19030203040503010617100902030118061d012c0304031b0e060f 65
    0x200361290074810702e10300308080921140c5900100c014071f40540414030ba0b041038501c4540f1030207504040400900e07040001500909400721034030b2020b407d900c8115880d00c451007038008981e281103e0000700d03910380c1d854682d5074a4042080780301c0e640400800b4030880f448041211803160201001d410460619046400700b2800903240403205402c40b440350003c20a40d481d2401c6200d9210780814600001c1821108507030004010b00068200340d0781c2107540c640310300056440270a07685a0312000c1d417041c44103040614065441c050041c0040c02151100644503041c0c4516141443c0c1c101c0044c0c0000c03e0402441c00c090013078101070b201c1020400d0120207840c610720b0380c3d02207006011004a4403114141c056481c00c2d80141e841d0a0380d01803003031400c003060800398054006d03c424a0190400c00341000260181031145040300c01c0e403010880d81341c03030310040b80c4000140030300c03241100c6000c100303c00800548a00341124501500b000034200443c0b40c040c00c80c00c0b80d40000c181394092103a41c0e070201c2e55540c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201402742 1250 201401492 201401503
    0x10305070e0f0402220e0f01151403040c0b0a030c080a0c0212030c070605040809010e04090c060309110904030314010801110304021318050304080f0c09270607080105041b02 76
    0x10b0041d240107032a8013005020000c1202ea13a01158907040e2100ba0114407801c00761401807145124514070000b41e66200002c096103c42c4d03d4600b400a01d100000b4428003a9900095030894029402c0324000c90315042c904003254040d2428802181e0b4a4004020440d040412960320030f41c0c0341d1003000180292807029403562182c02d005011650000001a60031404c0429240399a07000002084240340920b4000c4142d48041300080c0071401480b40209281740c280035010646500c000140442458258150003a00b40c145007281c4211800d101d1410a46441c081540300390700956003c1030801d01070141804440341a00314050590603c400c3c1c01d860b080400483e90002ea042e2074003008044021828001020f481d1202d5211111503618803041c0200000540180c5113030070140c84891848142175599540c0b1610103540011078400080c031080c4c03040c00d00402a204c24109035444100d5140e0940c00c19000312a5600400c8090740103003e03030308182c801e14505001d490341003032100900103070281d90703507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201403992 1250 201402742 201402769
    0x4050307120203280318030c15060515070b101d070507020409050d0f0504051c030e0303220e090c0d02030f0709050a0b0f0a12062009010305070e 64
    0x88030071190781d1001c0c1e100b00200c3d103441c00c080c41e0410855000c80122015000c0c000c400030002400d06001000d100a261080e045d0240d050312441d004107800c1e51014108149250030654281e03a0f0440040d8545655500c030510310011004180d84da01c071440d0444e02c5820203480d50030a61b0031014140302110f1102e01314030784400100c0c1100308a54401c1d0013110140700d40301d0000d41060411031760a0403c2000110400ca07507071292074602c0c1c12500321170b0031181801136102c1c941e031004012504200d05800c0480c1034003071600078a006001c0f0f01151011919680c40f11151007203108400c60202e4207410000380340009022a54050a003600704810b01545d90804606000d220300c5100e1030803011540d0400802d40b40c0320001d420b030349289079030342d01440c001c001c1110300640b10f40c28124010183e1600011f0b03010388034401080300c2c28060400301c24880403030360a80100c503416500c243c09074a0002d08a04c910f100c80d402c50f003039aa80e60000d00010240c4201030001414080b0292526280e6903900f098580c88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201405242 1250 201403992 201404003
    0xe010f0501170a1506080405060a051e090a0f0b10061e1107080f0f12070309030f0f0213020301031208010305070b070507031202031b030c0a0f050c030f0c0109090504050307 76
    0x2a440f039560480c01840f0143c00e00880e80d001c48000a98503420201c00c9206600071303030550304c55070340c1d2009003400d0381c1c400c85600c200e00c0002000360b501380fa03014902c142c00980071012036103410201d40d20f01c2c41d2140032050a030f5103d0382c075000300200000e04036590382c0908081d2620300c68003007282412608410078200703103600744521400407405a4108000e0f84006203000011224032015806459483d266421a802c0d1176000f02c0394640810000801103e00703c6625a40d60072825280d515110403003009401f0843c1d6041202c002200544c2d00c0c81c100304541040e640b00183d40794594904101d06103125030a0f88280551503004002203a00443c0907402c031190541c40c3d0395200030a1030140d0601007150001400d650080490f45001580040a4809110b40e50b610b0a00c403021140d20390356078080e5250814065102464610004101c007801580140c0310b40122a200c128120001c0e05140031a44440b1070b65201e1405c4010035030b0300a10380001012a01c004115606080c1c680030784038803c1d000090031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201406492 1250 201405242 201405287
    0xc030609110d080a021e07090c110706030f0605041404061805010e01150f1a07080c06040f02010305060f030a1106070b0108030c10020a0c1104020c1002040e010f0501 73
    0x51001c1d01115071076103507005081081841c0d840c945040c4540001c8484e5005106000f07130340e5400709080c4e22040500d50a1401031091a28002c2c46101900c03a0134035080401c010803104445964080100c800985625140410200340048402c1c003143c80a0380514072840c01c10f1100202da01d01890260b0b0860740001d4089000c07540c03a48109040c158000c0014115031134030305c42e4440e504041d40107071200c00c0da04165002060741c0c1c12a5181c1c0328043c0c0220401000040b01540400025500504105115035859820010700b00c0750f103070130107000302c40030340d080203408800008644c0c0c9445841c0d4840c10881c0c019100e0024080441c0c1c1e1014074810003030070541039610844540e17480ca400e03526619032001003030742c076981c513550155203d802444506980703100d8220b1541d01609123000b0b803541c4200c1e95a0700580b525641d1103e030b40c2d68041e5001c07150803550070412000000301c00d111210481088001c0540d80c1c6140901d1000c04400590000382010100e81007070200d41c1c0e002c2001c400e2200300030b07032050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201407742 1250 201406492 201406511
    0x2010c030e130212070807050a180504060e0702010507020f0307030320031e0c0724060b031602070801020a020717070e07030c02150402060301052421130c0306 70
    0x41d5042100e80aa650002055440300d120115540040014040840400078261500340054507007007810354000011130780034030118210a104010211010282c0682c1d000d0300c0f81d403103000c10111403480e0459500c1040c084100a5402e03024000d41d50002454801881045509031001e81c69000380c2c3d200a0825455506482e6400c50645001c8030a100c42c2107855030340d040150f1b980e250b2003184641d840000b1542d0002500c801541c0c002c0d0750307410b80c020405004103079848989550500034803004410440e9107840c0400c0401d0954081c52082010b200c1900792000d8015000c0e00d8000c07258803032030b050307801000b200d1011503000c00e0f0041112210750001c8a9450850300300784c104071450304541c031090f0305c80c01044451540364104100000142d02a9000d48807401816510144202c40294105504000411450404032803803122200d551000e41c04103500002d40c481940d005021035003552400c0040095030280790300000390041b41c2c2220072140174050741d4803441d0a410f20321003e44550b40e50700400303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201408992 1250 201407742 201407747
    0x3021b090c090d080d02040807090e0a06050903070b010303020c19030c140d060c0315080f06040209070215010803090102161404020a0e0603070801030606060f0e060c0a081b010b100c02010c03 84
    0x10b03071040303601c1502070780c07154442c170715420080d0014415100b081c4501100040c1c48082c91144442c8005000c01403c88058682c6800c0098030024000c00100d200c10400040820701000d0454003a51080d0301030400c400495003001a00421840410355480c400c4c0002c00000341202c04031403c43d03121101c00c0c40c4000300e40c00015008003c0a0000d440369092061480c5081c2d495440303071907640c050001c00c1d00d80a480b071000699840301c80150340c00c030b41d01c03050104002d0710704410300b154007864a10480d170b4207118500d10400000f40a07404803c10fa84041060301e0950b8051010f44100c51300caa03441d600140c905802c111086e200c82803424000e640c00111461614405d018641104d0006404d1503503c0c248a440180012402d1005450080c580600481e09501c1460b8800078844142d40e020719201e130324003c01503160b0051740c2003040e5101e00700000b4005040c1c1c02c094200d8409102d805c118801c00031000500391140744242c60b10034810000703030000750f98001243d04101502842c1001c0c0b0b14101d032409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201410242 1250 201408992 201409009
    0xe0f040b010c0b010b0a03050732090301060314060906060907050715050c030411033c12031821071511041a04030c0b07050312040b0403021b090c09 65
    0x60004480d000011990711a480001e100f121700c507940801482d0307218141210350072b41040c0c003910007008840d0082001441c0025443e034210034111072a00e00284180028212405136000b25a01c804258282d221020705003d01584a46000702030a014500400001c010303200c000c041409028000c1884818080108100d04820002080420440c00c00f040138584642045400f01c9580d661502d21440c581404a1904440c1c100d0005c5a8003c542c2c042e44008801c180c0d598014000e42c480100390689902080700e80c3e65401c4503401203580c6d084c001d14150f0040542c2000e43e5440d8403a10004400440c9a401405010410318045031104100d240881701d040d0003034000d00919052a0fa607044003c0240020f004440344041c2c2030308940740d0078400403c0c42c0514030000c2c0402007014010005010028010109144240b0903a4900780813140b40021100d002d0301c0039661202d9100c100410150104480800c04c0300d880344403101607800400090300b104e001844034240c0301d008508030305280c445009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201411492 1250 201410242 201410267
    0x102c01020903031612090803090d0213020712090b0903070303050c010b041d10060806010501110703050a0605060a0e06090703020d140108100b01080106090b0a05040506190806010e0f040b01 83
    0x2501d030381c0d203c101c141d20000340b504c02d0150342100c40c18880c031441c14002c0c1c100d80308072003200d0061414000d054007042a142c0076400280e80001c100c0c21800303854080c51000f40380052091044c40e5803254038200080c8484a40d400210b4a640200400b43c15179800007071070307130440c0c0d450710b0542e544a2010030303040e0140c0307032101c0a190818144000404080ca50b0050714110206a10460b070014584041141c02c0e25400d1103002c00310b4211400520a65120b5109180240d48400403903402c190360b65141e0385050705460095414590303801c03d201003842c20040460003030000044d410600e00388840080e28901d4003401c040245a8005a403103422216604078942039601240d004085694810b0041d450302e845442c4802c01910389845d04c0741560003a49241c0c1620241d944046c5031500f41051125290f0001401c4002d00c00188000035072a40c41d80010a421001900d80841c103405c400b101508165001e0404c6050104c07000701b441c3c26407030b00215505601d17001c5a01040c50310802c0c2c016511200c9021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201412742 1250 201411492 201411499
    0x41107020904050a05060c16120203070503160c0905010311010305041b0b0c0d09030f120201060e0c09490b040f0b0f070507120306080d11102c010209 66
    0x4001c03d1080c0400c001c07600720f001303001340e4100780c3d1000d2044401c2e108280741c07407140080054000c80801c540190249108885004491500e025038071011318503040060704440300d01883e800781c4200100c00f51500000d007400c0905111950541d51928600c244d94408581090303070340d80c001810300c542c50010107142e249031500307045029250841420258446100d4036001c0c030412755414076152043c0380e020100c0390450751000c010481c6a5030300c980710305440b41d441e08541d2502030205036001400750705400340c0d1042c01804e40e12055082845403800b2143c83e50080003102c1020030741c02003181c110b04d09000c0509078141c0f80402100b4042000e03800c25000143c40d43e50b0b07003410881000380103166205032030f0044508134031355038407900b400703c030302c0da040f268140010350038042000040c06604240c2c000c003084d8140824550748441c121403920070350510380e0b800200c80141c0a030300c08a05002482c0c44041c2d250f001d0019030004240400c0c003446055500c4d448607119040d0320303e118420b41c15900b0300807004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201413992 1250 201412742 201412759
    0x180c01080f0a0b210c040b0f090403180504050f06040c0f020d0309080f0a0924020a03050309010902030f0d0e060f0405060c2103040201030c210e03040512031b0a0b01030204110702 79
    0x1401841d91175401c40c141c40e00451400e00714000030321700010103682a07280280f45102645da0b9071303021688005000d030642d000118140002c0f483d40d0f5280030f02841800700301c0b42c0300210720300f0804101c10380340100700308024800b101100501d1150f000c1840d580303004c400c1c1000b0030350300c54502c1c20001c244249002208000004a411224207a01481c0c1c01c044131071048000c2c0c0c20148004003003031040b001a682202507170048801400003406403014652000041c4000907001030302d500400d0400740e0031034101b040343c0c100d80d03a900c0955811603000710b80c00304241ca40c01d04010f184551401c40303100b00d02513703100300002b08004610503010460440300d441d010303800001130f0180c10030800164100b0380d000c0380820304188014034070a1242044202e50070b41441e41e5047d00140c0000d40c2d0042c03400c2c0c40e0300a101c1c002040080b44944601d1000484610410000c554412001c443e20042801c0150318541d030790050700340c210226050812060543e40c0481d0002002924180f20500c0d5108034a0002c1d00040b0b078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201415242 1250 201413992 201414049
    0xa05040b030906071103042d09050403020c01200a060e0f100209150a12090201050421170406080a0f02090d03020102030f010e010503070902030c0f03180c01080f0a0b 73
    0xc10080c4c0103950944400381e924480c4116162240650301030b844002d442c2220111800d020145515440380d854030100d0700260f103481c1e200041e124220740035070241e4045400350645590150700512640f1040f035601d046c01c1006420240c0303800f05a0009880180c4a1000d510501018002d00c7c0c6000c0c603050031101c210131020000c101035044405410320440308541c8018180c42c1e010110761910b54030b40d4a00c3c00b125070b903440c203030f006068000080c2d04020081c0004954070404289a90103441003a417030b004107148919221090f60400b03506113081c03241c140420003030305400c1454030360400c03000e0b00b02080c7c2000108103e4000d01845079500c0c0d0160303800b1000e00c1415010b40c021030142c110003602c401c0580e01d4103c441e1241c1c40a203d07040d0164001d0008201c0d86002d80c0c0617541149500030b445142c007111904003011038005a0b140da0f1a042d820142090f00305003005200414402804e041d001071500d5501000e0303000c8000e1201040503107840304d841184d521381c002c0c1d4071850f12050811001014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201416492 1250 201415242 201415261
    0x6130c02100c02060c0d09170418060f05030c090a1506080103120807020c01050a0306050d080405030721032001050415150308041e090f0515190b0a05040b03 69
    0x11110070112140c2c601207080306141d20104a8901c03070701c041e0160030f1031710110050b410014010140281c5044511001441484921000620080405812840140b551020b00c030040307400396841511069a112400c0106840114070200904012038411a031640ca183c080f80c0079102d000b0940c0b8407001000c401003060b68000c400c00d030580380203201c161724006050070280d840010584084001d60b0140e8103104240d8412002400310144900d00450220759a6010410511015004680c6000c000c5020b00043c14100320314002040c000b00b41400b544507611a800c08075154010107010059102c030302d04600e0b0342c00c405502c10180f0200003000302d880c2c10b06101c0620002e22910101450801d882d0b691b100c00080341d0502070f07030b400c21006803410346005542c1eaa2564008004104003c0c00d40d030003d02102c0718413401104200801d00800c091400e01401c0700f010f0542c050f82c0d481406030452980614440c070007002e0695800300901c076a00c410760102031f2000c5c021a1f011031420580001000408036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201417742 1250 201416492 201416503
    0x80c071203111501030b0709080304180c0c080d0507031404140d090501141b1207050106050108041e050c0307031a0c03071403040206070c090b090105040204060207050906130c02 78
    0x5029035121480c0a0106070480d446889400d0701030f10816600d401840400c120b02021a0083e1300c80c1407809000e07565034040e906540180d8420780d400c1d108010346180b960800d0080d82030603c020b1400c11500341082da54681c07240241114402c559503128001625030f4001c3d40f1101240c0040c40e2100c0c000c0c03501e4a050054000e00309280321150040342c0e400941c050181d01268181c510507116140d081c5035410a41c131943d04168950110700400c05403010348044107118400706410481d5035580c0d5911503042481c03d43c0c0407a44014100a150000c000c085000804d1550001510b00180e06215406040c02c0c1e02d41081320079603550501508500108005040c00c4d01c1c0104589907907504050340d074040302800580400c41e424000b044071290540083c845080045902c50710007001581010140c1e10703442080304854002c80c1c011595139009107402e16180030424010b0a0440e819450181045c400a480d0141486990b00807200c04000c02c1803540c800307039641034206041c28200210301c18690000d5445 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201418992 1250 201417742 201417779
    0x1d0a030c14040b0102010209030c0402210414070501090311010807090306051602060a05072f1203010905061f0f0302040302060a1707080103021c0212060f060a0b0304050c0d080c07 79
    0x1603280903e80e65041d401030007a2003211034024058001340c8080c3d400d20010350710a0908a0122105195000e03450040e030300ca0f607014901031100c404680c0012040c040ca84107480d000181403001a60741000003401e822110507422500703103401181c50b00c40c03103400d031180e5045e6000240b0003810901042034820860020106207503855084a8a98952541a404860b41611000001100c0c40030116038800344101140f04120100c113000114201207203001e0170400e91240540304242c000004120559003405080c0e000181101d100f1141c6914a0801007041010100c500a20a08103444500303580240d040c0c400031500605119511460943d005000f200a81284c41038a100800401c4403948a10f10080c180d075400b03080c40c0d42504c00301d200c10702520181002283d10032032501480284040500050f03020340b0012550300c1c403501303001e010003000c1c2800e038100141606041c020070012803130001342075080c0c035004d880403150560300d4100003102d4454030714105414070031102d0000c0c0d4010f501240c0d202c170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201420242 1250 201418992 201418999
    0x1090905130303020a022d210426010507020105060108071b170f0d02070501110f0a080c19030603150c1205102102040b0f090a050903130b030907060801061d0a030c14 73
    0x14405138009407141c0d03a010000400c54501d081c0414807407800e2940b80c1d64100fa00c22b47d000388040f40100c010a003903800c200c40304d40c0103035102d00038409213580004200390081c206040c05001034542c44101c403070881c5c50700300c01f07040088a0710040701d501c5000360803074800c000340302d00301661100b811081c4d001944c0b2240003114690300c0c04c4845003c1140b800d0a07914001500c41000c1d00d0029040d40884e08480041c1c1203140d80e80c009c01050703458901142010951482c142c801192003403950410031b00d8664403151105603142881c0b911b081c172130b6000c43c0707001d100030803400c000070140c8030042e00b4001070240b81c000588405010b03e80703440d840480e402c0b0132802803003250240107200e0a03e0600c031081c0000300b559900a007014010641c1d11106401051748244040203ea05064a2240445c1c452006511041208000209000c01e505051007004d000e40054144098254581000108840301041c0c02211090704c0d90041c0005aa03103041040065810007a0a5141030702d443c00c050100055038806da20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201421492 1250 201420242 201420253
    0x1b0506010f060801050a030b040503120411010e12030a0809150106020f0706020313050d1104050c0903160f0e09120a030e0c0109050a0512191101090905130303020a022d 74
    0x2a464843d0783c080d0b0690310050a181c404d0361460703803821032100d00074000b00d8042c00284505142d203e0505032141c440c42c018078440c050403055000140042031540c3d4100d015851040c1c21008dd4400041102c090038450302d40106c40b96902281c1398108482410100d00d1504041c0002620603400100940c3c000ca80c00300391140c1650358003060360b5074400d1145004000e49984401c201d00e1410459909016003e5241040241d0040c00040e013141e0b02258201d01c000400308110b0b007181000c000c2d64014404001601814509000c10f00c0b1440605103d00c05c02d040c148000907500c0c1d10181710007004801008074054850b540340c48090090400800314109501c00d680306600d06600c01d10240c000c40b03a01400f9510524217020034818540c02103260001c6903c41d548034650242d48001c01d000d41036014150714210759051000040c680426680003034201130400701440710480001030754045c0d0580c107060069481c5240300c0141e040a140b00070b1074905a0000d5021240203540d004e00e42d20018030903051300e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201422742 1250 201421492 201421499
    0xa021009030324030f030e0d0c060809190206190c0c0f050f0306040c060305090102281b050d0f0c02280b12040615050907030e0c01080601051206011b0506010f 70
    0x1c0070349000e00c406404818000010b00111f40104500e0860100140032403442a81507210301c242100540e002e04001115802008480b0400348481b03d0445070b0003040e81d400761000d07000a0003901458001c154404d42d01c4a01c044500e0003a00888451799100b0300292070b0a0340e810000420040902c2814020141411440000c2c6008980c1c075115507400100540c4050030850204d009000040c5518001d6500b008190b00c0c0c0400e18940c444140116413103100b10100d1040018240c0d00101c10302003c4840ca80e040f4030000d080403c881e010780c4131528040c0f0b003180e283c02080343d402d109240e000e03400400c10508004503904442c0c9048040c00b2801c0c40700c1c0c08558407114070341c443c801c0109c020600001400894009030041d0062460f5840150103040680d840b0000148060f00944104000c00d90b2950071300403038441401420710500090a0511903403501400280c1244541d0700100083e0100706c00203490781c1e001390b1200b804507002c4403124152554038070700b849c0e4034003003800390808a401692000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201423992 1250 201422742 201422801
    0x31c050601030f050601080a0510090e0615030102070b0106080c040f0e0603060702030901020a030e041d0d14040e0a1d011b0806150f0304051504150c08010605030c0a0210090303 78
    0x14005c4c071042c0d442088507525114403030020b00c0c003d807507030000120250f800140c10b17650f80107100700031040c40c01401640c2840d0000b581c48500005030b8a009900600903640495601c0325491304442403400d00c910250780d040041c003100d1256800008400310a00d4000c0307140003000c0c14107071140030309401b16030b0140c0780c8031301c183d0362806400b403081d0050f44035035100e500180c400d441c5018070683c05030021442060028442c3d689411085402e101903102c0000140030a5201d844000250100351999203045e09192094030301d03120041481003141e8a800540441c601502050304075007080c44020004800ba000654800019150f5018000b03460400031030720510b051344000c5028039590618a2500030304000c2d035402030300000c0060714140250311010728401c1e94080524802c2d0300c0707505008111142d8007940b0044551803480c200400070a07400602030710390004200c0f50030890f000d440b203403503509604040f072802220080c8008400d00302400c0300200f607016008a02c1b008500d107030f200314640c1d01c003880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201425242 1250 201423992 201424001
    0xb010311041202030307050109030e131505040b120106031b0f12171303050c152d07020a090504060506121203100b0a09030c0501230903031c050601030f 67
    0x203030440a90200300c1005016401410150424806030031750f130401c1c0d07164a4050840c0c0c5030f60300540c0841d505c943e90391154500141c00b228900303880c80042080b01a103400d040070180141c040d42d4000c40c1d0380d8130032001030381c3c40301b031641d41910343d0b000240034507a100e01d4160304a0003a0700300f21500b001220b002040c018101421903068420781101c00341564416158500141d611b1400d5601d079400400103400040f00803d1500c4c0654080c00081c100c3c01c040f002400310b254100b03180a1000c0805201d1a10700b0302800141c0c00c039201d1048451010f04080350100d1416201d4018025032012440c800010003686541080c0e204a015140400403580d6402c1403140c0900c4c184c02e540c0c104e402c005113800f51008444041e5400100300b0b40c0c000c9125445400c40800d035404407640394003250040804004115045d41c01744040c04080ca00440d20031007006201c02c4c481c800c03115241010f900401e90510a88007003003074401d05020035891b07950b001c80b96819040189026142c55000a040c03880300c0d41500e42c076024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201426492 1250 201425242 201425261
    0x6030606020a020609061903060602121809180d120c0201051b220b09030f16050103021b03040f0305010b010c02060706180510021201080c03120f130e01030302010b0103 74
    0x3030010440b0650030060564003000303c45a0180080c8088112007559403140161300d10395450000b4800d04086010740380c450070580380300d9000400c001d500c034103070030380c06501c0010f00c0152030f88081900e5078020320650201d04402c1100312310609895411455000c0024541c500c82d082003040103000e001d03012401d850f0215003060014120607600c43c0b1b4440c455000348a98031610300c22070203a08411180074107914a030f0b0700601841038003050310166445d081c001d0385044c110b48801003004000c5645000c00b6148544030f064103041c0c1c08101107080700200212014120b113034109496580ba1074000002451510703001c00c0c0c0c1d6075843c00400e0040c81d4011505200f9141d001068030f8103154065640d2005010782000c8101200100213000f000034504001c44013005484503005030711074407440c0990a013100b05900c005544d03402004605032544020031501181650100529036500900c01400c0c400e20503070a40162900d8101c0c000035280340c2c10320805068a01c01d82c028000324844000441c10f490f540c45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201427742 1250 201426492 201426497
    0x5030604030e13110d02030114031606030b030a02040606020a032006060d02010507060f1a0f0904020126010b041406090f0f0411031302030d0c0c0302040c091203020c090106030606 79
    0xc01c154443c1c9003500f035105000540d018013080071130070640c0c001095005601306116054001c070060080c40d10001c22a114084190020301203140005408a00a0301e18401c0c01300f85542e61030540244d0300c00380038000c00c071038010f8802e00600707543d41c8000f9a10f030684081030b000503c010300c1888141158698600070407a40c0740040c146030300c50a08000c03800044017422414442d0400003000014128000da41a40500e02400108100241800c0d00b803040120040382c41202416011045680c8180155070459028a045000104540c07450f030b4100c5107042c0e10141141c5080300000d505044003000300165015004103254500562050204900400c10000e82c000c030035003100390b41d42c00c0168442c00b4108004001107040103100c0c0c0d00700e450f94015a10140001044801c6606508041041880003001342c9046450300007152940c5007810384501000348510748866a50759254810305c070450291103a15144111240b407407401a40c0c61075215451801800706100014010317000b4400c003003c03118180c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201428992 1250 201427742 201427757
    0x15090606030112080a17070c0c06020115030b0c09060c0a020103061205030313150e070f0e010b040b03070903021807030b09060604030602130b0f07050105010e0103170304020301141f0503060403 85
    0x20f07552190a42c01c801c510030204180c0449660b0301140e01b403541070144010b5180e41a400401d03007402000100f50390030440039a818540d61300785d07010b501d40400c0308480c3c21600041d0591a0720080301c84070b2084d5520107074000000700b14862001c4001c211000024400d0300d0400c00e240e5180080c03041d411048030302400c3c07600180300241070f0961400700c003030741e0503c2107020710410060071403550215890346403000419480800c080c0155440150000090840381006421035850069401524443d600038450600e4000c0086096640298041c01c080c560041c00c000716000d1040c1400380051044a40100107800e001c1c41210f1410905401070150001602141c64075086131070b0400030758030490744408421100d10740003c074055900060400d92070607180ca075a0310812410190b09450341078001210000001c2c004100190841007107406500141103e10784985d2580000ba0040101c00000207081c1e50903020000484900c5070390b808524146d01034546566124024142e55450488004000c50b204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201430242 1250 201428992 201429029
    0xc14030a02010e09090a06061d0a0203010510140c07171c0e0607020102070b0403060507140c101e0e0c01030f020f0a0804080d020f031803120a051509150906060301 72
    0x4c1002641c000140005c859080c9100e030388541c200c0c0c034540c1c072681c104034080b00c084000711644042e01e9000441c900c000c3d400d6504010001d00d40c5120741c2505418020492464898208a1429600041614800d41303c07061380d5a82040c42c0c401ea011801c60090058040400b860304c40c42480409020541c1e40d01250f4400d0340041c8402e5600002d41603040d845a007000045404454006101940c4030b034401082d182030078140909188090b80f8100000310091290080561000811903240880403030f0200303182030300302c030b4000710480c100f003000f2405420182c40481c00b5034001039950a002d000c3e40c040150311140c2c031141d000c9005074180300200c10702c1000005143e83c402c09881e5002401041010320700f0800ca0395a00c02c90303000540344210240040204031080a0101c018103001341401c0140d032900300341c13010511551000030103c4a409503190081800000d00100368405d801025000c2c01c103a003085881c51000c6019104040e1164090f000020000c3c00d164007038904840d003080b624000c0109 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201431492 1250 201430242 201430249
    0x7050c060f09091801050f07080c0f0d1b02070b0a05030412020c1804020a0605034302070503010b062a01090c0e070809011112060a030507030c14030a02010e 69
    0x100d5100c03890301d030302801406070301c0d6075044205001d1919a58401c220030000c001c41825104010b0080c60044a100100582c00c0d4010200c280d0050009010655406200501031898010300d109000d00c030b841d003c8001a108545078501d42c81a1160b021181620b6882076000028421030721020300041050021800041ea4504055009100d40c0140da000c06102c00204400e81443d10038a0000c010740c106010542c14040c004801808003460614038610340b4030712192120b90304000c0281e4030240300400e50880319034146030071441801f072500c04400110405000303544603014008d46119511705428400e29180c64000c0f501c103019024126a00c0466005001e042511007081c030304d1840d502c801003440040c3c3c01446440c003802000720b211201d0b0a054800a040610003880641c0c0b80c2c0c5041c0b840389a92600e0400e40d901e01c0c0302500d030804035a94980c0480c0c541942540001c10381c1c4500030001c02002203444d04c55090301d02d45c3c5500001200700100b0036130f0382e94803542c0103400705000703103003966441c01d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201432742 1250 201431492 201431497
    0xd140f0109060b0f0c0c09270a02010503041e02030313030317090a0f0c1206020711040e0303013309081c0f0c0f02100207080d0c0b0f04032c0f010507050c06 69
    0x7402e046e0784129980a010a05018013181c14441912000341c200d5a05202c01c241c940c0d070000e20000500c4084442c0e0300107003485c800a072010f040700d8103028041300c809810905009260741c3c098281da454600502000021010347d000440c013090320f004159034800c44160300b1a1040705000000c080710103081d100d00c40d03006400c607420345040080d0440030508030040c14221002c0b52040c0401660758100b030520903c4060042113aa100b06d040101c41c201e4550000150b9064070794402842c94040c0000340061580319541d542c004030195002d03615048240c0140028088500b140196190310b2110b568810912410581281c003044c6407015100c4814490310104029500c160342449450030230750002107140d40d8400e4440c00503448120b013800000014000382d120385c41142040f42b4558403d581d0501e8603032006105007c51313811000007906051160710400001c01140d00141c030404e001d10b58112602e00f010004038042c0100744907410081d4031910840f5911504a0701500300942c1030800c200745903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201433992 1250 201432742 201432757
    0xe191502070905010b04052805060c010204051302091c0305030109020901090b0d0e280f03020c060d0c0f051206040c030b04060602060411040c0807030504080d140f0109060b0f 77
    0x61040100108580c0d55520a00e030207052120b01741c41d1900d10300001c020701e194241d0b1065002500f44901501c103694400900720a580301103c04544a0036010be40500900450307208552219045500041c0c17000c035540181445c18080e41c03074038041d01022a890500c101d1402004000920810041200d420340e540a4030b4048c4051610000342561141c4101558110f0090307462241d42d40e03212048039080c20840100107103410030300691101d1460040b0581440e4121015000101c0c800c41201018403d1262545213000103007401d454040c1d01d84100c0081c011010381c000480c042841c5a14214043c40c181c40c85001184a24985544c03100140805800760400d0102415162482004a580c90b4000c00c005030480d940204041d24060070b040c024600e251491072b000700d1401d00014909588103214a90002813400c2c0880c00b07440c1c0d071420741028030615524407002071030910f0030500600112822800350a004809007801e07600c48001e901110f4540c4140c40355040100098840c45d4421030141c07520 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201435242 1250 201433992 201433997
    0x16141806040b0310060813030309020a0b0408030409061e0312230d0612020f0d080f1605010b10020705121006092a020a0201080606070c03030806010e1915 68
    0xa00000001103240d58016822203402c0d01408400c00141c40c0031040204010100e030f01e400800c9060209504019900320305020301016120b40040c019529007a000f4002460480003403966956190140da450760414040c810340d50b4101103000034214546e665000b0800b03c00c038103041440d45143d50340703140c40290291280a00c0042c4000080503000e100b00d00d500f6410f4a04966510780c543c110403002c0f90083e400103c0002c50305000c40c80540c445d03001aa28030030781034900403840e41850400303060b140108140f00d030302041e00051250040840b4500714003194840c0c00280500c0c5566420080325a142c1c0c2d813000d0050f40314000030405460f00204203580c6078518420742d00c1941800c803003842552040e81009030f20720788880e00551051154051141705820241c4195540d401c3c004000b5115503401101904206020f0081041561400c007150308041c0e00c220001e880942c0d034607001c2c0080e1011105507010907008500e00c860b80c1001c104000c507012180c5a0102428108034194480181442c9913004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201436492 1250 201435242 201435277
    0x902030f0601060306080a1203020f042c130f021c020402031003030e031b100504090e060103060e0a080906030a0e06131709010203181f0c06051614 65
    0x1584051180814600516000d03020560625501034150340d002d52041100342e01000903040840c2c0c2c00f80381074042500610f000b6940b00314003a1951502d015580100d0746a0107814505c44186001450105012040b00e40080c0c29584820006880344c400c017001400c2a81a00500001481d203c1c0e10b0b041c03c95490007200c04082d11039008038040303030000c07034404c00d1580805c42c00f030051507040540040c86010480c01004a11260054550902041600b0300d00032189002c00078030407406030003614045c02c000c1c0c50421090300030050141e5500d40070712040e21842e241050303004c68400d01282c412481e58000600d586024048400d000b025803008050800c210303600c40341c14070520814040300d800f4501d0071001e110081a20b060242e2040340f0403043d0040206c081000078402c0c0d0300030080d0340448400ea07c140100c40c5010000c00e42c0716680c00a042a10302a04044202e0150442581d52000c0d014001c100130300d55545840b00ca6001082c02040d0105400c450a40303200c02d407800c0180301c26183c600714481e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201437742 1250 201436492 201436511
    0x3070b04080c150f07061116030201050601180b0405060d06091509050c09090c2a010c030f060e06090a06050a2c040206090409060e0f16120c0e0901 65
    0x1089402680040790a0b4102c003051520030f203019080c4869880ea80840549804010900f900b400d10400300b0051074207860301e00310700c2d0560803802514000650040309101d20789040c50b000b8001c1000b01c5a580c08180060b07152013200545040034020b54440440051500b428a410403a0b0742e0052203101031010340761800031600200ba4040d034090912148a200d10903818522080103561008103c5011078100b4480b0100c983d5400c02d040c1e400c902e0007400aa51519820548284400310768500000348445040b4080b11010540c080e8070303c2c0c21150742c1004600351115040c03090b40c9291160440c64a115400f0950502d400a03001d43c0100340400c000405a5848010a11260284e4400c0160b40c45107100d520540c01440c16540000d441c0c1c07080a01c075894a5070014040340036509038140115901c510140400c0b85a03442118080202000c030382604c90b86d070601c41e541e440e6410b00b0807208460008000380d00040246e200300444e91090040f1121403c107414040760280c000d18856542d03482d0852603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201438848 1106 201437742 201437759
    0xa08192003040b090111011406030c06030103080a0305100e15090c030f0412031d03040801060e010e07030b0d02040911030c030304060c11011e0906020c040605010e01030b0307 77
    0x4540310304c1c95000490703401602c003000c1a40c0c2d40c07030101160044c480d18812180304101c00c07002c89101c11208428800180001c1c440180307050b03130038402c00190718040c0e0401a0300c400d5003181d103900d095690101910300c01e807c1e514082ea0003c860601d040303d0504042040d44021720004482c9141030410100c2400d01d0010405090018402d0008010512030b4001c8107000c0361f42022105241e0761554070711380307941c41849210b030f20b507180c03120024400324040d02660480301d8203920140503075a00b407800e0303011341261420f1540c0a4524110300f001650b0702d100e00c580b41270203002500d0902154109040c0390500e0204010300c2944180f00420103164040c851604580c0c1c441c0c01e083d0140d130711400580f45641c551980500c96005030141c130700b200f60f00040d014121501030342200d000b14800700510080b82c1c860b01406000500c1d64652055a5002e504480c400320030160445281f260707184500b = true := by decide +kernel

theorem cover : BRFrame.Cov 201258992 201438848 := by
  have h0 := BRFrame.cov_init 201258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201258992 ≤ n) (h2 : n < 201438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
