-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:41:31.14298+00:00
-- url     : https://prove2.me/submissions/31b115a2-c14b-4407-a3a9-a956c2623533

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12769791 ≤ n < 12949647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12771041 1250 12769791 12769793
    0x1120303020702030303010e010504110406080a0903120614090a0e03030a1a040501060816020c030307030503040c05060712030e03180f0301061814060f031e0a0204060303050c0606040b0a12 83
    0x1035810b039604903034001d00703403a600c1d65210307468020000c0a0107428030541c6414000c05402c0100d800711412958a80c070703074a440e40e9444c01d810000380901c400c107406010105404901c010000d21802001d0300100c04130902100e0801c1c10303c20918402881a03c0180c40e00f40750b014603000000a880c3c2c0544020300202e1803031165101c0800216081d055035420504000001c1011500036111602c1081624004c121203d4843c400f2a500c110803a0100d806810401600e000b0901c520021350748540215111048541c1e00e9000c194168419401502c0c0100b046c0141c8100d142d140c0540b45018010000550500450021044240c08508015803080010606144486d2400e4100750300511901115004440880b0050300c003410010000600c125a1000005d4452070917110508007035030302078001c01448071540d450802181c41c0c640035001e14442d9401250060365a4085d06024600c00d070365460704c07081c2c0400410318011018000512407410300101402c2503c550300e00c2c5080b0342400c01482c07903001c0c40d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12772291 1250 12771041 12771047
    0x510020a0501060e0108010f0501050a180e0316050609060402030601090e0f070906050f030102040b04140d050d0c0303110703020604030302030604020d060e1b04030812190e011401051206011203 85
    0x1400d00300621070350038940e00040382e03c480075405048401440080c404294001c41d4082112824010543d01442503041880010100440891055003400c0009602d070b80c0803101c140b86409c4055a400342c4031403401513204001084c4101d5421003c03a0005100d0ba090650000b80c4400c014080c82e0016550713446080c41c440c00800210403043c03441420713105025110101100a48854020709001c0e8160900b9aa82c904052084030222080c064101d4203090400d0050304c00075503809075040c4d01c9100c54404a0105105000d50200c0c040f25884903c4940c1c404d04d40a010b81300300c500c0801400d5021b0001c400817035008201642d00961600c0d00599940e14000010000e0181228440082d858190b020070800700c0c41d02c0c264060003140c0aa2007118012240042140c4541c0c04001c14a541c240207485680c8078080b1010381215280120864505542e0f400310304540703a0f0f00c1090343d0390b9140d0550841c065a152401030141105031819405622020742c400e961302410f03c074203031000d59000039200174144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12773541 1250 12772291 12772303
    0x6050f0409050415060609080a060b031c0302090a090501080a0b101205060f0f01030503120403090504050a1b03050c0a1404091508070801021608090d02040e01020714060709051002 79
    0x6039458100240d0a2a0034000c082c0e80c602c10b204400329145c074038003148041c081c40c2810212184030008080d10080c1d60b984002030040d47c0d00c801d80500c6103c4944a40c0c1020042c03952400513540e40c0162540790303401c100b00407011a0b5210b6400a4a048018480c0180210360f00101a4121420f2440c41e01c0d00c203c184819986540074044101c0c01031006002c011002c80c40314016040c5030041021500da444052800810a200042056204000c040314402c070208110364824003909048141c41d6039071000c00e041d94800c60301070b03040550b2452543c2074004041030429100d240380c6000c02c210b1030110301340c04582c1308080d110024001302008590014144208840140011800601050440004d0300a449000d80170315500ca0040000c045400641442610b01c12031a140c842c1c4440300c141c0e181c0c103170191320265489030010b03514072194001d42c840c4d00078001100c0c200000140e4511030386c100403022004100e05d031204c2e40c1183c401e21040c6a070002e08182910822548802d0700c20706072030240d20f000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12774791 1250 12773541 12773549
    0x30402150a05070302070510020606100302090d03050408100c050f0d06030f060b01080115080403080c0d0e07090b0604050a270c02061005010201021908060112020d0501030c080d0906050f04 83
    0x141c8034121a840000340c1480c5101e5001c460f11140c035081084400c0d00d60303c4100c1c0043c1d0101000800c14508400742517002d1080d400c0040c0340503410030100d03800600c80c9138194041540043d00704600c26003007003900701c6084000810001c0c2c0045460040182c8681006031244e840080341d00384503901c2a6004400442d4018141c22081942d840e1a501a02c510341040d8049148000000b8145020347c03503074030310202e0039a50903078141c5d160780d0b080d60761400141103504204014840c0694003d060320404d0a040c1741c24004200c000d01e411b45400c00d440c0e000d04494026842408100080e480d0740405c02c09846000701c02001100d88401e10b82d0060f0f007059003005c512418000016156900442c6460250b208800450380054071000168240c2c0308030758009040da101c441c4500f07405031058004580101c0145400303140829100c0c0f02d80142d8002e0382c5880740c4640d49400400810094101d840c0c000c1c8041ca0242283c3d120400000e4004c00e0144180820f01000003121402c00c1d0204007110054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12776041 1250 12774791 12774829
    0x10605030312010306050f040f15090209071107050a0b04090e0c09040c03030e0105090f010309151a03070609050303041a040b0408010b030105090c1c06090506070519030504020a0902030402 83
    0x60450b01c140480480003844184c810518100103c0c00070040884494400c5800c00c1c000c002250f52136889504000002d545940240c1d40e0b09550801a0b440081c6030740a4640c80d41c031074040c0c84441110324101100c0350b100900c12a0b4021080040850038002d0f1801c030303031b02808002106000290114204a0301040d00d650209030b2104020030442040304050540c2d0180e913650030015440001500e00c0c0c072070300c100e540d031240081c10391584c0380d03120341c1190110074802d55030141340b0300003080c0303c80680b05400b90146541d590170090f408582800c0103120001c152514000314024030740360210781c981c4101c0c010050300d0008040c905030901c0d08402120020304940155581e600d5880c4e0301d16009241c0c681c00c1503c29401c150200d022001c00103240300c0031400042c900c49c41c0c1c9208000c0865802c80b02072040b00e00b03644805510000c100c3c1030040610079080343d01c800d5601c8138a52400103404a910303000006042c9810280b0000d40c542d000c0300310030345601e56001640d0783c840d400001c0100e210354901240c0d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12777291 1250 12776041 12776047
    0x1180b0a1506051c06030b0a0203090a12020c0301180210080a15090b0907030905060c07030311030f06030610140d1401060306020d0e010207050c04020f0c0601030f030f020102090102060a0e0106050303 88
    0x90690100050074000c4070104c0b1010030620705804c0909803001303480060b03c180018800b0034041900c6a000359000304101c8201c2d00c01e584144d03a4125030b01019a55032000d40c0207448c2841c02c1e801c00303016040307001c4140041149485515030006400011108520041200900018a54805550180300e0544241b04598482d541d01c1c03600c2c0001d01043c1c80007500841e900130110350341a0280c010740202584c080d0181c01c8946c1c5405001400c2d8000034000c0d4201500c0382200c040d1032441100550142020000004103842c003401410300d0103501030400810315a40314401c010744071140740e414248200071580c501d031210707003820700d4038481140d01c03400a42946010800000c200c810350041032006001402808007e0301149007600300d000d0050702504a8100034020a080d00d81a4010210444006106410000c014080628010003604110303030b1104148801d205054200200c003141544500c029480d1405c0c040000f919004094091060070b0348503a0b0b00d0740130060171340050024007805000c903a1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12778541 1250 12777291 12777299
    0x52101030807030908010203090a03030b040b04050901020405030601060c0c0e06010c06020d050108060105030d05030a0b060c0d0305061f0c0b091e0c0f03070812070203010207020402030106030906050901180b0a15 93
    0x782588018811404600b041c100050811018000e80c1c0c42600380314060b04078070600c1c0d2401d0300600094001c080d80141c3d2108009000d5403075205d818000c8000d040016142c0b8103003000c3c5442c0a00c10780205040c0040e101040c0001441100e9020070340300910400310090301c4410060304c01d61142c540042420740042070303000442c5100e90006040b2480c3d4000c40348607980c1d420a1607100c8580000860019104200103081031049402c00301311040b024000d0340c6800b00c41d03a01242040c08034901c0782c00183d00c44003170000c01c0c54001490880503194240000040e42034540140020301c0810300240541d4a041c00511400414040300c00c40c45000a0b545e00c07600d4100440d6510b0b00c418551440c45818103d0cc4540241800515802640c00d10402032809030081002d40c0c0b0280c202034402c0b070f410340d02001144010f03191030002d140280103070344011801d0361041c0b410320203680e801030940c0c025a140c60310100c81c1221207004140c0c803e03000014003e11f42c0f0b42404e000040c00038111070072075200c2ca9080001e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12779791 1250 12778541 12778553
    0x60905130221030703050310080118030e04181113020406090609090501030302031b010b03030a0e0103050f0402030705060901030209030604030c051e0703120215010e06120105130305210103 83
    0x44118401c8030280b00c00d0050031000c400c400d00300d11000c10907910030300403a0700007805000196013000f5480703580790f440b079035030101c0c0c82c2074503407071800c01d030380450035035415800c1681005404900c24030071642070003c1c0c4030880384512401d290010261100300c00c1c810341507240e158404003545401d04481c00b55540d64036040b001d8012007640c42101e00289014038000780e250340c40d204190690342c0c1a8045c40c0780c900c100800e20720040803c1c516540e01d5684101d0070840f50340c1040184810180303501c44c0070380100880f0000d412614014002c40c0220162000c00006039404a54981511801c544050329561030000407402805490050382c1c142c8115000c0c0418140c00c65160055903118404641c2d0b20070044c40c0d030318500201c100c0d415100f0340c03283c50240009640708181031450221881220902c11101c1000400d0550070b80c0075007085066401884424101502c03451798025550713009100a0909091000e07901240c000042c0822401055580c52106515440750031884102039200746561203084c07103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12781041 1250 12779791 12779821
    0x2503020c15070b090714010c050c040507050c01020301150906110a060c0302040e0c0408010516020706050333120c010c081303080c01050708060a030206030430020304030c080303010b1c060905 84
    0x5901000c2d040880e80482c0d885a048c140000d0352020140141d2141002403001420004e454403080c8030040c0940500b0710001d101850003040e080c4426541c1c900360810282403d0400d801210070482c54000c40580480001201608154482c6c030004003980e050504a009000b103820a95180c5140800d010400101e5400340050310b1000c002040301d40c40b05414611481d00e0700c85201c025806c2454104178990181020b95031245112a60400e5441100391600e00e00b1200d064000c1d514020300c5914243c1d0400603400c000f00c80105004003c003508040004c0e20305d8000d24001171204000080c200c0911046e00b40340401181d000703180035100c1c080051900e01030482150302c180080e51087c00544146004031441007141e401820940c074640316500d401e10405036495480e0425000180e21004d41a0b40c126030703004500c0030754051500c1e10b003549498840410300d68040f2205600510042c045421128100c50341000106483d019034000e042072000900308584c41160000d24080030461076550102c90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12782291 1250 12781041 12781049
    0x6121b13030b041208060307030f030c0c0e070809030a05042304060602030307030506030a0309090504050f1b0a09060501090b07060f020a0e0301050603010516030902010c05060a022503020c15070b0907 88
    0xc14500d00c030700544c04c660002e8111903a55050b0301c000c0041000c940c150216401583c068034040a07029a60b8407060141e004a501200203620408100040305502010203500710b902940034501e4080c21000050845c0118028002d0480c0340c403e1055002942c0130ba4034011810203442440480c1d9180e00103901c0e0340045a66038042030420000449a02d4003290044e1180c0d85034941201107814841003000524008004580d0391064000c0405002020410542d0388020403400310b1201c00203c080c0b0a1485165004030101824007205010580c0c0200000c02900d10343e110540d05c030443c80c2004400741280b07001364082548001a10003455500c06118420305805030000e00440e01c412080c14221502154000d503100451040e101c002031082c0c0140480c82d00525285030010f01c40d441e04d070b0400e0070a6514a202d80da00181c01080f515414001c038041801c1e0703465a0f070816002d510080c4d121001c0f8819a403280320070710b461005031403500b41030740ea40a400060400583c54031410003030740c642082c09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12783541 1250 12782291 12782303
    0x1b0b0105011b02010212031909080301060e060403051e0307080d050601090e070e04020d02070203120304060c02070303080a0c090b030a0c020606030c0604050f2b1106121b13030b04 79
    0xa0040c1d401c0b400b00e89042141d030682c010440828451510900341d040600a407010392121096030101030030501400094070b000708410b50352540341c05800307003452581387e6401c2d020703050070b00c400c00c04240080340c08880780c908140900c21000c0071100d99800d40c030031640020802031001c1504040c44146510051089000303032185130040d03448a804120340b0404982c0040081c04644004285081036000390107450b500c208050f05103c00c40e40000c1c02c01101840f58001d0550100c20003041c46028001c40240d6543c40c000f9021190075900c0042404200500010000c0d03194000310200340d104a1010001b00211009c15031203040c0794110401802103000e20700010300c02c21000c04c00300c2c500801c0b441092100201460310b0146003500340502142502d481c03d0b0b003c3c6000c41c0c001061803e800318640c0c1a400c1040b1000002100c2c948026059a9450b05502031407060044203610036400410303039000640b4400320340c2c8001000400045622900954020700c0c01066400003c2102c00b20905e4000e0344542 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12784791 1250 12783541 12783557
    0x103030e01080c0a141603020a02150a0c111309030c02030708010b0d0615050306010609180204030803070318050d0f0215060307050105070501060b1602040c03050903090f011b0b010501 81
    0x116034500c03090f00c550183c04810451309051130300400d8801a81c4400c680c0d803a05085c00305041c001d02c00c1c140d00c026800750304400308c58011450b1065030044440c2c50100ea9906219151134024504440c480000b00303072462a0f0501c41d4982d407030718200c840d030300f22402003405468440d1800410306407688000303c0c0030b0320070043d0203d00000306001d043e4072102e02508601100059442c4c0f40007030322034000d0488030b85402e9031021a154800b404101d010f0400d170f4480c19035003450202c2410b007100500d0303001030031644140000d10010300ca10f422a50070003075528000c90240d80b1540d407500301444110008003d481f030700400c4014160400c03407240848055809030307680c443c044890410303450004c80b00c1e42d601d41c000d40c0e401e102c1c0d5802800036010080c003c0d80001078041d160a103051103036220b914450800c00d0440328840451a05000703044105480d0b1609001d00e00707003101b01d00c1d52401a04402c03072003080080305104060348a400e2040301c0e103140406000324a031260a000e95280700c20b0107041d0014a6503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12786041 1250 12784791 12784817
    0x902040e060a050108070c0303060320010215040309050103020304060f0504060e0d03090503041a040801090c050f0303090a090c0c0f08040e060303041d0c040302120f0105060414010e0606190206010303 88
    0x25410000883e201070311111929a03803030740200c0d0000da20303100407000c0c50741d5540007002003580a40840d184560740c0c400d400c0309540c604006072520601c45444590783c211030040100003684494a0004c079142801c0c05a03c90701c0758030b03084001c1c00000303034034414a81ca0181040180146a0080d82640c05080e05558180f40141411001e503680008041c041d1b62040104001c81c107074011480001c80035890b50141050f44421039035003903482180b0107a44031241a14148a549032a8036030011011341140110300e811082c002003140c940c0d05e440341581c204e41e00e404003c0b03800d0087e584074440356448500581c4090003490030034181d130410700038504110300c0540010b10b142000070480d01903410b00e90001d07a204040b201d0304001008001c1060801100c18040000141c403000e05002c2601c0c000c5010700084450000b426085641c02009240301c1c07403c0524a8040c0402865110b05465840303d09568907a03a4101103402807144001c01c3c810361480d624442e40c035560104215060f0b904c00d55400c90101e0310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12787291 1250 12786041 12786049
    0xa0501090b061e09030d02030a09090c081902090a06050c06060904080f0918040b0708150f040e010b180108070501050306061206180a0e010608070b030f0a02090306010902040e06 78
    0x801c0581500000100016620984210305250307440e000504998a0407040b8404241040e0040c51550302503030021510b080350540058800f03000d803036104001c11504858000040251002074264000071025105549003400150125460790a02030407480a0954550b0010815400440000c00600505020030310920b00803010500851f080720140b03090803144600d001003640520101c0707134001542580c5007405040b03070034028840c0740105000900c03843c0c40f10014200c500024200002c0a007680c0c8070803aa680d80005c543e165042c10b1302e0009203c1c0b0f05007a80d40c0140098a401d41e882507031007414000010071504c06a06862111080d40c546a554100550300350000759501070f0300c88800d03c00303120050958400030b80e1244009012650242040c1d002c6c1c81c400c001078400c500c005480b200c014150107401d0092340c00820152009050052900c20f03c0707021800007400c0003440d60307ca40041003848100d901070300d24518004054501da960b40c0c4094200079030180c45400001c605400011f183c9143c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12788541 1250 12787291 12787301
    0x4030507080a0807080c07030b0109050612070620010204050603150118030201090312020a060903020616090b0406050c0a0c080109150e0d0e031e010c17011a03060103060801090b0a050109 82
    0x503004840904024250f621705502da00000e51034444c0e032042c00f40000118400d225014024000a01c1c0025a0300701481404400703100300c0c1c44040e80b98400c4104118455002031902a11404c040d1050404019411081e01911950740401d900010110601c600e82c1c0104ca0b42c0010780c0026281c800c1161900c20284140100c80d100180c0030810303040d070410106821441285491205105550307907402a6038400c0c084a001960a0340107034002030400c286c2d03420092540d9900200c41c1024420f9078a01050f0134454407c40c000e8201304070011900703a22008041000f04001a404081801056106d00d030f0701d4001d204002c0c041d521005110101e2149103002d2090b140e1038030850010b840344950751041960030140c500e0643c1c2d018840c44800122070030410308000f440c3c00384100082440040340e072008100c001009841582e0180c1d460040181c1c5034940c1070001869440c041c6d0b141c41e65038190041c1c0c0180b0303889d40a40c1c119401c1c150704008112004681501c07400503005d00300305030b0341c80d18013080447c3c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12789791 1250 12788541 12788543
    0x1110613020103020a0e030a030905090703060e220c030302010e070504020c0c0103050408090a030b04020a060302030702070e0c12070503100b090d15090203031c29060903070f0b04030507080a 84
    0x69403000c66503016511a80040144110506144615186080c00303c0e01e0410142801c1c1e00081c9030400c140454038041010703036000116803070140101800c1090103140301102038615601d881d035812103200c540e0554540c0c040c0c15500711507070072170803542d904000e40078003c060750608141c014480302051902d0a0310983e507500100c00010200b140c9444010340080c039004e88141ca0b106814424071010750b0304d1a0658010754400d8000700c00792300b064418003403403000b5a0000300900d4018405c001210354009030050442ea4425041070407030b11180390700070300c0d0300c26203401c518619107540821214030b4015000791301401468200041c160713a6034031811160300640c1102d0b40c0c49600e00c2c546802091980030722852281a494002a0b6003d243d03001a00d0340e401101f00c03000c5021030820f910b864146920600d040c04134407032058100110945080d140c0e100003240494411036001c170744c18009490401c00a4041c1c03d6003622500500c1c0c0f544a925800d0f042840101c507030b4840c072000481c0340d05010400314521 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12791041 1250 12789791 12789811
    0x20d09051203090d180312020f0102030109020706060f030314070f050a0f021e090a020a03060f0f0501080a0b030606090a0b03101e150b07020613090f0b0609010e01030c020c0409050606011106 84
    0x50840ea130b20500c7c0106040d040c1d003103101382c400d10480204203200840c02000e114000580d00e10f140d1802d91700340c1d00958045038228140e0303082007001c01e40082c19a0701103400c50946030b41d190785910740725904101a000280c00c501ca00c925480402c907800303245061040c000c079060407503001c0c1c810380461449e001c02102e94010142101040860030907401608400703429080c08110030307481e14440000c6281950012200300c8640b0800c00807543c00c4640c0c0f903001010540d05000680100000c01e50720b10018000900402c035510002d000e001841d0301c11007142100400342c81c0c280d1401e000803030151461461756170a9008444290320441c88910684045600181035410f20b80d14103000800c4540104406980109040060300c00a080e442d4803800078029a910002c0e611600f000c0050443d81118002c0d405000c00708404078107681c2091850503440024a008940c1003400e4004a0414000300740f40b54119003021410300c100400072034840e120700e50a07a5624803098010a02a5884030140d03500d40103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12792291 1250 12791041 12791087
    0x10b03041a060102010b060d06030b16090302060702130e0106091d0a0212070b0406022b080610030e01020c0a020316030c1203020703140604050705010809030409020d09051203090d 79
    0x803001181c103030a03403101050000060310701e030400119034158002110280720342e9641c40c05004010200c668160041c1d00aa8500d030003041e1000c01038401c02c802d01010788202c1c40443c050b0308550360301c0e51741201501b07181d0080c8181c0c81c410100328040d040501507103001c64204010780540c8045c1d09010040c3e1070b080c3d4014000ba050300d40030f01c000d210b8440500c240034021260b01042098200c00140010701c081d07802841e0b0208100080114800d03c0d440c15240c40b0306441c00011030a070f001d418550855801c66620901180c02c141c1940106603500d6203030309550000c6050164050041903080071607009030180e58207064028907407008244c084c00000c1c100c0750218003e00c001e42105040030442440ba0040b100f0041c0c0701d80703460200c80141d100c100f15030b43c0090100f10401a00b404020000c040a092400c100d007014a14203450340518011380c42e050340d01268640a0010316048414600e070000c0903204c0c200a044a15090b43d4400c03210480c00c6d2041c00d800e100c05920038000018040758118401c03003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12793541 1250 12792291 12792323
    0x1b0303090109050f03070b07030c05060108031204030f0201090210020304030309290c0f060f0712050c0301050105070206040b040b0301030311060103081813050910110c0c0d020102100203010603060509010b0304 92
    0x3008503138003881d15416100d00d0001050b411904001041601d0182e110040c142e090f600d400c900e0f102c0140c12803682a0020700031801d030118076524640d00325505081c1400841d9000c407041b8010412100060760110510301000c1d0419000b000030019a03001c0d940746a13003103884904598008a5215800108810400310f82018000403000360041d0401002581c0e5842c500c68201850203106981c40041400c00c5014070200c103400825114014410381c42c02d02c1145003900300340039640014840c05041c0701c2d00040c000110741d0303040201d030003405800060a44482d00c070035110076290401d003c1100442c2080410080c41040094100c1c12298404041c504e400190103001d002c8482107480745810076100000100201a24010244281d00540041c5a4140e4008a403c1601d40c045180750350118100440395070320a022032646015001aa030b2400c02180910040345480b030b8510100702d50703510100011401c9545908408121601201d40130182e0f41c881300c0d140014441603030010201c0442820b221 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12794791 1250 12793541 12793549
    0x503040303050f040308030f0f0f0403300608030901030522020d0f020607030806041803090b0f0705060108030301050406060e01020606040905011508010b10030516031509020c1b030309010905 84
    0xf941804090000d0926640e50345103044c0ba04191818060b84060504201840d032445c034000740d10490103119050f5905041e02c018001000792012948540a0300804013610100d0700c420700183c40340c0090401c0256900c00440ea140c0e080422402d0000e070405c00411500082c0040080010480040110055030b0560800001005035402101c01c403166074800c4001d45c1c4e030070002e485454026100d041c0c9501d00f00e02000f0455400c0c102c0c60340200c03010b0040802199120031240240c034201810713669540c00009000219025264008106100785400460000804009103040350700c15038043c0302080e103485080d10b10b00d039941d20040c0140d0020000803840c0c6444e4202c80d000e036004100008000b1105079185050440541180105a464502da0007007070404060340540b60559240130805801d00260b18121408002e40d100101510360070071300d0109060483c401c008041d445011981d41d080103a2140c1c6444100d8041445107000304000c0d413141c02c0200456000c150b0503543c40e80c0d41c034101000c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12796041 1250 12794791 12794797
    0xe0601030b1501020c04020c030a02010b060f090402090f0a06111204061b031e05120604020301080703020105211504150e18030412030305060909070303020a110d020907032403050304030305 83
    0x2030f41184594502c1d11070350f481e2440106a05245c1001650355494000700190965101c6602c403405800208405044c0c0d000460030768044c00012200580e07240d112900082c45005c0c001d40342544069156400207440c0c0e04598900001c0b000002030b51540b0344181c840240d40e008904c10700012030b40413102d8808001502c00c91404840c801d0401d074000d4032110340c4c2085000300b030344004004580001030710400307040c114421aa000d04212410b520f55070400c01d8564403000540701c001d06000022032a80d003501c0030842290014800c203000b0011501d42404016468015294a01e0249103408040e14000031500503010030303924109000c04003a2102c41c140d401c176404091130a5248c0c0010700012506168818950640074001d55000c24541004801c1184a0401230141890340d0701084c800c00000fa00826220b038540e800c1001020403803c1a0045007251b140f400340254091040401c21903440d405a00480032003249603000c40052003001c810313240c108224003000c0c00580c4244020000248200c0013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12797291 1250 12796041 12796081
    0x3070f0201120606030617010e0d0f090324050c070b0601050a0302070c080d0315060206040f0c05090403030c02070611030f03040804080307060e060f0402130c0e03030a030605040e0601030b 83
    0x210744403800020044103e58242d00940006500c0c0c0c03108010050f0b00c851040d00c10b2a00ba07000f04241c0d60401d170f0710f51f52244000b50303003002d00c60002420a00140928500001140c005001401c2402c1c2c1c0b2020b031942072007000e9a04c1840340384c0004207034001107110580755401e82c480c60303100391034455000660701500404851003c1680030410311000a0141003003030020000700c8010f248907001c1c640e0217400d454007a2103601c42003d0004040100690004143d42c001e40c001001a20940c1c6508180d00840c080b40c02213600100794070284410980e065110305001d014a03801d90b034090313461307541c11503203081241201034243c4c0c82031000d40013107071005c002185c01500c50840145020340d0b96030002c6c215005068255000b41e510542800000310034440254841101d416000140c0b03001d0303000030390f10400002c0091010b65520f110a00c040d00405030030b114540000d00302d0b912000c00c000014050501d501849001303e080a8895440d48400590207046e240d2002e40304000c1da4944400866448402034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12798541 1250 12797291 12797297
    0x90503090112021309060503070b0304080d0903030906050103050c1203090105070b0a09060e030c06010b040501080a0b010e040501170c04020a170702160e010303020606030c01021209030c0402040b0703110d0203070f0201 96
    0x5807610391610843c4c00003030414904c003242c00b624000805042c51490b501c070b01440303202041000b0010b01043c2c00c0361034003005203c0000d048105801c0c00c90082509040007001d070341c82c05001100307001001902d0f0051510031110001c900c4018481c00703031280a0035a5040c0891401d00000001030828503842c1d03481072200c400000c0810040d103031023056602c240302002103500005000e2650b800c06105282c00f5040100c1d12501d8503280100007821003800800d01d50700c15954074220242c581c81400110380c0000d004106111550310340d646408110344d5400900e240784178401c0d403100e0604140c0290f509411064460076940c1040078400380a0600080030041140281032626900c4510b41d000000509a44014403000f503040d032902074502080038080900c203038054460105079a0f40000c80d4131801103001844e54440c00501c000c640f40945042115a21600100b4003007800b01e0400050185140280ea400c0d68151400513425201c0c243d18429400681041060360003181c81c060300c80c10131901c10b02d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12799791 1250 12798541 12798547
    0xa0509040e0106030b040201020f1605060a111006061d1509120106080604030305060102060f010302060c03090a03050d030c08040b060603040206091807030e0705060d0c050c03210a09050309011202 86
    0x3140e1242103c1c02c0707400807520161980148010340d60704001c22411080f1240062604180443d441800e200356441010310440001a00c8400b5510036510425092800002c135082d410080010700c019000740d000d40c6001500007480b020545029240313910142c0c0024110a0740e054840e889040194005c0d400b4980048a0351007800c1088000d01c1400000c0070304402503d10b0b030030281390040550304003420160440d8010400e000003030341c0e42c007506811680d040b04c070380795901100408141180039a20300c1a0380008101400418005d02041c4092922225a8100300e1000d20450070382c0c01d41d00c144d4001e824580e00c880000d40d2400d0510085400900003080b250620090000107426918141030780e0450861030028003840c6a014082d60b00640c003008090004079040c00f000c140c0380c2c0100100010259180d410101940340904100e034440c940140c141e940d281c0b00320304591140440c0c08442d21482c0030f00000a2a1003403e0f12400442c640d01801440c5004052001100c07803108204403124042e40c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12801041 1250 12799791 12799811
    0x30a0908090909100609050613150801110304060e01060b16020102030d05070c0c06020f12070c05060a1106060108060604060806010e0909010903081608040b0c040b0304081206010906050a050904 85
    0x8800307142c0c483c081000c003d201320f40c80d004e00d03881960b2565001c40c1010707040c101405429031b1001c00d14203042c07116000018400100940e54145c0a002d603014510075481c0c210003541c041c1a543c01540308034015a0203110800c44032171114203c2e40c1c288503c104148046c882c0380341041c0c501c95036109a80c01441102c4c10300c0017804d2200304494055030b07448042004a15068200514a84c03000010f28150000d442c40426000859880310071a80d20b812002100050000400180d039035072201a0401401190715036500d00c00203401908501c202c51b2113440703868001007880d17104480651003900094409400c292512009840300070000d0650342c103100d406000358495845112046214004200011400a65900300900200400340c81e44c889a102e01c041001c203d078003c0800c907002940909400320380d80e514000c5050760f0082c0d402845031904000140300030b20040398040d10303082c1d03103c0d9501103054a84000540742618548202c0005ca2414044035a00501400c0544074241d0043c2022500e501a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12802291 1250 12801041 12801049
    0x1140d090c170f06010308030c0c01020d09050a051603080a0c0501181104060806040b18070e0705180603040209041b0b04030f120503010b030604091106031302100201020f030a090809 80
    0x5600000301c88070709210782c40e40c441001c100d003212072070244014000700e50554945d118140f00050101c84940000140b6480200c004d50465070420780703215040106800d50b2070300548540c1c040c081079501c3e03c6040908200107960011040403241c0c01010b56182507502c1d001524459101c41095800c0d558803100034039142c400811145000c0e10454201c010a51100100000c950380ba0704070311150f9101404000000b901041d01e141c0000d00b9882d006800d05620303103c2481d00e0202e81100c0d4141e802881840001034011002d000700b89071020341c0410070400c42013405810f0000700e03070195115041c0404940070a2000c1c9213540ca05103891407070044d450311600107050f294850352040b13421241d0f003041c180c00e03c46c007901d01e402d0880c02c03032606920310b5140801e080c41900002c0d04542c8100c0e5503030562400c0284080d003c0700d8150014160325128038010311102d60244500e40281d0140f4407030109000c1d078902c18800c131034101125010042c02c6032509044480140205070045035901c0c002c0000f15034540d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12803541 1250 12802291 12802313
    0x307021515040c0e030601060905010c0807170a120513030c110301110c0609060c04030c0b0d090204060902071a070903060902190e190902010c020402070c15020a02030105060303070201140d09 84
    0x110f035141c07400f0721038000060500d8100305a21281c100603921a0a011580c0e05c01e9440702c03099000007916880d141c25040824150018015200d4005000140c0c8004260048100c5454050b80b840400540c1c0e540c0c520700c003401034140c0d4028001072a0038900d10018002c11700c4642403400c007070300015045241c01c0d40d1103510f42c03203d094024a944000100702101c0d03c2008140d511482c101a83c0b0f0405c0c2c0303195580300d0286003d0041c48a2200702184c01c1800c1851076120460040d00180148250790392108024000d600c1030800762000801c3e1150046620224001c00e401260140c0d5a08000741c5980c460000410101c5801caa0140c01d030740e40206042100e800d040c1c090720341d0040b40d40090602c01040c00749503e139403544000b500e040400719005070b03801c00048140680c0680300580c1e1000140780a030346480164100a007440600c3e41c482525581c0015114526072081c0c008110340c3d161041055a02d00541100034006004111401c100c078480c6400340030703948900c40c00031031042403a540380b1b81428 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12804791 1250 12803541 12803561
    0x1103010803070204060503010605010212031b040f090b0102070b031302030f01020a02010204080d080402010504090b1201090b070f170a0b060c03040306090c060f0206180304030213061703030702151504 88
    0x54004070702c00080d85841d21950300240340450007008071510301700010703490b544d040e0440b0740ca090010000030300304200e4440c9100031140e0000706503512503c2d0700440c0500143d40c0a4503100e60300c1d00408182035400010050140c48040900300c3c05c0d03a546000c0d0904880b04d0b520100e0b058000d070780c004001c41c10240042e0010340141d40002da00d40f410328ac8118588040105940300b00320244d024040981d030014121400c2c1c0d03000c1040480c40b80080340c085818640c0b108540c8140b5840d01d510501840b468042481c042e42140d51203031a4088120700854004200c0d0700e4070703825290f0f83c1c000b013446084a41d00424070b4420140c4403a0412002949690650f0060347c0280c500589900007001000304030803245001d450b0710304201d40c03290b900c450020750791040200000d08050020240d4585a802001580d008541c000c2210510030580380c920809085580f2485030b0300501d104d481e0340721590102c20313248951a2039008100103a19403081d1100c02070003428100e288041c44584400035155801212070368 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12806041 1250 12804791 12804793
    0x509060a0e01060b12180a030f080a1404030305040507050d0305040504020304020301060317030402030c120a02010c080405030d020102220302010c030e1504060c0314030601140304060608030a0c030e0906060f0d11030108 96
    0x103183c100380c81b8186d0062902091241c0e041301c1c94400009400c01c000b1104400305141400d1195a42e914030380007080d0854425910701d00c400100800c2541c5500700500c100d124005079049142d0381c07000e000e000b04504200074042031050105110f18240f9501540e4000c0c001000880c42c10b40d2511440703108021a6800c03002028000200070540c10200880c0c00d1220b02500d01000348910700000d903486040c8100e000f41044400c00c540d506000000c801e4902428006041c1c5440c140c0c612800381c001e5021103000e1030030380f08842d05c42c010001c41c2c14121041b40d03010b84900c0420322071560100c80141c0510a210b5205d4114500c011454040c50003030009441c2940312002e84448504018021a07803054811b60014000c0040091a990108440e410014004084d0740c61391218941035019003081d400c0300649200104000d8035403a484000416490b01a442e041040b22000b800e006810340100c41035034004100308451801a11030310010104000d080c10001504203e03040081840e9100707901a0300c40b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12807291 1250 12806041 12806077
    0x40314120a2a020a030605060f04020a09140f0312030709080a0602030405013812030c0d080a020a050f0c0102130902040512010207050706030c1b03050417010509060a0e01060b 77
    0x15a02d15a68070320075082000c1c40010307040c00306600181c000301403400020310080d00c900208500b61201d031208010342030001c10642d11140c1c940402404d00b2450701ca0782c5520300081d14161404c2c1007502000524800180282402010380e01100c651680080d03e40810402c003003100040d808024000d402d0444c0c46000d0250740d0f030410b810480d0a440410800c07480b950380a15501040321445a1030104054071640807010178980c400000d901091404082e41c158000010640d100690200742c422010b06035031114039580e01c400382c00b00c1c00ca020f480c441d040803e4040003040c400c00c1c880b20181070b000c10640002b510b4428400b00f12400380c80d143c0d020401098010400703000c0d43c90203107000441444200000c5041c60881d482c0d00395038032180e22400081c1070303032040b000302da0510841d0008040760410305840000034003440c1c0104554050f2103003068000226000c0c88a0000600826010f01078200003000d03103865030446400240b034603d86000c2159622140007814212030000383c040c5510118144407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12808541 1250 12807291 12807317
    0x6091e0c090f031b050301050907290301030812010e04150b0d05010f05060f0102010e0304050f0a0305060108240105011d041b05030412030e0a0803090a060509030a0306050103060b040314120a 84
    0x12405040b43c100500c2030741008100403440c27100180038001ca40046000716500c5081195880c02e045903016106030007440040040107000284000b00100e001c0002141d00390380e40c0d90038400150009481c0100160302c131031081803410f01580c002581c1c030000100b00c01e90008840d034039a400c54032060041c915403500c81c1c003000110f14140c0700e0148014004cac00244650001c001c0450381301e00c90350095903c0b40c4180002d4011540718940c2c0702024550080c215061941c44901031503403840507080340e40c244117859003000c00603425500c407103040329410f84980400c13000c0b100128403404070b1000300c8c64025a071841145803d1348000a11050700c0784680f5410384c1e9042c6410201070300c00c00460001c003418200440d40005020000e81c010485400902c080c1d00d945072810510f0628038019800344c5010b00700024000b0100000c0000e21001e403c0351810072030070341d8540c01501554880e10501c02c1caa44180820400309079140c05980d45940340c1800e0390903200c0400040c4000740c11030400140018041540f000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12809791 1250 12808541 12808583
    0x1215050d0f02090f01060f03051b070308010812090d080342040c0509091e0f1509010501081602030c070303090e010611061303020c090c0d06091e0c090f03 68
    0x5500010203103101c2e1201e60501c50301070105070207c0c41803010150744400060544540c0042d50007200403600381c16599100b241001031103a0000c1c09503c407a80610080b01c4a9581050304680031500050048081c40c030749900d6001703031500000c145800902c075994030901d48440c0d40d0f1094203c13001c0b1945000249803200007411014a40e10001c0d4000d40c6003011004a054000007914503002081758030700402d40d0707100b00e01502d45080817081014104a0810310012540c903e2040e4801e103e00c0090740301300200041005001c0100b880b0b03840c0891600400f150640310020020100b0440c41c0c01160700d41581e41103c5403804642e58826030009071407039000c1c410f004481d041075004102c0d0740380c040d48400310400c01381d0b160580604603d2251541c00b1482003014000d11020340b0b042c034001d0480000340381c000840c0006034032040030003a0b00b0780380c00804150358086228000c140c9005502000a0a0262a07184002c1070240540000d10008240000d03910310384c203a600015500ca1f821f003889101d2117400403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12811041 1250 12809791 12809809
    0xc080106141305061207090c0e040b0d03050f09150a0806060c0705010e01031409060601020d0507030c0206030406090506010308090901090b0d0b15030109050109050d020703031215050d0f02 83
    0x81c004100280c4200328080e56061001c0c040c801d0640c0000403503885000018007490096000035078a4001c005002880e0030003903008844841da65203c10364105241e1042000711928140e02a601c05d86542c40b24020a100b28043c106141081c062240780800c01400121500e112584543c042c100019101a800750310008403074000c0c6064900c1820000500e00d89a01c2e064607008490412611141c404080d0784a60070240482d20000000c5203203003442001aa01e61000702c40b007074054410b9140d0307040c0b003138420700c01c030b40c1c1464065440c1000d1300b4241d401c0005030303400500140c0b5059156035210012420500a070386c000c2d48140703a41036642d5400c10500c2116013059001d8590309192080100440d00c2c2c440342c01000b00d5001614154558540c4100d80d11f10760546584c5030190702c0c09500e8020030030158004040d040c01001215007811440008030395070751190000a00003202c1c40c62040004000e074200d0038250301d000c4c00300103203642c4950200302c403140891000d8400c161450280c6003582851200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12812291 1250 12811041 12811049
    0x702100318080f070210020a02010f0503072001020706020a02030a0908030703120b0111060c0702010306091b050a03060305010f060306050601110c010c02030703050303040503040e0109020304110607030315030c080106 95
    0xc144100306070348120519008054001502030640064280490b0f14020103c500311036006000d02e908925865000356180407204007240811100c03a20b8032085809103081e00e204501c16a1010900d0150100421514404410342d0001e50b40a21141d4001a01070024180f100403690085072200840c8100801c20070340c1340d100b4405900200302d2031011941c0641c2a820300d104400303000c031308a104c03200100c488504001c0019450b0164506004c11a2000380c010302241d03000344c4c1c060054035160140d40c0200c0704c024400c81301d040c0244503002c40c0140a03002800c2e00300300e541000514030350381c4c1c0c03100350a40701d0a0400c13503d403d0b6030383c80600c01c001c0280b14064100c542843c059040c0c0303003003c1d2034542e5002c295003070505100681ca40c00c404c40d0b034200100d03009194044140c9460f070406107411641c81d0003a02490440300c961a00100b4158030038400d5234403603500b1900c2c903050352155074180800341e80409403c0e810107440b40082080300b1120742c12200154414081040340d00d1501040d68211549600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12813541 1250 12812291 12812297
    0x601090611030a0525050c01020c0303040e130512120402010306090b090417070f06092310050a060905070e0a0f05010c0809041b0207050103110301081b0102010b0d0503070210 77
    0xd41c1c414104002042d40d03c10350841c02e165070345500c845466000100740700e411409402038020f40600b0071002241040c0142c030203800f100c261040410415849010b80d001e088184a22840043d001b00540c0c0c400d503c1c0d0344d00600c1500e5415000d2074481c6165409440300a4180809000f03010031941d240c0b140100802e121503007003002020b050005101c0c03500141c00900b1003181c054140011091810885100d00ea01c0546406000c1103480c04a0241c6240380090300c0012848999507100700743d0810310410089210058010448410000320042c48003078440e0340c8590ba03410300460781e800ca5206882c014000380c0c42c3c2d400e41f00d01035003c11040d55126086030b500036190100400ca240d03041056443e04540c441015034445200902181c001c00d0ba224000316070841c00c250004045401140304d400f510402e0341c082c415602e00c19807941a500c800c1c4101442d951080b24110100305c501a0b601c80c51000510003ca1140c00a5000031904d021582c000d4032250070020b0031004501c1e020903807245420b0181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12814791 1250 12813541 12813557
    0x6090317040b0a0908040f0f090f0b06030703020a02031207111015030201051b03030c070c0608010501050f030702070806100f0503070f06080403020c090103150f1b030c050702030102040e06010906 86
    0x16844408800d070190030f5180d5503844080b90b0041022a4080da00a0005540301d0400c040c2d607510142e00280c51403240004451030464041042c030303850f01a1000c984400b42190f460740c0c6600e1b200700c0c025840901c024003140424405502610740d61000e140c02030303981e9982c060030a00004c0d503150502e021803c020191624161040a0308413448581c0c0040742c1d0242807190300d5515102c40a1410180c1408107000c17400b0000c10860708990240140c15603a005a0343c1c00e480c0c90f00c0340400d550210007030150302e0214000b40000980300e85503400a540c04400c2c0e00c151010560b403090814030340203055540c004a01001d03d0117000b0525001081c00007003d0450043c0b11781898500280e180204502489040060b5600001c0926008010400c0030302005000d034551580d49017800c4921303800c52a103c054540c180340352007510340054001c403001881d26405041811030404000c0d00201103050040f070900000b8000c00300541d0303084c400b0f00700400c4681700080992500c04001130030007142d5048241440a10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12816041 1250 12814791 12814793
    0x305010305070618171c0503040201020a0807140601030308060102010b090f010608180f07090c05070320120c06060103050106050307080a020906090301020a030e0607050c0c101b0609031704 83
    0x29000085401a007004c0480c40585003c01804403103d40000b0b40403000100e82640d01c6900040d020490112000ca9202030100000110342c5071009940103401a030200b20801d000c904070100070f02e00a0320541d0528503c0034480801e50429400368420313000305122002308101545c0a01400c0d0391f280084801050f5450300c10642a0b00312410700030481013200c440000b4080040b50041c01400c010440120382c0c00303c403442d4001c0d075254580e0084004450801221740c06042c001e00607142540d5240d103800c490000701d181758011040502c40c011540f48501c1458005c0424404020040d201c050009402585000d6001405480069101c02d08000c0104204552541d0054000750050781003540940d440e40020005142401400c0000c0c0d81540b0000e1880c000ea900744c1e01200c003981821003aa60b81e0358455906540d127008103400c50302d81d90046000f1907804d20380008042541c4c2d20314102008403041c5040c0c4441c4048854804840c0c0d40d0350313603140805068000303a003070800c40040c0c0f07552186450701d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12817291 1250 12816041 12816043
    0x6131802010905102f120d1103090303040215130603060302090705090303030406050a23070306080c01051e0d0204080f0c0405040804050108060a080f01021e04050105120a0605030a03030b100305010305 88
    0x204c9440512442d070407145d5040454000c400038080700c0f00441260340c00c81c1180c260100e075501110050000c03500e011541401819144256807003248480050342c00c40e5625028800c081c0c41d416595843c04c0c0707003001401d00145e0116001c1018121640d0000303038040c2140706010039594060580341c03c2c4001482040b103d9078001088a0340141c2c00700010030540c51f45500301029218501c045a0020055407a0111002c0c680440c64400c0019540510195070307500700700768458024000c0e01703002030410000038490301e44200c1c200701a614001b1100d4a1721004c9040d44007207810580001e01e06401494482c00c08060411040c48a942c041b10204102c0c20650746040079440b9034490b035070620402000054141d543c07141e41d08000d04640e4182e4134038028100540703000790701203600052400300d80c21146255050140981c7d081c1c603c10b86406181c0f14010901c003810b40802085040341c1030301c81030301082d582c8090080b00540e61098030041150524102003016401c0300301700d5030b801c00d483d1400420218078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12818541 1250 12817291 12817307
    0xf010b040b0303070f050f010c08070807110303061018080102120106020613060504050109020325060c050607050f040306090602030a0605010c12050a0302090402040e01050f0108010612050613180201090510 90
    0x10307100740040041d171054505541007880588213613406529292154501d5500010264031940c920f9688a541d0b5490710404c0e244002d42c4544a2080e40c024070002c0d46038201980c0340c400784602400c0c015000c42d0745880484020b141d80d0007803000d694010034035441e0700c030b981a000b0b80582014009080c05140c003121010803d0054100500000d1700c07800860140002940b000b100550041d0a641b128958141c1d000c26240e034081703942204080080c000203000b4441c00d02c444810764084050041501c030300d0380868682d04240c0000d80c0501e010003001000580030310a103685140320b01d0016880345041d0000000720b0703844da44001e06029901c04040c000072280846220b134401c003801c040ba00c0c1e032110764080b80203000d0303195031640041c40080d001c1a01020a0441e038100c4008407010000158920011070382030100703100740c00203d50f1a88591070780a1039a0482a800b000c0a003004804c14010480c000c162030421003030340c018070040302d01d4a0940d41d125513a04040d26007540c160500000079200103000e50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12819791 1250 12818541 12818543
    0x80409060608220f021008060a08010b03031c1107030f020601050a0303020307021306420801151b0305030a0c051809040215040e0115080115050c070b0301080f010b040b030307 77
    0x605401d655410007070302403c4c02104030380280c4410f000200c45000a01008000d0702c606101da41d407980000390400050183e4134192034058083c508060089420581a44620300180d10481d22070b100c550030045108003038a0307014082c0e41c1d107151410384031a01a040c80010b07001700d409019904001c1c400300b038000046401290f41540c003000c2c51001448240f00070301481c0c000c2c100c480d801441a62103600310041d000c1201c1d0001400e0b0628000150607070100364511040784000c070b1442401000440c100c407801c00c1d14910a400e01d403501204c1c50342951115840c8250450108101100344440345039180b0401c4402d41140c100315241c290394041381206003914402440c410b5081000240441d2190000281c685a160b013085840d5921801d03600305070300b8240540340000150102100c0c030140f007426914125904c005003105511004102243d160303024002915262140c810001500012a1700035402041c101014014091140e403569096071395070700e12107110b40c2c01c1648281030341c4d4010007124441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 12821041 1250 12819791 12819841
    0x25060b010f0e060a031508010c0e090103020d021003060503120a0206060306010b0d0e0a0c06080115031b1b0209040311070f0807050405190903030b130903020c13020403060603080409060608 83
    0x941d13000316040300601801c5808840c1c00260000004180c00150404140100745440f00412406c2001c01d22031303400000d04c0b029501607030031a009030150600500d0403840700ea0a29001c980b036511000880c0c9800c1d03805646035a00d00000644100e1a52305110051b000301048010f840700f941351020324607141c001c002c951140030b41d54007040c6002d5a030400541007c690b0002400c6051952008003a140800c244500e0705507410075207109100301c0c401d204052900c0034003044403404c0803e159048401e4005420401240f00d4200241c5000d81d840301407007417041d0703c80e544a1081610744520faa0820b800396000c1d44031066143c0302404070b04030102c0c0030400d0b00c0d01540c1c00105640c42c142c0b81c5d0007074548200a207100d1440d1408040078164140c00c0079039000d000781e6500703c03c1002d9103c10011104002c10280c010b030001c98041006103058646c019141c802000c0c0903041a441791107000480704640c0c021140305900160070840c1a0f20f40c00b5a0000301302600304900545000c16803041e01441c005060086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 12822291 1250 12821041 12821047
    0xd030e01030621050105010e090a030309020402040b0d05060a06020a1104181401140709060807030504020f030312010e0901020309060708060607060501090209010e060306030307061125060b010f0e06 87
    0x190340301c0d40c03104000302110054484030444080030710010001c600d006449950030301001084100040d01c4641c01841d48000402003102c56403000c500500d02c4000481e0701c1038007080000703101d4a02e800039050801d9401000142c9003031100401c016990b19070301c0001550010000c25001c114180c01848400c07000b56000300d00040302c2002000c0b09580d10300010401c040000e91058040d1055011244000203c1c81c0e0009544030802c050f100320f1001e11a400002d074500b0002168144240c2001c4e8100d4806003808000390b0b1410f0009007036420200c0d03a946820b41c1e10b801040b1391010030003c5a00000301c5402145141000d24041d40c5600008055409100d0700001203980c0d80c46c1c2c8412a41501d40110301000556115540c1da0065070081d203102e80010003c95071400240b42c40c9080780e0040345e0080040d840c241c03103580c41b0005000706851021485406010f094070844c021a0f120410103140040640481d405103080c00840d501c9207200390402ca481e011566590307800042c0010790044c00c581031030b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 12823541 1250 12822291 12822317
    0x503070501210b0301020703050408060708010f0b0c07090c050a030609020702060f03090c03070e060306060a08100c0306090207060209011403091009110a0b03060a0902030f0a02070c0e13140105060d03 88
    0x20103044a41083c03505584001284000c1c1a840400b4000340d814003000d40c1c96980320031804680014080c000d0b80d40c1045614010020f5180800040c0b81c802643c6055031a40c0741d8415920701100d1080c8080c0c0c000c100300050800c10b040d41841440e0240c0b4a4080031410f0240301d40200c0e00350700481920081148002010610b000c0080041841c0a10010121200c840d02c030503e84002d010151096406489610b021510520f85010180b05503101d03c4e00600a08044148000c09030042c0b802140c01c0c95903600010031040b0807400140b400d00e001d00c01c0982d8130007828000500010308205100c41243c4280244030117800b0120f0032050344404520b02142e01002818030010102c0051000c992001e04000001070302d1500d50302643c45080103d03900e502684c1d446d800803090b48000c07070300380c1c1550110100040040c0b0b02c5038042c10700b10740034400643d605510b40400041c6940181d0392070504001d2880038004000d145002800c4810210000307006505003030f4080b0b41038000c004402001d018406402d0300c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 12824791 1250 12823541 12823607
    0x30406080705040b0c01060311031c08060117040c0e090a031d0111030c0106031407030c05060f070b070804050c04020702010509090405011104030303050a061401090603020a0201020f0708130503070501 88
    0x18002c0c200d88402151780743c041a80150081000784001c840b240d03c498801c494500c0d0100741c0841c3c20103015503402c901502d448046440030001481c0078144114606450003c29603081b01e103100e54030030542c4d00585800c00300703211741036800281041101d0f030050700910006507200e801d401c1c8442c17010700b41d4190b0b41c09140c01038550445c2d68000c1e0840e8440440c03400d4030f00e8015000101160300803007076018004026846140c4403211400083c02e0505074160030003039420718200030040302109400182c207000450307583c6030902c20180e55500019011070280414014103001a8400040c100d85c1149041c4240c2d00213485402008055441907042c007000a052000a4221784602e0502c2041e240d543ca40300c1c90041c008280a4448900c260718010000c96801016048081c278040141c407040e03030644c506003040380603501091a102c1155000e00c0659041300c11200039001c0103200c0c1442d292240036022101805042c50ba006620070b5100000400c60740e600f103040b01e06e41b1510881d0307001c00100c054cc0d0007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 12826041 1250 12824791 12824797
    0x80313030b0f160807120e010506010801050a081e0f01050112050d020a030806100c02060a0201020a140c0c090a020408160e070f080112020612010f03120c170703030e06010603020a0905040509030406080705 90
    0x184c41b8281845151038401748190300a17403142c0c400b41c0700c080380b5907229404c0c4181640c5900604025a02205904901e400000c100d820110501001c031000d0203000081c0368252a4280d0000100003551044081042024403188208003050b100803c01c110a98800604030b0401800a40c0504484000c00702c030544070300707665100c0e5a0080e100603614007540744028000e500c807076030910000701100b42c0c10700d40000714002c0340d5100c10440000d00014080303401708003c21001400c0001311aa0070880042d12035030a00c000c50550300010010101180740c28041083c0260040c9030f401000041c81c00c000390306400c000480d05448000c9480c20074041c1610108540e44501041446440343e41000041d19040c5001d078201900e10500c814808075654600c2600d0088050b04024002400c000024440800220141144d1802450081003044110180c10705004c030a800c038400280e000603012010541095505000705810b840421035440e1403030600d034603402140142c0c000c200d0f0313520224100b40e12641c1a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 12827291 1250 12826041 12826067
    0xc1101050c0105010b0901020c03070509011a0d0908030a0b090f0708060a0905011404061208030408090f09040605061c02030a08070c05130c03061a030a0c030204080313030b0f160807 80
    0x3c0100c4d585805072650355400c00d91400f40144110b0710710f401a0b0501191203811154058031420142c1d00340009450000d00c602081c00c03003041e080c07081c40003e0316035002e1811300034003502b080c0c0e5607403e00183c0481544d008100301030040d0078001c24401020841c01c002c2c1c3d881041840c00402a8071404000f902280d03807544829120b5003000d0001c00c0202d144184180445022101003002503900c0e424074110584024000d880300d2030610010b408608a0b82c001d01c4c0c05c04009015500a000c00f0002841e60700043c0e4040e00d0b01661482000581d040002451070403101ca0240402586440d500090795800c0b541001006803501043c01c0782005101034921014100041c000958010100c0107000180090084407000a042900c000340010342d4045c44140c022010158901e10381e80c4500420241c44070b01445402c0580c20400024014001d1000c0d007215020490010715035481d606180030100390290213408003805071014000c000b001d83c00d88030407200c1103091030845517840c1541604e440403032501d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 12828541 1250 12827291 12827293
    0x3030b0a0e06090901110a0f17070c0b06030f0d050d0b0a03050604030212030c03040201030207050f01020a03150b0307051207020705030a0c080d090f09020904090204020c0609100207030c1101050c 86
    0x40c0101c1c02032040310845108007001e42e0300b10020b50303580c0107a030b081c6da004103c01c100c2c0d0700c1c0800c0102d507454407510304002a843e4a0500c001f03004000c9035546018942200e000e8000760884e070070b07013081041e402030094001400f100182a1a0522000d40b0744451003088060140400000c800d99005691b811900c151440141440d200300c0e581c4c1083c1da110101200e08030010f001d40790451034500350312019a4007603440440d1160450791281c3c0190000c0d0300460b0252414400c0700241c1c030200100340001e1003280c28070f583c0840d00503094451800c02489540180080d440144200031000390300c20240c42d80c0380402a0120075a8890800507424071056420031601030107502041c6081c0010076030044111030071502107580a44214130122081342290044032511040300000708800f504940190903001e0005100103620320403540013400300e038130050142800d900304e6810400c41d00402c2c00021081c03544507005502d800d000c3d60300103081c610f000c40e0090141050a02250491344a0000e94000c43d604070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 12829791 1250 12828541 12828559
    0xc020c0a0510030605090412080a02030112020904150e0c0f090402030607031e020426010e0705010f03020d0203040c05100518040207080403140a05011d0303010306050601020309030312010302010905090609040204050403030b 98
    0x70400c04040a40c23022001e010403182d42c04904440c0180c402c0b01e0481e4145900380e600166103a080013643c0c1c20182c0240d9502c00b4415440e0341c6480c4500c52803166011000041c600948100188407030700e0340083d013007840b50500c50200300140e20701180c019802000703464002a020401c40c038000c0100e4bd183e0702c41c3c500d2032012501144442481084104c1d10420210810351f81078880401800e13141c60400e480001d0700504c0e8204001d501a543c115030480781804c0144c1841150f400c013108070380084a00f51a003900c0ca02c02040241403002802e040b000840c80d24030318200c41804291500c40858000078013a640c001506814407401c4030643d006150b1004500c04282c103c440d41d40d40d1445001c0d020fa60a51034040c0d900900b002c40c150581542807131001071030845e8a1501c0f0a0020a40109110b056020811609400d95002d00044c8108901d4405a04440d411400018061009600524000e100100901c6981c1d619a01c55580c41941103402107101c1d5035610301180582114064680c2041d001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 12831041 1250 12829791 12829793
    0x7080408070e0114010c0605101d0f0a050702070b0702060405040603080c010b0405070c02040b03010b06220801020a09030f020d140f06090c091b070203060a020a030c020c0a05100306050904 83
    0x841c0240c00c4502c038401c500142d9807100748041404401407005400300e44600c521200003821504a580c1c80f5810b10400f101442e900c015401828040c110800d260707a51850400849114000440d60000c4440d0740c00c021a20307003544060760b1481c09010748140c205020648038211354444013124050000070b00240405030b031300c2c0b82400c3c5540048040c00c450b0b508120815a290030300340316592195010741c0e95a800b010098080c440101410540300e9015521340404d20740d0794603110028440b030304291880b4040300240c1a04a116030200e50000c101a9004008420415034071440320400c1d6600801c524501032168030000d8012503070000020881c0e10241c000340c81084001ca00016903011400541e03625941c7c000595885909030301d4a5903020328410301040c403401c4815020300034100340104a9260100c01d40001380703400b800303c40e04070070113800189007407125038103001c0c0c0300d010403103400289000c0f280e050004144804500915010391100f486030403525109810480041101070090b082c10708007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 12832291 1250 12831041 12831043
    0x6130c03051006030203010c03090201020706050c03121608070306080a08030c0903010c0306060f0203040e0c070213110304060b0621060a0504020c010204050a0608040b01060503070507210206130c09020f07080408 93
    0x102e403100717a21951030b00c0e03000c0501c40e0080c00341031421541640541704e0036081070b109407016040b0000407a481c5c402404000a09542500154000c00802d002d001611046507401483e16800030054010581446410001807034000f414119055014600d60780701d64a00c9024421400b500342c0556241d0f08140780081c03003903050750011080d22a25910904d103949404010399991007107101c1e00607208094400a00c040c900311001d0724001388000c241da01182c1c440d080390415500d000682500480000090008021003840344244801040c0e603902e0503c280401023040010301c0075280581d1440010005200b40e4a40034040003030a00100215100c0b10748540550003034001d8040c00c0c0c0514140c071008107050303000f004400e00c1554001407902c5c075682855400c8955400142c00c48040c86400d014080000e045001c40342d072214200d0001c0e80c4e940f00c003070a00a15014007d0f049010401400c0d03070303410104071122044420b4580308900540d4410000360702c0400b03446900b40140079030602140200359440c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 12833541 1250 12832291 12832301
    0xc0905010f03060f091d0d050903070504050103020306040201270b0414010203040302030a1e080c0609010f020306030703030305150916030b0406150804060906050901020703021e06130c030510 84
    0x1400e9903081801c4034250000e4040340d800d805100940c4641c0c10040050b020544c200201c4a11410000c40c00b070384401082c2440c001001d402d03080403560208403103049080c01c00001000b0001105c0501c2207514580100348c85140141c000380c10041490303c20002c40040c2030030b4050158200300d00745d8a0305d42e10342945125402c603000340054141c02c1001c01e441c662000065500340c94009000d4032812403e503032501d1404104550340341d1140c0b404110400803c840358040c01d81980310780050700b2540303070100d9800e00710f0309013503480c85540d032062080c80650740b40000c200c002e41c0e07454100082c842c0c0300c00c0014400030f0b1041811652154901003040782130306200322040398a103115141445000c0f400000c100c2a54030ba0300483c1f866801a8410210061041ca18141c20501030100010f281e0f41503205c40050384d44c115040c1b8880e030340001d1410101030341045402405040301281441c50b800c240304498403071a01401e80300d48900001f01e0b800621800c3e0700c1c00e6000710b43c850308035200500d100303541c800900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 12834791 1250 12833541 12833549
    0x20903060a05070f110c0a0306021c1505040b120d03020a090608090a060c030209040c020102031b160609031106010305010c0818070528090f0b0a12080f0705010c09 72
    0x401640d0200d21103007540d0080038094855604c5a280700c10f0480c100f11508442c1e186403021a22031a00841c0440d150380d140e82d00514040c0c00d000d43d035014408200950b0800c941425a000307807410180603012103c0815030fa0035204102d4000ca0140d07881000181c0a0809000100790703801035210b240e442a030035600901c0020401d485400c80b40e0364034441520b089204451409803900400d19080018070340f640683e07282a0182001030420800703001040480b00408012800340c2e40c00800e00c64040005100100030440344100a441c2c2202c00700702524000342d00c0c50081c03003640c803080b04404040c024000380c0c2c0072004080c2161020340e564100940601031034150800411000c42c0405c0d80e10745402e1b18600040304140060900620700010b000d41b6240701011a01071030020312281c1c0c3d065007007405600c010251990080f9082a04619080498402c3d07101d161041002d030030100b0403000d50303511901095422074215900e90a1000c05880d182c03050b07040040865107001000011641c019509405070303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 12836041 1250 12834791 12834793
    0x305010c021f090204060b071406060303090a090b04060b1206150a0203090108040c0902070b010906063908041205060c0a0c02060304050a06020408060106020d0903030801090b0d05060109020903 85
    0x24285010790b10b601c07015460700384200b198428850000502e0304860110352003c0c0000402e141d032004070392043e40107158201d50121410390300c0c100603001008104d4001e04200c0c06180740454075030008259030064481c081d82240c0310300c00689155201d0f800076000b030202d03000083c0d8561120500c501c1c0c8500031288079118101100742c032034041e50120203440610815070010344c506040c1c84015a0760000040044800c031307400c6800402c0c1105240041d06101e8800da607412029410720318058240c900ba5041001003200580d8a909005001129900344030150110001001495540f521851078144409020088001400190718140307401d01c0e159240034400f951155155504040d8032440b6440c8120001490700d110403000d898039a00854020f485a003c8420622847d99a001681c00c10b61044845405c200c004002c025010301100090081c0f030f18000c00424110740d0058000700c810301030f0310a5980c0e00d0614800d2615144038160b00d4540010480e0b40b05e40c1d503030144201961250f06161b0103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 12837291 1250 12836041 12836051
    0x80106080d20010908130b09060304020d062a030605030d08070807110a030801050f010305060609040c0c060e0a1e081c0207140303100b030f06090405030717070605010b0310050f0102010b0415030501 87
    0x100084180565508c1900203101c18070f15200c903000c10100d1440c0301e03400d0380d89543c0e8615000c4107440e0056040000110003400301044604640003608546081d03103c1c0340030703402c40f960380300890f07900c0b02d407090f80034505050074000ca40301c03094100c8182c904458420458030492402c1028550071922503030403240101c8051904010030001107066400980da203c0d04035009203ca2207003881c00d6002140b80e0764052501580d00c0529072500d80c00d948a00141c4603c9400045400c01441009450f041c24002100d0050310850100d603181071440c03003a50504050a50702080d000152035007070301101c1c0f489411000d4480c140b20613401058581d88299084652020315400c00513a219241050701d105001d6030340501429600c000030301802040040086807540410801b403c00144071000142c4050003500301d4503102c03141890101d045403810703000261850424000c101d148100ba00c94a02900c1c0c0994002080450b080010317400f400c164542d1681c050306181c0000148928000b404007282d00400003442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 12838541 1250 12837291 12837299
    0x30a060504020c0a06021809011212051809040206090904030905030105010609030c0b03130803090109020108070c0506130501061701020702040605150304030302130308030103080c07080106080d2001090813 90
    0x1040340f1031040b00c1c03440c0740c0140c9007600c04190070343c1c090910001c01c4030702802003840005c001954540d090b0030040390202588004402c2c8070240308984000e01250400610304048610006911241d01c507895120342c05100005046496460030390301103c1700903020824504140c43c002d0040403080c014280079600c1c16000184040c45081d5000c1140c0d00114a0700985081051030034440c1e00041c40c03000b10a0182450074006209034000b14480c551510000415581620004183c510013400b014100714602c04107201090000c100180c002e103030100c104402d10000e03c0d04602400c1aa0b11503030300054003541156942c44190003c0940510842c2d041284585a4040040418906031940c1001400f4000140028000d50040c654a1038145031040c685549903104c030300c140c0c402d0f003080702d10220210310010458020000d040103011000000c0c010b450800c010a59600f074981510400c000312540e000c0c0c02d28010090400b210801100207100750000c1e414030708100e5002c2025042c0604d084c0b64001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 12839791 1250 12838541 12838549
    0x2010218031207030e0a0302060a0f090b03010b03070507020409080a020705090a0507200304080106030f061a0105090607020120060702070e07020604030f2615030102040315150308070602030a0605 86
    0x9162006440b9100d8200704094508461103501062180c0c0c1050400c003012000da0b075600e02901d400c2100c1d5580c9107400002c908000d20801c095800203403407220500052000245200c00d480c2d00c0310a0b0320700707030b0344a080a00018014140d030f240b0207490001c1c00202c400382540d0110390402910425101c0c1681603c075018010300b120021a0607000055078407444121401444102c56014404141141d05040e22407580c10300f10f603d140d00440c1e40380c05544404003006158040c00d840e015054001103014403142002800c240704003816944900720028402046a004200d42052111628125100540650000e56840105852950240c411124001824110f500080784a807a256011744620740752540e007a945030030107040003c2402483c803590442d0400400e0401401107841500790114100b0100c0750003068501c0003114000c0c0d00420044c404911401c1600d10120340911000580091500d011401c440c815040100160780010380d010034040290003a6001c0c10320207000b006000c0d2b540d4200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 12841041 1250 12839791 12839803
    0x41b1806060203070506071b05060a14060d0b0604050604091703010501110609150a0204170a061112040803090307020303040801140f04051e010b03071d060303030609040f030903120201021803 84
    0x28416401b03080054202407094051001080d55003900a40f29961640c401c1d0804030221507410520b5506c000c4082502703803a04400d60000d805654104501c040ca0b140d50080c080b00520740da0140343c6440124105843e180c0c850075507190852314414415a44065a4850341d100b84100b42c0001e44100d103000e1841d4000c00c4490041d10540c005080018014408441c01340700140b0810307000341d00380000158540c5d40306003044101503c10150240814034a8060201c0740f291020040700741c011b21607116510364401102e600641c1190302d503038580c0d40b0340024500c1e42c1b041882c001d400d0300022800017200e240541207036400754041c02510100c0c2c0d82d5640d101d20707118801c480c00340060b0f03c0300311154680d540e820700c84030011950000210742000817502091404502d50321980b00301e0702c0b021055030b111400582c529040f08084000d103107582024000070790190005400980b91500c102d41120805016980c0e807802540d10100b4070f626a42201000f9000b0b4100c1c00d0700413501101902a41440d240101d01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 12842291 1250 12841041 12841043
    0x206041502030c04150e0406030302210c0709020c10090c030b060d020918011409030901020610060c03120603060612110d0203030f0c0c030a0503070c06091508041b180606020307 78
    0x41400c0a150000b00790f03405c0d29807000c0c4814805034100b101c1c120b850364014280030f580070750014082c0480c0b0110004298600c40c1084050800c144003000301d002005c5200b0b0100e42504001617101d40e00c442c41207082a02c00800c4420451400300442c0801040e130082e2001c070380c0165040202c0c0d90f070b403400f4040c5241d01004000e6218512000244003200508d0211650124440001a2a001201448580d041c0a40d81c40c40141e002058403905580e04005055101c4d051400c00c1d04010b207000009058244041d000030144131030700c1103151020f60076500c410b009541000b01441566a5040c4400d080e02c0b00c0700040c0c0d01c1d8007d1840f4400d60381440e0b2200c1100941c068011854032007040c0b1790f40100c1c0c03c880741d0b4030304a001d07808401c81c1c02c4c0c0d420001411000d002e000555500c02c4d01e071520781c0c1c1c01c040b5640f100080c402182c070b041020001082ca144503003090341c201964980d0f52440d002d204074031500c20010300d0202c2281b020800b1080303801d054030504e400e214104030391929400141da80f40a1104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 12843541 1250 12842291 12842311
    0x91515180f06020705270f0610110c060a050c030a0c06140702060406020c0c03030d0b010201050702060702120d0608010504030c02010315050a1401020309030a060507030b090108061b0d020a020604150203 89
    0x5400c0200d4280a40600c1000d0200c0501c2d02c01d5400c0980f40240d405410303209500031080e607d042c848903180c0501040d0070a0194145000400503000070b05864400d0a0701d840c0c41124040b49d2100d034070b40140100c4040b00b0009043d03035510001b00c2d001802c400710810702515158901140d8092032140241628010440c1381c00915081d81d5903a6050b02070740c4500c1d030028684c02040460841c80d1010000f4080c02540700e1030100d02600c8072000203085940060446086600010030303c1507194011403030390f0101d211541110b0b910b406449040380540200d0b40100100d629142c1000281940b103140301095900c01d9a040c84541e0042c220000c0500480c0200b591003552940f04006410b00f00c5080c4555885c10300540e401e007a05080020300300b40e42010180c4a00c0c1c0c50384200f2002c0703603044c402c60080c1c42c0201c0790350426505240e22180d035202c0041810142d50300c040003c00e00c0c0742240d001c0d00d0300f12a17107400942d0358600e0303031800946407441a20111000e0a00040c40028a83e0900903680300341480e0b9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 12844791 1250 12843541 12843553
    0xa05010e07090e0309040905071503020418050402150702010905120a0203060a020c071404090206070c030515190c03060305030a02070905090604050a080a050f03010905250207091515180f0602 84
    0x9003040000e08200004071b88c984a41c0c44005407401d140082000c0c0351050780c80068859180c55402c144141c0126030100320b4901c0c044c10413005070707116240482c0e103402c0d01c000740341c5441041c401a0b0320386a064000a601c621210901480d800000404408091080e0260b8259443e2407c6800503409881d13120040f58001d414107001c28a070341410105174000050012079000020b03008504240d004080039209040c01403030600c1804410400343e0070314007000304c40041c03e14107080c40340c2070f00f09400500600b09031a4201c0700209446500f02e00b01461700941601d944c0c4010150207544d9000340e104a08695040c8000200c0b00350b000314205101c2d9420001034520510560b992075010392080d8015002c0c000305010300c0720b82a0701200558060f05070210300050130708110580d00c80e00840c80f015801c114199940b06014540c1c0425494204d441001003c1225a000c80c4496910112604418291000c031b03500f103107485a00c10386e4111342c041c50311a42c03080325441d0f000310140406540600c202581c081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 12846041 1250 12844791 12844807
    0x4030201180506060f01051309060f0f0f0501030506030307050f060601020f011103010e071209030c02090a050402130e010609150906080d050319020f0705060f011217030a0b030a05010e07090e03 85
    0x96410701d41c035131030b052400e546000f49800f4000d0406076182c114540c80d0b8ac2c0d685091140d09400c40c20030340905816a12410306901d000d2a11140c1000c0d80a118101511003000c9040b03920300300b01b40c0d88200da000c001d035400d140d0602030305507462008544850051045942d02e20081c0c4041c8500080000c025001d203245a00b48540c100c40307003402819400801100881c000104880740c41121204c0e03100b030b5510b10b00300440d401004015407015240c001542e260200303210050756003102d50b0b18a014820408556050180d00781070042802e41d03c06640e440c100344490200c00480844902035070030840c0b00b0400503841e50019580c42c807103066507a02040003000030400c0002100d9950300e041100300005441d04040351081c801c02d82028508031855403042062120340c05450301804c1c003400b0005642401c0a9017911404d5000421003102050360300f0010200319025241d400c5141706450207011989d103e0350900d0118020f09200c04843c44601071000e01080725000307400b03001159605000254101080c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 12847291 1250 12846041 12846049
    0x203070f020102032107180b0315060d0c03020306130203060d030503060d15020705060a0b0105040308090307050604030c030b0a020909041103070503010c05040602060105120d0c0303060504140403020118050606 92
    0xd02400341e05501c0148004040004455441d4200a5030480310100a04007200007030150401ca406203201000c0880f0f0074418a0b080009403a0720002802da54105001c401d0007140962140300844850682424220040c0030b0300754000310b005280999612240c64103030701451041b4082500c545900000184003170303000c03d21075005142c0101c401000c050740108140c0c1c0d40a02d035038140c3e00ca0a03035180c02007000c02c02d0000c2480700c550b0114240d00207100007805000024094400e0f03000003030800d84045506580303901c0030403a402c0540301c050310007581e0b1600c81c2480380595544e4441210040d0000e40041c15402d0f0900079102038050140400e525500d6035924107a15500742910580c1610400c50300107601e640c24091040640300710f4840ba551079060400090400805805c103d0295000f0701d060080114002501445140e592510307655a20907868124050304440d41f00e03e62141c2404907103003c01d040000203c2c0500d00c42c1d00204401d1990a0220000b402098070140050300300400041c4c244c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 12848541 1250 12847291 12847313
    0x201050703050304170d050f0709030302030906070606050d05010e060c07020a0311030a060c0305060102010b0319060519060605210f07050a0c0b09070305070b040e0a021b06041208060a06020307 85
    0x5c45840c0f40c8404c503028188144803030f001254100807141c0c569080c03141100b02c013a40540c020305242303412043c0c103085460180d80c034030812000c1e0b030045100080346400e001e403e601280c05810700822242004c0c0803414450b020381607001d84502e4034001c0c038010951140c044401c54401580c090300f460b10640c91500d41100d49020881c44941500070020080005111446505144001754a00059500f044c1c0002821641c4190010340654021a4030900000c150f0098400301c1e94001c10104450342c0b00c103002001c0b095140c4e01c2c00d4500782010701c041503103501f040c0502600c0c1103096107001d02d0b49642e00810b030300c0741040d40c06103107802c060320106024510450040034a51140e0801c44600100b581d01c60501181c00c5802072881e0b00009000e01c1009024001000204109000c1131b0815090040c6400b9054016104084180d400980040952016051850711301e49003000c2d00d80510b09130500625000219410000040700800068154944070540c501950b015500442c100300c2241e81c1c40790b80359 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 12849791 1250 12848541 12848543
    0x20705010509040e01140405010c020a020d08031e01060503041a01060e04200409020702040b01020d120504050c09070f030507030c02030901120204030c0303020f0c010e100509010917010204051207030201050703050304 95
    0x1902e8540782c4004e00424040c001201103413480f1501075262900704942141d1b070400100307085400c035002010140ea42c0c141211501030300700012650b2071300c0341c0080404511003031001d0f0320203184400000488540010140d48982c3c01900400860002c48848402c1c1500034055540861407120604045081c65070049c0040e0440481c56490400d040c800f09940c0d1300720381c0c45019100e40001e82c090440c14140580b2070250020b0000300542020800c01901c4001a12070b824501a0b43e480041c05000c1c5c01c1044141280c130140036002c42c1d0410fa10024040ca20404a481c04242000003188125100e842915040318841d800781d4100031845004580b000f4140c0c2c900b00b5420380900011010400742120700005600ca03400070450100088811401d007507a690b0307880d0511881c84208000c5803a45640003181c841245480741d619500c0c44016074201d0300c59000300e00c116031040b80e00d00380800c055008009881c41113070300f4000c4201c0742010955400c0c140c0002400540305001d000c00181c0036001864003d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 12851041 1250 12849791 12849799
    0x708070303060519140a0302010c020d151104150804150b060409020c010e10060b090f03030d0509070518091c0c0b0907090e01090209010302210703080702030106080706020705010509 80
    0x2240d9603000110480d600307144134085000101d10401c414080c0550018989500303440340c40c82c0c545140c0000c0c11074020f401d0046c1c01401d9054465040081c140d0305550305a0001004004c1c030305c035002940d030b0705800038006c602075003889440c0041500e0242d07924501c203603031201082e440103c150179040090000603103101c0e0451001e00020401d00b82c0383c0007504800d58036100002d600780650750f0272407030045101310812205107000810b012188400341142e0a122003520410b10405441c80464513500c07500418a02d005d150a00784000c401c0042810b40440b0b504030780203c5050402140f010884106031815503c65008400f44034a41c0e142c1a29241441c0007400c048001c005282c40310140f4810841701003000341c0000e42c061203442c1551044802c0c08a0301002040b5040382940414000001808080e100c0c0307401715070300007400f400c0d007140180c1c00c0c900000fa203070050b0340d27840d12650a0704900d0040340f1a5080480204500ca030028040d42203440603402003003054504001981c159100324402608 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 12852291 1250 12851041 12851051
    0x509011704050105041b030503070201080613020d140a021303020d031701060314070507020f01120b130e010b01030507020a111f0806030705010504080304180608070b0a03050a05010501050708070303 87
    0xc4103503180c0c864880c90007a00042040e20b414078044401081140b944018600c1c035000c1070000c10400001d49030842da0a08048441d511010001445804a824541952030000034000e00407000e42e0088107041c2c10719035900945845150a0400340d000c0e0304075080019801d12410070142c60841502c0c00b009000b81000480c0000c80c9a85890400d400d82000b00440d840c0c040b101005011000c45540c03102c49d510b0b015080ca0203039030000e81c0840f1400401c0d810007040d00b5041c80d1455103039001c074019200042507403925a030115007101c00740040e440107100c25442c041c0251190b5000740581ca07c1540075034050714131095950349046814000200454200c00342c0084208501080b0002c085621036945a0001c145007030002c141c0b0f4503c1c580c01090400c1000d00040110b6071000040c0c40a40d141003101600a2002a80110040115a101d803002d4422440006141990040182a444011341d018001d0b030b902d400c140c100740d45080c4201800030700c0800c180c1000c20a640050040c0074424900401e0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 12853541 1250 12852291 12852317
    0xa0306090302121c02090406030b18060709050607080c0c03010c02010b0910030c1206020702030102040e0612070b0d0e0307020a03060204030b10080304050108190e1c0305131b030f1a0117060403050901 88
    0x21402b80c0c00c64128982c08080071103c00031490030000c66034003034071720b142a05d03201d814900851000c3c02991401000c10f0004586000b4040d014000000300100180c000c22040c240a8002406800030f0500c0c039008140180100b1404400803c0da0307001d40382c1040105011f103140c40c043c5416200308000c2504c01e0b036400c0c004c24005a03001e000820003080315401168150405100704918041c0711075200c02141d010320400c00609010390155903002d440301c0c2d800603d0100c1d81400fa8114811010000d60042c4402c40110030004240e001d4420307680203103023514071503842c1100f46868414a00a5a2003030340140310803c62984900e040360392000072454410010b19035817040d28181d4040048a1009402a802c0908032084060000820ba0200d290500240c00c29201207070078280000c07805007401c040e0301d502e8102100386400c40c400555101034440c44d848814108104031014014800f2a0410300380300000b19144c80f116501c4280303212401404075515203950036078030742d88440d0360241800324003c2c500b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 12854791 1250 12853541 12853553
    0x9070203041d0106030605040207050a0311070302031002030f060d11040c03020c010c02070305060c070308150d05030a0305010303180e0601030f0605032b0f020d0507110a0306090302121c0209040603 87
    0x201d00b160200508144035410f05501900381c4002d46c00c410300451050004c0800f0520016505e0311007038050030526028006501241d081610907000a90144214842441101300c1c83c0e00a601c6180c00d441e10090701e444a0302041503ca0703d10f41c0c06086078030900c240c03030b84900c1d003030380102a40c030528100186890003070860282504d8500340001d0150300711010801c2481014040305a010002e010700714a0300700a0365014109002c080c1c824100d01103c01005041d5032945416444816041070480351926410300000b0003038582400f0442c0011442d80054005080c408860004d581d10720402c00c090356125001103000f0108400e04801260301c90000042685051000d030003110030140c04110055103e0b04181e5030205000e80708800c2000340740c3c4004602da40441d01d04618000c61a0443c1d6070300c401d0504020a2035101c0340746600a0b0354100000c104595680503170940d1b403190302514240700c1c4601450f2680d028455884c1c00d242200d40c040514155a41c1c000e02d40d594008000088c1c80d0340344d0f00d0349 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 12856041 1250 12854791 12854819
    0x21002060402010f050f040e0603030d090507060f080f0106050702011e0c021e0108040b0907150906030c03060b0a05090406030602030c1c020a02150406090515010906050409110907020304 82
    0x25800c03150900065582c041ca070308040c0003643c00c10a00c0c040364820707824803601c25407245002c1d0a5400c80859250780d03051040350400005250b05101441486c00c18a03207600040c07041d0804a80d00c810681d1866000740171142c030030784442c911030986030301e0300b9803e032195030141104034100140b490a030418020003c8500c60840441d81c2e4403290f58001d4410300c000740c0302c000d000325080aa18865644180c1e4031000d1a0382c0b050b400b02c540c9002c5d031500610315207001c5003600300d0319214141c0721240b043d40c0d81c889124012110240d90a01000c80000c4098003210000d00440e214039500300a07503100580244000c0c83c9081010703000007a0581e603621684100d8000762911440040700140c440035854084102c1c0d40c0069200341d04520307010b40340402954611880901290202c03028001a081c0800d0740c0c894461650040203890741c0b03002659002481c40300c01d0040511143c50b0840100d207508051050400180c1d021442d5460641d0741001c10208010007412031045110401011a400706003d0017 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 12857291 1250 12856041 12856069
    0x30d11071209060e0f1f050705030a050307120207020f121509060105121b01080604090501050708040209090106050607020d0804050a08030c0c06071109180109080306040507080103050a1104060302 86
    0x2d5803900e141084801011490f8100b105031090303203031811074091592000c2ca940c242c1800101410309004628009640c035001d20040500b680c0804551105041d4203c0021b511524241d0307100441040c603681d51404134018020042d40105100ba2816050300305400400108000380080b070726141003d4158828401c0112122809900201c00400090400040889084006a01400c0d2810343d44041c205043d0302840b10904114181c00880e0060710313580c2c042c08010360018001e010702d10340640043c11902c0165001c0340113030180c1c0000342d0031a00c184522429a000200f0751443c0c810150200400e40c0600d11003681c07401020040000c1075660a014100141049000303151034012a80d05030303003081d10821016010780700c00c004400000f0201080d220300740f0411512080741d41c8034040c0500c80032440d07011801d040d600e403103000c01c00d100c01c50003e103111360011101800f05030365510044405910a10005040c0e9010040503000148000c844000a41002d080042c00550f603030002580c40c109609 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 12858541 1250 12857291 12857297
    0x6111306020a0507080d0f03020703090b0a020303040201090e070c020103020d0204082407050316110f0105100801050c0708120a1e1a040b0a12020105040e040507170609030d110712 79
    0x10702d000800c80140302030b000810f529000340c0314040390101c010b41680404c4140100301680011188100f600801c0c266001c0e05400c01170b50740351030400f10065900d0784241c4050f4003168440a00003010545003094038861403c9030707510710340340d2802d40c01580a500303c0110100c0c6a03400b44070109110034100944640300c804802030540f00100081211304800d80030700312600300030080080025040c480c001c1c10707440043c3d42ca024803085a480c00748504040d41e56000303141365400c1105125000055007510420b076080c8000070066510b0b194088d100501c69004000d2000701c0c02d0102144d49403c2c1c0035140c1d80448c03550404154040703552542d01c05117220360300e030207582c1c0ea60740543e00460352000e200c041503100a48003007051010040006018120354481c80c440d9440e000442c408592044080e90020300c5030300c00b65030041c141854201c2c1c0300e00c0d16000c0c4460b0300f0707480100a80d28030720000703e0741d009003200d00c059881d11010070702c0c0030040c04820710500310f421400c111340c5000594458800c40941055030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 12859791 1250 12858541 12858553
    0x60e030403031e020d050d0207060f06060f021c030e0a08030f0f0a050907030615090203090307120f05030402090402040e030d060501091502120a140703050703091d040611130602 78
    0x202d40544000c0403a41c054401c3d4001c8030707030401c0c1260002180e5903260054200300da25400051240e03006449200002000d490501a084103e401c00b030f005403041d9034280d141c0c003c1d61001004c041b83d0300c43c0d4003030703000d00e180150010092840e402948204210b0b0710f40001c3da80308d555a03888680c0d503a0b10940724808070b00070040c200030190580b84003031500100790800c20301490600701e03812551032507580005000c0c1c580d210703000c2c54110001c00d964001400100030075034403450f10b81238131926074010391003c0d41c21002c400c107402c484c2d900c50f44032280c01d2142da40b101030a6440300e40901c41c0d40e12000f0000c80e00150f0b02c090b2280303400740c1000a08801e06000c0404140c072810400010712043c0d4961052078a8100c0d21b42900d01e094010039181e9152a0881400e51103d60203007044540803030070640c40000540c00908103050660000090034020b010f5107071911050b699100c0390316066041c0c48642c104240d550085000507015410880000410700c4c0000c0c10144584103031015011203a0052000d80c1c010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 12861041 1250 12859791 12859793
    0x90203030310050103061a0d1109030a0f06060602030310060c0606030c170c010305010b09040f0b060301031407060503040f020609030a061104140d0c05010f050409091212060807060309020d060e030403 88
    0xf60140344060030003c94007e40c4441c40d07007101c1e021030080000145101d52965241500f220043d0299549242c0080c1103c10b18001c60420780140c0ca0388020540e8050300b00302c00850098000811030b8041d2a8407904d140c110707450440c0884500710400001c445041d158030b400408968003410f41805094040c014a0b500c4243e901c609140940e1407454605150901c401007084c24100415a50b11442c1a41d000ca0503085440d603c3c0c00070160032604070b520050220000c801d203d8012881c050f440c003c1d030f007100c0e002d585074001a04c850004603802001070200350035410043c1444009021808805811165840d040c0d03566003042d642030b141d034402003080c0406c040201e0401c1302c041d5044c0d03403420788a0303c1038a000c0f42c680b019a6904c3c2d00a86042c05001818030500e144114116801414201001c200246051901d4412132195210302c03070000e034444405103031000b0307188904011038101c14001c203007851410f0815405489040b0040e644101c4d003120720700203c1c45501031180340b00d8140028503034580c11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 12862291 1250 12861041 12861047
    0x3070e01031803050301050402070c03050a0605071805090105010507111e010f050f0d0209010c060f200310090c02120c0607021203010803030601080604020702030d03060509060102030711040903030902030303100501 94
    0xd0264003942d100001a000109812800316815188142c90151b95400f03182001c40250b00c1c2035100405a10588980d07000744085540081d01480550342c034141a0603180000d800c07044e40300d0150940c000a424010001507024000409a4503c200b401d0b83e400ba00303040004002083e41c06d541c840404031411080fa0075a445085641580d80340e042c040e051500010208800d0f0292481202840350300146481c0305a0245910300250380e40010180600700341031100502030105c0040e851514405400744400f07503103040095912403101c0078251220705180c200e0405c0600140d00209003980251814440080d4206008110f170401c10001010a801d24110092414a201c406a050600140010300132200040b0860340c2010092030501965101c9a0002d0028440d55400960510440034140e000c03a40540120b0112641111003410350744e44d20300166103d00c28490f0050003015000400d42440c41d2640c09000c00340e01914000400004603070109281d5841910000d0400c044402c0070801c5681c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 12863541 1250 12862291 12862301
    0xc051902040c050a0c0206070c080a080405030118030203030a0525021c02070503030d0507021e0609100e0c0108041104020406091404060b030c03060d081c0e01020403050601171203070e0103 83
    0x19551805504c0c3c019100307401000d05283d250300030312400b00000c2c03403800e010000751950041c040c12020b0740d070070660a2034580040d41c130a1051070b01a5080150310710301d40c11040c01d40760380300340c040d001396103541d88503005c4100520b8010b1480303004030a00451081c4805200c0c520511443c0e00e600100044180450b0034074004003160030103400c41d0300145003409140c4000c02034425031b0102520105d0700e030b115410240e0906030316100311061040301420900c004e09000a800c2d0250810304295111529032101000c01d0301d9001e060145140e1100418085951040240d41d500030300927101d00000380042000201603a000c0d0b40300034001550301710240921000303850245080c10040b41d040111134a02000401e0a0200501503101c002c070200008003161a0640c0303c11986074404071a0f55110550211000180402804050717118509072001c403c0c08014421601500e80050051040b41c3c07070130070498640203000300400f03c0d40c00359510980b000ca21175005140103502c1902d42e552981076540005088030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 12864791 1250 12863541 12863561
    0x20102100e03040510030b0402160311010605090c0904060b070b0402010207080609070b160609030504090606140f030601170907051206070f030506010e0a0305010c030b0303070c05010305070c05190204 88
    0xa1420000340204000041107030f0482d5810b8402414225443d4800d800816400101940084c000203041084c0c8611410401c041482074a80410b400b08080d04542211075500440d0380181000020524804085000d04858071000f00080740701c43d03c0e40c2ca01c4c01c4603003040104449980051090008545c0c044c00b0a8010b003200c400100b0309454503107002a03494582d40720300c0141c0c2c1c00020b240c0e1803940d46600c4542d02241c104506000d189024600106568041e2144985651400c01c0210341c0b030388107201e080d4a46058030710242c14038044e000c100c3c0c0c080d400985802c2c140030b62603406041d460030344880244510410009000d025103000f06205501081103e1602c80c0e401450070401026003160b000d01000388507140c00540ca80ea00340c0181c8241903800d1403181e0040346071a00204100303054010350310401c8913075020300c0400d5062003032641d28014000000c204180d02075003801613500c680c1c0305690000c907918040548001c1911010308000c03160ba140000711016a842034250300302809810325074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 12866041 1250 12864791 12864823
    0xe0603070e0f06010e010e06160606080708150717010b03070210091e0503090a0308040f05060405030a03030f060302060412031805100c05010f020c031308010204030804050103150b0c0109020102 85
    0x1440c142c44070a00700580104601e060010f1044000c005c3d03481f820380500c192002500a9030340fa100e164100085402d0002d040314035a0038007070049007151003c1044405c031201c000003080c41e0109000010100d0500610280400c4000c0e86510b600c40504444a8000d10f208e0307600c1941d034200014020705010200029828440c28904a500000c1d4226444044803074052429042595645001405c6214003032625500804401000c0280b091080041c41110b0840091070300f056600c005104481c01180b01b11036041d00089204070120f4066007007941a0798660300c0010302903071282e002036583e420a41098405003802a400380406820955502c07001c041c0e4050341d10322501e40400644030900c4044c002c0300300031320900d68008202d030941005007550240181551904180205e040e501d03084040c4851241ea101c000000c0d40d0b886c18400c980c152078000c0c02e560310300390600b00150080c000f2012881d2448034410b4001500c1c5410201408000604c0c200201c0c040700e5500009140043c0c400d550650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 12867291 1250 12866041 12866069
    0xc040203060a0b090102070b1c0e070f0e070504080d0503010509060a0302090a020c01090609060b0112110a050306030a0605072006130f020105040801060e010e01091503080904020906040e060307 85
    0xda995004079001c21549405289541c43d084c0c203004070708101e51030b4014a003540740424104100c7c04034030482c1c944040049020411002c1c11454103a40b10032a10500080d1104035400b40480b0b40c4105280303501500313a0408034501642d8410701c82c07800080440b44000204c0c040014001880c0520080c3e070012011680240c0c01401c6070000364400030b000d80310070300c03a80c1c0c0000c0e5030030b06060a42004184503000001040348441c0c50030414007900b80354014070b00113070304158550001c41152090301c1d081300300c080b0100e080003c0d07050150707001c0d40041d0039a80e15200d15018500080d00d6405590b04c505002c1c1c4c3c07003075003002070000340001c0000c40d03400002d8690070001c104442844a00b164840300384d080701e90460000344500050301e0314481c2da042010300b9409c00801240813510800c2043c104c4540340b00c54452aa6900070038400c8414141c4814455149048100003098842c400b8003180800240010302d0402e00000141003503001d603211254100000c010422189001c3c05503a0050044c1c40f41812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 12868541 1250 12867291 12867301
    0x10305090d0807020703060e06060306090a05060106080421030f0606050c0a200607050d12050f0f0402010203041503050109140112080310090207030201022206020a0201050705010b03060c0c0c040203 87
    0x18661010000707a10820603640c0001d00194401c1101d44029600310508111702ca9000010686464044403001e010b80b0803000400c0c5400800a0403101903608403000d0485a408e01800700d505020140041c0c0310003002c030210385903c420502071351103290115100058104002000c0405803643c0d40e2000c000e00405000f0120300800100d50750200310707480066500d01c00ca5005c4a01c410036100c00015401080100d01002000741c00507840c1015405519484a40802440b484e419107004541001c1c1d000a11341c081400c00c04c041501d1904284140196030400b40c030f801c415400398200c0f0f003004000a840700c2c01002042003910034240c451900e420b00d1155981030008070341c00c60030032040c01024114004000340c2490801421003002d804000030541da00c10f042c0c14028040d4224003440c4003000d03000c070300014130f80401101001c00c0f11020380262076034030640d80065900380c1002c40152031719501d0300f05041007940d040c0022031054905240300c988861007541468604091401d1744c501a52041080c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 12869791 1250 12868541 12868543
    0x1090605070e011d12070e070315030f030f0e040e0a0c080109031407110d03030b010e04050702060601030f14040302060415061202040207080702090a06090c031a010f14031303080601030509 83
    0x19950228524a07403030500b100f201041d49440035a20208460096000101d450340702c2c100228003c50a40d41c9c240000c1c02400a90702c1904c010b440010300503500c0709041c2c00028040d8190581e0480d10303080506516500402117010307600e0310000c10015420105040c81004101501c2d0740161001e00f000b00601390281e0b4010b40b10303681aa10b05420700101203407040c2040070300040710046500c0038080c4140c07650507282c040d02402c001c220250102e001010004001d092500c102071003107900340d00600c5292564001500104192100c10901e50780390070044024520b10f801d103a0180c2d2296008141e54503240c2404080d0f43d0a1941a01d0100c0c1480700030007524058103e840070480c3c048500681e02d0865240c61200e40c4600040250000c61440070050901000d9014508a84100301e0034004170390140c0e02241103d00c120582032004803009100c41013944030b0075920071a05050304001da502000200d0b0310040b600f084a02c0f420301681c80c1411400c141d840803000f07400080c203007010b2016007803002c542 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 12871041 1250 12869791 12869807
    0x405060103060506120102040602010b0a0b070b01060e0a0305070e0a050f04030903030513030501050a0507020c06040e0a0f0605060c0109020f0d03050702100302190201060510080705030406050a091401090605070e01 94
    0x15003100d0700c2c3c1c4082101e950f103100c5540b40c2d0000180003190b80d19510039010b80a4040d00381218400d000c402c1000450790034500440b07601c164048103135a80b51b0308000741560741003030b01c6240341e8106036074010210000700100985006001c0e030740680b00c828a025083c0e14107880e0b0051100c02241c09000c04d120010340c03c6100d0a0a90b50f044c00c090752960b40744413100c1c0f160f81140d800505907600700300500c4100c0d10075a00030b5000f02055825a40c0461284090014a118a00c1401c8455001800180f010030051f4010100e80307036450f2021600d581d84000240e400c3d0801000e403003490b5900d403101c0b0704602e4035000151500c181945d5400c4000e1150b140030301075000f240c00181c05881d40400000c80301d4400e504907140450240d0000c2c40481c03600100a0007400180601c90280ca50020f0000c1600e000da521248141c0140c0d0b40d243c0307103540c3c039903a6201901001c0c124034800d0341c5a8607020b0001e100c404005012200d9140000380490007801d0000c00c0c2c3c0c4025207101b0620140002c80f0145036800441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 12872291 1250 12871041 12871043
    0x120c0b040818040216050c04050712050606040504092315070e040f060605070302010510120807030302070b041410050601080a0b030705060a030e06070503100603110d1a0a06080405060103 82
    0x250768a038000e200c41001980e004662541e07106100040b0607010980c10711810504900850440c2c01e00d21290040c0000c80b10150354100124031a00c0140346010702e2500b040b03600c00809001c082c02c084d034071008502034030705015040b40d051a0b0f040d41440220840d0b100c0c4195100500001d18090800803201c0c0c2d40c0002c00740c001420084404c0300000c0d2034640b500001484055403500300103007541c03101c0040c61a0801c103000c41c0194285004603c0403d12014245c00740c551001c1c40020b504c51503a2140c003113912903507003107048c913400740203150205401e0804039100e03901410344c0d0103451814981d8541031001a0f2400d891a41c6400d06011b42644d10510b60b50340860080c0b000554850788000192034803007503500c20380d40054001101003405a25030001d004841a900480341d81c2e0b00ca07003d095a0700c1c04212085410046000300070410b0071302c80d4102818503800fa00f541850044c80740c800b032050f0b800b80881c0003c803510000610303920741400d8240c0c1005044502d4003c030342c6c1c2051f40e644c1d6154181840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 12873541 1250 12872291 12872303
    0x90604020a05090904060209030c01081b0918151002010504050721020604090b0a06020a03050304170405030f010b01140405090a050702010e0d08070305061f110c040603050a120c0b04 80
    0x118103103114020341c100c43d10520014070089a9140a280c5907001e540072480690290089882010042d401191000d00814000500381c40000e1fa00c80011460380200003540d50184165000d1011015403424003802010b05900c10328141440300e06101484014520840840e85401c0c10003001c500d0100d405001e4900481001c0404000300301c05034044403001c04043e6001c1c5d800078000452440f60b030300c09422688240d401b40341c00b9980c3c48003030345c5074401d010001c1c0100b48200002400103009a01c07101e61005298501800e0944400c0400e00c1c2410000c0e03800f65a0303554801502041d030700691111002d00510f26114600f90504020800c0e10300041d0021003655110804a51818000e4002c04080080b44045071070030124490002d1101c00c00b5100070011918260214000d82411210100d407c4c156040201c191500f5850858000c411880340c0d20700c82c000c0c81c0d90901103603074034014140114013440080a1801140c20300340507003901040c040080c011010000300001d490200366940c00340d0058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 12874791 1250 12873541 12873547
    0x102070c1716061b0501020409111206060c07060c051603050a060608060106050706020d02090612100605070b0f04022202040e0a06050120240106020607020a0201020303180f060103051f060509060402 87
    0x105e0007501a006030380245840704d091100e104600d20312180546401c1e150309041500030b84540c402d01000788148451000180c202e00c20500c0640e005440c010a02407103482180ca208031070110300a0554041c0e001100c01d5085035600e2070a2207024005c4502401402014101365417412401908a02c2484070040c00203030042074040540940364140c80381040041d01b466522020407a029414042c200c903c400058861100482c48034400c0c8146d8920542c010352400301929018034401d07046034024400c80e0300200700d0204500d5403903403c074a0314001c000c4400c00360700d850800c0021880e00340010700301107040346010300400181e81d10159110309054440414461034070704400950600c12020500043c82c004410340500e00100c103094103040340c803258203a0b6101d8440000c00c0341c56007030341c03e00a0b006034014004200040c49000c4890304001c0c00404540008400b01c00b070a0500c0001d031300944540c1c000c80810140500c10007444105504410b508200031400e040000d2418a0b010f0b1507103000315808 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 12876041 1250 12874791 12874793
    0x50601110c10020f060a061a030402030705060912070603052406041a1e040302040e030310090b04060915061403010e01030b18031308010f0b1309050102070c1716061b 73
    0xe01c0000c2c4c00210410555100345804010358000c0c1046129081007040c1808454a00304502420340f80101e60042c040d0078102d00d0180ac00040d600840d07400356210b1034170513800610403010002c10f00202550780307000c900c1e8502005556656581444d002240e080180780e40d051b00ea880c103049405032104015485801482d028070304000340280c1080400d01e00f0700d03070a00d840c203020040240c000c0340d100311030a21201c3c1411560946030700050342c90407400301001c902405a24015008518900000352002400320fa503a00040c083e40c8a180c806050803803100414007038558050513030410800550240d500c2c6500d403050000784000705104c06040c007044140400e8050b07240940c403000c0140d03441c0480b61241c20b00c4040c0180e60a0500c202019903281240c2140945000e000350b800c06c2900902104005c1004544040900b0320742c041200e89540c2048031800144000e0b0681c0007070b24407044204020110008111315258951001c0100354442d403c041144503441050081c81000f5086c106800c01c0726 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 12877291 1250 12876041 12876043
    0x8010603150f060e010807030203100b1f0e040c03050604060501080103050307120c020a03150501140d02010c060605040e03030403030605010804080706090201210b0f0a03050601060503070905090f010801050601110c1002 96
    0x368000300600940b420001646d440c0000d403200613240210140c4111041602101c411600c0501e003840d004859184078205160400003d0b00d02c0c1401402c08401d203102400c000307000c907504607501c0320101c0e030b682c0c1c10b1041c0c03410684100009842d003030030042c0c590b506684a0955074021070318020110031142c000d81c02c0c4030344181c52103105ca50380500344004503038a80c03030b084669080d14995062210301c2e02000055406900c0d030100350503100134151401d41209500112191114902d0a6810b1600c40340000344c43c0c0c54500c5000079490828000e19180c0c1494540142550030603404981082000414040800c81701d41c1180c1a071684044c0c009070032116840113889841d00d1185c0e0140440600003a40604001f541103403011080455094003c0305100c0100910810741c0d00028105a001000500025029100540d0800114100320046a42d918005481003500b05e650054000b02a401040100d1090282c80c0d041030027402d000c0907142c40c40c104d03166100710341311050348102c0c08075001329a0940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 12878541 1250 12877291 12877301
    0x621141005010e041a1b0a05041203050a14070c05040504030c02040509010608070b12010308031b0712080c190f0c150c110a0b070c080f0d09030908010603150f 70
    0x802403040c080c03507a541d1409031040e0401c40b400d8036659001c41036614289000e0001510805a841d0940c00345541a03500400f15003100305641c007805010880485c012502c20300c0002014480d540b036690b00e81c0b261000414000304441d070760380d170f81809004503000644503440b000b059031410340e40003c140d5240c0c101110711180a00d00079400c0340c41c0c081400407031501900714200356a241e5003190b01840c0c0c0c0710381c5000b00d4411204040c1d240e15102d00148000741080d0010350300b0150103080c14800c1082c4044115aa07031001004444240400c1b118080041d0042042030b400a41000881d051005281c40d803e544011a0403400c1003094800f511410607000c0d1010807513154200091021001410340400000c010250148001c0340b0b044040e800c0340840003d80702150b070361210008049803250a02641d9000c142c210846000c6000d10000130b0514492020300401c0030301c0e074804660300e5414140039102c18115000f12103140d0501c2c80510105900c00949074070000071120000d0701c0cc00048800c80108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 12879791 1250 12878541 12878563
    0xe0d020c040c1b0c0806070e06090d020d0c08030d0b01050315010e01091a0c01051501020304090b0a0e07080601080105060906070206090604031212050906061c02010201090503040f0603062114 84
    0x3500c04058405001443c804e00e810b0b9a041d0b0200e40e080d86482c2130980d03c02d03814040c2d03181c4c0110200103003800d07410903d07a100300e100d1000c0c3c0780810310082903a914040b4020303038210154a6201140640080723486001e803040314042800c000b40f66003010348a5071748800040c852141844280400074006900c2079a01000409440c4140c4401280c0807900d49400c0d03024035100f0170705600700408500c442104511280104105070011840c1030716101c8030030050400d00441962042c2c01500000740c6800740ba0b4102d11841040d5540800e030301d0800c00140c482001a0800f5000b40301c244140001034613000c1c01c0301d10464040381d0040d1550442000130f8542d00c100d4200418076040840c0d003500c0c41c0e401008910007002a00418021aa10030380341d15562801140c100d640140700040c00c0d151420700c1c107a5140d1142c010b200103d4115004c2d03c03040d1660703000b640300440090300c0b900104140e0b6807603c54a0003401914a4202d541e84d10400c03880d11110700610f02030071040010f60007404071501040101801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 12881041 1250 12879791 12879827
    0xb16020d03050c030601210203090c01090f0b04031b0e04060903021501050306010911041e0f120506070807051201081c03060e01050105030717010602060a060504020702031015050301091202010e0d020c040c 90
    0x20340f5050ac580e03511140004c4400d400b0070610f80012500c1ca030b80d0706144096074003a140650500e1b02d076840305c5d9a1aa812402d9041207040c0d6a004075810405800087c80349005100201c0c07040d4003890000d2612216100c8032400648800050140782e40104805c0d0441e9405034006c10950700e25456041144215404200c41419900040302990f60a248100c200c07003029207101c44095643c42c10592108003007000409a4105400050402d809180043e400a480c0c3c81d10034141140c00f03018020400d001e0304082142e9005048084010000c44d40f000381458007480d003403000c0303858008031009081c070600031b40781400720200000b2403152242d24054004081c90465699650307541002030344802e0107440c050541c3d41403480c00719250805000f140c011540c09002007680781181c10a1100400410007030001082c42c034840003803d1740e424003406121724004c46a205088046800181c03c403146642d03805ca094101026680e466500030030352050981042d100454102c900c520111848081e8410728589 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 12882291 1250 12881041 12881047
    0x227040b0a080601090606020303040302030a030507030b0402070c0810090201090302090903091e1903020102100b040b0a03030e0f09010e0403080a0f0f0b010f08010b090f0d0b16020d03050c0306012102 88
    0x10b1442c002803650489001e24020031469895402c101d0b1244000c540240142c6d200308843c5214a2003980617960140303451900107800880c0b500018143d912084c0203440b092000039090040100a001440141103c8402042444116800604940028400a403150321a00d00003025144140110798402350300420480e0040000c005c4103012810320740245020300d030a1044007000b5400f03c0f400c04140da4058008240026084d414a805441643d904a0700b058460070003115a0700c03080b150b0405580f10362a1403680c2c20304001442000c103a18035006100d00348a07001042032020221083e0b80080c4c041c80c1015850340c90446a401802c001010306e1819803800c00e088251b02c0e925400a01c030584243e98213050800c0c1d41100311437480d030a01400c0c007051001c0000c8065890700e5081850380311030150110442c5d140c1515069542c0e81c1c101c8810700203071801c0e805410496810301101c08186411f040c104114100100d08004a00000341124140940d00d100e45100200451040c2022516948155a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 12883541 1250 12882291 12882299
    0xc010509031905130e070e1507020301110f070b040512070b01031e15020703020a1401051b0c06060913020405070f11060105060703031503080426010227040b0a 70
    0x95a6440982c0e1011600c0c1200080c107841032059084941507501341d424202c0d0346041040c3d940b070180707002d8101c409101d0f1003100c0040039220b030001c80c2c16280711700c2030321758884540740107050a640d184402071b08088001c01c4482d12040541d019101c00c42d4100c100340300c4964503803429500c0c200c9507921440403004049900820042c4261419040c0c82c4a81c0420b62862801540c20510580405d4000d1490821200c20607c841d0340e9400740c080c0d54000e1044840200c015110081000c0e000d000e00d10b8141d44400400c02c100055000e15101c41c015000528504280b00a2440e151040a016a8441c00074100400c0e2030f1b016000f400890941c000300208480d041a0102a1882d48080d464001041e55100c1248503c00040382c031504844000e00414138024565408030020003102c0c0c0a071078900031400d000700108907490090300142c9a00d000f80c55104040310150300038203041c00303400f181c96030042003e0080420000320301e007104444102601d000512035400036010340f0343d0800c61a003004951300005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 12884791 1250 12883541 12883543
    0xf040f03050606040b030313050f0f09090105070915120506010c060c08010e0604060f170f030d05010f050a03030203090103050c210a0e150c0c01110a02030d062102090406020c010509 80
    0x98022481180c0800c2445070801c00e05881c1c5c000c0018016910004000421050500170344003842c0328402800104d908402000164133040b0941e01030009079501d00c10009c285030171142e0413021700310865600800b5005190300900300d00501c00f0b401d04031500c1d0310114001c0d9014061200d0400c0d03124209001c406039001004010400c00d10030318241040441c0894840d040512503c0d05503548168800265800c000d00c2c406c0802000541d08210f20a4224110240400f0700151180300d81602011425525200340b404d004070158011501c506108013040000a070000203c1e81d400d40203013008207080c6d9812180d41c40d58000d03a017a03d01862500d56001d24100c20301565107114603280714042002603000214543d480441400103207064000c038012403401001800540400c004200c00414010101c4d44492040d4000309403c030050b03032010410141291850007000301814002c403e118100307042c2c0c1d03070b40108441042c01c040d01401510f0301050034032034580c044803944c10020009001c5030030402001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 12886041 1250 12884791 12884803
    0xf04090615060302040f090207051212070806010201140f0601020a06180312060609060503090c030a030801051e030c010e0d0503070f1b0e06011209020d030203031509010810020f040f0305 82
    0x404809524031002140c118001c0c0301780e9040e207004482078140d80c0c1c1800070000007503100007000c2e80c441c40355240600310004500000c10b03110728070140241c4d030390901030000b41194a01070312144c150f90402c2000d480c403c0b00c80100961008200700446102e881d4000140d00b410f2002601901280c10080300c4c85034005000b00c808020340c030941d150340d00b0701c1d05441d1244c04c541c4140500c00019442410030031002d481000551703002440d075001e07201c5283d002c0c13001a18106004000324040760780480108028a404552210110032929011b007465200f000042d85403544a80003605014190401080980b40c502102d404658802e04481d0f5410190a21220b0000012011030f24040b5a4150340c032041040980c03082200d018110140050b21803c00541d4880d480bc00d4400550340e80c1c21001025940368a0010031060181d00a5652401d201010150701d8004890603805007080400400c2141030000d503100008010040058407044410612a024412a80500c610104000002c01401004523074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 12887291 1250 12886041 12886061
    0x3030a0e181510030b0a03080a05120403020606010e030309010905060a02070902040e15031f0513020306160305011e0308071b06050a020105011d1303050d0c0507060606020f0601090b0f040906 84
    0x101503103401c2000011405c0d60342100e0b07190b401c50b1405108100003102d80024020074030300707402c24a080403800a155110080d080341c042d80141d121030184411540c111226005040c801c2e0003031072405984c40000703840c002c0c080c4603442c01441c00241e000c400d10f10a02c00c0d03c01520440c5070a566a03550341316014200c03003096490700b04107800a0300204940c80c002400d030b40c40c0e503985918801c00c0005034082c0b03002070030010b21a0b43d100c3c40000315403005a40502403148200744031003060307509030306c0100b000f81141e0050f0400145210400d003121505d20903034003443d04491317000120756a2141286416060520000010369400d0b000030004180a60000701900f101c1c0040d90003040141c0c0d07145243c03c10311400c044031000c04100c0e080421504641a44000f00b003900a041c1140341070040303e0900d040f2070324112003000188020800c101040058003440c0000d01c0f80d40b008090a01800e60500d444803010710982c03c1141e656015852507841e009408204100010000c02c600c0c2c2c49030800384081c10560799 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 12888541 1250 12887291 12887299
    0xb04020c0a0c060305041502030403051c0515030105010803120c070b090a060515060a050c0a1e050f0a020312070311030301030803091c0f030207060212010f051002060603030a0e1815 80
    0xc4003040c0503104c1d02c101c0c3d120b542c1203a0b000c200c00011441c8040258006803003030b010050308010f140030382141d065940c40c5102040c0d40008240c13030030843c0708800c01c0c1148c2c1858400c3e41008010060210b0010998026900703c0300d540842c0d40fa291065640f40c865442c000703106955220800001c4600411840349081c000c4100703001a5440c0d03c00000320100741503a59500007000d000c0f440103140f05a0280003102030440440d403100451f40c441000c940501e0503600c000c0803422209008001091000f4001c00c2110002030500e40819030000b510340c0117a404000b140080800d80d001410b04c9030349242d4600100c5402d0340d640c0d584034100a01c0940c42200c12203903c0c4070705c040140c8811034903180340014454540d0360b0504080c403240101c019500018051f1180d0b1740902008410300b4800c03c41c2c60080820049020485140405025040018207468002e54016208101d0903480c0441106d0041c051403810b0f4401d200a140018041917410760780843c050585401c0102d108400d6000080540c0111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 12889791 1250 12888541 12888563
    0xd050a021002032b0e070b0a090f05090705030408040b0705240601020a0204050a020903030316030501050105070c0909140a06060501030e030a20011803020102040501090509061011010b04020c0a 85
    0x71100380c0c2e41c0c2c0b00d070f485800c1c10b02c1018801007161900701884c45506455030b400c080b4403513152010152070303c00e058000c030103507070340c0005e2140c0c12640200101c0000c2062440c034082c4a441d2900117041c803032008240b4010b010000000604101c5040101d80146c01004800d549400c1203080c000da40320380b00c0048800083c001c0c105c5c800c40d101d40a9490740700c3c4c00140e00a0078044500d900b0300c80030b4240070b441924170355020f1066101316507050000d18820440f0a09040c0d20417112103000302510310607403003507043c000c080252001041161040348140d0350840e1021954550030701d01541c0507800280302c0c2841c2d016402c065003c10095070002d0b02251001d980038013030000d8200b8410b40f43d100c1d040c0448046031448051410a101000311090100100b000000c0c2c0d01c140e0308240c141c14000781d0700c00c0b40144d6000800788174940c1c00100c040302406081d01d54900d60b181c00b0340407502c054554404075013481208000c2d0f9080030006d41000d154005c02038030079900c9509100781140e46a000303901c1152156000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 12891041 1250 12889791 12889819
    0x10b0708131d0c040b090d020a0f0305030904140609010308070c030602070809030c0604060f03091a01030302060708010e070c14010b0402160c050906010504060f05040801050c0a0f02010903020303060f060403020d050a02 96
    0x1d0284d40540e81d00b40d1800349841c0301201000740050000c642280c0200b011400041c02d0740d007019001004500540196644460303050402c022120303450002c50b12954203409000d4a0b403503500c0041d042d00c0c0d0040d025550760000d8105031118083e0303540010300c168000200d1008011002026000c141c2c415003c5800149000c0c0401c24240518041d02c00040c105042c44030035144260010600f4034007521034942d041c0b007109c03150340c0c500800f44c106030096030040041c05092580000c2607401000030313601d80006800e001400500d40141510040c026810034800c55400110032341c08042c1542000b882155210780c6c0e00c0102200c0f07400d80c002502d014415000c0040c0e642440100e052040740140d450a1800e820150141d90409021900c4002c000c1c09020208940c1d409104a50042450700b0302c01d602c40f15070701c90080c0f2029181c10203074116414031410030000303a00041500d42018040780d00861114000c004143d07a0300850f40040c0d8081e8100303880005118004c100c02040c14020755581e01c0c00c1c429 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 12892291 1250 12891041 12891061
    0x50102010f050f0c090a05041a1207060c02061b010906061805010f0509041505070305041e02010c080307110307060204060207050901080c1c2f0409050303010b0708131d 74
    0xb03e074800415844400001d9011952000400c04098020042c00b840d135111700c041401c441246020000c21945071000203014a045010704c0c0070b400305007005005032030520000901020301000028040d07140804c60042650507488240c407401100030003041041e2190070628007401a038403580c0c0d014102c0c10201c20302d40d4180d000d0306042c0c5107002c8440320b45500d020306000c0e508200600a441081608143d5074201079107019442c001c5142da50b0100780381c00c26081c944080344246181d00c02a03840a02c0c41320051340c1007003a41c040584c100d0312154499503108420b880c842c11562040340280800500401041011b5000c0c100760b4520360308558040b515002444501c103000c2c00340141c10740c04150107a01c689000c0e403c1c004c880e41d0610030324118100c0e913035448144038545002035801e481222503100120010749000348028a04035401c0c0031600c41520746544901c418000c5400400c4009168014001c00700101c5403030410032448014144d80d20340f4407201e83c0d1040780c115101c000a5001040748410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 12893541 1250 12892291 12892301
    0xf080106020111070f050102040e04060506130204140103050402040e070305070f0504060f0e0405030906040e04021005030c070605090304030506010e070806030a0c050607031205130302010b03070303020a020603090a0803010906050102010f 104
    0x51103483c1c1e1850030b0810340b24400064030701c200895080d9003c00020030341c00410401c043c001c1d48a07680c085510300b81441003046c1e2141c402550038159105010821070a1601c0843e003001e07032020300700021035031102c2c000f08028207036100b1080058400d90740000100100010258110f40312510381210003070b16441008241c4509125502602c40103420070f1000900c4003c020760414821800c8a14008d0958045001070700b241d0700c80700404560408200541c285100c64261010307580c600240f0b146080044502e45024886000d01001c0d038480c00603450740070410440f0091030b086021582c03150380d6103a00000903d4100c5000001440800c0402c405040000c0c04440f44c940c0040034048450421040c410079420903d816000c0214003100c205810003a8414240514103e101e0307900440c1c4d0320306002c0d00351070110111600039800072400700301090340825a2448075a0446480f41d40e600d0b400891407408040110150903c0800000040c0c41c10280d4084003c40350281c0080c0f0400035200f004070300710b42d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 12894791 1250 12893541 12893561
    0x90901050d0b04080c010b030106090e0115031e11060f0702031902090103062403061b05090f10120501080d080906090d030506040603080c010605090c0c07060509010509100f0801060201 81
    0x40b00300420001071003a0041c220710880341c0d000045e580f640d10b0010342550340c1603000f900da181e41c0f080042440d803400e008012440c441d600314030002c680b6580d0703200382c0400e12815401c0000071012540c0d00700300e1181c0325040540c0004100c0340e1100c1d54514501c1055016220491207880303510320404041041c6a00301c0800d6800600d0749080e030f0f1950322503001511107080700d19100b4007441488440c001c4480d01d400702031030050f640007954071807034117949503903d02126030b1600b400301c184030740c440640e00c01012001916003034411016400f143c210541d5008180040c20801608080000c03c4031040081c1d0b8255144241c0d070f0380d0100d920356804450321b8550039100903082c0e80201504640560198005a40001018100041440d901c0e00c1d099560f03001a80070385d54907512643c5c104003520700f40b40d120b074111320681100b51070203034043c9006030784100900c181e0040c002c000c100c80b2080e80c01401691280b942c0035080c1041d00312540b03801008610004410000b0802a10021500310302c14850aa612 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 12896041 1250 12894791 12894803
    0x130603060f0b0d150b01111501090506030c06090f0105040317190f0806041d01060801020d0c0306060512190203070201090b0c0c0a08031008030a0504080709140a0f06030c0b090901050d 81
    0x309000403c1394082d10410003114140a461040c9900545040140480544100c000b814180d4103101c00441511009440c440c031030f921400d80070550303689550407074014100444020440e085541700513680d40c02141d101601074202d8031200f00f40114904020041e0348180d18035140d0900b00088182c56820b441e20f0924001040040011818101340e44000101200d0000c40b0381108149920142500d00d140c0008445940128a80c05501441d02030b01c58141205c0c1010b0180a04001e00145540a4001142c00d51103190011890502d030341c0b00641c521100442003990b603441c1c4901e0181c0680410202290405a284001000c607a134a030182e40c4015800c9000d4071004500d600c1c3c880741900050502a11540e00640003d00200b042000303200540301900c1d0b0340d807982d20b800405401e1007200d902070032280c0d060001400c0c0d0759031309000781d5030b100070141c0f00041d41c03524409ca00b500812030f94000174100051441c0101d0b4201d81000a0201540300b02d50710501a03885000344040700c42d10711001420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 12897291 1250 12896041 12896063
    0xf040602070203011b030903021e06071409030115060f030504080f0c0309060c0c03070b130b0d020909011e090902030309010e060d050c070b01080d090311130603060f0b0d 75
    0x128660001e10307407940014008142544101e61010843c1004080100440d40d10b6001208158044c003810502c10820b11101191401c5001c501d44c55180c028808810001400c0c440991443c00900340c9040d004054000c10040c803100d1880c800c0d1480500420021410402540d504540301c0c7c025684150751003131003182000441c5144d480c103034100c6640780126000601c4114907070740301c42011b8101114090000c14045049009050511826400c4074000000801c0001e07294241c0c00755280841e5150344000340d840120308150070081c01140d040302e92001d100c3c0c000240480000284920103446220703107085055440600340220b0b101c103200203400d41c0081c000d200482d030041540252003440a0200c6140100e145a0b5030b049813000c0b56080d4560b840480c0d540c0030711081441d0036000d45003900007040854481e00000d0b0a28101d44001460b8030303000d1081c0181903d40000c4545266502482400f2542e1213240032000b80a079101c40c2c101e05403910b90001028070780481b216180a800514038a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 12898541 1250 12897291 12897293
    0xb012103030506010e0904050601140d0507051009050306040c06110d1706040e030304030309031205150f0a0803040b0301031104200708040509040f0302070509060f04090c0506160b010b030f04 84
    0x4090b10008110301e051104030200c00b40c0640b603001485214038805c1010300420b40c1004407c0c000060711010f0103001d00d80e110b4a40000440001c0d4400550704200c4c0c019000b807110500840c3c1c8050203070865605405050184410000d403100c0c25010307104140c541803502e1001d065140d607036000c42c4000e200010030806078100f00303140f5818165003083c8058030100c0e006d10003174141342c0345500c1580c0c12000680d84403100000d141e80701c10003442d45903401805000d142000217148440344c0040c02c20501c5000c4200c1280d1503035031040320309030003845e641d02507903100d5680d00501c2d0500d400c24402519404440103c1d1803841c9003034459101052070050020410b5101c00314408100c1d04801e0040703409101c100b00214583d6914a50705200358400e18008022504a113802420500c01ea0304c03042c024140f00c0306002c039981c0d4450310507103001d0301030703600144400603400c0c5400d411200d544100d030401c50000c0da50703040440120710252624000d4540440c0d990340c1c0c181c490518401291003900611640010070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12899791 1250 12898541 12898547
    0x50a03020c0708030c0d080606040312120b040c030603050c06031e13050a0b0712050405070b0702030a0c08031e0f0417010f0609020316090509040605060d050a08070b012103 76
    0x441c06104400440e101c65403100d038814610f520400c1001000e0748540120740280d58443d5007141d2211003500c0c050308180c03441d0b4540750381d601c01d0143c100500000c0c0d40d880544c50880c4c6c0c02002e901c1c500510501c114086841e0107002001280000c0e02d1500500c40c1c58029030405c001124041c075a105006040780700e141c8507104420700c01034524a03400d88001700305030200b58100403c941480c09140300820b00d08001c040600f44604881c0c54000032070900e1304100c0442c501140c080211111109010350300d040510000e0f0512481d80030007852010018408610120300002801041078001542d0204030090715040b07090f406051201c041c042c40400061181000078015418007084580000c40c040005a000d2425202c1641040103440c0d4084200302070114800b0000344030710807500301011840d091a0116918038002080603128580714408529140c07074484640c901103810034103503102a19946444642c942c406079060311016150f20000c81c02e800310302000307854100707090f901442d5100070b81e40607 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12901041 1250 12899791 12899797
    0x20306130312150603051609030201030f060305120c190b130c03060e01050603010f0b0d14030f0307020307030306051f0807031508010e07060201090312050c09041a01020c060307050a0302 82
    0x100e0402480c2c0718140b100c0d00c22801000d4942000000c070303007201824004020101c0c0c07001007050203c11001030500d62080c1e004640a03098a40a1170b0201c0c07400203034520074001c1c0401303500040076845001003e001d00311018002d410b1000c2010141c440c003400b65400c09101941003c0082c10402111011461090128101e961050f22403425002c4060f41e0703480b1282140c0040300e0400150f5101d40422146103000c0c0305202010004110070480d2003c610003003503034110f074400010b284540902d44000003d8081080c1e0741d0448074200d00a0b501e282c00c2000a49030340004808a002ca810428081010705e0001212030646406a25602c490f8600000482d20041c2c0079213404281950340c40c0b0030341e070704001d114060040c0604100116046e01d540207035a2401840d6030020045900d422034890001c0c0c0d100000c80600e1000c840f01088985610403c2201449203d082c0e070b62043c80c0403104450004100b4484140718003d800b032381e001c0c010a4003403103940d1108a483c0300c0041c41c00c210a1000500035406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12902291 1250 12901041 12901043
    0x10f0308040605210711071a0a140c06041a01090203131104090b0907061101020906030105120f071403010e010b010816030e07030506011503020a050901050f070c030c060f0c02030613 80
    0x21081013103114100100c49080640f00000020001c510350214120708000090041c00303c3c03921032010011100c081d003038034000c8403a80c1c4104070321040c2c00005910540f0640d40392a8100e8140c80e024181031514032600300b16402c3c2c408010042d0310000170102018401c0d40e00c0344c140b22072100703812201952401044500814110791095441c201200400c1c00845811300c601c1e03151005051141c1000c801070503080760f903a200e1029a004024403201601c0f858103803811103c080d960b6807888451003840d00c2c24070110401000380da21900d84c002030034020104510003440400c8d0020000c01c9c244c1604107080c0c488003850305020803103200200d6003170204213640e02000c249034a40010b1643c0411241c0b400c0c0030180e40306480700c1d0b11020041c080c02c01001034085980500b8101103140c20030900001e031070307401081c0d141c6040c00b0300490300c090510464000c5650b035030380c40f07000f100d05a5202d240c098070f03802031030041100040288454070506030040714101901a00103000740544d568511000d0140103100030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12903541 1250 12902291 12902317
    0x703030c02011704030807030b04051302010509120d0302091008070206010501110f0703080904060503060411041e090309090c0201090308161704080d05100302010c110a1a03040b010f0308040605 85
    0x80c46103c016541e5890142c1c1c825501c1d080c041c108143c0041c01e4683d5110490300c44c2d41303060309000810b0740190642d541540e0a080281d221981c00380041c0400310000c00303040c0c45000e04148039855540c075a000700515042280c100240400118003220104801c442240241e4462001802658003e0507008406440d0340101c6408086110703105061800c60303841100d1100b40400d801e16245007d01a00740034040c01d40c01000189440d856890f00241600d800b94011030340c030321000c0112000d02450003400710610406128401103450010f145010501c100d1114502d0721840108551041c001c03600702d40c2d016139480e0511780b01c2c04201103040051905050520240000b400015440a400302c0d10a1740510030450302e811000c04042d0540d00300030481c4084a03a00d010500051f078110180054168020641406e0ba1412101103240004140c010300d520309081442e181c0311125100082d44664820046072001e640d95000034007040e05036010050104a0500040c805c0c2e5200300050426003078550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12904791 1250 12903541 12903557
    0x7030e030906072301090f03030902032103060901080106050105180d020a0609030b06040908070f020103060e0a02070c09060b190207090204090c020105060f10030c020c03030307021c110703030c0201 87
    0x400081c00a51203c0c0045072105800300c031640352806035240b00f04105842070002d1214050507900c1103d030784039465005082c156038007122015503c080024103103040103035802242003560b054030060300b034104541040c4581b0710314001280861044c0a644102e60043c6c5480d414800150701c03040f00c590200109a40100c052030750080540c1c0c4031b03603c0b94020441c40c0c440402850540c104040b58480003031005010b28209141d82c40024020011900a0354001c00b8560314080c0701d100403070181c610f541c00a201020b010741848a4010141d0081041a101c1c003006107a03183d85015103000c0d0b452500c07803804c1c0c00201340086101c3d29461110007130107100310700c10b4940c980d844d43d074440100c0c1c105400c014a015170301c01b0741409054091003029001502105c0071540689102c000452040c14124201c1c1095101e00985074098020001e901420380d008040c0c2c0c2d00c0703261021000355a140c070b0503035000100d83e0442414138481e015601ca51015450000a0300c2c500e415514265940808480103e04102d0f00c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12906041 1250 12904791 12904807
    0x1050f070606060801080717060403050903011d0f0c0d05060105010309030504120f0c05060315060f04030501020d230c0f0310050d15050a11070b130503040603150603090b07030e03 79
    0x161050b07201400c00d80d12800d20715410480440d1600105401120310341c010000358412020300080c20740d0f03005030705180141c0d8406060010901421001c48105070810034004200410900851184c0e2002441811920b4401c11801003001c82452200080d00f80d0b0009001032200b0751083c1c12140886000c0c2c100030f46050780e40e03440c0c0402d41100306030035103a125078a844942005003110020004141c11282e46066041a821308045407808502181c411100010604584c404490555000b590010021512443c1e42d407030300c00150500034109030000291460820401004001080c05888000b05083c00c2c004d81c1d400001d003652000d0301e0424034580b020301c006501c2c0c1c3c801398005c4201c0e20030716001046c101c00d1030802e800d507240a40242c0002c1d04200710b01d208081c14509072040260408410347d01c070b03200e504001841911442000d8224080007071b000c00e149805800255841c0080620413000582e5258114215000004010240c0d400f06e004960010310a4010b4a00c0190039825a441c0c4406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12907291 1250 12906041 12906053
    0xb040c03020d050709050106110303060409060f06030c0e070f050708250302030c0f03040612020306060f2706090907080711070807080c0402070302060106050703090503060a0e1b030c01050f07 84
    0x7965004540c15400044c00340070ba00914042d15004141608001f400805260f00550f01c07404000e100c0ca000706d43c2c0f840d6034401c9c0821500040c1e03204500c600200309842d102d0034421044031545c050002e141442502140e489071064083c51000050b503510310b400c100c444e81e91400980d0103440900c699202401c801602c542e00c001c0d18880246c82500210740e500a104021800c5c82c4044480c0d4880f500144010040142c000051043c124143c0e0801642c135925440010403038061200100c0c82000045421030b0321410f449500420304450145100703c4400b020304000182c461008115003010201c030114030680d004ad0b0301603802441c030707041000c4009465160645440031590181a2540c8906001c02c5000303000c3c000400801015607055103071002c80c0d01d0296540704184540001c101d00081c03070005051045401c88003401b4000c00303484050501e4100341c00509251481c994a078051095000040d44210080707040000c1d0150242205110990045d00c1075082140180a5000c080010000042e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12908541 1250 12907291 12907309
    0x1d01030b040c050406092703050a0f031805160905151201020c06040b011509230307030804080a1203020909010306050903070503030f0702070b04180903030b060712030b040b0603040b040c0302 84
    0x401c1080020891010001030b0003070744030600460303510307e0100f240d03034040f0f54428102c0e0031914060409150441c560842203000745100046030300700f0102d0054480c1004400b01c1c028030001c0d00f00e003580c1c039034a40315514481155020703078021010200f40e5600604a00b0b0507051103104100c40800181048451415a4200303441210704440041c081030040c481c40520b8003080b9100c4140d45032040100b4180040c52080314400e4224901c1026410100b4806607410007036480070b075a00c810071a13229540d0b10011907684140c4c42d400c848034405c0551a110462091003030380c1c1c007000c00401c242060307440c50b210040185005003520129020410140020600400043d40910501038010241e4501444000d046c04141c0e0001801814100010440014070300c002c03141001d8081400101c40e0101d280603401004181440c503005800801d40b1414004142c1ba900074990b042c2d2130a1108403410030400007281e000d9070300e141d4001001d1020802003041010f0780385d0722910691050041da51130790005401c1c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12909791 1250 12908541 12908549
    0x318031e0209150303090607050a0f03020d030c03180303050a020f0412050c030f030307030509031303050c040b060a0f1b050102040305100c0c02010801150c080f0c071d01030b040c050406 82
    0x28400000c0c04505016610b103501c20801140550401e8020001035164400c40c00001d218581c042910700a001c0180817400f140380c0d01c404000c0a01d821403a010b502c6010a000e101c020910300080480d00e00e00130f0003040e00351021811441c40146840d5020f5009020103051842103680c2403141041000000c8024006044030301c2d88070108000d64900300349002c0c03460305c903540a5042070454024441c000000e07203420001904001c103140c1e9030b06551078614007504c0448040e2a0000c1c01c000140314020442e0703140072100340c5d0140320040900081c4003851240502020000702903c00280020344901140780d802d80000308800105452510f98900f660486e8009544980000040c8a81461140300300b000d00310603802c1c1102000015000a000705c40140f00e042d6048100d140a074007035521440d851b01076907920800d1300f92a00c4104401c20711641021120f1042e85c8104000031440001840c0800c010b0a141010b00705641c0c2150380d0a400c002c009881200d02420170070700402e05907614040c42d0702030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12911041 1250 12909791 12909833
    0x5070203070605010803040b0304080f070503180306160207090c090902071a0709030c06030902120a0605060109050603190b120102030903030402150a09030204020a0504080109080408060c0f07031803 87
    0xa20341e906061080710b10680c06075007190700c200000c200242d0b10b003096960150300608002c0d03c40c104c0220540306840785120003007060100050784502407413446c070304100c1d0460903022500542e56011002c0818804103003600050b901000040200e8040e940149402011520701004117958641c038840c00e980120340c0031074250401d4001d8030b083c5851007051540c00043c5190018206d840c40d12410044a20303130046070205611030825400f90345a07004900d40224500c01190846549801e0050040030259100c500245520f04001910320f80384066a018000d402d0b0703884000202505070000400781c6059150b0044011500c0c146186828409148154181d102945d0359107018410040f004554400260007440140001503400350310040d44c6059030343c107440060b0389500320030040d505070040d90301a9401d9801d044141c070411012a01900071145d1b900215003003922409821103903805807030b0703081c1b42d403010501580d00820300c500390042e16260800301401d10551030b5150641081c0c90100d0000c81 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12912291 1250 12911041 12911047
    0xb060d0b0a050403020105060108040f02060f0912010e0f01020a0207150c08040608010503061015120e010e100e03032202060417010903110105011203080402150309060403090e0f1303090905070203 86
    0x4c0c16028000c0c0c03644840e00b460008050f1810303a40d80380840c4100b80c80031b80201e101007144041d2085000454003100001401844035501c111070641c043c08005038170a401b4041e6a81100740d94a0500a81d0722009583e00600036140c2480f001c911142a031401400402480b000c1040114800000600142c051070f47d92181c20360501c0241440d00001800c00e0001c02c6d140641049603103081f10100701000701f07619044000b035041719413020107004400002c1c80907510b4916054000000062031402a814101c8144004018440341540b640030803500200095003040e1018080c0b040004001781c5141700501c03003420310b5143d20300c0b81047c40c4031800d06442c583d5030300104001d064202c0382d1900d8a080c06d0f4028841c07581031500c0b4910300444030400509011380203002c10215501d0a688800c0751004411098403490015021036a1702c030140c41c20390110710b01c10400f00c1c1c000c40c11540148104074000c500e4829071a542c552482c0d0545021050342003082030307107002c2184501c600826003d09095401962 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12913541 1250 12912291 12912293
    0x9050415090b0901060e0f0703020901020c120d0810030f0201080a0f020301030c0303022a121002070309050901080a0503250219080106060306050f0f060c010c090f15020a0b060d0b0a0504 82
    0xc05c484035904003101c0780101c1d50811014144000c10640d20408914015031105c0e00c650040c2c0c64625181d02881c1c0c400c001500c034008503000000c0255152645036034a4002c1d459070142c00341201c4041c007000d0078064600e0082e030055409a0700150b0821580c0e000050301c1e5501d000c0c500100d82081c2c10840d04c03007412900400130715038100400401180c126500e0340c2140200c1c84007049500769000d407103009500d20740c0b1450520506100100c801c2c00c04003c1955201d242c0d1400400000050048501c030f04e070000004241070500240ba0780c40243c0c060021403030301c40d401088000c06c082e00c0007840c1c0450302c5c903010800162615000040d030b900080208001c014244036102e400c0d500d45400c16006c06240060402ca26580c0c4142085491019240551920401030109500340704120084181d5802c10502c0030481d03510100e00d2088440e45641818003a4640e0005010103002e14480703001a8060042d00c404501110003a81d003103540102203010400d40ba6a50001d41c0008440883d50580d1b6002084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12914791 1250 12913541 12913543
    0xc0904230303010f0603050906042004060306020406080c0a02030304060216080a0206010302151213031e090801060506030702030703030b12010f0506120604030f03020703020c09040510060f060909050415090b09 92
    0xe1700c3c15050900440c0703407071071125564180061025201d00c8502c4010684440440310202d014a40500184106601e905024010b1352192107a080003a2506c030024007d107030b0040565414007020741c00380d451038590381c450101135003102d810501621a00e40360f41002a4060f0000e01201d0903c1d000b8148661550040127400030f40c0300311401c40c400003000510482d00d10540d001d80c0c070a01188005403980070a06044a140510351454045440503200040001e03422001100840f13001c1d2009218030341d00c400500089020030755511002d82e02c00d100c5640081d000c1d800c400340120014103e0032a0035034060900b403c0da50b96032520020240d440042c001241403003ca6481c40306030303810080c911814990340003003d548690003401c08041e070114000e400c05209005142e80071300700524108003424541032664a605420707040b40c098901d400000120140c50510341d004454140d2240030f00b0790f03d4800100e024200041003241c5e404001d0b04132441030345071703031140c1c507482030181103500c441d03190a25503a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12916041 1250 12914791 12914819
    0xe0c03060711070303230301081f091703150a0f031e03020c01201b030f0607020606040903030e01090b010f06050903100c030e0601080303091e0c090423030301 70
    0x41d10030007482d4480c50b01650300006080741140e900d442c01031085000c0881c0c003112091894028481403100000001ea00203002800b0410720802c007413000618201d160380c803011120b103074a0051a03180c2d4140805118804040a19800415941c4030003800540760009040c80d601038022030007041c0040001d1007808405200c1207440c5049119100d4000b1203074401950b0383c10794000480c10054996803e146482200e02d0300c4203480c4400e411282c8503040ca0038604440102c1d09441e500078410314a01815004001031154040c0c07585030080d10b00780d102c4c081030001800341d082e4180c05240e01c0350000c00003094240b00f11501c180c040c6180c3c4406504000da545207001c0141d1080003081401c3c04010040e5502003501042d44034005000104c10580510680240921801c0400607004d0000005403500000c0015486440d0030b10594140d0a00411a00b0010b0f00c1d1604603842584201c080140c0760802e41c01c4a600700740a446070002003071110400b14580040800e031102140c00100c0101304203115042c1c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12917291 1250 12916041 12916051
    0x151002160909020a05091306020d02040302010e01020a0c050108060d0b0a0c030b06040602060c1e03040501150515041e0f09020405011206030305160213090c05090708070f05030601030209040e0c0306 87
    0x20b21108600d0b40014011045500540c0c4c89001b841e40820310a0384103000380c15a445d8482c2042d51607008401080000350001e220030b80c08900b83c80fa4841041d0310220b80000790782d5024400804090a00004650240006096903007207210071100d80049480085014400e000f000c101050400362420024240c030004000207000d01e009100a000664011403484e81c450a038009558481400c148511a4042031041100c8925000030502c42800019003000311100d07203450786031520b0743c0e0350400c0c0242000d0080312149850405d00091100c4010710b600050100902056061826118002400e40800d5a0300c5552030300d40c0064104615600080c52a50800341d180c4104001840c584026085114003061140c40d101c041c03204400315980c9030300e58a01ca60b11824200b084c44c4181c40c0c910501c082c00c1c0251481031940c20009403080d4401c00c04548590129650300c100f041880340c01381c50a4001906881c103143c4c0034401040142c0b074a118800d4031004e1a4020680b004503134040c54103000c400b42c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12918541 1250 12917291 12917309
    0x301020c06010603050408070b0f0a06050a050d03030207020f0a060c060609020a0504140a03050706030b0a35010908030408030a0c0c080a0507030207050904051c020c0904020915100216 81
    0x22008000c10000301d40a41190868100483e05581c0c524080f8842d1240e80e0703008054000040c00d01c140700741c3c002c03011442a0000c0d8400c0103a40e40780d800300480301da480c3c880c1c540c1c0305909851001c0006c0c4a80c018004591019080c40c078205000c500156005d509900090f0004a42240503800d20009005410040032103201c21494080d80d200c00405510071800392505524030407100301c031b0980f200c0390b45000440d0084156041c141d11b131000103001d0300103441b4507031003201604e002198901000000300300d028109140c489920018a261540302201c400300c0010319542c440319800402c10000c003c5214030720800e00300d6500c4c41c04072240320840e91079148100c100005401510000b80c00082240c0c486141c0d4101280c0344d8100d458124501010f41c0c001d10740204c10507044c0303c200b00380040c2c000000e0701c90404500d282450b07004200c4c0e59400441d046030744101c40c440401c1c054108251002c1d0000202c8241036150095000450005a0800e440b03100590140c0840100865140442d101400c1d000c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12919791 1250 12918541 12918547
    0x9050d0e010c080703050c061006090b0c030301030f020307080a060506010f08070e130e01020c010f0b0d17030403030f0203040b010302040506120604060203060111070e10050402070506070c020103111b0c030102 92
    0x1000080038801a5140140b071100f002a5100500d80075000b900d5100c0060303130840c0c4013460000c3c0e180c401c0140f03034030950001c6113030080082070060001050700c203504090070045046a103140c032035000031030480710181e070075000b070f0007001c12040c1741441100c6599004800115080c10810001031841110034080c1c0100010708052108595105100c0012024100d46220641034082500b40080c00300b103840342d055610004484540c102c041d0825503151054031030070401821001c0501000c48a11304004101c0e15103010040082070041001c0c541090292400280794480760410340200da0043d10103440b0060f80708010021460113014441c0d1000d03040d078440c801070124020442d618a0054802410f440d000f20004810764401c05850610000c45001c03102074540c0c54900045401d01035800601030f420054010540c0e091074002c440080368000c0052600d650f5040c4201c0d2122440ca408074100340c3c80e42d480001d2012040301802000f1401c1304c035242c40b8500c40603d686848018101c45010b64014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12921041 1250 12919791 12919817
    0x3040e010e0402130504080d090c0315020906030103080705030f0a12050106020321091c08040b0906010501050904021e04090b01030605120a032a0b180703080a050d020c0601030609050d 81
    0x540283c44130401e21480c003059075110b6140c070355501d0086001704500b603481c0840820500c90546070040840b4060000014442400c03211201a4030030200025040700d0108010000a50000001c000450090341500e007001e00c9100089550f9110038842c20000ea4003480401d0311240b244103981c0106268001540b074456021500300c00311000200001d43d074649540080d907000f0302404214000a100e0ba142c6d8002080501c010b000094252000d48502c0e1070b0400242032001c002640a0503104141c6400e07050014030400c100c0a5030004640c00f42806401070030304240d5030410003510280081c03030740c0400c02e00100750004080702d8844c0e012505c03a0400b4101403200b1080030542000b01354161900040040158600704414400c40f4400d84801c219800088140a50916401d0080d00303d1000c41c075000000541d6503a81c0c090302d002c09050101c080180b41c042ea8040e10050a42c01820800507040c00d03c5180c6884c184030f000d0b40192840364031100c201003081024004510101994144924003c6c0780c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12922291 1250 12921041 12921049
    0x110d0207050d08040506030f0405060f0402060409050a020d110c010e0105040f0f020604172a031e010605031c2715050c160f080102071713080d0203040e010e0402 71
    0x40748100d0b40220014140d00d814446040200d41c0070740005060766503039045c10301d403002e500b440459050354680611404034006040c0c60b20154000e80c0c00900e12804c10742054100c20003003402802090078281d00b0000d403418101c003030040c254905040e00d8880e40b01c1425490341d5007910030800302c1101c40d03450b00003000002180c07001c1124141d9001050723280b2520b1188042042841141c010f8a4802d9139104103028170700740014202d1580300400c4081c1003106c0c203607880722040721420031643d515811600c0300511512010341c444c840202e42200100d226591200400d06190262504010149074500c203071216981203003a8801005021903550000b15100000e4200c1c00c08030701130150350590700914810400d00c2681034902200030304080c2c8400301403141d9141d5542896110300072401c2e40c0c4c00c10004075461b040c4251001103402814041d44100104001c101d95840140c0c0204a81004440801c060b201080450301c480e02030380007580d5640c03d2050f980800c0105038080164485140c04100040e11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12923541 1250 12922291 12922303
    0x60215010b090109030209042103020306090402100207050607060203090601120f080702030111030906090d020f101503080703020607090f0303090b03181209010806030304030308040b090a080301120201110d02 91
    0x41280801e4450b140074004072a241d103242c0c4041e6210b00d0943c14401400004100c4090b8030440540c00203001c401414140c0c181e000c200c4296612804120014000d42040b000c85450703140303a44140e41255450f800010a0fa0700314140c03d07211154023108122900e0010000c0301e01414054034558040d503d10b45d140361080d070407008020001440450030008540f02500140c40454281a400d40c49160180c0180d075203250841d8045403610076412001092800402c5084660b640c0e0f1025080401d446942e17000070b00303400d031150344407001000707400808a036507500509060ba119038040c00b45400e149074005d0420b401904400c040b410002800c20001c0d41041c0140219190682e05946964807002c88400e410040b0114440901030460400803188000000b05607029090321b0751200c0c3d884040a1690782d000c3ca000007000324078240702203000b04221103c600c1d44031070054212a224451903031070040396002a413000c100051031184110440d030f04150042c0458030407800402c2c200742000b9009559403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12924791 1250 12923541 12923549
    0x1501080f04080a0f020111030103060902030c0109210206091507020306011d160309021206060112020705030304080c161d07050307021203060406030f0c050f060403030c06020a031416020706021501 86
    0x104c00c00c28900c05503070007900100003800745850503903241c0d0f07980c0c02c0c4040075018044040340311b030088081050341980980c10180c19564002640d42061503403030b0b50720340d0f20301c032444041c1da21800501c800e29a941d82c034a07040c200c41c03500c52505a105d42c3d0a01c10b02d480c00506800961445411075034208402d010847c106034081412840346a9400071300c2c00540040444007006900140308032078144900000044141c0079400c01e988002520b2031500c441401c0780141d05004001d90000c10220700401c0480019118a40c22141510502860003005910862455106c000f0001d0791407003040d94804140320042d800103279824014910310700100020344502543c4800c0319031560200100b60b8035106d503801040034503030059500044045504002c0701c0340495102d91489410030240301d990a080120a0704c04495041c1c0f070351401e1400703d07130316000603400c0441c0c030000b01640c504913181e558102d03400441c00762401602c948042d49030500c000303090061a400074420740d0f00c00d010414100b240006402c1c115 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12926041 1250 12924791 12924797
    0x30705151606090203061003030906020a0c140402120f0406060501110d0315051806030607170a1a0d0f02100503130803100f17070603050c0301031104141501080f04080a 74
    0x1245061500303070020f0218000280d00351103208104150411700c064440c041d603001e51610042155604001ca0f5100007101005106144880017080031030041c261a030568031b801070025040036002d442c060203030541165014a44c60080c400c0c001400707000d00c2100c1c0509004c1c43c00700c2540380d11031180341ea0750024180c98810140e84001070324010410040010103404010518103d010350140c45e4060384000f0765101d4828000c00010402c428060040f901c50303ea0780e04517040e02540d81041c0d4030000c1a4102c841c2051400e1884086c0e226541c4101e80c0800c141704203006240d070111030041c40f60304a19020312000303210701001807000c46000d00900d0540304d580821880d03500d6580c00a5002c3c900b0030341e4007442c1c65651015012480d03800420aa440c1d1400301c030102d6407882d1360355500305d003035820581d00111500d400304010720100c1c040d540003490000e070107400801e2490f81c0e1041c2001d0308104031004001c1c1902800700d04e2296078010101c5410803010480001c03d42010789640d80a4403841c1c00c1c04c018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12927291 1250 12926041 12926077
    0x2010b0108010b0d060e071805090106090317070c060c060c03060302060f0705030d06030515070203040e010b030a0b0307150e060405130203040f0b04051608010e07061202040812040503070515 84
    0x440540c0228014180a814807000c07407c045c600985000c071640d018619001c80c54a0115540c100080e040f41251110354074180c1e020f00e036450343c078017040d0b038103840507103505081001d900450000c800a00c01844590748047c5e0944060500c1000c83d0b500d59988010141000b004201513a0745805881e01da103000b401c00b580d02d04062a05510394412102d01d482c0300c038249180002030140200303201c100040c40c0d0122003031907a02c4050482e207a20030350140c20700c2c1c002d2034401404010110409580c2c0903100381d000203003003a503280001c3c0c83d21010380d1010074500401c84500300d4050307020481d01c912000964100d41083c1c00c0c9030005038a1195203c5140007981e010001800740f00e0300099090180d170708aa8070752041d04081c20916210394003149000300c0c2803510b42c40064152014412500740700da002d0090413a50742416822284400004c2d00c00301066001c0c803010500391018400100c240c80034203c0c160780c40d4034041c140b604250f010307880b16118801c0b006d141042041130004681c0000c00706403100355 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12928541 1250 12927291 12927307
    0xf02060306060d050a02090a060f02210d020c0607110a03021506010309080a0c05010b0a03030c0308180f06060f030303010605070b090a06050a051e15040908040504050403120c02010b0108010b 84
    0x740b240a008203528806043c0700c103102c80000d440d4020300d8181025280055126103c02060b00c1074618a001400141e00031030a000c8941e4000203004440b045418038a45042c9a60501c842a0b810021018845e50060424003e18542100341c0e080700340158000780c240074006440180d21849440f40c0301f06094100800507030140e100e64400b041955004030b58039120380790107000600b80c1d0300401c0100c4040d071030a0518070b030a00d4248080001c0b02c1d80355903101181c181e1540c048407540f0000d01018010400501e0803010003005101d403900d0541010001d1409103068020442c42903c1591042c0c007030742041005100340742c0d2000c111141d89400071a0011540c403050144c0d441d04400000290904d4035050034060666655084079010f08410300d81c4909090358802000e8400601f560701e81e10591a94401c944142040d822000195004079100750500d90344030042001d03510300f240c00b1000a03503010103c460240040c4610907807050b6030b20007041a40045000038007200010b000d001201900407034148 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12929791 1250 12928541 12928549
    0x160908031b0703020d0c03060623060702040f05010801090314070b0105120f06010603091a070206060111030903010c020d120204080304050f120d051803010209031c020703050303070903120305040f02060306 90
    0x2c010342d8050000c0d40c041355941890310f8400b101d0b0004454260404500158401c0110300901d4401031807000c0303203d40c4801c4d404010540c4d01c4008103d8000307031070306146c002c14030191041d40d009001c84400810311440901c0c0080079200c200210b00c0300764030280402808500d00a2480d41500c1c41610600c00800680b0340710361501403c081c0050045c4100400030032501c2e419044004040e1288d5003c6040d1404a9805205040120740d800c00680c05800042c03c00d40c0b24800c441c00030305099059914203890340c0c000ca42555010700c00c0b600568401440000119072144900c8402d4030266002c60a1031304186600340c4038415442180c2c440d0b0901d40c00040c1943d0b5410502d0803404a880840c0d10340e40001c040905035401074102d80c0c600b016504d1403503151382010300840740c10a400401038120400b08090f0070100092180000d41144074031480800040c4c000c20003180209100c0e107620031480e103546050b001d2241018010b03c10182880d041c00001045001c908003180e604807403050f100c1e56248049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12931041 1250 12929791 12929803
    0x1030605040c03120e0a060309050c040209010309050a050318010f080f0721050a0b040c0207030605040c03050709020d1505010f120b0a090e07060e010504090506040609090302010203160908031b 85
    0xb074440072071582141c0c00d40c1e1700141c3c41c9130340100603500c1414555030790400380d088400c034440241c41c40d0845d0301d0004403071821b03500038120320805040002e4041c00945849103040b600100807100b6a01c0000c60b580c003070215208820800509107020303404080f8401000b0300d0243c000d0510101444481d01082005024500c01c41c40f984c082c01c1c051400b00c00610080c405000140c40070b040052902003900c405041501880303c0305010358000f400d15030b1840d901c0400425005000340d60084101002000184081c0079620040500050141e1691a140c070528200c030307541030b0103101d8411891800c015a0741c0225174103075030607510304219111950b40200700c0040c3c000009450303804070b80b5038000f1a0b041000c0c2d120814819404049038507560301e0312000c0c3c41090070f689001e804200103110405c0050b0181d002264400800303007010415907900c22810068481400e001c80c0035035008003c001c480403141720190352403022482c000307100f1445d000e4031940b244220326901c0400c40c54500009840b000400c42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12932291 1250 12931041 12931043
    0x103090b07020a03090504110909040203030c010203010b030a111908090705090907030506090d0923040906050a0513021c030e030d02060108070806010b040b160f050709180b01030605040c03 83
    0xc0d804945024031000707440b821502c0c0700f1800b1030349095000c98a410039209812280b146c9001030b514000445040001809000380704a0341403100700452030031743e142800a94024012500190345a040c0619100e0581d00d01e0001041c00d940180440a004080f0700c44440b07201031207041050880e100d280800d0304004e800c0e000160000c150b0000c0c84140040000d420303084900410035a56147c070703803002c115200d20090030040000f07103030304500713100000da10519594224000b1405030100911032002c036040d140c1d0b41005a40303865480b810484866001d00507036a01c180721650303510482c1010341c0050920110b178a083ea4040301025001d0301050300918089010303142c006c085811906016200075540d110074021500c0e0340c040c907000040d50440002e40c80e41030700c3d00ea0903118181820264505165003214107202d403150454508071012a543e8269100e41c03071301640c040e251050a043c801c1d000d9070300c0c20856810003003103a01c104020845c0c2c85800c03410350b42d01150115081e142c50030140c1d160f0a050300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12933541 1250 12932291 12932303
    0x3060409080702120303090f06040209010b130801060618080d020a150608030c03091008091c031407030603030e03070f0512070b030702030406080105010e0915061c0207050105010f080318010309 85
    0x14a44c0d03990000040510311070032900d000c844030405602151a103a800a94000b5080502c004c010300c00c05001501416514280b07601311074041c0e0360341c00810b0945407258070800c00700f02c520124402c5260b1400d030100240a0500040090386c203042d2000b5511400740901404803202c01d0751940400340741c1d03009a0000c3c040031080720b44942c0305000041e1650f0055042a114400c0c5005400c02103000b1031404c0e00c248600805040071542c1480e80102142000c0d100104141c0c0e00c003481150400801003c1e03000c1c5106540000c0e2850861034054100c072083c0010a1007a8080182000b074442e1514a9030300f6260705480c03000c00902c000100718680705040e0014244c044012082040c115400070140080340c42070340e191086a40d80e0001519803c1c409828240c102080030001031584140d480284403041018004518207010f800c83c51000c03614098485d035240c1c0d000101e038818400240aa20702401c00c414294a8992804800ca95203104601ca058400c0c10390b400248400c0e0300a41c00480c000317401207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12934791 1250 12933541 12933559
    0x12060105130b1b0c01080103060905010204030606060e03060705090303040303031e05040b090606040515010302180307080f071418070302040b070605010518090309011b050f0c131103060409080702 86
    0x18070010b41c58000f0b03c00c0c00c0c1418582940001d084800041e20740b11030304183c503894116421510384002402e610002522159001c01001000440500c00c1c10024503090f0f40b4074420040b080101401c5c000c005e07103000c04211041c81500403a0350040308550490303600d8200024130481541c81c8424400040074110412440c0804201c00e01c4107901d120345c402c1241000341c828a9441100b00411034005445004615149400700003042d4040c4d40140003854039100300510540080001901e041c403d500320b0400d64002d904422408078017040b00b280035100c20110b0b240c199080c131012445809402100446600412020415090090781110081c1c00d403100320b40e80c1c510f4103040203409014288101c9004034903400c0751710b840c032a03c810301d140210580b1000d1442c00c40301600443d0922000034180790350150001d9048002041048180403020440f4003030000c40c1503203410043c4001443d43c2c3c1d101d2a906003000200214880350850340d012104035000565844c25003070910b0a4040c51b20001c2d0000307491 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12936041 1250 12934791 12934799
    0x3010e010c03090c0812040b03060613080d030b040504020303030c07031701060302040f06020a0c090203091002030a06030c08060712020315120a020306011e120611070f05060604020c031206010513 86
    0x240c3c00c001003c1d40200100d0400c680c0d40d604007580d03100c003241805803200b000d100c14407075800481c00070754003c14000c041c00c3c104907001c0c418010701012640b0940e401c1d48410903001002e0713018002c50f500d6640c121420003042c64203402003500d0344001403009007002400109002054001c00205100034004840807030b4540c0c603484064001d41c0305014400d43c91007040710004940b4800141030007800e6211941c42d42c040c4c40c0c0480000a500301400490090283c0c180507041c0290034030103144900d0000d2408070340e20745941004801c503903158008403a560007440803c088030b0342000301205003c1365600c005036250b40b032454100100310f904550a40c8211000d175000146100011040c2940d4021401e40f5000e036a940e15203c01a20511b043d80b46d100c07088a01004100510480b091859000d01004104089003c40648184d440403400f00c4401d03908008101c1402410005260702c40e405030b504520b481d981350703840c0b0743d83d0083c0c3c2d01405d20070008000054059204e0416182d0b2090380030714030f650440e12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12937291 1250 12936041 12936047
    0x804030803040c081e0709020a05070f060623040e03030106050a0f020c090c0a14180904050a020910030b071409040902011e030606020c042a03200a02010f06030c120203010e010c 78
    0x241e003101245200e041c0e804a0250400d100f2286024001d40701c280c07a02643d0340e0cc080080e10480000e82d1215554440061001c0704000c6203011501e8103402801c8141c0401c0c00c02007102c560700e0030600305900c02c1c4018022a500705040700e20b59502820075080c000c0000e0012442c050386103488942151000b8140700080c02a14040c1c40174a0960f00c0308695429070080c48000f5014440120b442010300040b28612414043c0c1100d41250081c426a01010701315004542030400a4036450520400c50f8001c0003800304401000750842028a81202071640340320401159000d25103c843c801c1d0b50382c000d08021a8040c0ca81e640d0320b8140028810719400c0500d001070000c000c140705000c00b5000303000258505241600c2000282501c4140c82108611040700482e0b18510b440f840009142d500c1040020503115100600b00c0ca142020409681303c05156000342524011080000c00500701401800091903842d0baa5043e0340e50002410301c05006800040d01408401c1c140080d41c1d4070380105402ca082e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12938541 1250 12937291 12937333
    0x501110a030f0b0d140313031a07020a0803240904080406020f010501030c05040b0f15030a0606050c03030703020a0504080106090912080402030703030e041104081b01090e0a021b010c0305060901120804030803040c08 94
    0x840c1d40c0c00309c00e5a0398440003a40c590320300b18001404e1103420400526402a44035410541903d0418003c100b1003011010416481051708c00391208900400c04010b01d135070401c400030351008280700a00595142d0303512200d001d1180d0040d0b911841c1c5a2103102402d4885040400c42403038020f01c007042c880808104110141e005a54100d001d80c140803010451078041c030b088802c000100e000861641e43c607070394120002d4010440342000c01004010004a0360400d004003c05400076020004042c4124134003104035141c1d400300082400801d80800c00540d502051000482f605414521010180b80002600801c2e840c03060184240d4040303008a40074400150500c0804c01005a00b48a00f62020066816640d18800d01400e185d20800084150140780c0140a03690152031840d11150140104203081d11021800200003955850402840b8030746051030328010130034003c500c1140ca000e178980200501c150700002d05000000400b0808020303400c034907900140001810380395200111541152440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12939791 1250 12938541 12938573
    0x4020a08090d0207050609040207060603080c010e060f190e03041d0103020a06021c0f1407030f02010f02090d0201080c0408030a02060f09030306010905090a090501110a030f0b0d14031303 82
    0x40b25403422500118000105801580c600501150030495200200720180d80844005c80721a42c45200000000309000003a100d151501d00012540c80e03074808201385040c90041080c49a900210203005110380d00291041c43c04108a0002c1480e0610809852070f52040e90300c1000341c03414501d001c090342a04d041d0f02c64180ca1080743d9680c0e200d40ea4202c1269106a00103414101c5d2100c3d03284030360b466010380c1c1000101100c07801d0001356000d81140a0784142c02521051b00481c51281144c0c1001e6828071510301300100301e0504500b0301c50404082a482006200000c0c1030082030701c041041c490b10f02e026a4000d0415104a80e520400404025260003003a182c1000c00070318600400e022090106c00c1d2881080103070b6455000a20b884108814500003500071015942d54608100c0840c0e030a0013094a4000580d003500e9507680180e070010102e60100c0d001d82c01485c6404100c030841c2d0b403410300f07003040280c000e80041c2d003100300d4072003440c1188900e0407200040904007900004012288001c0070001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12941041 1250 12939791 12939793
    0x607050a080f0c090904030e03030a0f0e03120409020a05071506030c0b030613020708070c080c1206090d0e0a1205010501030204050906040c050105130324110c030403020f0f04020a0809 81
    0x40c2c1c0b01c40c00701d20b00c186429540300c1d1100d01c3c1030003034668504120703410640c020b00074500040e240341c442c0042400c5502c82080040000c84507a410090343e6000100b10400c050160003d01f0a000c0c95020162076001d80d00a101c8403a40000d03550706500d10590170b49074901c0c3c01038801410115600d001000800c960b00c81140c20b2446a0400501c0d0301102c800d80f80b0544000d400400329104c20341c03c0c28001d520080e02201c0070310041c400c002c081245641d480300901030003c02090460183d904100c40680d81080c040c041d0340c8800c00b002101040495100c4804005007404136024022a00090362403280350054083d003420030840c0300501c2015000355048034002d82c2c0c03c2003640c8480d01d00769200c0c00210741c00340c040c070070000703040215510610042940c08104030050b15425129a5016880042a1503140b11004900705007040020789104040c1030080451206281c440b002030220349901441c40041e21854002010f00010b44440c60304a04c000c5000b0011555110207000240250406030386030a11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12942291 1250 12941041 12941057
    0x3040b03010e220f03091d060f04020a0c0f020d020d0302070e0c07050a0b0a060902041409070302040302030d1206090c0804120905010504030b0c040e0403021b0a060503010618080607050a 82
    0x2d0881d040d0001c401212000354408003611035465813002800a60011410804c0e114000a070014007224440d074103030082c01359070700c05040c080d08008800c4058001e982c031503841000103408007138002c0100a0b62a40c01158017a8600391400003542c0c15001c0794010750042c903015a40400c041e4003250190540b8004000c407a030139252900458414014000018240d41c40300b48540c0c0455846802542c0c4405201030104045483d8100c0b0b00070303608103601c618401c0c52089a8124649042003030140d004c501440d08500b0f091070340d00065503d03d0036030110030911403001d80601101c001904403038090420748600b40040c0d4083d00340240088011202038070250075111440c0b41c124480c00700d840803584160340d05414582151160382201e40c0c0604520b0481104001c0018855101482d1a01c01c500136009000b010184647c000d2151001400c0c062142d10306035030a209140d0044140e85c10f40d6614941610202c580c0650055656902d03042803015126010800840d01d910200424021007107684d2200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12943541 1250 12942291 12942301
    0x30906090d020606010504061b02060a020c150f0a0f0c0206030709060215010f06050c01180309050a0801050405071202040b04140601120509070909020105121009060b0304031409030c0303040b03010e 87
    0x1840e000f0545250b40085e500b0001009128454400c3c00c50002a45807401c50800c22580001d4031644070303910010158104810341c40051070300700003c200744038404810310b1400c500c610b00064070344120081e1030305001c0854445801184207000c0380603130b00e07405010560f690a1210025100c94145e214140040c401c251310b10310038008841c0564126050344c5565840b690400409581030703001941c4130764040d903803000181e40c04200c0816104282d4001d8603415100b904103810f0003407078406031300310480346c1c0e0400c800c0c0320000321300082c944120381141403a82c048070151b01c0000c028103040390600307a001d0700704042c0d8805900345a0343c1900692090f00c5581c1034400440005040c0c9100b04e9180403940c0103034004114128040e00041881c501c1403410924001e040ea24170740300c200c02503a0310036844143c8034081c03003000f07000d02c5081c0240101010750b40c1140b5082c0d400414040005889461081d008581807900792000c1003030686064008041c1c075103039034030766281d058590402d1040340b041e0320b8000b000c14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12944791 1250 12943541 12943543
    0x604060902090916020c0a03060506040501080307050303070e040e0f1b04060e0f060103110d0b01020106060903110d140708150a060b0d0e0313080a060f0605131a030102030906090d02 80
    0x1160140b003e041004580e540000000a50302500d00400075405003411880320b41e038a694004000e0f42c0b1031080060103080c02d01c140300072a581604011550b0748100951000300313800106490b0b1003003d40c43d01c42c011105041c0410050002549103110314481e125001406107004140303003400301036011300d40081d01d10010410081d6507452046024003175008020800c1c000710a881c05500c41c0041c1000318031310309480c42003040d6a0001982d20400c40d030304c903003c5495603820b0080c00c0040c50341d40f82205600e411500d40c0e181d00070300005510310807003c1180c203104110081d071901c0c540341010000d81d400b01d42d0390101e1139240c681d050903402d88241814009001c54980784201800d450801c451503081c2054581d081c801088507440c252002e10007070043e0580305c004103038001c0191000801400c0381c1400c41c940740c1d096035a90713002c480000e4184a020710140d2202c0e03402c20484440b000d408280030b100001d5001c0280342c4070840071b825500010070400d4420000a446010b5607046044403a540108e00080f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12946041 1250 12944791 12944797
    0x10807081003060902041103010303170108060f06060306010e040608010b010909020a02030a050705100515010f090e071b08070f0506010909080702040203090f0d0f02070e010b0702040e10090b0604060902 89
    0x942003540e038001d000d2001c02c60304c0e88600301c2c662018000103006100c0c58202001034100342d10480001d82d890032516410b940003200c0c1401400c440c00107003210304244044101c060801019140035542c0440082e10b1680304584410190380d01410401c035035511900c1e8540a080c000403040d011400922000401401078400c072412051107030f014500741401c2c400103c80390351020f0002d03186485611001e03a402e0049108080c007807004070a9051240c440d1000140006109005100500070480001c02050291108541d03000d1098030b052240070300703203507000501c1c1346542001038400380010448108100001c0e0740200e00a000710100c65807070383d881010030305032002d030300b0001c01000c418450f100040c20300740c02854118550b00c2c1900d2101101c0751160345861450681e14002484c04510115201c1d014884880501b4a00d00c0c40441d543c1801d809004512030f0f6940203008543d00d031041c42e41c1000034050042060b00310201401000054184200c00c0c51003a07500030300c03982c58014001a80d0038a4030031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12947291 1250 12946041 12946051
    0xf060501020f100c0c08030705030109050f0f01050906011202120a0b030a050304090b0402040b0d0b010306060e0306010e07022a010f080402130e0c061308010608070b04170102040b070503030601080708 88
    0x4012400203071000c600030300850402002403040c40e03101e17100000d03107442c0654841c07156030343c071203031203600d01000401550809004005d46034460000e004902e88030501007410f65a00fa10402d141b51904001221032070700000110304000e01c08906820001e030021001801005441018001c00030010101501c5440303a100c020020703407080004200c4c044c180c1e00079000c42c0030000d000604041d6035101c107000d0350f44014200c7c19015500d0b40d00a00c65038161080038081c0810746031403444c00070003001082d40c0384810700442d0105072140d000200600d100708611035004144044910003505074000710601a60442d24080c081200241d140000c28805c03c500742c45a42c00800780d180448000c45038800504c502050f05009024868840c03840341c03100303002030040b41103105007030202c1c51424005c2e41c2110b2854000014a40003548200108491401600d082e5000c02e003500c1c80d03100240303010600a02c80e41e404180705a07004109002488804000f45200c0c20003a282e071011030380c6e500012600014200d80d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12948541 1250 12947291 12947293
    0x9010f0e07110703171c05060f0409050304150203030108010c02211c06060c0b010e010302010c0206030703090c0f09140105130f0609110705120a05070201030509030d050a0f060501020f 81
    0x80d03021440744114140c0354074034205503400f00c4e84a40325840302141011491560001c00507040080401d0070340750703070310400b0300031030411841c01e01000084c603c2c400106414412074a8001003c00c4c0031092007200d005180c41681c0a211800c5010040d4480d00240301d2200c0315441e1400c50ba03201030000c43d07001c12190280c141040c58400f1078640c8080c1d0342264281e000f249000800c0004050100c0c0726100140c000c5407681c2d0710480031442c01e0f203a8140140c01c9501000c00072001000142d802c012030f01c54041d8101c8145899a448803400c07001046803907005400c0580e040c000180f02d45551b0311050566803c41c0052203040004009152081003c0c8515600100074039640b28104000394400200903c21400104001e0b581c2d00d084020b0b55a01a07620800000020b1756408000c0100030004054610740c0d6035600704148e414024216000700d40d8003a041c15107420025141d00024000c80d40d0a59081c0740400103400c10018007002030500085021289191060110b540d42c000035034100f071030030300790 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12949647 1106 12948541 12948569
    0x80c01300614060c10090f0605010e040c051c0303020a110f0102090307060906050403080f120403030603030305090f030319090c03030c030909090809010f110706090509010f 76
    0x42e032a20702c03410342040110700e110300101e1110050429814000313500038407400c001c00e915500103001403d081c5002c0c00070912203090441c03240200d019a0340920381684920a001981e00b0004194000304c41484161000a21a40081551000c2c900d001407040ca07003000307010710f4401c0b07a025030b40260b50042111041c0742410044100140403070f24022841d10f203000f001415034862800050402440003034409040b541003021110720300d000b040209103070f02c3c0c5820300500522007030104400082c02c04000c203501c040002602c4c451624002d0240d46540c98622151144902031407005100d6610703860007401003203000040c60000c6020f40c551034003002c85440c008110041c20707081903e4080c038000d03012005c100501c040c0d50034034100303081c40f1195451100c0182ea10b01d0382086920824031501c20040750031540294410100c07241900c000b82941d0b00c07822150040651800340740d0030034a0314 = true := by decide +kernel

theorem cover : BRFrame.Cov 12769791 12949647 := by
  have h0 := BRFrame.cov_init 12769791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12769791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12769791 ≤ n) (h2 : n < 12949647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
