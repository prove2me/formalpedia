-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:40:59.798852+00:00
-- url     : https://prove2.me/submissions/c52f8655-fdbe-4b11-86a2-d0bb0162aca2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12589935 ≤ n < 12769791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12591185 1250 12589935 12589939
    0x4120c0501170135010504120210091109060613090b0418021804060204080a0804050405010602030a05031501030b0924060f0706090501150e090705010201020703050702010305040c031b05 82
    0x240080381d00e0701c002500c0c6281a54141d107400c4c81d400d46242c850084144601481150042c6102040000104280109441140161605540b84c440a8002031410b040740002c0d02c0400c0c82e0090500c000f0b2068010314515041c1216250340603103404000481c2441001507403003c00249100010384051103070400d030010541200c0401204010784044410600c59800095000074800300d441c00d00bc2c0b4105006420034002c070001402c041e2650083d80c03620f100480d06458174400400c0801c008d01e0325008140c094035803032002e141400040900503040e0701015182100d80500c1e24418034180c0d200f03601c91b004424000700540d8060030041c0b04007a81840ca010103030702031002d89885e1609400c054040324a50004a2a010301e00102511098002c0441d05000c0714903540700c4814030301e461140024000a0700110580380e4103420800c446510f400b11590140c0d0659006026040200740c215003a61a055020308002c12103954510b0101e8214015400040942c1128000400c0504a2440c0344081d5841 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12592435 1250 12591185 12591197
    0x11090306090d031808070204020a0c02060a020a050f0d0206071b060c0e130c09050105090607120f02060a090201050403080a1206080d020f0a1e020102070e04060203040b06120a030f020304120c0501 86
    0x2c138006030100b401025102410026041040310014213041d40207080e4016649002009041540e000070f2030313607004051300c00040e1b21114010050040c140004403400384880010200e00c0701041c00a5103035940104980d050101010003440c1214003041c0142c08158400010040341003040d8028103140348524540d8003c0210a5506010686500c20038140400311384880c0f218510304801103690b0750141c8002c1d0f40106051144800150707e6008000314003100307032250091000802c40091800c603009003681061424881d506000d80d0f000301c03ca034107490f00006003642c1c4081b05802912420f030303d40a45400b252408200084864022640e41000e01c0682d00341d401c10a4500c4130542c1d83c10500201500c200d40314200440706005000d100ea0780707944180182d980043c1e4403032171001c062208450550701680c00004100820062204507a4040022a96507501d590103103412a52021801401401e00581d07400d0100341d0b034001c00c00c0d140104056072020030150b0341c80c9000c82298280e03114243c00b06d10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12593685 1250 12592435 12592451
    0x1030309050409210309150207140303150d0602040302190602011a1302070203070e010303030509060109050c09010809010608030a0914040902010518040f06080a02011103090a060311090306090d03 86
    0x42c090082080c2c0542003116001e04100b18002078803410001c08040050580d61103041000411590b4541442e0b40c0e54000180c50b4090740c20f2041560300700c118500102c0d04104100803907008901c038554103400c01595000100c8c145c07403818400078407072600702031b6003c0c41c1c030385601114580440d54031040d911103034024015111013415200b9054900c0303020a80c0028240b60407502d4200550141001c140000c0460b440d080d0394400d1003501d150700381c0007500040d8a410400c41106001c10005004000c0440200f00901e0a071044801038005d0000d49410420050003140107054250003202c050001d80c0280c95039140c40620103010f0326024403550040302e42402c441c9140746482e2044d03162140d01030315001d03e400000c0f144541101c100c2c0f41e105078401d58407004030010420503c600000b4001c0840107100e400403500000d00100850b0f54001c0e0313a54401c22225400d0b440782007490003204d0340b078180410358000e000341040243c00749042d0b0039010300c00c1800f00219400c0009852740ca0100a84003000458 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12594935 1250 12593685 12593689
    0x16020f01031a09060a030b010e010618030b0402010819180c1403060610030e06010b0705011503020a0b07050a0f05030304030f0207030305070818030f010f0f0915090203150f0103030905 81
    0x222110360303031021038454151050312401d0030012164003036130040c40003a01d43d80702e90340c0c4040e02100b85c0210900d0700c001342c018040b0f0341d00101520400031490103d6050146599a54948450010300c002d0402244602007035200034501500192421110002e01c40da0650402200c0aa0001241900c21103002c580c0000c0d001540302d2456140103001d8040c25541c1e440c507003840544214071844a0805076100400b55440c5414040325000c0c013051050b269940083d17052190a4500b9103420004140d46c5a0702000141d4401a9101c100c582c103403a283d0320f17441d0506111b03040a08440f009000d00911100d008100440800154802c6200b525403004040c42088200c0c0d4845a03400000c0110b0b40811264001c244820301a003210008031074440f0000c0e0304000800d04013034107007058498a039118900364904409034014001c0c0071080300f10810004142d91190840640303041002825036030f44405000a6403014800506a2000171b08524114105a2082c0383e0b1414240b01c15000102c090002241d58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12596185 1250 12594935 12594941
    0x9010315060b13030f050a0506090c09010915060e0d06090f050d0f0e091302030d02010c03050901090c0902030606040506040e0402090c090618030f0d020708060108010c020303010320040216020f0103 87
    0x51103440c03d1402c1d0303c60556030b8045003002e0494050303030140315900115000490401005115510010281c0041c0d65204107110b51410113030415980d003820109030291310044400490116415494149848075144000c1094030a100c840a40000e00f4040400207014050790450b00e00391050f0b00710b515015540c070741125440300c004892000103c03c072425052500d01141050341140d02400f610348441e50581c000b03441c10401c0e00201015035114030f0314004035601481440c1e80001f060000380701c2d141e450394511017000124003441c0c040c2513021002c1340c515218034042d1006448040e041507985c036264101500046011a4100d1007000d110000402400508054810045000c3e20181c18103262010b488040006900015050300c59600e20180e02c400421589401c2d84c041c0e0007420070329091000035800c0440580002d196681012085e0031015400421039044a40225082030112081e40c00c074014150b40c80d030b0581d4814008107030010360407041c800340c84204cc0b084414400c2419610010340c25 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12597435 1250 12596185 12596197
    0x106080604060b04020405060c0609060a0c1704050102120c04030c0902040b0414010e030d09050a050f100f020c0303040306050601030c0e0303040b07050f0303041a010b030103120f030b09010315060b 87
    0x105400c09408a40040c50942210284940080001d410151a000401c000f0303001500508d20550145090042001c0c05110f1250002800c64040c40400a41368024042806d03524070ac00f48000c00c2d00004003800340a43c103890030110100410129800e040c3e0140b005074000380410307555a600520006000825803080764210354402080604062034454003002d01c51171954200c3c1031103a180c92310b20090fa81400043e01552403519171182c000e0902c1c1c140301d200c1445400080c010303100803003201c045559541c1a503c010b0039a140c103440000000f00101c0c01c090302e000a19406100c0858044200f20030794120071311614080c0d80800400c05885801c88000c80840480e40d00758000300410701041042d00c0060003403d0140c0c040314400c540a4441c2c81c5103a000329015124100f500f01c50000140d46018068010640c170380030f550455041d512440300703200c0c5450403003041c0028140084112406a00b181e0501d030300003851a4669a900e003006400d0010320f00e0281e00040c03030140003007440c0c5646015100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12598685 1250 12597435 12597449
    0xf0308010f080105190c0201020d05010b0d0c1d040e070305060405010f110304030e0108090c0d0f0201140a02030412150203160306050409080d0f09080313110d03022d030d0b0a05030106 81
    0xc1503100345d8107440700901040b100e03c02195000c01c611079410469019030b6000b0880d901c801d0b41d030f81018103a000100c4540c4029002007015442100ca0301910f1309809010303171903040f036001681060340c0e151103145c01100c1e84010440d0080004210501c07070190f002c04a0146e149805010200099691440501c822076008000c15614510f24145c0e500c69000340d0340c0300410400b02e07106115420005a4044503074207084400d158254910307821940d0003590400c00e64029a6854285014a6400b030349a0195020f00c2c0f400100802180b01842086045001c0800300b14008540c0c07418580051480181c3d2a0030b8400843d00300300780003c190919200704a0705607001485c007418400b401190501502000c003070100d0303054480d00c001010400380343c01540502043e0705c41c000c44058900d480e15165000714081442840303100c0110380403d4010400300c02000201040841914120b11440c040c0c09040210004510020035409501c11281d030159901d190300f00c0d9072100c8141d64200f018280c2d04075004100e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12599935 1250 12598685 12598711
    0x60709030312051909080705011407090e04020102030d09050c0109080313030305030c04030812010306050606070c03032105070c0203100516050f0f0d060608060d020303031b04030f0308010f080105 86
    0xd80300c1c010b580440d40000d50304c070800628509400500040d507503000b40650b01028001165000c100e400d1207400044006007030380c02507610380a14090900c50703091081b54410603080b400901103a03c03e2003210f811440c02c600821000e00d003820180d6954100004540c0414111400840d0781c903c0042500e002405500e03034039403d64115a8200c406030400f402000d081182030101000040c0a03001820b8004ca20340f0700204a589141031650a8134409080e0a01030f034400c21004010418000c1a5403d894060406070014040c81c0610070700c8113101c10039140c00e94507010a004c082c0d54000700c9c034a20305008a04507864071302030081c503504640003035a40202002c01100d003026818080c1c00a0650a480070014909203094845503081961000f110b05000740d03900c0400f23115403030f001a01ccc45e400030410ba420710f1151180e035010079540c1c031002e01071280010501f80000112001c0008503070203198003d600c1501c2ca0366516014003002406c0c00f408041c46a0040e0100e0705160522590344034444a00d400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12601185 1250 12599935 12599957
    0x50402030309040e0703080c0303040c0603020720010c020910090b01020115030b1009050f0601080c090d03120e010905070303110f06010b0304080c060906040302070603020c070302040509011b0507050607090303 92
    0x4020021000c0b0404c150080e002c00001141c024000b402540003c64080c5a803803409150101640a054000f00c0c24140305010800100d407001144101c8416668003010350300b411500166100022200f00a40c000e04001c03c000b2031204a0b809042100c284541c1840f03038545400040e400e03200c0940301d450300e4105103001003000c1000d180c00c003a0070190b4602c04d400916100c202c4842a50004c4403907041c4500e007030301444500e580c0108141d41c02550032450508180368007000858490382000080c00304800388011081840080e400080500e0041008000e2102c1c130340383c0756407191120710050300415107150100e00041c001080b506502c0d0441406008181c0c00d010072f80440c2d40002d8000da84a607002d01903080d40b1542005901c1c021102c44009081e5890186802440c0102a8120340c04040c010300495000d403100040c1501929411540800c0030b50310b400505004001d0002552400865403600030351054000c8010100940124152911a5030789032064617004e030188002000075030041d0072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12602435 1250 12601185 12601189
    0x606080702120906030a020c0a1118071e03020405100c0506070503100b0c010f05040302010b09160e0f030c0d0f03030e030f03130c081b0111120f070501020f0a05040801050604050402030309 83
    0x556028410400050408e000748401a1807d030700c00108a554000e070b201c100106150541c25440c0d07000c4010142c80603440c0050f07005103404100355080840030310030300e04441c685003c2e0701580c000e0400503010252542a90b40024000c514861042d501c0b40124000f051401e40f00e40d049a100d00203a0502030320051410000441c6940000e41c5400195601c0309071a9243c5480c1c0a040d01950199001099240f122001c000d5a40c001030905a80002c44110340c1a603d60030072040d213100ca20880380c08020445003008281007154951940f41c1c004031b091341d5603041001c09103c1d4402e46000395410402c1e0030b0030380c20740c941c5c1f48910945482415000d2001860b601c80f100100b0205a124452041a0642d40c007411440c020b1326101d81e445d4894212a414041c0d40cbc40300c150102094108010900b951b140410410203125414507102900c200080c100c041c41825011281034032400c6104503518202e241313009000d03400500503030006500341408294949080d0040b00d0089800030042e41ca0300d480f500c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12603685 1250 12602435 12602437
    0x1b07080c03070c090608100902010e01181511060c090109140607060e0601090e030301050901050d03050c030a0806040c050a021203191407020d09060203070204051b030405010606080702120906 84
    0x3980940921003001018002040c2000301001002c140d40d000c14200c0c00c003000c440c01e01003a101050703800ca10700082400540e901200d8401c200c0303c00c2c28003504400d00c2103000e42d0710340c0d07080e0032408804041b2103002503404d1b4803200002001000c1c0013076078059242c150340c4040714451a035055000481c1894103109032403400b8402402c003d00105040e10b049503030b656140540f640d80c80444c1c499005500100a038082070701681c2d118080b010003452031507040c031000800c2050b060142c24001c20706102540f0030980684111950039444400300d98542d00481001041810121400b5001c1d42c140f644050881e409034041d0742c0c034407000e074018007012075134000603c00503000140300d401207003141d503645003250001d0700c90410300c2044100c170407800381781030b4102034580700239401c0081c20400e044208200c129404000c1c2c8800560489011403184c5828015a54040801d042480300c09000000c3c0f008100056204c00101c540e80c1c5c449030b9140c0c0d15030302c0c16600d0328401d10000030146000c10600b4a94a0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12604935 1250 12603685 12603697
    0x7050a050d0605030f06040606120510020307030915060515030708060d060b060c0105010906080703050601060c051e060402010306090b1e130213091104060507030305090708030307020706081b0708 86
    0x481c0025902d9910000a403420103243d060004d244c0290080c4001d000d07550142c000940040301c0088107015032a92515030b10060a01c100c500c00d9804004140c03a01d10a4101880c015040307480d40c4440700440c43c80c40300420309881098854085c02d14141003141e40802a40d00c1860350ba1148201b0356560400e0110820044038100e0b5043e41e00d640d2600d2594400b0003a2100c00800000042c0d0341d818a030420003161201d0308980030b0366004000c00c000281e80090410b05543c400c0c035000300c17041e1042c50801d24000c508142e90404a960001d03c0a220000054003840b860003660144149030b5608900e130115050900c20035044241c0d2038074030000c0b80c4d40150380d40090101820300112122241c052000b00d0308024507030440700d58030141c10007510480d4040c6031101154200c0003460645868000713400e0b841140c8004040c19202c80000f000c260040c09134500520802e4190ba950b0b1600d584000d45030407a90040d40b0100d000d48010a10921003070f542c0d20000e1080241c010b14000480d05c44100c107030440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12606185 1250 12604935 12604957
    0x5070302040c05120901060806010501050f040b0d0902010f0806091302060705120910050906030402010311090a0828050a0305070c0803040b070606060807080406020f1e0409060b0307050a05 83
    0x40540080103032118032416640721015503619440f81c61141469881410140020013541e040c10f20521500e480442c0c890b0440d4403d00b842c543c0ea4800340c030150a140a075501c031000d01c035000b0901e1402c1c141c0d03503080404d2452003642c034002c40342c4096600340c65000007a10705036001150400001c40c0ca0b0326250400100381d00080c00341e402c0c440c266403064a0000d03c20b8842c0c440d03010100316200503040c1580c7d40c0d0116000c1c2d0409504010940f40852140c2c040100082d0402d0f8444448106030260302c4111808040007420a02c825905d41481680d01e00c5010711450010a040301034507181c0213182182004141d104002d04804221a2000c07109600002025140400d95040021b20460304000a00090109501582e26002241000d9086420310303401042401405400c120703240da445402c44c3e91003035000d8001604d55007540720141c9180183c805a00000121004240c00d44480001030021074980c3ca40900c211030f201c8250051a003c15103810340822400c2c040c00224a0040b80500b42074452 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12607435 1250 12606185 12606193
    0x80c03090d06060509010e04030f0305060a0b120105010e0f030a020d0501060509010e060406060806010816031b050705010e12030a05040f0c0306050a06060f02030406050906070b010806070206090c0603011205 91
    0x345800210405520201140c5265507581c08004908051403100d0062486081c651f815107440d84000c8c0c9640c0c440031441080594803400601550b131826081d0015040700c00300c50392507010020416140940a000310350200359074007810406450305540c1040002c1c030140c01b40196442603800d0000002c50144122030f81d540307a441c040b507192a40481c0c1402001c2506201056050041c01e200445580e50409000c201c694820040e40e640c005040c5508498000d112103c03110b2108001c41c010003039120382c40c006103c9450304c0741a1592100207400b038680100000c00040d000f07a50b0255840c80041280c10000340203000240c40c0910a9000a601c80e0044119448074070750342d901c0030070942e8140c00072920307207070703250140180215544a0f00014014a041408140400d088041e541c0c0c05280b258901300840050800e40c0c0c2d403070340010380d000740d0340c030511110745540c59500d180c0c1c503400d0032121031005100e003c00103140c106002a100b4071900d000382880c1d26690030100c004001c1c0808910030741311842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12608685 1250 12607435 12607447
    0x70b1c0608010516030c020a021f030608030310170303090d05070501020903030424030e0c060711040e0102270105040302100201020c06040302060604110309100c120603060204060905120604080c03 86
    0x350a0090f64468009601c0d520403031101400c0260484440c25208021940500035a80050b01e5198540144051501c03101c6030007060b44000310082c0c20307203400c12082c0d0301011040c01020044810414107507084084c6143c1030140300e080c015920f01080b07490100c06d41c4054420548140036a0007000110b000300000340ca0b0446120119245074041d40c0060500e0141140744454070822001039444201d10740703018000852a010342c6c80d5150521442c092041c2e000007081401c0046c8901000600c13a070141c0b0600c01d00b01d04480060007504415031240044201c15510b254803003442e1942d00500005031607a138205403e503000d11038a40781101c0751400350741d420084040c0d45a000c000e0302d80305920907801000e292070080148002e80d41c0d500c400340301b00003090050180700c0c3c40124056101c1c0441841c00100c2004155003151a10711905220203000c1c1b4111001c001c2c81941e400400a540c2540c0b107961740b003507860060007900354184401c0507994001074003103030006886030000c22050748c503e4100c0f41440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12609935 1250 12608685 12608699
    0xf090d0b07050901030e01020702030a0b0a020d090804050a06020f030a1209050a0605090c03070317070f02180a0501061b03030b0112020c0c030601080a050307030e010c060c050318070b1c06 83
    0x45060381c100300031840100300d4541a40e4580a00400e0719810340003542404030640c0882d650b03122a900060460701b1000002d951045103906a134104800b0407000d120710805410211a103900c40d0103290700401940c400031401c0740c0005241c50210710460020361500072000002c66060300c0d10f11000350004d8861000c0780c0450820458001d250303018200c0003865040c800412482c0c080c40c1448180240c1042604102059050b0b0b25005a4000052116511080e52404c4038800c0c1080780e000f5070000c1360f1140c040d0b208807010000781c4210111441001280d8994205551000a442202c2e42c1480d0a8501e680024845c1e04803000900040c1420000c0858801000c42a41c1100a43c8483c6038801c0c0400c521a2804024060040150601602c41c0e18100d03100c00c0d840303229040c6c0140600068903c03514460744511045d01c402074014500300503680200a0003001c0780d00554501e030f20f1b200042807011060701c0106a940441e003403100550718000b0071044101400c00680400280075a035440300013015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12611185 1250 12609935 12609953
    0xa1404060201021c05060a06030209031e060405060109050606030a0c0306050402190201140601090b070503040503010911010201051e0a11070c080a0314030402090c0306030102070204090308010f050d080f090d 91
    0x19141070340002d6100c8043e07038100032941c4c068001e0081c041d8140320920419460380d01a60b000c2d20314516016950f04c484402180c41d003d080c20440103001144810b0018541c000301e42580a24800c5060300d483e641d072081004282e64003500c40aa00820400c0860441da88940c0704111540f501d09020880981c1c0d00009030481c0c0001d80800c5000b0090004814503540c20700c910412220076031110011801d14100083c1082081d0240700e0380f03580700003100760a0202c108151401400018002d0207415043d241030340c1e0351813114071580d0143d824240400c946d400803002a001140024078502c41070358494280002800c0c1040c2c0882e0340d01801c104040218038019802000b03021148003c0c1503030141860000c0151058044c103d210107428003e0100690b03a0b4005e40d50030500120328141c480e1034000010340244540003009500c00d1600620608040e08082d01074102c0f42c160754104026a601c00c180003800050380002010b01c1004c000d45149100c0d00c2022704440702c0301500040c08601c1035540d014403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12612435 1250 12611185 12611189
    0x10912020d140408060103060b0612010306020702040b0f0f092d0103030f09060507060b0a090510060905011103071e05030a081f120204050402010e0409030507020301180209010303050a1404 83
    0x6800003646000707071a401c48801c401c80c900000340189001e2074a000591640010301000301380b2900c40c00b00000320f50741c0d0303404c0c0c8003c0b10f1520704041f60b6503520f10703205d80298400c0742c00300c1c040d9040c40103040481c908242c5200b08000050a480c2c42820500d04114401100400c0201c0c0305031420f031607041c44880201110186200050504069411800c01508061103510b40604004038401c1c1403100780d80c04019075400035480725000c1080e1400030006224000d10350010000c95180c68200720f441c00c02c0900300f400315001600c0b070400d966214001100c0881140d905820154002c109150000702d00c184c0d045090343c0c044221030130580c0b46944503419544515218400601181c0c1480081d070041c134041d003080e486c24681502002e182003100076507070110050291159540700001410b41e400380d8403661901000034800c000108091034040c2043d000b43c070341030707000c1e610f058010300000c03e1003400795000b6600100240c03075aa00c4c0d0f507011030301c82e480304154408000308500c003090030704854809400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12613685 1250 12612435 12612437
    0x40333020f07060b040603030c0602030403170c0901180b040e0903070605180106120b1602071e06080117070509040302030d0f090210030908040b0c0c36060109060c05010912 76
    0x41d42c0c010900308001070f505040340d00c62096240000410000b50040a40d110440c1d10040c0581c0742e41d41d0f814107a410003c8000711080c2c03451a40100f09000120f04010074140c1401d0303c441c3c0844a80070b50402070400700d4021403e010a0030003050000c85101000707103070b0010700d0703404030791801c1180d503504020b8030720a41c1c2100d18500d441c0c03140c1ca1480d00c00c1c080c06010b03081c2e4040c811151520b9403680c4002c2e50001e01070b840ea008012441216403031082c0602c90207441600c00d5034901007404120784948448502c0340303c00050304840003085405d03864568039000c010600040c1101810001000350340c2102600c22030540c03100304140616a24540900c0e404581c44100c0081c0301c003a140140100c1103100d010352020946009140c4000807402401c0d201030315603102c2e50070f4644d07401300000f520f441440c0f03030f5260b400445600b44202015a040300b01c4d001d04915902441041c40d410245404039209480030b501045c0c5c2a201404814883c01030312072880d000324004205600142c07038802807104141c14481c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12614935 1250 12613685 12613687
    0x225050d110a140306070804030315060906020d0203030907030308060d14070515070b070810030203070e070f021605012f0c1c020f0904080c0f030702030111040333020f 74
    0x44107601d40b101c00d80e801030108095a881070880d03a0006a03d580c8000d01e41d100344502040072400b450303c281c0c0074106080c003020799402000c0d03d4039805000c03441217108000051040a52001c00701c0e1001c401c4e24002e40440004154650542d0703800c1c0d400c51001403103030350802c4005958002040c00940100444400c50001e06103a5050905100c0b91001000e0400801c100410580700000c840f0b07012281d0098035071412803800c0e106c030300e80401940c1003580003a51510421901060006c05508254025029502d801104840c5054141d03210a800e040302005000092002c000c5540240080710000380b0040c880c0c0562480c00e0b440303a80380c210240307203400341d0b40c0021401c4502341449501112819110f198007040f104495000070022a402c0705d40d5400b488c03601c4c020508200c505007c0e1503801410006950300656010303107495681d000a1410b0f4403941c206030084101c01c034a0000c442c10b0340e803c0030082280405d449010501d10101d00403522049000c000859401c2035544050002084481d48003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12616185 1250 12614935 12614963
    0x10b040801140601050724020a050315010801030503070b0604090602070b09010c03050c160f0501140f0c0403120503071205010b0706060806070503071d0405010e01030b0a050105010225050d 83
    0x1608480b14003181824035001c4500340b010a0382c0144c20744034001d61150003d411a4000b2000c0035800070000070600b400c0c2d002141d0040c0c1d041d082005980700d070341c0c0c0c1c840c6400c503111b405c401107910050030701c0090010340007040100d0116200121403648090081d00201300c910700740d42c0f90012603011010540315100284107002030312000303020b02e04018150b480c00b0b220b1400e25a549503094840c2e41003035040c84000149090030403a01d940291540d030f42120080050801090705258620001c55121440001e000c002400b2400c04000791407e80383c00c00d501c02c0d00010001e605441580c0301030950024070543c00e81c0d14141c02c522303024090207004d8110070b0319142d501d14034010b02a942290040c400c2c5400c40c0741005070080c2d1190503254000c0d260f150111481c001009051282c0702000b0440360031508040002c100c4218280e6010704a82c482e81d458145071341c0b001c00e0501210303828042c00340142c07c0312325040030300c0c141c458a403105140307024901c1400c0da503142c0000708840c000c4103003141c0d8500c0d16030f10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12617435 1250 12616185 12616199
    0x30403080405150c040501120603080f03040b0108010c080402040905150a020405030d02070b0f03061807020105011503020a09031205130e060f0a03030207030609060603020306072c060417011103010b04 88
    0x44007480b00f9154164000c54140840803080501071401802e041240184c64150480255086000115006880255141c0d91700030002c5030795000f00d40503103000c4803800001400140500c0f03100315414250b9600c02c8240c42e50350812014105180b0150b805120f07000c10740c00c894900310440740c011038028500580c0e6601c3c1409060400c8802403025042d900211400c02100b80030b0001c031800d0a80001e0065540c0c0d0f1118001040c1180500107a85c0c54416082004980c58055104a060302c8110600704440008103000b202688103000d450000104443c0d41040040c4c0002d55040180e101818031381e0404030249c104001d4810700c1d074012040700190301c00740012030800440c00ea0110740180c0d8500f01203820b684003e560b40b003c0303100c0104041c0c2e94845980034082d066010401840c0e004007a1040b9062401c0c0080003030610420744007044010140d105a8008d11031900c03010b088015100c0c5041614000d51003441005010401c1c0701d55403106c00041c0404541002075001e01411043d060b00d07181043c40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12618685 1250 12617435 12617443
    0xa0510060507020a030b0c04080312040302060604062402030c0109031d010201060e13080f070b040b0a0c0e040e030409090804060207080601060c02040902010e060301060504051905010e010507030e0303030403080405 94
    0x40400e007030120410180c00540c440f04031074025282c000c0c00140c242d0300e802c2d10340119446a540840214000810b5140d044040a80440d004034029401c03a030b250b46074982000122041c91052030010301c0c0707048001c0009243d0188132845a0302d2030040d241001d0540c03102c682560302e100b0049000401d440c2d40405401c2c04542500f940060a04c02001014140a42700c4408540a0200c4011f403001100704010445442e040f58a0003140700c0040340c86076102d2401d1280401c003910200c8112085c5070004207001c20a102e1460f2a1000350740d034019105107030b4107000003031080400c03440c0c2a00081002003403000403401621803c41c4103a03c039a0350b55140841c024200315882c1c21021441d08601c1c0104170040c1d0110711042101c3c0c04031800201007007030b40300607510303805d98504280d007101010000103021504000640700301c940555090b110728115900003464081d1a0051901041c182c804145081d4450000b501b4079a2283c01c0546c2014030040009195400c201c0e02200001e0310b1174100410044140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12619935 1250 12618685 12618689
    0xc070510050c0405011b050304060f1214130f0c17060c09010c12030f140709060201090203060a0509070902071101030e0d020d0f090b0c030d060806040b0c07080403020303030a0510 79
    0xe50108240d00701074910070418402c1c1c0c442d89040211842100280b010031200404e6140d50007411646d45541d1076501903c004441320508000c280a0b00a140710700307005008403a0f01660f601ca48040741e039a54094445c0c4503910300c0c82074915440c1c210051000482c1c4180b0640030340a04902d816066180e101c9441c50310200400c0340606050a201154040e6000440c0503140fa07803000140c0800e0700d01c45411001800740641c65207039182040c800d14902d50716601000d00881540e0746002c185611104181d00b42c400319034000750541c3c0641d00081d540f484039485290081d2800e02a0345c1015138903260201a0307005810f068941d1521200160880d680501c20004800d80c038034081c00c0000700d00c950103920b5880b040703003480c01e008001850002443c803d10300c5d40040c0207552400383d00d80b8400e06c8482d40c0c81e0414000c002c08207241010206e0214000500715211329807010401d860b0382d80c1c0d201c103070340385800808080301c02d10014000440141e030140055803240459980009091070003032600a040347e02c903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12621185 1250 12619935 12619963
    0xf04050a0905161106040305030402150703030c1202070c1818060213270507050c0a05060103050d0201060803030a0902150a0503090c0a080d0e030a0b07021b03010b1c03090e0c0705 79
    0x104e40c1074004803902054080e881501810b01580340d951b01e001090070002d060942049016000031a002090b406922101d20f0105c181d81d000000c03458843c4800c201e1050440242070700794131070010040d0f02c1d2107990b2400d00d07012481011a81441d02c3c03010884003455071900b260184e8010a04410014203c08010b0092032419605008907810011740f03c042ea02070042c0030703100340d11280001d20690140741201d864440200c12605071a255081142c0ca81200b80400c840c0c0d80034409000c174000d0b10502404d019185610065861601d0f8044224018120444200d0b04403000e5401d481c00c50400a01404000300170b80c44481c0e0700d180000e245406c102c00005503d11030440c0f250b0500810b100092001d088040e20305050500704080740c002441d0001c0c0e40b41c010810303210030007003202d540da02181d8201c1c410648141d03903400c801c40034205400d90f00b495003202d401c081c5615107852070044604001c1c4119019003015560729444a000030401d4004640c107048100780010f440041100410140e44421a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12622435 1250 12621185 12621197
    0x4090506010e060f07020d0203120d180b0105010809070305010203100314060103080901030209040906050106051b0c01050307120e100605011202090a0b030405070803120f010e06030a080f04050a090516 88
    0x142c0d00080e000d401074202205100f20041062000c41d00d4090408a441c1e0300201119900c0020100d00300c5558015607170440c0c018100b8041219001c001e14500c07056680c0010b80c005140e0030f20b4011111440c004261301c034103104ac0f4100101281d820300c01180074240d640d05041d4281d043d400c01d460791420807410500940d201c1001040852100000d070f032442407003440c0140e40c61452400060140a00b002e0103020103107003400000306660408004e140c0b0840c40f0154400c090803410301c035a1216503c41d00c881c04607034204000354102e40300d004085241055010001564290b100d100d6161032100e1003942482a07030740d0380c1400309681143c0344880801071440c0030b43c6411a0040031558801d0300b480782e61031001c8040081010454140202c101500c100000c40340c448810400f900703c25002610000d0003858001d0010480000d8a00302038410a405802415000f5069840c102541d119100d0401c0140045c800443d284ea210240035006107124280450141442c8bc0001100640e002002c014042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12623685 1250 12622435 12622457
    0x90702160509060103060f0b12010e090703030305040f050d080604050c31320603091903090f0303020f100902010906050f0708041d0106020f0c04050603070b040b0409050601 76
    0x60514841056074020340d041c1c01507844100c0164041c00f074541044007042c00b01000411421103400140080712011a000030300d80c0d9840d2080c10b0001c10640344000141c00c081c0c018404640250005604584141c181d5585208191506820844004610b6001500c20000d01c0134916060050580242d500140349241400340304800f5001c0c41c000442040c4001288101d2082071a41c02c90307540102000c40901800500751810042c2d07009641c1180d84809440c3c50790101e6609100055900c0746038a0f600410004101000050b2000d60100d01201003280c810400300e50150a0055a402944260020619051a030450908049000c0203412801c1d01c0c1414a002603130344131103802c04540942c186165104001c4101c0c641920a00d20050100500080d0010380012178070703040b1072410085090f62520382d803240c104a881c0d2507411681750315a80801110225460968041d503000300b03009080707807501c40e61081402070b144c2190f48548500d01001c10100100d10f81802943e41c03194092802011002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12624935 1250 12623685 12623713
    0x30b04081206300f030f0705011401060c2004020406020a020102060603160303120f02040f0801140c030109020a0c0605100501020d050c07090506031f02040503010b04021602010509010c08120105090702 88
    0x564840c440d5420110600030480b0b080fa001c0c4280002001d20b02e060300d0341c400665014160541c8007500c222181d600e400d44180300c19504d914550b0595400d0742d200c449101042e00d4051910181e1004000c61184052041c005550741e84010401800a0340103002074500328000641082c2e401803009010360044041100d80c810b010100e0401c0c0c13603060401c0150b0014080300705000703068000081241c5840054081007480c40943e0312412a41d10b00000e01056005445014030490280e500700d003150028801446001c1107a0050070a070422071a0500450401e03840311401c0d20001c1d24642c00600c08854140115613040c010041c0114170b60501501e01103840c3d90003a0303558030b40d00c245072071307540d8902c0480c80303640d0705101d00f0114242c2284c03401076091840310442e00a40c403511a85100c0d40ca02055100d640c2042c0c000c0c1c1b810400c1070041039081040d55001503503154013901c141c07410020b55407600703000580028064524210120351418a031360500050084580e0080c040d201558417040511280c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12626185 1250 12624935 12624979
    0x3050d03111206040c090e01030c15020c03060103080d0e10090b0f1608040212030d050a0b040603050304030807060207020909030405130e100902061306030b040b0414040b06010504030b04081206 85
    0xc45404d82d0f000a5038441c14008036030700210b50300301c500d080c0460800003050062a4a0413000e80b00612201c95104540c00010303640c4506100c040c40c0c250f00b04000400104000c00c001d010018035034403002c07602c80003d011403030504401e2041c118116990b0903108062180004499a01035080200215035081108000c0e506d91200002d0108001704c803000202152200d5040081c00d0442c0c808903611042c0007003d41010307110032074603443e000d4030344103040c691351400340110404c680c1c11a02851901d1305549609040b0342c4142c00c20784031907808200110040e104d041d04680302d5600c2e40095900c0e241000304000da0070400603049d0840c141410b80b00091614003040b0b2040360b440407075001803c0301360352010406038007844031349400722000e07444d0004581c0d0b05a01b2510741da84007200c040204a40b140c080104a50000c0135014254550000080019078800e0b91a034125405060481c203080d81d0307681d10b940f10036007100c0840e500840403d2071080c451000e0384c070301d030000c000300c88004c00d828030040a0050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12627435 1250 12626185 12626191
    0x150d0204080304090c020c0901090f14070305070206070207050105070b040c0f080723130b012001020409050903030403021203070908190203060a0e030910050702031006051f0f0302030403020f060103050d031112 92
    0x20507680d4611211103401160301c0280381133002130000c455841c4c4002d001e00184000c8032480050f0190100051180784081040815554140c507440c1c18440c081c2c49003041148000c0c0110f507843c41c0755201240603050035104000810a440040ca10681031010307403080c880b011a480012005d410100c0003940d51040c0580c0e4045c07403154000120b07000d10000407129000e40b17816004180008584980f440c81d4190010030603100b0408003071009032610718005981c1d1000300d0380540103800c1003403510705541034030009540000041c40c100c0b00d40790711009514241681d029151450001241503441141000e114040e40031126407820418151985541512480b40c0d100061007000490780d1031081c940610160b401080c0c0103001c46403c2d1070f01c404881c008044c0d5025940c810300000d03c1017a0b041001030030000ca0710807540c2d19486d003c1100300f4294043d4001420450540c00351b90b800d088601002c000d02402140148010100c9010511015044a8104026807010481045101c00c148140340071513070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12628685 1250 12627435 12627449
    0xa0815090d0503101406160308060f0111190201110601080105010e010501050307020d110a080409050103171819030204090501050a05060103020a02061f030c080c090601170402150d0204080304090c020c0901 90
    0x40101e40c1017000440500c40c401c1ca500d0481011020300c0e081c581e118480c24800c1c2c40544034046a100840d0055a52030301a400b000103980c815200c42c0d80000b60b000c80120142d00c10706044038401310061550381041400d801104075030307554000410102d1403843d041c500410003030070103c2c5141001c56000b51684d00d082e42400c00e012f9920f40e00403c515017000000192a0000320941d100c5854200c0c4c40040d200a1109981020a040004c2c800c0b01c00c074000c892000b40e82442501d1818a00400d020359805036080c19448044a084c000001d600c0381d00400303c03101c0c882c40000a00303203000c420f0700b41243e4026090504051040c000d084490360001556600a400c500211100d44c0781d822000f07000210700d420080c1803141c80c82001030040790001c0c4140e03851100316050402ca070740e03a400444110329190800c20384081101c01181c058104941102000b005500300903181c44650001030040e40d0040e4800d81e402c0c1e10008040088422034460700011400c10b10207000b06500f9a00090309121060040c15 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12629935 1250 12628685 12628709
    0x5040e060a051005040603080705060703060605070b060402091507020103140603030a05160210050d0c0302090a03020111011d0a020310090b06090709090603030309060506040c0801060e0a0815090d050310 89
    0x90f41d44030000641c0c0000c02004105100c82602c1e41b070301c0c101c0d603001294101c400c2e00c90100071601490086c003034481a619180e68040c02c01000d80c884d6034184a01400e680d0300298200310000098688480c2c9401101e09190394641d030710424030006040301c0107000c040c042611715000b8021166808011a060203089103005911160726540101502a01101c020740c080c880e2110901419005805418940740110f000c100c07241107040c0c19000d0744600003190f90301061815042c00158001c6800c038141c5d094000000800420540c054903038030702862200c40e044c1d840790740d0f40f00851404011240510200f120140300352407295446080030380c40a03101511442c80300002524035071090850000400302c040c030600602780d503410060020070b480d5600342c428505003000a0001e0a0500070201d41440319076503d1a160306c4c10000700e84118100032801d50002c4d4660000500200801003403562561504180f80c181c20045400c0b4030309540d0b00194000d0020500800c01d55004034160b0104480a1150780 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12631185 1250 12629935 12629941
    0x507110c0102060c1605070e0f100b1309020a050d0e1608010e0304050f010c0609061b03020702010f050904060503010203010b0309011b080105061b01051503010b0402070b0a0906020f070302031305040e060a05 91
    0x6030816240da0451402d00023100304100140600d415218003500581e11007003141c0e91160150034540c0706118152240c000907210070440b4100540c0101056031691500d40e0500350f81190060a0b2051460200b0683d0300246101202c8005011900020320415000f0881d0f035100323031507540c1c42c1d00940c81490b1080403104801e8406074014591111541d511003400c011050452410700000d10100300c0d40c03143d000a0302c0046412600074421030b141c40750140c6880f000620411000c40e5036030304c085801170b0003940b07a1200040f036403000d001650203031404080e91501c03031808814507821a0304101c9007444440c8110710b4210016041600281507403030030b0783c1d800d40d80c121400c00b1290121400070441d419600e41000c000c0404a850315400d40000d04400038410355008000700400d900038500d02908900c0b02e40085109007296a010b018014071445001d400c02c2842c3c11414101d4108001c25005a080003a000400c101140111000f60800301c81c1040160344e00814181c0d86c0900921441406680e0008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12632435 1250 12631185 12631193
    0x102070506160206060609011710090606080610080610030515060c0105040c0b0301060215180102040602030d0b0307060c02090601090305160501030f051501050f07060507110c0102060c16 82
    0x4849115800c2001c444082c1410b51150b014000c00a40180060042c00e0104000345010300884850020503910008480c0300e4405203440d2420280a009510850324400200403450740075210003070041ea00c1e007001e14a40300c0180440e11000380c4d8040100004041000300d140c0d03507015100c940c0e0806280c0040d4541e1100c1c00404034001d40d00c5c01c00d520042c0402c0c845600481500800d1180d44124018540300340d82e98a18140c60100303000700c0700507800282c1c007405400812a0050f91058400d140950b00065401c2c3e580d08a912a41206006800004042003480c000b80203e1411303401c254000d100961a0807001040008880c070001d01c980e01a00c007041181e032080448902441d003000684401035001d18500a07400c02602c9402e020900740301400e85101d80300e105082c441c4400707200b9500711704500f83c01140d540d800340c40c0d403900440c0f09000f40700105a052088510840d030319101d104107890101c82c840d140c0f12600400d01e0455014034100b00f005c1c03084800f070380d2010072416490075400440d460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12633685 1250 12632435 12632437
    0xf03050708030408030103150902060d09081306020705010908030403050604061d0f0102030a0c090311060a02070f0603020301170604050c01080a020904050405060a050117150709050301020a030b101704080c0102 92
    0x10301802580d000310500c014080010001d50413680710304440000c0780c030100d042405541c4030380f2002e90f00000074040348110200680100c0c04442c17248180c940342140b242014071201050b03800000c010f0380300f040248500d52704640248081c085800c000c6041a14580d44c190f9100c1f0b008100810300b80e01c845122800400340814002c42d0318244040d0b540784034101300c07418001e41003103440d031400900f0198044980c50084035542c013600d8000d402c5540348c450300400d125460380712000310300440c810074030000707a48546c09281c3c202030201690056a40d51400280554051044100440e150440f80910000903000a00c0844550082c00d01a055944501c1020004c0c0200c2c0130854000c0d082408000400070042802480742c80c17580e00030848c0740d0700c0b6010340c14402d428032a0014554070800d4501c2c864104901c07850350190503490800c240c142c5600200c1d0070b9030007151514000c2900c030b181c60b46003032805580c1d4119a040519007143c07030f030b03810444041003082b0141c8040c1c848000007c010901c103c00390 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12634935 1250 12633685 12633697
    0xc03110111010f0b01081f09021806030403021516050306040c051c0203040c080a03120b03030706180203060c09011202070204090203010c1e0509010806090a060f080d0207050409030c0f0305 83
    0x1c001c10001d001c00c66048003030304038510720b20b00054124000581c50800c08452420310300306041148030b03403801c10800900035031140104051300e104041c402001340d65000c0083d8400ca00c65405402180d0540010301c0722064003605c4000f80704030052414000326803102c16030ba401002200c0110b001da2100005658a11840348501075151303040e10100c101044a400440c000d80c8a08800451141c2d651030868980800c14001400034000d80c50440c00010140c21044000e500181901d1502c44036546403011251811035905c0d695203040d48400962074140080e03640b00341100800b514056080000030080d03142612240c0c40079602007400c0c02503450741e5008244081d4068001c20040300410000b505400c08500909041c4522000019481e4416802e44600460684540d03005071a442c2c10800f9540d001065a81c0c903d03a20200016001c2e540882c0da001809102c02a040382c450020009050032400e4220b24026410002285c0000794040e00c210441d980103113640030903009526044400d8800c0c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12636185 1250 12634935 12634967
    0x20f0a08060907051203090a030803070e06070c0302010f030b0f120114100807060306080703020d02060c100b1801030f06020f0c06150103050f040b011e0b0d0e190c031101 75
    0x104015142c1d600241c0d420541c0e9040303c00d48000b80301d1664890f960b2003080070a980100b00b4020802c009001100515004400d90802e03204224001003c034a00d134100a07800e58088400110030825540c002e0040941100f5910b028041074444a004c41c810118000d18940542c555000d0020316103020350040508644c0341050790181c0c106449a03490309100e5005092040c0180c901c00500107020f807085000b22241d030340240103414a181c081080c081d50101d401e98100104228003441c0c084144610540401c50400015080c403841083c410120f00484900305040c0600c40140080f0716000680c0c0c049079400b004c00742ea916000d08020480340180380300702c00c852080900740b19800c200040041c10300300c4207980420941d9074500c450395001e00c0603034020344802c9040006000c2e1910814910386007188540400d540281d954601e81d89590000100b084603039915210007005140238440e11082010580031000451055190002c2c0600940b0005060103403000c030000960340200c5c0c9014030b203140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12637435 1250 12636185 12636193
    0x50c010e15040308090a051209010c080c06041b0803030f04030c0f0302060103050114131202030c100203060f0402040501021f1104180b010201020a0c0620070c0609120b04020f0a08 79
    0x18000e800807a850160303000c902040c145800100410400120040c005c1d8000c40100b031807003c91665041c10f035125020710360410005202c03020219011000030a11032032144007d1202d40b4007400c201c05521007045507001003818140d010804841c1c000103a80d0050300803403c0c9107140e2194034055903125a06000142444040000c100c103064001ca0010304032400355009000e8034041905013100c00324212011041c00c40e5414a0f1404210b1004480a1900c01401203e190110b40e240991130403400c0e4000f0300b03810b50008100480e0f410486000d4000c00000e540660901e03040100107500c4203c035903043c0711201e4080c05e4410982000360480c000084020036090b503915214082d040c12050481c0c0003424403401c160b040c10321540b0500c2203031090303d0503a031510001d08503591400040c0c2100c03d6181513850619840c03c0c1200318480c01402d6040c0704540702508603181000181481e011540013030340c2240c1000d59080801c0c4201c902c1907010b681242d40e150501c40500006060500e01e800041891107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12638685 1250 12637435 12637453
    0xa1508060415140f04050f01050a0911030705030304060c0c120605040201020d09060509011808030a050406020f010504030503010e06040905010c020c040b0d0210030507020a120305010f1e0501050c010e 88
    0x2001003141800303030780900c05041110305004070b004150362002ea50103420500725000110014070311402950424819000c0da480e01307046210359421740b80c056800e80704480d542c00741e032020080c00d46499012910700b030f400350043c20f103407100203070701d0f07000b948a4401031010f034030819801c1040c07070301c06440070300986240001c82d4000c509100300108400c0341c049002d4420380e00c48404d8503000381c9104007103419580d03441e480c1940716801121808078405146103040d04008010541d030750240007800c0325070f040f40c1d5411303201d0b4984500246031603450b60b05840180d14140c14840880d901c14100d0707064036100401043c090b113405020030010540807101602c6544cc00d154100e22580c081070308049040100c0301407000079450010040040a000701c02507201c2c02407940070b00000e01a4101e81d40c010424010b803212518152111480e000c120740344c0000180e5500c00501c00d00241d10007c001400c4103103074000410700220149044c2c2031351801490705012001c600b909040e6425000303404410306880981f60500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12639935 1250 12638685 12638699
    0x3070e040302010902090604150303050c0127020411040b1e09060a1701050103020c1b0406030c17070605040506070b100b0f030402030114060d030f02160303021605060a050405010302030a15 83
    0x4904c00d50102e205081c208080354036454580519054070b04c50004007a0424a941d42c02d583e00e40c485605450740d0b5480f16505200110740c3c0380502d0783d010712604090605d24140c81004200c1e103081c400d1040404082c8414824410007a003030300d4840900401c00c0e00c1d6030f59044800181c50141141d89648040c00080b1800620b41c4070504000340d410152842e11944d8a03500194140e00825004103d181d10881000d62940100b070348242e441e00c409080000c0c40358482d1200344602101b60400500100740421041c10610b0070000500108050700e0000e00300703824540001c81e0307440740d4000a0102c20200c000b0502d01080c1c0042400141101c0e2030690380c0305c401c00d040d2041900110740a80c8030754605882e040c000c8a403405030511400340104850103c082654050f40c07101a004500e508511411003908002d0b098201804051406a0000c003030000c0718000b4080ca100c400c0d0045030048030300b84998a080b070b411100f6501038039024200940c60f9500e41621200420000340c41a0406050341e500003041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 12641185 1250 12639935 12639941
    0x70305090607110304170c01030c0e0d0f060f0207050a03080a0606080105060d0605060c0a1b0302060f0c0703020414090607020705060d0b010e030a0b160503040b07030c0302070b0f090c0102011b080603070e04030201 94
    0x524009c1e00e05000301d94148000307481c00f00d2080089604490f01519210005611290b41296940324010005803403048022a20403608001412142c50340f00e00d07240f40605400401c9181e1200d040b040a004036810480c00030316424041c0300d000d0040c103011815058075880d9401050141c42c3c040c1215031141200c04200d0f030344100050701681c10054610000ca25400078054102c10349401501051828141c445880b03003c1e03015a880350403e00941e4000300c011707602e6000d030750025803226101601d10f0034031280003410a440544118259840040108625201d03c1c05440103500c4010f40043c484c200080141c07803101400c0e10441c3d041c01850314510407c6001c0310314a0080070345403c0d404440a2031701041d10315100546e40171382010400c000181c642e80c8a90010b0044860034640035041c00304503541c0085e42d4400f9107865005540c1042080410b420030071a01624100920081c0304003a4044040307a103182d422050f040810100d00005100358604210320300c000c055811410800e03140508000b03000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 12642435 1250 12641185 12641203
    0x408070204110a1409060f090109030501091a06040515040203060d0b010306050f0702030301031718040509070501030b040b0105071403070b010803041503060501020c2107090f0507030509060711030417 88
    0x1c00c000c85442d0303200309440000d556117104091300c032910700240c0551004e03541d00610220781c100110840c2c0030000031400e01071404031a209070044600f00408281111404070024080e6002d246010300300300a0420140310b4581606081c2c40c016a00c0d1190804a00345080608010f810000c0107400081040180d6100d54030560340b04c00100303a0f42d00c0d00842203032684407e20014109640e680001122034048074001d1218440400751207459014030310226050b588101c1d540c403c1500504420000307941c05000d40c42c02c0350800c403000c20142d007070440045c0c03c9006080b8040c0a607860300b081e840d4686001c00c1140c0e40d0310b8000d00f40303d40b2581e40b08a041e540f540710340603400c0c50241d00c851001c109402400745909070b40d016000b0704880c00b07540003400b00607a02a548003c140c01c4005090b2001203080c090078003c3c200200001c165030806503907071825900c01900d034004061900c010001400c0d80814465080234113803402404118110100300d02e140100d4006403841007141040311010034001481c02c01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 12643685 1250 12642435 12642437
    0x11d031804090c0314010b040e010b0109050303041a07050106120f050c180403051e041e0e090307021e0303030a05070206070c05030a0c140105100509090a0201090b030408070204110a 80
    0x111905003002488203481294900521021901a0078000600d001c43c1c80c1d03505102e148000140c92202500140503100b49590881540c1d5613400d0141081d40d00a140078050b00e01a030043d41340510f01181300004089010100314286400325250041107001e42000c00203004400210350001c0290503c5958403000240880303c0c0d00c10560607030b019080180380c8594200d440700602d942540e0341c1c0c1b4140c560b680200d05009400384444055150b80a068001c0d0003e0090303060090485801c06a03c001050040d070001c4070b4401c004410450003600010443d240264181c9844610020000d80c5140f20b1700c10221042d8035010200800c00c40c0d070090381c00a40310b03003841d03401c480b156280c0c40e50503a03041d50848009007080d0820490389807040e01070701c100c010030351150303035a07000d0000c04c0d03503c080c02c40340700340c03888140004045810001494828452500552010043e00d9400051360028054046900c540200c1e448003100260922000030103075011aa0050710030711200d1404203102080c0d6004000c060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 12644935 1250 12643685 12643717
    0x10f02010f230a0603050d050d0b0306010b0301091103102706080127030207210b090615030d0e010c0303020403080a0905150901080c0921030406030605120307060905011d03 76
    0x1e0180d903d90144008407a0040064552404104c3c002c40301e035449000711420840d142d1101c1d914548040120380d00070704122101d00d40f81d5051400600544207200490440d1210a03c1885945501d203546403044903040b442d1a41c50b104d0074220b40514692000300b224003249008800149e680301034111120040604420030180c01940e8000031000399860703000340c0181c2c0b1a01d002c1c001e4145520016105410910030503090b000f60380d072052503e070b03400c03184203a941d084401841401e00e80605500c0d9012402c40c0500501c04c20368000900c18030b500d420044c100100c44242406142c081d034110303005180c0286e0416619120703140041c001c2407951180500845c940c02005d06e801502c1c1c0d05680071032205035030f0031b612611003910b40302542d007000300503a41c0611442c064041e02c80300c5045d080c0506004070099507c3c5c41c58600040c003115840d6100501070102848041c28840010044588203a40f201b00021407440f40d060160042c1240d82c4e1040104654504002107103000201a15039540320301c3c00c0c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 12646185 1250 12644935 12644941
    0x411010e06120a050703020f0705070807050303070201080a05060604050d062003090a02011409030a26070c0501050d06050a080106030606090209100503071e0c02031c020606010f02010f23 82
    0x1000251058845454403a602040425405442900581c0d00070030586000340c07d1106512305c0800c1c5034442d001c122090350000508110090060069400a003012400365046c510789400203030101000500070700c0e1460341d03080004d4403a540c01d000d840282902400404c0c0400e1985045002420000c80781c04001184001014421009404130391281d416140a403003502041d034015120b40e204181c00703100700c5000703001d58640750714108210500c1600842d0000b81003001000d130200440c0042403000040b200800410000c207002100281c1110b10078a04280e6415a1800410042090303801807544146030000000b070900e415084801940e005003000c200c00c641e503103024801c0384502c007500e90708011400500580907010750061940300c00e0500340000d04030581155003030418040e0a05002041070340c0e00420a5040c100400103011054243d415140c554801010b940c0d881c0c0140b886d41000300e100500340c1224800e40294007003402100c0e0602c07a10f0100102a054182d03910745580301d04900b8000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 12647435 1250 12646185 12646189
    0x11070b01061d0a0603090201031112010e0106020604081602030f0a0302060a0b0307030b0105040b0105040b03010303050d0507080f010b0a030e07092007030504050105090a0806041202060a09020310091a0411010e 92
    0x42c02041900810388407003d40781503030680c0500b6150310142d050541e40d81c10203003800d401000800e1100070a000700340096040c041203030b05280040c0c2083c811580325100b00000105580110b9002c4051813000c0d445408181c4002458518020840c1240e0300906101900b00750300041c0342c50050f15400c0080c0085002c0e0700506540b25010700c03010b40307a00f60a0004001130308159020001b902810716001f8500b03502c88400100302c1c0d0080c6d00881c009000010312000012191281c581c224259141151180c181003400301c034501d0301070042e2001244000317003440340d103800f90b406042c20540c40400da41c20107030f540c0ca03c10300804070240804405100300b54280c1088542500f15071031940d058507110301701414107004607800e412203403201303401000b9400c02081b4094200440c41c8a0351040c00004080c001c41c0000074185070001e4143c403142c50602d11160010303500414001103075100c42c40c0015180301c0c2d600b0008814900711341444289201d40c820311050000240e011166445d003a01e601030705400c1c001c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 12648685 1250 12647435 12647477
    0x50307120203070e09160f05030105130b06040506040e0d090f080601060504210206030c070311030307050909060f19030318060504150c0c06050706050a020a05030c03090111070b0106 80
    0x1002075060700011004d10103144000c1e0b41a801581d684110380303c401849005245000850b0403148694190b00020092440e00340902036100f9a440490740154225590300300c0c071003902070005803145441d480001d4031515203503c00c0650069440488016a82910340907140c05c18038084d6200c1101c9042000c141c04c0000501315040301d4a5a5074103141914201c2c007080d2000184004440100c15506903001507036500010b903009002100c8120b07512592407a014060f45800c20300120550020700030080c01a0300311701374a03980c003010b0728001416030399800003401c01269001616400700401304030205100b614100801528400e8580e0780301000c2c40145491600d10074410380000500401c000d00816000c041e03040011000ca041000844860f0f5480070004210303a000030340001c402046050038031a0f03a00a480c1c01800f414403c504d421217600001700544801010582d40400020108484080035441542100c0f0201030160301d80305203151120b4210000e1150000151050710b1184160307204d14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 12649935 1250 12648685 12648719
    0x80307030903031110090809100c020109051e0a030605010303080c03010f030311031309150f03080307080408070506010803030f07081603050a0f0603050c030d0c03050909060a080a03020106050307 86
    0x910360940c40d03459036804541204d22a0710544c040e0003090000d0160300424014600520300c1100c1d0107440341c1d40d40d018411120b0300c100e080402c0008440700600541d810003585070644106884500dc100265004845003000c5000b646030400b192005c000244a040d600c071a050380e00c40e68489076a038840224482540c0403c1c00341143c5401e884800304002809207581c07800c0ca1101d1825a820b12510340f170742040107140790384446056074071100401403071685100080042c00c603080100c80d0082c195140c0d02210302004140c14148000003022405001e21401560f030102d5000003210300542c1c59540300c58583c0c0050750415903001c8541c010510042c014101c59102d0260395030842e0a00111078011000381c84040c18408400781d40d40c80d5610012920700580c4081c50081004103030b44107081060620b0b0041200c22070b403c2107040c044203000294080c0450b2030841c402c44880d256611880c00227068030113240d001e580b051042201035001c058044d04520200c0b0012015034500996505004200c400c02c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 12651185 1250 12649935 12649937
    0x60318050a1202010c0c080d1d0102031003020f0a080304090e010b030624060705030304030c061b090f0b0313030c0602090a120203160503100216140615040207030f0305070309060f0e0708030703 85
    0x5118121000d10f07203038000300000ba41030102582060322102718508a0f88190f429401c0031074120418415414411001d084241c4151003900a551520f6022074884c0a18026498a02d0f1034068812a0007025048008440e03030041c02d68a4a041020031911104150b04d06910309001c402030502d5a40380c60015a02940c0e0440055859035036140c3d8100c0b14004103450071913100343d46100a0748902d0030038443c030001042545491020f00e0a01500800703803803643c1d0254900c00b0b4200b00f0002801d1a0329191801c5035890f0030081111546450050081e000b80c0500031303041504440c2c0024010b03449000c555645000307400342e46031101d5070381c00e1400b209140c3c050150107501c4019101c100d80c2c0c903540181441004015010a600007030303070322a0003100c8000c041c20b10039070001042c41100091880e00b58806001120110710346035198ec0c9c090f001036200d0182c4020b0654620003d82d2190107500801c40b03466110400304558642c14800d0700007000c28042c180007e2256140114005100108441841d905 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 12652435 1250 12651185 12651187
    0xd02010f0f1e02010c020c0d0c05011b05031303020f0a0b0a05070609060908090108070801030c03030807020f010908130806010302130b0d05030d020306010f02030a09060318050a1202010c0c08 84
    0x10145003614030003154840c001c20409100240c80c0810007a10b12503100341c000d03038004070343e540c400d0500030b140c4000d03e000580304201c04081e00f00014450480c034011108203003070415020001010b640c440204090010305140400184100c59140014910b82a80c3c0700310f4024000203404003d01841048c20301030300681900801000301e405000b24003030292184100c5000c20960100da5500040c1c6504100848400001054880ca1303076030403408542d0b10164514114510b0b62450311501036040041c40041d050125490224502c81c0c07082c005103907043d60400c000d110f031910501e018440e80e448144046062120800c1c0401c0300b1001007200c1c3d04030b80c2c0060141c0c152200c5001000d00814554440130307030014480851740d000902c140041d020b250007800340143c803440d2000025082d611440f01840441d041080b00004040d00035010381c1c1500c0442c6400241c001c100c2d068445840d1104c40301600d01d116201c6032204005908200c500c00100760b07402440224081c07002681c1c0b140317003820000c1900c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 12653685 1250 12652435 12652457
    0xc08010b070309210203010204030c0e06030a0503090103020d062408090c090c0f0c060112060501050406030f030e03010605060f1908090706050307020304180f050c0903071a0d0219030b0d0201 84
    0x750203030310492210044519000c90141342e50009089a00c00d40c02100e210300ea5882c100441001100e50070741c41601900a8440c030740c140d0382c0d100e49034410919843c1c141940800d9101200007107030b001202815245018400301815035403500381030b402031802200040c0b02c01c800501030540118880303020341c00103400906191268280840180c010400e0130503044018007003080f0014082000354024141c40103024441040d07030802105454050300f08034003a80c00c004c400c0001920042d500034480d50180b6042c0c041a40f02c20000b8090f0040d0350003641d0161000c40c1d5072004028a100030300300c0f542148e150403071000b00604255011001110544910b4002100801ca000d01901c0190b41c08441881603034174040d240c0d0800c074405014896107107405a951340023402c2a400c1407091540041244030118140805900000d65801d568041c03071200c5907080c24492090745490054a000d0711090703a00350b403070380d806441000328003c0e6100c41d10300090902e501407000381044d0070068055901a510500460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 12654935 1250 12653685 12653699
    0x10b0a05010c1514040c08060708070804110a090b01030509060403090b071b1215060506180a09050a20040b04090c051c02041509080307141204090c08010b070309 71
    0x182c11840c0a4a10101c45607504054511074450303103540140080314600d0301d081c0b0741054491148903070000180c83c3c0c81081408542504890340c80e90040326450b0088a56a440c54105103081220a0f8640c00031002c01003c11424a0341d04404503801c0d0a82c0c040050750745201c86265034245c01e03503025004c50b2960700144500d0100e0002049201d0240807009100c006940c0407103150b410310b600c20740b9202d40b81224842008810750107604042d80b40d1505114a600300710004d0309d58490060003482800b11a20314081035101c81120400074106081d0411203481e01c503e441e40640500149001a090422031840090b16010195020f80d17028506840c10142401d107000d0050884003007050a104080c0581500d40010484000012503440b41c090f803594a0716140d044080b130389050403410711000000034801003100105032140e050b08214038008020021204900b41002c03c0c0d0411000640010086a9049070340c1000c1455000395403004032aaa807007001602d079004a40000380003d0800c1410000a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 12656185 1250 12654935 12654947
    0x3140402060304110a0f0308030703060801020c0606010e0a030510020c07050a0b030606030604090f05150709060e06030403210c09090203060907110f0d0e0405060d0b0f070507140606030f010b0a0501 87
    0xa000e8601700c00c2644558555541000c90750044844107000000c1202460b13150242d0f800814076003000b903061500300082162034041c000e2401e4100310805500704155610070484400640c1c04c4070070303a0f00b0343c048030042c50003030350107100e80581920940c100000d00b4100011480c00312581c1280144c2142c031003008012180e07202400e0603038065140c500803004030710300318100c480c07140c0305500078000303044515070410000e10028416400d0000400d001c001858204080c80e01c1d181080740c0443ea83c1d5103914040d40c07104681c070352200d1403d00d8968010011940307a403001d01e44030301d145c80b4424410b944402038801d0707100480d0000d070000c0110001c10055030284010444030659001910355044014041d82c1c600f0310f00342c0c055030000d403c1c1001121141450312506030020816203000c0071a070496120900c0e8604081c211415080303c020001703050300d12070802e0b680041ea0000c0b807824001d6400304120340c0c918007500c91911900500240c501500c41c14400c442c15580007605c4020600d10b888019528 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 12657435 1250 12656185 12656213
    0xe0d030302070c05100c05010b0f03120c010204090203071205010e070e040e012403030e060304030c030807030207170c100510051201090203010603050715050c0303061005070609050105010603140402060304 90
    0x200258102c0118085d61158010000684542d50300e150210310390900e1402d5901481c600350146054861400d4192808a03c1c0411342c8003d441580d600c268054101e4020311580c1c8c07208a5a500c0131041c4440755504c20005400e80c12045410322082e41c84003a0801140b0b41545c240e004252070420840711070800381c00c9040d41c5901d40f000000c1c0300340c50b0483e072091079141e04521061085424414002c1541050170080e403a02c0c283e46040c02c40c035107680c1c007074400303440320030050180010350300011811480f83d01111100360388100d2a91250040400c407031901d80048446403103034020030702d840b5540740061191038452a40f840c074440351140380c841884440f540780aaa00030954039407003032001580703007400759a00440c81100180441d61800240f10404e12042e2a150108241001002c03c540320002c01e69412407812110703980391035040b1800f50703a20301c0b13118801440c1038180f01c61602844019400141200c59540307050094a101d00414501100c04071002135006100744081400704400c011003002d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 12658685 1250 12657435 12657443
    0x12010b1602040f0207020a030303050105040c050712050705240709080318040c0302040905040f030e03120304030f121407020607020f03030f0402041107060e0c0402030f1b0d020409020403020a060e0d03030207 91
    0x102d040c1a91b00802d441d11090340055010a4a42004000d5410a81b04803034140c0b00c1e529100e420034001c1c0e030300c42d4108040001c200c000c0100c00b02d0580140001445501201e42544040e15043c000ba20140c4c0074205048611001146a8140000700d01e0340c00b00072243c401c3c2d440c45044002d41d1860b002c0000400d00301c000703a810940e0030302000c50004100d1003510f0007540151401208034a451900078100000022440c1c01f0340c220450101030f030810841030326000750b4035043c440c40c4104801c40c100e455001c00c0320030f04020341c1041030306038040d600c1c2500640950056425202d0b81d41e914041640d49900406012030181d0041001811543e40c0780c021607007180c0b00400110300310903806030014603078001d21800e40320b0903900c40040441070010003202525039020395007035007503203010508454034030002000700e164000840048518010008221a106600000c04646543e11490240000e4101e804100d0048207801000b040b468001c0100c0844040d0090aa00f034092031551704030302a4002c407100701c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 12659935 1250 12658685 12658687
    0x3052719051c0509040c0504030b0a02160b0c0a0e03030405010210020904061703040f09050402130903020a05060109151706010b0a120c0e04050a0c0503012309040812010b1602040f02 80
    0x10204404568101d00b1240b4250b8500d0340340c181304000c002c11500c44003e40010701c002004204009000d441d06903610aa07460307030058030345803010198960b900041e40010300c4180e05030200800c40124001810340e03048144c1c1c0b0b11000340882ca080c940d80380b107a4000c0c03501603030040e862540034901d01e800070009000083e102042c2207543e44a00a104c107032145500007542c0000c141406401c00b882c1098008112054060090341001d40103c0e0305035285080440c1441e44880c00501498000c1114031680b5078000110707a0903607900c08030700c070003819021008125500482e4001401d81e000c64100c0e044600c0280140c03005074030340405240c06134450700c0c1e4141406151108464000c0c1c0303074481d0202450240d22440d40750303c2c01204100440f4801404402d40901c0c00210051039544007080c4c03819180024985081c465101100d00d40700300d01010143e62000046042000704900c40b0098004071303c0501c0c02080e9a600e8491401450044640c003046d01e461118500b405882d181c2c11108100000207801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 12661185 1250 12659935 12659953
    0xe060a0e010e03030702030c0d0318030302030c0702090103060606030b04110901080702070807030b19020a0207140a080105091c05120402100c0602030f0106021b01050706090206090d030305271905 86
    0x300d043d0381040700d5070005a040400c2080c4809401e102c2d00c921a5080d00e002c1022003041c06024160f0249008080c00701580480040d51440b030020072102e5081d0010441006580c2d03074a8654054010340c044c2800190070000c0310116804c4c240076160020307031403109150030075107680011a040351006090034118440d8048c00184a40f050201d40080c600400c0540000e00d004502c0e20700200140c2c0350098920b204100d0491499404031f00d0105440720050b0348500b1044039130002c0c64800343c580010b00c0651a000901c8081c2000040407000140310400c2e0310404141030a0640c0d29000f901030603541c29500500007801454015a50440002d060801403c0801947c99940803a0001c50b00180320000b444010302400c1e404012800005070980c04440d084001a00024414020500000c010a884181c02e40c21507450f01e054903425680689215104003640c1401000ba10054bd0180300030040b0f0391001e00c074400d9982a041c04e58888500415858042c3d8501d218981d0598005031081c0c020410300c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 12662435 1250 12661185 12661211
    0x91c09030809091302090405060f0606070b16050903100506030c0904120c03050706020a0c0c170c010c02030102090909070e0108010b0a05010f020a0b012d080712110904081209010e060a0e01 83
    0x1024000c7d801400100500d2401c4151407500306c1c4d01800161003408240440f400040000d08200d40c054070041d0788141c640c40229060f10340340034403401e42d90315005400440303001c2881c5a000d86e114403400c82c04c881d0703503540340000e0001400042e2000f0b0000654a24500e03682c90003958681c5605202c1c1c640140751820fa43c40755412600441010301c0040c1207418004140300e800f49401000d000403554a20301205041c0e05556103c03890400715051000440c19101550b60039070541d403c405000d451150341d450301c2d02c100c81d21941d16009165451042d40000300f02c1ea04144201e448140e8083d00580c100c609090054402503132062503581184504865480050703c1c05004600030070086958402ca841c3c1c0a0702090381900400089016040e102c0c0d0422400e10001607000031144903120b4a6a8482c0301d0408503241082c9055140d003008400d801d020800c050b9400030010382001441c5407415864640d1494281c0302c0458240d2a181d1051011032643d14807a03205403006150440000b40c042c00b1000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 12663685 1250 12662435 12662449
    0x308090d0512041211090c04260703030806030f0304080705040506040f060306020301080d02011808030709081603020a0e060307140609040e030c01051303050304060c030b0405091c09030809091302 86
    0x1a5011403a8001d5031007001070300d420085c007440c0308030360100c640d2600050280c018002e600c03400d00040f0580c1c50108070800c0712059074902e8500e29086e141c1b1582c803410b02414511050355150300920690080a448503400706c240c4d07099504000160482c40c0c600313070412002c7c00b0094025a88150789000c021800360161103404000c1d4800c50b000f40c0c482d85050500fa061040341c1400704156410610248107208008080c000f20070b90090425840352a1100c08441200c82a00f001c1c5043c82980665810f51440b102d043d0102ea1003154120031058aa0340b40b002040d0007501d509805900c01002070100b40d841c240301004802e0060004c0d41030148500001d021b0b15480401941180c10001d00b4004104c000c1c000e0550240800e520303140824000d94004043d8400104041c04d00c42e59800c1c114039140c403a4102d0420148001c006100a051581d5410707115100480c40541c0014202c04805145000303e910324120707904000039604000b0308a041c800e1011000f007400c440c2c58520741c40394005990b015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 12664935 1250 12663685 12663689
    0x30204090f05040302070603150b0d1404050c09061f0e0f0303040603050109110c19020402070c060f08070f050703030e030906040f080106060206010e0403030b030c030f01021806040308090d051204 86
    0x998042203d050508000e07050000075000300007014205a40304110002401c4a80c00300d9400200d070698442d4111925001070104180807c0c01e07890782000d000602c5000a001682003800300e0b807150341c82d11410b0401c2a0000b00415010003600042c00c08001140240b000104c1020081c140180300d10f548000a41150711a812000120781d4a00041c03040034058850302c1030096500ce100c80c903091a118644e95a41840489005906080d540c100c6c1103480c0c0350180c40407154402021911240c60300d4010b800c029941c04840d00140442c0000350649110700c000d24500c83c2c0d2525080d1030044903440c110060301803904200140c1c0300420002c1400d0302c0c1c030001003000b44110410b01140c10f08048d03800c0d00352511540304504541c805e0b030040c8841130604100d913070010740c0740c00e0000f0003014402c0070030b040c8090404c0c401d5150007030154044c805c0b60190001c0010be8101d100500401500d04200241c9000354040a1314140080c8862803240c01c0106200722194011400c80d100201d0b4002105041e901c25 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 12666185 1250 12664935 12664961
    0x9090c0e0a0c11011802060a0905100e010806011d0f061207030e0f0c0105030105010305180f030d0b150306040905030c03071a01060219120507050312041208010e1603020409 76
    0x10b00307403031207409038072040b20303411480c942000b07022046504c02c0f03118450703001c204c002e4800c44002622403c614000d4501400030f28002e0315901c410420080041e1800e800102c0080c0031600c03410003d5001d42c070804540c1c416004581319000c1c9200d51105011204114104080c1c12070420841061101c01c1104007038883c01050b0b402040c110030700180c090500111201d80e4209502c28110044180e8004007680d056403800c0ca0000340c2540c0791000000000c24207241011980075030b114140581002100412180400b4481441811503420904c4400b242c80603035100c0790340060010034100c0c90213030424034000707004004a9040c015002e15040c21a802a07404456284444241145e503d042590880c0103000a0018090750036503468080307810315a2050013440b0442d0401107141d40707030040098607071168028049a84440022030008078203c41a90203480305040030345030841641c800d650060503145103001400d19500c80200000309030902c40384030402e060f0248404601d42c5100c1c410525030140c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 12667435 1250 12666185 12666191
    0x30d090b0106140301030b010501030f0f02070f1403070503030a0e0f06070503010306110c0c04110d020d06030c08120d02090420030403080709050607150b040203040c0905071809090c0e0a 82
    0x15060003d01820410450080441010310040010840ea02c44480c110703442800d0105420004450400c001d00440014901c0e80c1e10205042e018045080030340d66a00380318502800342d00301461800b03507582c02081c00c003d0480d032040001949c0c03840300783c2042136990001d00855a00241540c161820000c00b1200c0034000707030002c001041400054041c6020320b402c52065140f4200100711540d840e105400340c114025601c5a40540d8044403c6049404251600788219190210246c0c100d001d010380e0b00c426604800200c0020131000c001103401000d92a000d508a880d01c4110280d01d400f0713401804007590301641c0c5a1240a0741c001001c95202c2500d5158820760352894185030113040302da00549180b040155440301441103031540310480300d1054001c000c00c00ca0b02e84810718070010b04500140280c0050020052008115154506000307440c00d11400340702c5a42e400c58119082c03c0c0c440d900844604000d0400c01c12018140e122101d2140240d00d02c4442c00e40b60381e40d5003005c03041540d10642a650f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 12668685 1250 12667435 12667439
    0x2070b01061d090709031101110d0903030e12070611210a02010c0e09130819030b0a090b010509090402011b030806010306060e03033709030605010b03090703080309030d090b01 77
    0x703408803030220a5002207600c551507050502c001450040a4040200307d01c110b1180c10415a010300e0500c107400032200308444030549030044c010659685440300710b02041d0581e0a1024900c0c100c02c0003d08000e2450007840d00518101089411100911044c10240600716886140c40040d02420601c80c005080c065640c13088850002c4c01c5500c460b501904220203080c0c0560280d6070b4450198000b40c1240c003000500700c1c0b40c2031100300d81c450800d01070072a8503d08001103400c0d82603042a000050110b80c0c0b106050f82d200706c101d0940707003031b94640d034005482004038420915014803116000340c010300d406040709a40101e81c081a0140358010f41c04250b00004000a56030b040c050040a003809203480b081e10f1120300c0210b40c1c0c1c0e00400c803008500840c0c03680d4502c0b000300e000b4920303100c52f074400180c08100c01011901601c1c2c807d081c00140c03030003401c0a0020074840490801c581c01540d0140040c44001c0c5107444640040c2c0000e018908580420040e10b5072031115402550700890283c04c2c0089154 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 12669935 1250 12668685 12668717
    0x405010203060a120c03020103020c030d2a09060504031217070e090106020307050c040207030c050607050304050c0d1109070201020d111201050d050d0e03030d0203010306020904050c0f0405010507020402070b0106 93
    0x300780382c0c00f0b20302100454404c0340c00680000c0004080f60342c207007400340e10b0300348540c01503056020300811300448038035010414288074440b000d000c1a40700711052090078440c0d03400d030440e1b0350b450300e000b10030114400708030800016404440400034400c1514028034501509200c0340a00e81007900d81000089440500c5050f0745400c401d50b44c01030078103000952070001199681a110180c0c9007045115550109031403041c1405070f404200308503400b50a0b505580340c000800752941d00b003a60143c0ea10721600d025860740f4105170b03040f2006150003940380c044841a00d401c020000c40014007010031950240030241d110a410b0060400d880c0c0c0401d5804d41701e001021003e00b04480c140d20189c840d400704064500030401c0803078900a0792025242c000d001030602004689544500c2501e0b0000d0b5100100010511515501420695404503414082501c82190045042c080c0d0070507609408030801080000358040d000901702d541c4041e10142c1004a03c1d2602901d40c88241c2c0311f980441c401c40400c04460b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 12671185 1250 12669935 12669949
    0x30302130e0a0c08130f021807020a0311010510090c0e1c0302060f04080304020d03090509070507120e0604090e0a020402070b040215040308030708070c060e160e0c0306040b01050c0303040501020306 87
    0x9400d035807814190f58503000d00c1305c10219003078400150044066001103025522541c00c650305406030700c01310704024141040e0003035440c22105820380008a503150b4550a010f01030217440d0086100c000445222414142031800801028401409220b1046030002f00c2d9140c1d82c107078602d40540040c042c0348030780c2c2e503088c06400e01a005014080810b008020040001e045034140ca800c10307010b03240790702542c02501d01a03d02e20350980000d0740c40040c203020800d45c10751210041500e14414003a07007500080b0500700b07480d500d84103043c0070b61040003840180000200313071780302074001400c04040358614000ba4012030203e9110704801d9840812490401c8103500388081e507140342013155541146018903603191000d5030b0101074214010007804002040c805440746105a80d5540c212004102100d16503607110750704e00d50910f50103600000013000007440820b08115521030500650b0b01c2c2e1075070b610042000014050703405d02505202c0103000c080a0740364104061845940b18800050750f9007029402c200b68 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 12672435 1250 12671185 12671201
    0x10614090d0311160f03060e1506040b01020106030807050303040c0b1305040f11030901060f140a090b1203040f0906050607050307061a03120315010201021303030507030302130e0a 79
    0x8001410490044541c407440101c8000c81d4142ca012403036030034004042c0d8100100d0090342c445007401c102000c1050090000464120791042c2010401c0807001c1c2841c0d529a411400c0011101400720000784840c00c0580150546c0c074014800080c0b10340d281d03031700c03c000360300107160549d0194800702c00c02c07040085104024015186050718039050007071600060b90708145600410f030203035071100120361903241035402043c0407204a5202d00e8032031a207640038500070007007881101100b0707803840717400115007600c40404141e81e1409401030103c542000007ca018144c460740064008244009042c0307412030510103040586201503603660725070b00d041d0004060710400e4114500c00e0000f040180e001900c0002200e044950000012802c0c1040c2d80300d90903400e1550140a801d80545a4000003580390328004521801c4800008211124020300480c200c2c0030f5441c0400610f03104140c184040b03030141019081081c881d01e0054980591048009a40380956100d03070400c529010500946050704d00074000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 12673685 1250 12672435 12672467
    0x60906030501150608010503030301150e060f070b06090c16050a020621151e0d060608010b0301050f0105180c0d060f051002010e0319090806040803060909010b01050702010e01020a020a08060106 85
    0x455040400003270701c07484107201d020b20005d0032041b080c3d00180100e5540d461000001e284940b5400701c11005055603005910407186000400d000948501d041e180031402030071a10a001e08101480d1203c403250301148500360362603c41e4500048c0142d0f10900200720070000c40456070700418900c00030f450012000b50080c10200d0000090311101e0b00d030f500ea20603512584002064961803403501092900c01c1303030b41014000c0c034141040800c544605410080300b507201038008124568515155a00d942021b0040c42c0d0f0208200c0308035041502e281e00b80c5504104890442d5142c0104840d45404a4545a21452000104007802c10a130715211100702c8014425000a2102c108074030102e03620780c460115101c0788400c3c40c0300314500b0b03244500f100c0c102a08031081140c0c024105400c1101841d04200d809600c80c881c0c5a000980d4120180240011500306844150071300e81030343d0040d02d400c1c0610498904501ca42040c070005030b43c4020703680c0020003032030000d05165410040001c05803600001141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 12674935 1250 12673685 12673697
    0x901080a03020a060903110a03020d0e09061008040201051b100608010203070804030f09080f0309090106050a050405010c030509090a0e0f03040609050f030109081206030706030e0d080a0609060305011506 89
    0xe00400e40103d540548140d00100002c1d1401c228941502c20b9458030309040c00e244a544052000c05400080101d5140465101c1c5200022400200f207018582207680760b13000411101b2201c5070601559442e034109205040003800c0030902405c00c81000301d02e1454a0346940224044d90024002d803240c41f01030410940250b20b145403941d00074002d5400074100804000c0000542020140b140c0c5030103000d050441c060b00c000100445095549400c4018918420503100c1d0000884a01031400c46882581c0c60321900e003094907200055030010119030003a020f00c61308010042c25070f51aa0340d40e40c41204403c8d4005000803541c02c0480c50601001d0008000343d0003003009102041d0480454400c580d01242c4460340051032078086030240c50407110082641c0c44c0442d2201d60341e8015200184034a0b82034044413040c6039078a02c12001c0d2002c0d0505a2200d13005003500000c3c0038411121154069072203000450032581c0e0f210200102c410700d40c0b003512035035941d80351060b04031008850f0310700400440c5031403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 12676185 1250 12674935 12674953
    0x60304050304150804021c0606120605040204060e060a15020a1e050c040e030412150216110105040b160203070b04090f050c030108070605070c05030607080402090a0c08070c170a0e090108 82
    0x818034502c0003c0b40e50b4540700681200c0c0040202c1608030700d0103040101d407640d443c20320f5441c21101a00b33042c0c40072440b490420078041440c882160f48540b04000040210303003502d123000a42e01c0e10340040325403841140154241c6e04041105003800020b213090100c072049144019040c91404c26000c0c0221a10850400d01001492800041500c050380e03d8000c0341d144207032152520345035100511000700c1c2854000700e800e64140c464403664480b000e025100043c8213030203d4004541c1442a8003d50320400701c14071454041c101d4010354840710a20180480b000c66441d0943e2451903000756000241c100d84460620011000c1d501070541c000c2c0303e54444078295410030114079103e0700940a1142003140101e0104240020702c00c03064020319000d0161070700d6040104004104090032581640502c4100317001c01c030800c140b40305a000315417441c1e8442c000303522040310031101071440800070380360491059042443c801d513110050a080401d5240e51744400e00c04030a10108800582c44000ca641001404d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 12677435 1250 12676185 12676189
    0xe070e03070603020c010204030b01030c0513150303030506030c040f0501210203060a0c0504030804060305010510020a0b06060a0c0602030901020c0f03030108030405040b1c060c0e0312040513060506030405030415080402 96
    0xd14103560070b908003d40c851046002c11030090280743e0000e003030034512074000018885521000400d80d94145c522000c260068034400e815107000001d55070104101040800c0840d101c0d41c801d50304840020152106902c078140028103030f800004040722903a07920300041107c0107507442500105030b00e001d141038103404a60002a184c1000608c14406c040e201d81c1c030390182c1c0b44260215006594081b42240d1180c0c1c80c0c2000070010842405118090008840300040301d81c0001800c4a40560248480e81c15558040c1441902d803c0882810300748000b5903040f00026600b400518486c100c40e000050300c03041042204d614000001a2450407500300b00010320000034044100c400361082500c0124800521101080d02c2d00410034031340140c048000d0710b000801c02c0395006102e038102103641e0a00c20078283d40c02c060700c2e0801001c04640415007004108131608101860a40c101a80c09000a4455035403002c650680e1003100d0440b4150400113090141086a1a6513882c1d50650b00d8500712500d042c0d80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 12678685 1250 12677435 12677443
    0xf0109090506060702150304030f0504080c010309030201021c05041b0e010905090c09040b070305010807050a03030309020d02100203070302060108030a05031f090f0b030111030601080403230a05040e070e03 90
    0xa1081801e031680c0009003151a0407007180e2880c0d5015004810034080719a154609800644040300090a6a038100540c3c82c8503005440a540c07541c00500020302c0800015002480c01c410101c00303554080c81406d05005001c58101090501c20a020515150901d0030a13414802c0c6102c07460f05c1c28040b4001c0c4501255001c0340d5054800c2c041000405071190983c06150100d06100264003a0b83c06042100b0402c4982d401030080f40c99407024081642c0b500080303034071000180500d6400c4203a007070707040021038401d810054503540064a00000703200d00e9000700d1040300d04909001e0159200040110070103a04114940c018028500550300700104a100104503102c0a0600d000e8a5507012003c4070b0371030300c81480c800401c40c8040402607442c024240e2001f074062241854429464600b801d20403000050882e44100016900e4028030741c1c40b0354064804424100d140000102070486075003400901c20300400701c01216480c3d9a445928100b01101c1403000104410304100519501c1e481a840000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 12679935 1250 12678685 12678689
    0xf04050d05100c0908011505030309130207050f1e010e060103080d0f0c020607090503010b0d02010c05030706090f0605070e15030903090a12020301060e010f030f08040803120a0b0f0109 81
    0x403260a2001168100a45801040d00c4080d00c554642191031403801d03001303403000c400c440f00d01c80240701c0c121082902c1e1210100620501c0c0c0c15800c02c100001d05da24041c502c038984803100b900d0050034035201f52200ba161507011017819807554885c410f0000e80c21076018040d40e030510090300034001d5a035241000c6882d1380c0e041c400100174850204400a10300100e800190160340e6652080125141c1c0020080d83d03494240c0f2100040303400140046035a04040c00b520025400107800c4404c120907c1c1e00450710064034000c141d5040c001030129000154441c002c4990203406030080e00c0c44d100303407420f0031350448070b0140406082c042458041c0d9455103500d00300765000d00d0000802030700d9030b8400107140e06510502c14900d52044a1800200c2d403143d20022542402c1c0c001e40c001c01201e0f4803541000d03005582030140c01d00fa0756400714104009144910b06004461003080e40600703060765011582c3c030f55003066240102240c520000c00035400c2e074031b02c98184460411a11301c0703200714076040060324108443c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 12681185 1250 12679935 12679939
    0x705030403081e0c07050a080d050f03060d0c080a0308060907020c09040206090406080a050610060203040306020a020a020a0e0901050901050c07020906031203040302030304120804020f060a14030a0618020f0405 92
    0x414403940400d0f00f1a14100400a009102e0369501d442d0000d04d600e0740003d008003446080485008102d01c00d0002d450f051f480c6503900c605144c07110021155410390801850542c1c0070449081840c00078404010900083c50000010480000303145809402c1a41c0105414000d0703034000200100240c0c001010410706400b680c901801d9121030021807614400e81d1425500241003110008100400080c04076907140510142d40d011340b2003d03a0119034020030b1140d140180d000f1300090001c00d0b2a40e0003041c0e41080c0c0e004407400c0c24465030214824600039070140207203442c4c4000308010b400b020f000b203907030180f00e01c07008229600d49131503a0040d82c020000003034003c1400b440000d4036602c0c01c22000b0170180d9501c07402c0380c591400e480c0080d603c9d441124100d81d04070070800c28008043c0561809400340f64018503e242d110281001d01039030742c108150680400c030134558011030f140c003090011402107940c0900814000c0c20310145079650318980c2d070a2a1464810807040480101040a8406a501c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 12682435 1250 12681185 12681187
    0x1101020a120b040902060313031209050607050c070801050114100c0314070501150b031e06030c060c0c0d0809010224010302090402061909030215070308070503070203070c0b040515070503040308 85
    0x1500420010504d03260000c1d0842c01c0002406100301019811380d02091081d50b030040c2086603084002c00780c8401c040010304682c44100820081130183c009000a114400e013215203072941d0315031b2142918401ea10500801015050003031207410038084000061041c0c0c101b035a080d03031259400401004040140c41d0b8072000114941c0c0030840b0a410243d40c0e903664000c10a1005c2e180ca5018990358410b032040b0b0481e00c4444040000308220341c0c4841c0c8103020040190502c0740100c024400da0b0384c807210901d0080d0150684481c503a50700c2908650540d1702070052244c40d001040006413070b0a51265501c54500480c40300d900c41411950785081c103483e41a5a00305050301c6520128200d80660003500d10744900843c0c803c10b000c1e41c04041c100c22030340200c5018550001181d0b83e100c1c1132089690140008604800245885009900070341d0440000d10440740303800042d8489094100250300700c500f01c0d01d40001d040046140503012074100040c10160340b450b0241a955456032841144402441e0002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 12683685 1250 12682435 12682451
    0xc09052d1302031005041803080a0f09050a0302060105030d0504050906040209030106030b131704082d10020c06010807060c030e030709090f030f021902010804020a0308191101020a12 80
    0x641c0d00039820828001d150a548a00340180d041d4401e098a0043c98003039458003201c841d0380700211042070701440c0c06844402c06520f0b81c450542c080c10b4800c0f0002d04045c0c440e10356000050003040410f09050182c1e004e041c40b0b5050104060800240c00092005c101c0188401d1040756547d0820980107003003107070010381d201c50180200b4013400c40b43e8005404d0f1620b940c20406400f84003400c401c00b90b842514807000040d40b03020300c50708a000f28006c4c42e03540d60220a9070320281750558404002c200d0b28501d4028251580b07043c04d490030b101c07a22102d0000e0f801185001501c0b00820a99001d09150005410341c035062280c0204190070740c49024042141448003010280c400b40181805002c602c50240114181818103a4101b1000c11003100007503100c0840c000e0452020032000c0c2680e0444040034002c401c0d9400450f08640060401c0c1d9100b04e165100200264100b00108004881c005503c41c00c0a9841c0c800b40074090700014036001640100801c0c44041d44c0680c3c10b40c480301000000040e01a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 12684935 1250 12683685 12683689
    0x7060e0909070306151418041509060c030207051e0a0201080c0c01050403090e0603070b030112080903030c061006080108120c0a050f010204050a06030e03030106050703020f0102030a0c09052d 84
    0x8503507101a00f401d1a20700c1d0b405400311724104030b9058802c03034003218032030340e1001050024444001c0305550300c030000c2401290009100e0510914038080c0d10001240860861310348000300d41940f07408201280c1d0006416041201c10b1161014100b010300314031401c0d002048082c3d48800712158024100490800095001d003001429907041c2c6442c0d0b00204400c1c6007915000d89000402d000303034000400c42400094162400003111410b44118044581c10340c1d20f06124844880310890086401c010103110403070b49600c04002900749810418010103041c1407030500c40501680c0350300090104036604c030060000450004092420320080d0846656a011514a850521803100301c010424040c0382d10080c1e00c410150003900036900122000795a4541e1903105904440c01036405e810a5001400100401400b4002506070340d4041c1c01901e0800011b03161031401c990086400001442d036503000b0303040703081c0d009a5000c0900001c0da044c00304007003541207264502d58000c0040001500e100041090341d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 12686185 1250 12684935 12684943
    0x13030504080d0e01030f0b0a0b0d180c0e0108060c25020d1a0601020a020307050909030f0c01050a0b0105070308060907020f070305060906060a03080301060309210509030105070207060e0909 83
    0x1018103070162a451400c6840042c1035080c9420000d00090030010b014041101c03911906442c914000d00e640751041c42c00005440301d400016580548969451504110046015001d004240b041e104d0034111818040e08850b09281a009681640d1001c01005242e8114804440c0c0726000981d54a0715200340c2403d008840d40c50901c002d4100c0e9044130705404008900c4c0749001c440c0403c50b168000c1c1c0c1d6941004a80c0c50b071120401030340c59440780c60f040006081901500c1c0e00881c1d550141c0340341c400004246481a0300ca21942455603542c3c0c0c00700003c6152038403d0a49410092800768540b60041c0c400400e444009404070348540020400300d1443c0e4020012050039585910649014a80d24207200f900c903002142e203001540101e0780000c0031807074052001000d580d8464515401d590926808400600c40702d0f4049590000740b0344500d0380b095084000300c981080e10b46c3c92695518141090500303492001d01010290f502151781488a0364002c0e07070b4407400d808140d5800085903034402c1ca0a01d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 12687435 1250 12686185 12686189
    0x504051b0a051e0102070503063606010f0f0f03020a0b0a0e040507050408010608060106050307140904090c05013209010e0603010905010e090604030f030504030c021806040b0f0913030504 82
    0x1100440c0383c1680122040603d801000c0304090302614079482d84c4200707040c2c59901c101c420080c034100c40c49800e4012101010b2004c04c038100d803000c00003664801000980390903000e820045d40142102d01c03c2203018041c0c10b400e0050010880c400182074611b502240d4084154007418449d84400320700181ca152040429844070600140305004078101900d002d8440e60160203080030f29420180045070b1190300182a80c1200c90359540c491840d542d041c411949152030001003000c07403d0420000d203a6956600401400074050111600c0d070600e0140050a494001041007480c2c0118801d44803400c244608440401d846144191b59240b0b24400100c8641c02a05085035100070080004102e5610551156058482400c1240c2c80754032903410351507464000b21001800145103008030312038103201e50403154110307100707082c28002160fa541c001202c44928001e0005810070002c1003000b03d15003070042c102148030984244c5000d10564010a903003190090450721703214803028a2804040c810022600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 12688685 1250 12687435 12687439
    0x10e03070f140105040b07030809150901050f0a0b010c14031b01020a02060705070b04020f01050415021606030c021b01090305030309010912090819020301061703030108100504051b0a05 81
    0x445a101c01c80c581000c101030084520300d04000340c01c450594001d00807907003901d6040c103c40d81843c5050341c00315880e070801000220341e4000c42e403000c5415900b2035031040c09604003100114051610401d00280d85200a00d8000c425040c2000e64500307907045944200b055420400c4080c4003440200c0302842c520034056910401086441c038030088600646c003510941c240c030713800d8607a65180d4400c22100c0303016205000d004061840003040c0189042d4882c105010f5040c1881418595110004c1814004440c0c4450260b0401c0450b2550701700001850f00107031550707050400c07403a101d2240080d40c0340c10001c003502e96510b1030299413125030301820111004580c0320007200d41c0e0380350507000c2074040c000c03031001121100b24001500065602454048040c0c4861130000c182c5400c4140a40680d60302c06a002ea03059580d8107404141c5421000e0314804014241000f5a03403545050b51592422000300130364140c00d868130080c0800210003243c0b17214010030362540c9a8040c81e0000c0003c1c03d02d115580160303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 12689935 1250 12688685 12688693
    0x3020304170f0f03120c0706140a0902030106060206010609030308250f1b0b04060903140406090303020f071a0a02070f090606030b0d0506060d03030209100203040f08011404030c02010e03 82
    0x10065440018203030905a02c42c400d0f0b802000703040d42026640e006507806050441020000200040140c2002c0c280302d6000b650081421080d200b00940da4580585910484075109c05860301941424041c00c401002c01e4802400503624060b4010210740395404000c007000a807101081c5101034840b482d000348200303640b02440d50300c02d124020f0022810100031101040d81800400507141d0346c004191401a00903480c5103c030355851340c6060041840f001e0450078411508c0310411200389030343c0500302601003a298200e6160450030041d25160410140d001d03150301200052080101c09840e240e403401e021149252103940b5003805034100440c6401ca51070364880c4e80c20000306240b5507041581111000d0f101080a40100e40602c10010300c01c41c0082c1c40c550007034010611508107031091a020f41c1c042d00c3c0040c00d0644110004840350711f60f035640b40c0180d01c0410240000300e0011002401086110000c000d44d040b40d9120b2a20b0860040001d0188100d010141081d64010540003030f0300c1a00805072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 12691185 1250 12689935 12689969
    0x1716020a0203070608011e030503040b0705100509010509010605030303090c040902060d02070302030904110702030c0618040203090a050613050d050d06170610090207021e0a0e0f04050d0305010302060901030903020304 95
    0x20304641c000d01c03845110b87c96402c1c8508590303400070303604000d6030b402501851503c0d0801700034510030b611070744040714984520b40303d00c00b001c501407245901510306c150000c50541010019142510140e4001070f01c070790070400038001c40c1080000c62594483e410b550208204d60b103800001c203c3d018144900502c0350001460100b0944d012000789641c3d0802c40f401c12980c10104400302d0b0502034210000e4260f0b014030340349002c920b0440b000e030004800180020381d44401000104007179030002e40d6140310703c2e40440d801f04200441400802c1e4844c8194100000014641c0c40e2255661000d11a01003030060009881e5054069030700080300ed4031400c4c600030041540074003255610141115184003d159217200810b044003207000721294036030001e00800c6c503081b0320000070b01890200c41900f903102c11808000202d03c10081300703040c0709071040c40d030121803494641001070074000503483c078404240c645401400141d50740300949103012000c0c07a0000e00c0b4a0301d8501646180303c1c82d08255070504070202e41c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 12692435 1250 12691185 12691187
    0x6030a0203161d070503040b0916030609050c090405030301030b060f0a060f140c0c01080a0b09040503070606120803070315090513150605091911070303020301090c1716020a02030706 80
    0x3461084a003001c3e103290610042400304090038100392040030005d1010004100864900301c056a00324815406690340c49001121414040840f944101d604507202d04c8010f0900ca810703c0700116902c0e050b20640d4852134280d550b2900c81c44140001050051101c01088a584406000c40400b000250242440c182c50f118041c110144d00801c080005030030300f00d500e1415608601f510140c4070410010401c1050314001925030100c0101060111a03880890403c5a1f9488081c60301490244001d190744a074541022401e48440341c10039680100a2130001000441e10811240c4c0075205190008052069441000e20b84401d5440342500b681001c09001502a0181e1140811485856000d46204c282981d030019520706100321503000030190000b841001d0a040f003d000202c0c14080003c1d180f01c0c1d2614852281c0282c6010350020307501000602659200744108000020740c0d0034450303501c83c00b0300c40300011013000400c03400113000b4508010030b00c18020804584540c0e4002c054a485a0300c03890 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 12693685 1250 12692435 12692473
    0xa0b0a0c05010603080f04090b011805150712030b01091211062d0c010e01060806010308030402030a050d090609050102060411010e04140103060b040b0a060c0b0705040506071103010c180302040506030a0203 90
    0x10b90212074640274130120b2540c001c0f81039030300c141908483c6144040c600300411103120000034800b90144000c01c4030388005108c1e00c13203503c000714043d28000b4044d40722000051076041150004030186013140741d103002040c403030503200c004488115462503071040007200341e001094100030307220840040906c14504000315400a800e00900c5d05000300000c980080d107072401d03103500d40300d0101980c01820050010400c03d900859100c1e00241c12035950607101c1d5039141c5440240040f080c00a0700a4206210307655100496000504c400d10081203e4202034807040449100c14900e1814004005002d003482c0c2c03610b40107150500100c408007d0340b0b607920700701100035180784040e0903c100d140418081d000c0c03508404140a440b5039580300031881c205030351340c3e84e2000c0001e002482800001d00c000240c0d50743c0d02005100c0c03903128100442d0190400002c1c5400e480640c0042400d002c618146004d21040600c5010116601120f000c1000d032607107070110742001102e64029416006844100500060b441c1d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 12694935 1250 12693685 12693689
    0x12120c0904022b06030206090d050f03070507060807050a0e01080612010f090614040804090507030b0a03081c06060f05131d180304060c0b100806010807030c050a0b0a0c05010603080f04 81
    0xb8003c04204081d511a2012204c05003c004d510842c20f01c9181a9424040b543d4105107100341d044070204000c48414a146070000441100c166221134130900601d90310060140e0840d006043c000e080141a07a8042d0110355520241410071108000154441c0d0750b903d8540c18415500008200d280c03124401c4201500364004107580150829100d4400d099040b943c051045030030174809800c044c01e118898000c0c0001500c504101910707100400c2c0241c0e04c028608008500c11481c01e96a91110181000d034007850406030100b091400e0800c10a294200342595501c0596143c260b41e184c150642d21360b444800c07a080940209864030640342443c8002d2030700c0d40141c016222001040b040e404507107559106138042c0d00005800e103030208001400301600107070810004040481c2e09503c0b02c40e12441c0080980c080c52441e40712000400a210140c1c140c0c4010345002d48061143c1c43c100748a00849110b10036071403042000203d2100207011080d4440000b45611040056583e140c5c100e000080c1d030030034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 12696185 1250 12694935 12694987
    0x6020106080c030c010f0309020301020406091418010506070302071706010303090b0406020a06051305060c090f0d02060403081c0207030504090c031a040b0301060801090f0308060312120c090402 85
    0x100c08003241c40c09001615080d240c500070010404007808000441c1c00022103c078080516459410000060703500b030003d07201621040d5100000a0701d85044400b0046c00094203500815801603854400c01e041c1400e13606540c02994555941ca00900d01207290200d1940581c06100600509051640001c5213040c101e138066a07400c05050346501c5841c44a104900c02c03480543d102046160005049421644d404000c0001005081901e40c48450510b0411541c080284000091410384c038a031041c001c004884003a00d000c0f00075110b40c0e0214000d485140006030603003802291100401800c048185041c03d10a101951624a5443c026001d50400e0040211441c2801c0c0d5030300005100b03100364001000410003e00e6030b60801c2c81444020040b02040f1074140d5200d40010404007000d005691200b4420018962116801d0070001c002280250699100741c1000d944030340700020b00010b480c5171002520080c1c150b62070711080000e061142ca0315007500300e800450032451203000115088420040c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 12697435 1250 12696185 12696191
    0x120a0b1003020910080d0c0f0203151b0702090a05040203011d07030201080f090d0c0201090504020a26240a03020a09050a0b10020706050c0102090901030f1203020304020d0605060316060306060201 86
    0x3d4440e01c1c003101d50150245c2140d95210841c028484c078031488203502c0081c0512941142c120103500464140101c01a00a90780342e01c903003e0003003100103601d010880e101c0443c1c805013000320b5507000030085030024200880403078540e8003243c10355800303601c9224014220034800301d810420441d42510f803d80c1d440140e000c2001c000000d9040340d0035940662144400c0d001a019007611400c0c1943c0c1400c030400c040c0d0402210b160041060340b01e030720042505d8038058440d411082034070204140004902c001014000d101e039024000d009040229840c696503400c5510701c280c0c541038010070014282588003070741c050b0a00000250140d410b5010138015840da110521103100c0700c40034000c0401803000c07103000581c0051420000c0358810009007491071801070015281075082e20019001800c01c1e001602c90f82c1407800c6241c00c0202c000e000607003011903800d06604515040d0002004201002005001103440303800099860780e0511841540a091155001c589512000014020401070140c90090740c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 12698685 1250 12697435 12697441
    0x50615010309031413030b09030c19020117090309030102040905060102010509010603020a0612060f0303050910030908040509040311010906150605040b0406050c07030602070f02090c090f120a0b10030209 89
    0x1110b4040e0071815a01610b41c1c1c058204820304100d6207034401410095590070b1190f001c00064021444540a00321481c01191102a60080b82c1c2c1131a8000780c01401850092500304010703600005941c488440341d040010f41544c0f0150f110b8158410031041d1503065200003400300704030990f0362229000f0031083e4020052a0745a100c00381c200d0b203103800042d6110914040400c45c5901c200c0c1030030002010454041034107659518042180c0110303030002ca0106401203001c000b1402d02e441942c1200340c0c44d02d024480c0500d0b546840d03109110758003c15000d2050301001505050292001c640100b990400800409080703040000083c00c3c40d0f4031103490012643c1c2c0010303a070f07403040c015501545c252a20040c50185046015141503124050410850203805d8002021911034400780110030301a40182003942035510402400c51402090340214202c20b22241e15240c440480d46546034800352003100c2460300c000962464a003101d20b0080c4142303150000c01868217a2410004120f174820366281c1c20a031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 12699935 1250 12698685 12698687
    0x1002030a02040f0509100b0a03060504050c040e0f0106090504020d020c0303070801030204060b0a0e040902030109020303040801060602010f020c1b0102071a09030d0503060102190c030606060314010b090307180f05010305061501 99
    0x341503c42d403884551b203500c20b1165814020003040e044149040001e0030682e54404141035400864018180301404903003040200d81e032242e01c80d030080c0c2c1201c4101803981400c01c0a8842c28450055501a81c0e010034403103400141681160000d041680883c2d80b203142145009041d8442400200e006500304400006d144c131000040e684c45e200d4686843e03800f100c114051200070001c00380c050381d05640301c0e24104c001d608c0a0005101501c880c00000c80d84609100000e425580c6803180060700901c1000f8580042c1800300c2c00101d030031941d26105c2c50851001004030b00d032400d5070b0015218540390406460035400c2e400c00a245032071084c0d05486c00290059401c1d1042d001c01c8507c01c0c0907800c201030b113000f0000c40d0034640d20300902c07428004400740d4884e1140c000725911074010f40f000c81d580d171400c0368602c0803008040f4018a1140007081ca04400d0030007181e252056845580843e9168040061648110703401403c42e0384100c290800541d81d4038146a5035408094814606680308190194465 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 12701185 1250 12699935 12699949
    0x61503060c070b09010603020a1e060806010c030c0501200703091d01050904080d091a0906010b0d02090604091b20031b010b0d2003060907060302030601021002030a02040f05 76
    0x60000811140c01c0ca44142c0b210f200500d00140009400e550b038200210040c3e54130580c040280c0b80502c002851049184424601403100350042070a002e0010208282c0740e90244040301c03156818500400140301d01c0c07510501401155040e60044006151401c82000c0710701c000d0700354a4026600c996400b69a201c0381030810a00b00c0190680000030001030240b0300708502910b4001c0d01c01c1c444580f42484500441f02194211141190308800100511100c449242c014a8009034030300c0260443e0b500d0300e15600c03801c3c410424450302094021810210380d07600d40c415240200210a001c0c01003054a40414100c840c17144507c0c00400c00c0e06000000c80d0444048000c15001d108000350b150000c50003400307100124404851070699207400701c1000075100d240c0000c1c000e6110300c900c0c2442c694182c1c541c00e100154508d01700d020340e200804202200e403000840e001153700e142001030b81e946031440100e0508540c0b0070380c0800c0500000900c22022110f13801041112000b10b03810030500e855508209203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 12702435 1250 12701185 12701191
    0x60702061e0d1a0a0501110307080706020403021f020c0103050703090b01080a0c0e13060906020405040207110a090212041b050603090f0706050c060613020910020a061b08010605030a020f0c06150306 87
    0x9000d03100b06000c46e50080742014504002481180e041900c69500c07585c2c00c0e48003000403141c030713500442e041046080c40c100160300007003002c54003412030032807100003980c600c0d01b04003450405458001060340030f4025400a41c9158100600141030f6841d611520b82e607010507c1e0444081c100c07003c00140511041d84035600030000d0702d00003440034160751038010107091580c2e8241c44d680c0c1d08201c00922035507075100402e038143c890f01c03014204201e03d03000c12403601550750000c0760440c0100080380c0081c0e1001c0c1a10b81c4650b102c0c04920032150856040118226543c02594200200006100702244005441c4131648980011204115212401102e030b03402403445001855100902083c01c80c81e142004000c245040000103041c03119100024070b082e01c174980c9550240c2c00941210041c84214001d2140310601c460980c0c200b00c1c540780b4028407040051181c002002000700102e484201c0c103404450b00c3c4400c00d0b841741e881780300000402e81c6843d019240000780802e60365000c010781c1800b0440e588 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 12703685 1250 12702435 12702439
    0x1140102060f0702011104060c020406090203430519020a030921050106060f12050606041203020c0307090605030f0d02030a050901090503150f15090402060702061e0d1a 74
    0x341910b4540b410101142c02a00030025952140c2911038034001001c0a003008260540da40588a48a40144401c276a007035004101214010002c10082d0442c54210b00100c285120141603044203610f1001112403124440d81004505a0303032419080e6848006010840141c411020941034002c106aa0300e400c007040040126203855820040300da0099a401c80300c0c801c20090240c1141169280ca0071110240c00c200301180c042441411041d0340b00003210b100a036058020082420184006040f9004920603102510504a01c80d0209031003030003c6100064060212500c590f107504640e030140070103004040c007911030f00302d841d0000000050700c2c00c10420281c014600d8191160400c4550f41e001b006400c4c14003810080000301503c0c2000b00803180e01003414031481c030342456040170882c460041c0482c1140c51640300d800f060366890720000d540140c2d040380c0440d611003d9101144a038015030300d1020303100201d4079403182858048001400d1403c1020000c000000d07016403080004000b04a11136 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 12704935 1250 12703685 12703693
    0x9050609070302071a01030305030106020c0109080a0f0f0b0406060302040c08070f1407140601060809030c030405010c0201030b0409060606030510080a02210706230a0c0605061203070f0b01140102 86
    0x941d009000307900810040780200b07403e0b40308048000800c421035500380d00487c0025000001040025814004005100c5003442d00034585841c02140c165a0603a161010701410800100b400422170300001088049612842143c0d05280c40d00300078009000c00d01c0140e0040e41040907000516205062003403007019180c855054118646c00c0481d802c2c04019011300c45100200402e0002c0340c40d130a95081e1203070b5000c00030311507903040c50f80c003c02c8101d0180400c4a40d030b1043c0b003055040c1d175022060b40c040d0b407404c0c6890164440c10f800120301034040005043d82240ca8541407006100b50340c0c00460a440040c0c40501650325402d0030b4945078080343c498101c20381c11016440700180b0340600c14901520140306640f020f034011031007450078040c19602240200d16030700c00342c12455101c01601c854000001e0a01c40c10000e0011000d0600030f00440002c242c5580d44000840e0ba64030b104d01e030310301462040c0c2101e860310036514101302c164107a0542526044084400010702034450211652810010381c060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 12706185 1250 12704935 12704941
    0x30209011706030106170a020a080c010503041e140a0b06091303050d0e0313080606010f0801170a050616090801020a0e0d0302010b0915090709081207020411030a051009050609 77
    0x4508007100034000b107503d55201d80d030000d0810002c0c031200740b1040480002e80399000b11403041082d442480e80c80440c5542100324100541c1e0b81000c10780768400d40140040c0030441c0e80384030300b007917104c10100c0081551a03c0c2c2c210300c1c030780c41002454407141c0d8422030b401502600e64004004a0f19411115450102c04c0200e0801c0002e02c02c03005840524802500850024035031513025045801545800760107030f400520400410108001950b00900223081090648800c010300400080c0140501d4078002070f040112131100508202c4074000c66041015604903003070042d0b00b183c070ba0181035980c81c0040c488000128010350103200703c1d603403610184c5072140281002801d0003240307600d1500030703002d5550300c8446601d261207418140d4070648804091840395103a00003041003414014015400700302c0150010300c0000800904140b10030074081c400c0340c0713500540c400500600700484604103800d8020042c4031803802140c01c841e0142c2c1000100c0d0400b03523103078120078080b1002120080c5c3c0c481203036408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 12707435 1250 12706185 12706217
    0x50a121707032c01061205010509060106080402102d09050a0902040b120403050409020301062d080105011101021b0102030405011b05090409020619020604020901091505040c020f0a0c050103050703020901 89
    0x2140f1040b04580340045050b0b59240b0290141010441054405944420800c00d05c10020302105000d48640c2c00c1c14071441c2003503004070b54070407211002c20040c0031a048036800080b4006140c600142c1d0156400e00c1410016240241000ca0340d129550040640c9100480e00301e900303009640c281e454041c80b072404d003d58242c11402014014106500344001080f001c07504144900045019114076224404000d50380d6036809002071442803a83c2c00a07241580204a40da0701102c207074111103003464040c0020180c68102e60082c42040c0c030001843c0c240350348030780050b00190091407055000c0e800070480a902c420380000040e280d8181200081d004010002d981d16203039101082c2140042c104504041e10000482c686805e01d964081c00740e88014104406c500d41719222502402d0a403506001e0b41d52805212030403036081d40a400c2c45242c80d00360b100001c9100b0403802e11031400c22022640c40f00e0446c04c110143e420706001d028006410200003480c414001d001300d44080006079144010381d804010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 12708685 1250 12707435 12707501
    0x7090305060c0307031503030c020a090b03030d110c0a0506010812030106080a020309070506030112060605060a0e040f090501060e090d0e1c03120c0e0a12050c0d050a12170703 77
    0x400a165a070320101c1c0410b480081b200700914480e8590034904001170040210402d0541d2044070712604000884901e0344020064403044080500b020031031181340c40810752140542d100c204440c4c070840d0407400920031b0018403607040b909040c06464000d500642880100d200901440012178148408100010050790042da8814070000c166229262246c0004403551300c283d00454a43c0414144101404400e02c624801407004075031143c94030001c800041c0c8100a070f10f00c80e62082d55202c0c120000e07440c984d04140c0d502c42e4084020040b03180c07a500e240c1e009a40030750380444c50b807294000c6202e010f80910400d014052004142d49030b5203450100c880320101000004404110480e60302034000f00b0140550070050342d00d03455001c000d4032403405014500e00541c2c042d14260101050060104001045c41014003c0690f28188444c8190801510f008c4201c00001c03c50304180509004490703000b086102c900e091a008042562500345089043d1045594482c100301e0701328008402c2c89041c0c00d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 12709935 1250 12708685 12708691
    0x3090e04050703050a060c0f0905150708040e010303020109050d030e060f0702030c0d050a0f02070b0f0717030c0904061d07030c030e06090309030f060c090f0406170a02030607090305060c03 83
    0x1c080740d840d26102ea8916050401d20201240c0450301c81c00c1d055941a0803103400050500e4502c0c041081c00d02d001c3c0043c07004100c3c403400c0090101c000444600348405a41210041c00e40060b12100390b5030740e40b1b8000d001741034107070b41511540584480380b40f10070301c03d0007201074028008000b0400c0781c0740d520b220b4185020103409201944070400018942e00428006c0740e2803d01e0369111941c60f041240d80c0906211445a40c000442d0400341c4244402541d076020ba0b400004144503054a0716803a1a00304242108d10003903443c0d8160100800c959500950001d0080307641c10303182030218944c0c980140b6681d584814803003903c0c100706400219400e1113a4001c503a140183d207030101e41800c060312141d040000030388400e082c1d42c00000d04642d65040811040594944a400401c0c0b82c0c03801b4071244195015410b010f40c0300c1d0109224048180d5256001403001c2c002030f811101c0b80144408480ea9591f10341c0004074068000c020008145c14010803c0c2d4048903013140103070802e55140070140036554001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 12711185 1250 12709935 12709943
    0x302031503010504060b0a0504020f0d050402010e060304050706090b0f070201110304150503040507060206070903030302090103020d05070e09010602030306010c08090d080c060403140f04060c11120102070201030e0a03090e04 98
    0x544500c8106540034021240914000c102c0003071001904000d20200f0300064001c180aa4010410203e000a18600300c0301d030300c0b01c400400101a00c4500c0101c4070103003c501c2c07041d488031021081c0030901201141c402c00700d41e1107486038614541d4070400104903000b20104142e44e05418007940000d540500074402c007110901c02603a20301611111452492040400500c2c00a140881000100001000b81c031029048a00090540c1d02d0450402865601103000003404c160f00444e9005083e4003d4040d1060b40e094005c080c0407a25101a00500203d00c4074805445541d030200001240d60000c021a07008030070680d030b6949c01c010280c441030440e07481342c03aa490b0016084040391011800d1100070b04007843c240000351110303041c58103000742203418031104420625010403030703d2200c00050048408444542c28045840101d03070801146c4201c01420315030300b1440c0706603103884070710042d8000d21000b4400d803003c00442c510b0006d000c0d558926032074020b010803d6807005004075500031070300b141d00c1446 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 12712435 1250 12711185 12711211
    0xc060405010e0d020a080a0b0f040203060103150603122c06040504020c0f0717070806010e061002010b030115050103060902180f03120c0d090605030402030a06050702010f151505040312030203 84
    0xda074042802e60120b58801031054000c1d1107114200030410032300e0f81e040300041c05044807505040e00065100c41040c070005040706800ba001840341801600b203c8015138000010b0140c001c00d04001812098a41c9180c40d12050031407190443c0700042c004107180240c01030301c840c0c1031500340018440254080001c0804031700c1040303e54031001c0420480040504403a490403401d00c0042c040701d81c07804803940c00c02400c0703801c00030041c4540d204d5011a40d6120030120740c0f6502d2451404001d90042c03040a5806815508021046528140050303400c02194030aa0382040304640d00d64808081380180003005a0755000d0400c001d02501e80100010340712007004041e200d400f400c0d03204d40f6580340c1c8400d500e42000d42140060084c010f8106455100414160812514601c0d065000a4441c5440d603802400e0310b41e5680415120b62003544840625000460104248a0f402400684c85802407240c081c0910742d00902d19141841581036900b100d6100000d80091400c001c2c0c16406900010480720000304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 12713685 1250 12712435 12712459
    0x30806040e120708040e010806010308030708071e0206070f03020c0a02190f0306050109150308070210020f1005040c0501020c06070b0919080c1005070c020f03030f04081c020c060405010e 82
    0x6816001400704038840d11001c0e0f07a880c0b402e841011b030903d05901521542c0c100800402c08075103004e003107030391059603840d21a00e1503642910036030310391a00c1c2c540c040010503101c0700d80c602c0b26000100140131b40f6007911503001618038503104074280d100d0140007181039046141c01d0401810079603046801940440348000d0060340b00d10b01c0800800099100750360040e100c00c0100600c2c42c03144504010620300d0310b011000e003411070300c0300b0a1a00c2003640081c01621386480e002046c52003448810568607030002942e4100d0b0786104114094141924140e8040d140382c00000340c15800040c103451003d4018200d00d041c0a040e4444540d5100000c00c40080c5000f495002c848201140d03d0304a6002d1080450b90b460380e580e8049649440c40100440390410714100c1404451038001d141001031650407181c0b55802d1165602180c00d40c02180c510f01d20254000c02d01181da820041000c001d04481082c84112008200c00120f0341c4098044181d60441c501304010700c160751141414182500300a807600c01407103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 12714935 1250 12713685 12713713
    0x2060705010219030f060b04030807050106050303030a020706060e0f010317090603100305010f110306060702031203040803040201020613080a0509010203130801021312020f040504020111010504030207050901050607030806040e 99
    0x83d1004014082d280e41c0000b04404864152040c4040000000e40400c9120300b0b003681c001c428804c5002c040e040c1c42c0041851010028250050005810003409603503c0e8100f210074480a90041c09007100c4060515001184c5440204142d43c402c15a4416085950f440c40d160081c81c00310b031110f1510404810001c005468540d01c0c0158005e4060020303101189242d8203003242194280000d2044181c01c0200a07000c4812040c192504070a0031203a16030303602d8680c40003c1c90600c80710300b000d41504005c01013000f0b0180c030001031440390b8001e030241d0749036036200d4071141d142d20380e0035500a220840c00d001e86003071140301e80c003d0188224107004072480e140f100d082c540da0325859607100c040e0b01d80d00000c2900001d00f190001c84001c140d0901000502c40c40d640c0041c0f488421105458069a84e410014080da0f1040402c3c034846e10100008100d6030400f81002511802c00d405040d00a035113540000030242422800c45d0381c180e40607a50502a91924001c1002030406980d512501d0300c0b5140300c000c040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 12716185 1250 12714935 12714937
    0x5060c1c05030106110d0c02120708070e0603010b030f0307060b0111060a0c02010f0c09090c0c0b0c04030b0c030c03040f030504181407030605130b130204060c0506090d1b020607050102 81
    0x2600c0281c40311502e075803501500401c074141c40c680d1480d03142c2211380711500c6150018030101085a04039100e0710f04414035040d0614201d042c0c0e00444c15403141940006489801300340d1b10b40501c0301075001f40895031200d000c1c1a500c4040003482c0ca038551080001402080c070765072042600c1c10381403400c0700b07a0568000303160f8a0082c0507102c02002e01e48c4c442c1d0ba00031b070755024841c650407030103004402e201c414400c29010b00100355a01c10b0031005621122180300541c4280d0f10b80b07200d10b074011009100e41c102410545126040390200702d400c001e0000200b10300500c400140ca2041040096042c65a900c175a242210000d242d07000b2001c3c81030901020842100c60145074100c2c0c000c41700002201d20855000d4802d0701406828a41070600e40745c4244420781317407151406a4001c40941c041002211f85020030074008410b81e4009400c0d10106d00030940a52001429911a00840858840c0d07216294100e80300e442c00c40b401404102801c0001281074842211305c0911070000b040e150800d160f64030b0b06403c4e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 12717435 1250 12716185 12716233
    0x207020d0303020a17130201030f02040503030406090807050306010b070f03020f010e030903010b0d03020d051309020a0804050d0908030301060e01020109060e010603021003050c040b16060c08010504110304080405060c 95
    0x200f600401c4403841240e1085403c01c035186070f0705070b0449504259521b0028104075071b038060704040e00d0700030b12511740b074058044400804015044070b42e510384d41c80006004441601a000b024011140e000849140c0042d43d141a980d04c20341442c61b08040d41d40b0004250028101141540181d01083c4074151302032041045803042d0401071941d90030307008105800c6655500030307075104440e0b243c03032034001c6540018861503007a0b080c103000b50f03504000146c0e855040c50a9014010040c00000d1031011194072a041c6405548520110741d003620b0b1541064a018450740150185a481440100005032142c03003e1040300c030060000165001c80c039151034082e04c5034902c0d0780a060703440d8603007082141005010405054201d290401c15810503480381e03a00f40c4100c0c402c2c0b1148440100360301803214100030315001015803004003000781e40d00044018207460424407031a8401d5107040492140190941708881c80f40b940145d0f440c3c905030401e02040210741060708506000c2c480d4900e503e8503400340c0716058072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 12718685 1250 12717435 12717437
    0x60603050108010e010504050d0e010c050a0503040603181a10030b090a02120d02030307200f010e0705030a0f02040207030e060406110c010c02031b0301020d06060c0203070602070302010206010e0a0207020d03 91
    0x16035604250041c1e0940d109400b8040d00e580c5064100804200003040f4000c2500c2d15103000c032000080c1000480d0f042c10382010182060041044410401c100000140126000f58500380000d02c05000c04c000c50090b0098080d100015840a003003036124928100d03a031041e031400082480300d03140d0b02d1b4440907282c01c98590006602c030300c00d24401e5103844400f410300064404000c00d80c842e50320030001e449000c09000f007024484028403500080100852a40041882ea0b00b103a508489000400c3d001e400480410070250048004c00b00d41410049140d070020f81d00b11014000000d01a400e00c00250711403c010780070001c40c10385540c0039a54800060008003920764a518411280700c03966420701b049840b0003410b025807030f03141c0401a1000303d0700352a038054000d1009020020800880e0280c402d881c42a6455032a226002c0342041e000004e64178010b0094045590080c0c4a0506a80e5002c1d2400068013583c0494010000c1001101c0c8040e801111030350003600300034107031380814140460030804034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12719935 1250 12718685 12718691
    0x6011211160213020a0504030b0601020703060203070201230903040605031b0408060702070605030114060a1101150612060311091005040908091e0618060c15060109140102060c0a12060603 82
    0xc0203510f40200300040c8079800d070750114a8105501006001442144401031001d6076540008906038000c0c0410002103800c180c0a40d40c034545020000c0c02030003904000040000c10000f035810201c5003111240c424000a0000c610b06410010281d6158000410304242004030303100c24405401400b01030002004204018201400d096901a0410302d19403c40f03001c0210a000411900c400f00c9a50502c010050b1031060742c03007030009400c036442c20003502606030560030040b410300c4841c1c90a1061044540d180d071031880304007940e0700307a9007503410b248005041000d90304401d031702c2489c0040a05800038098a2100349265849011800b9a1130440080d41e2100700400c80d01003d04200303104403180240d1417542c2e0b005514101c00114940994030021a04080d035001140d010349841007100e03d041408e104641091201100342c5640b1202100c2c200d000582d05040010000321881d2070800341c0d41c058000d00703003c4e9120154801aa0400822801008404024082c0c018001e106410103024a59804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12721185 1250 12719935 12719977
    0x1020a02060705160201030216020a0b0a030b041a01140417030301050108070c031d1801030606050f09100b0906210105010f11060c091503010801020c0d080403020606011211 76
    0xe420090024480001d002c0704001614084180c01e56a8040543c2401c00503100d81060109548407281d03100c000350083d4078068023280500241d4058613801e51301341d81c01d204920700e400030721040d280003482084103c1c0484400f0801c40d03024203240350402103080c02c2c1d1410035030390f14004030121710006103111040c0c000000511265074085050340e0302910900701552411016680200840c0322041c22180a03107041c00210140d03070300d6018020100030889032103541d40d40c41e42002401046948603070f80c480c11080400c1001c50504002843c85810f40d50f0700300048518151b030800b12541f180442e5076010104016050303244c1c400040b0108485cae18502101525818000090b02890350b0001107c203001d620515840300c0200061170540c840d07840c00206440d00b2030b52021030b030400b900c0c1e134a0f070001500200010940d000150301a01d1200880c000701d0b50001d0615005840342e9205607005001600100c2c00940d03994020700403a000d410703000d400002c5401c01040422a140c001c0a0741c951000710302040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12722435 1250 12721185 12721187
    0x110613060f0c080a030f020c01020d020408070f050604090504020607020909060f01051e121c02150105060310090504050f0615041a09010302150f030c030a0e010e1e011b0201020a 78
    0x1d03021010441c20726007a00c02c416141d080440c0200c10b0a4000c1586510f40d86a100005405845d0007000c0312000795102c140e1507644001075041400f605580d8072414000140d10058081580d04981003e03004625282c00d02c03154001500d0010400e03030f003000b0108035610050700e8800070b080c03203000d5585c003510302c5041400720803041e903c045c1d0200e4400c0b000e000000c011000c0c404400075031003030121174064002d1b5910b61898200070400c0c0b039820300b0184016481d441d241d004603c0c243c0b031071021191034503503a03207500c208002401300307480c11081c0f103000d92028010030940da0b2105030054011000c82d034405004169640c604501110f4500d140e03030480b801c5050034202b80c003442425254940000d0240100b520100b22000340520018cc410198045015a144140011110303040206030303100b40d50f0f103441000010581d00a86056041d82e140805200c203800713041c82648140c0c1c44013009814203a068091090007102c03003d40c0ca119a558840d082c0c0d450014050701440a42c8013600090b807222400e00c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12723685 1250 12722435 12722447
    0x12031e02091e0109090e070f0308040e0705070506010e0601030b030d03020a110102040806041101090801050106030507090e06010c06020306120102030406050405071d0a020a05040b07050f0607020a020d0f11061306 93
    0x9a075102409050411502031380c003c1460420707140000b8000500d0000460340318a05161544031000b00d260005003c4248034081c4000c1040e141612013401d05511564000c031140c3c0300d8090702400039005940148a50000c200f03219401020524000c101114070900090800c20104101e0000ca940011700906040d0003d000c1100100000021402c05203401d020f16243e2000410041c0303542c0603d000c009090303004500d0034016009400c020400340d0385401c0081c00408041c2c1c0c200c03002c141100744c0000c03003400b19003900d8401c25041c0e480018042d4955282c0000c0d41001d840380f5403145e01c007000390141e10403d1000e903108074024000410642020300b02142000781c2900705101002140400010108600550039040840f1440060340d49050400481c2c0c9401107401c41e1801c22000a04a8144040090504144904d01043e5000c076222080243da82d1011808000c1d00003840c0c0c103008020544403480c201c0c12600581c3c203101429071800000780c442d880262074600418103100140200c543c414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12724935 1250 12723685 12723709
    0x3120702010501060905060904091704120209010f15080c160803040b0609040201090308030604230402041b020c0d0203030d090f12090308090603060f0a060309030e1c12031e0209 78
    0x420034141c404c6c1480b010070424405c1c00e29407806151103000700c4041040291440d84044450010182c5403900c4d107c260213900d5003d00300381e02c90b100c140c0010942c961007500000840d0b90780d1240001c2028404400d403024000280000d5101f0010700c825900c40e1010400c2c80701c26441103d500b42e4900d440d1504041c42d4101a04141c0500580c82c00c000050b41c00110003c190380c0c210750032548036035441c0d000401400e40509101e40d080704401d48184400c5c82420400e0050b842120144201c0c003000c1c20400c0e61403c1035810320010390184031707290b0b0503040801003504141e00207400c0d2480c4c211590414025100d1402046030602c64580c01c071070601ca2843c06052041e105403030a440e0561940e16904245d00800141c0c9100e47c500002043c11695010381000c01202c001e001214100d0307440030081c0040c8003601041d07011072820b0f00410b4107071034840c0741c1d503040c40044a41c8524040c1c1d9a1941e00f0344224540c40794090542d19070950011070078181c81181e949401d200f0141c1e40784005c1c81805a410b15035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12726185 1250 12724935 12724937
    0x8060117011506141605070b070204050708100b130b0406080103150b0109030204050604020702030d0e01030e010513060504080d06080c040605040b0d0b090106050d060504030f0c080304030807030605030312070201050106 96
    0x164205100140c2e203c035440c1380000398080f01c191039161944c081703440f4014459004107144610000040d0551600010307292260080342c08200e0380da0b0f85141a50418001c807101d00c0e44410a83d0144060310004014020800c00412180422a01c03081d444465030f11a400900109841d1001041006a011501810625081e038140700c082c0c0c001c0b002030b1481c4240c1c0802486261110f00250f056243e0354180c41001d40c00808450b032581d14290080c000081051950b4002410404200d00f54181401003d02820001c454042400b10540300c0ca401044080d104071104e40b4100b1104a000c21540100d27406405c0040190480781151810002211620b0b48518055030426041c03010b981e44142404041d56040124102541c3c1c030070b066140106503c0e004150b0256465403110180005030748601c0c4a1440f03504c980c00010740a020988800002c240014500e40c000c1000071300280c45040c4a43c1c0040460401054598840f00040d0858000f00c81000000d4401400c000b911381c1d090090500501c0740e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12727435 1250 12726185 12726221
    0x60c04060e090604110d050114030708150c040503070b090301140601020d14040b130e0c03040206070807020a0b04080f010c030b011704020a030c0b030403020d080c0318070806011701 80
    0x1814002030010440355501c2846403010500244a40d01c0c0d90b00941e03a0300c010100746503074a00424020800403e820b001e0401c9032003a80780c0703084290800161100542d81c00b24001d00312030341c44810a0700031101c028440c00c13440d10240700008090710100b00c0040603000c0c2c4000070340c032040c00e40240350854042c414686071114288040c07240f2a6004151682c04403a2032904546990b44610036462500c11a03021101207035000401c14040000190800309480d25100950b926458004082d004d0340020341d4080d60102040110000044040f8000c0a0b0329201a107106510b80c0d60303105021054020b90721444c49600906108413411401303205620b01345001d41010040e0740c1e00e50300000c2104510300d00b85101c0d11607420101d8159612000407000542c0d10010b1441d586890300e049a9403a041030301c0c00c0b0054071851443d00412400f4000701ca01c1072508004a90859680015030054051140c0100c0800e000301c54011501803010310046004e0041015500305418000008034219802d0726910080b1040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12728685 1250 12727435 12727439
    0x20f01021603180e070306050a05030c101d0402030406050f0906010602070603020c0c060412050f070308030402130227030d11030307030c1b030306030317040b0604020c1002070506010503060c04 85
    0x5118450419494161404030843c103070004030041140c0d4150000240780c04c03035804200d2140e034160841c1c41034403c16900d42c5c00706640c0f0001c1c5507481c005110307680d511121a40303a07801120720400320004c12803401488200d030050a403011030308a80c410384007030f90426110000c001c1d0243d050400c11381c000c0441801029250b24144000b900d4070326034025074040640000d8808228517003045900522440100354030794841c1d81d980002c485000091007210b01d402080c000c0c00710400007040180440c0c1e0400040e034559038540e8200200c27a2240c20312b0768003044d4240710100c80b000302c202007820322840754290003d001c991002014a054032428100041000020303041c0b20403000031040d0780e0003100700c0c2030101c1e404801c60000c1d40d0b00c0c0c42c88625000c21010703c2e25030000389a0b02d6044030048030700030b0302c40c112200d00c0c0303141840120350708650250400e18000d010924509051340201040700900d0141c810b40c44844420740107aa009038001d94182d840301c80117004502d01032000340c2e00170701c1c141d0980c0e20317042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12729935 1250 12728685 12728707
    0x30c010e01080c0706060b0a091a090609040905010f0b0906030304050d061a1801030b010e0103030c0b09070b0c060115020a02090f1015051306020f120d1d0706020f0102 74
    0xe00005294104041c48000c03a03002071018040d41c080036030050381404110f80340c420132405034200d2426240040c000c0c00c80003800b84168462100d9583c45100b40d10b1801c6c6000080c010707150301010b06c19800c20381d60802d54012032000e100d12002c14405a80109409151804201e201d440203450603129030000c000802141e17450b0307110703400c145074000c10108140c1c40d15000c2c040348491030f016050b0040f07105001001003080b4455490706891042c2080103182e600c0700c07040500c1000900006002c5080d00c5083c40c007090704d06103443d6115081c01e045903502174403600401e000d078215141e0052203512000c0180000341010025241105852000b080d00c416941c0014000c0840601102c100240280110788039800c0811604003800810740810110005010000c0065022a10030450201048000b0844903c0400c80b03c0a0b240c01000a01408203140504401a4019220a05c04a030b45100d001c004811200f440040f2505e00382c083c0c61002e20308140607003000d94500d000c00599104105a050341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12731185 1250 12729935 12729947
    0x1d1605130509100f030f060606020a0c0b0c16060c0b01050d081603050d020708030a05060d020303180409050f0708070e0108070b03040201020a3908100c0c0605090307030e030c01 78
    0x850084514030200e464860f6a124140d0141d0032880f12480034040c0403040c8100001d01e29002881600c1c20002c19942d100100e817120903540d0024a540080203081001003010400b405a9050800a1741e1503c00f40d660248400d610301e5005a02080c0041c54000510a6440c043e900401d030950f0300c3c24501c909507544984910a480c1043d5120f2600700f5017009162180c0113451048030314410465480b040f50030907800c6038104445503420700d8213120010310300c0e0820740c50b40440c4550183c01141481348130005071007144800b00840b900130ba5681c40e10400300e40c08201d41002485048041c1030031a061124403801c010068108188910000e001001489400a0410100d031000d101c521f49a403100c2c80100c1c100414030002404030403200340c41260100a5228129501050310803903010782440301d40ca910b1010041c0319041c210342000030001c1946446400c0304c0720170092868041ca02c00c082d42d5403e001c903681501e00c0701407540301040729020141c01c1640099804421002018501e82c2080002c1c0a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12732435 1250 12731185 12731189
    0xc0703030c0903080d090204050705120a0f09050a08040306060506030103030e0603040201090e09010501080106080d020a11030a050a08030108010b0604030209060409080408010e0606040b010801060206011203091d160513 96
    0x800d41c0d00d841d0541c81620404000000d15888403c0f03036a90059440141c02504800a05034071444c0b8080c040748200b8010300486a40b03440e4032a041000343e5520001c0e100605100c103100d01da29407a102c50900040b070620030300b64a144034001440d03c0d075080d4105901240c803244c1040340101d90400c01070020079004046100d03482c0007210056526030f0f40d44012207042d1055800b81405140407414001d503987d06411040c165002d880003000019521088907644031600c81d1080d02513000301c02e881020500c2240c5e0400100400b5085030301802c2c0c165195490240442001d5451b41c1c070101c014096401c081c05680b9a0610480302c56040038151780001c1e03482c04001d807015229590741c01100d01008103060030f480051007468020401c0c201c2007140716407102821545280b185181c008039484640c000e6034240d05a6405500402481c3e0030309038542c4900c540d40d0300c19810300403083e000081d211540218a020489441012a12410107841140310402044800018442d040c03081610f00c203421aa1041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12733685 1250 12732435 12732437
    0x9010504020d0609170408031c020f04170307020d050d03050601020a0201050f0310030503040803090406050a0e04030c0305070203070609260316020406031407030201080903030115051803070303020c040e060c0703 93
    0x41c00f002d4518005c0d0060103c0001503008140c013203800611600d0101c0500200040c444c0d4858040c0d00d1003402c00c0803445011841d41d03000340d081c0000e0100c45494003c400e00014400110382c64030300c0c513400080a28001c1c0d80103c82c16030100c41d40d07240043d0b15026032a0000400c0c001007903c0d29041d800600140142456a68904804400903100e60312103003c100003140c10009aa544a440340402a280d9020003021400769050440010321402c04980302021078485007010145a290340d40c003243c603010145800d40420000f40f000d4800b5907020300c0410010029500c131b00304194980000c00c40c0d007000d032109068400140440b21010300b9404800c641d42070080043c2498801014400a0002e140a03000940485600031600b150b80034001002c005581c001d032101c54095840441d000d999120901400f04804d01c3ca54414100d90f000b10050095902c616100340f102400c0000030030302d4811a0340c030640041e8000c0302c1c4814541024410301c4541078421001d0401c910701741c001b403640c030b20540e00e00034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12734935 1250 12733685 12733691
    0x3070503061c03020601080c0d0f02121204090b0103060902070b06012102070b01050a0f081207031209051f140105060d0615020309011206060c11030f0102070803090609010504020d06 80
    0x380d0207958100c4a00b00d10000000110b28002140c10000d5031500e0034050307603c15200304010a110b40c0f274969485900b86034040d1401040c20210341c244200041ca40340341000500c01c106001c070f8280850f60280000c0c02d00d00c400043c80350051000141a41d1841c0d1000981e01d02c10841032010031180403055520030003c1c00d100c0c84948207500c03a1501812007070301c0c1030707000303440401c0403020005c203042c6c50360488404072400c1c4288c90b152040c0c00800c0410340720302082c030b034001174582041103100c001401c1042d00a080c030b007134003980c0c0140e1101661011a8211081d802075240500040142510f820050769240010008442d01c1d4040120013031040c010a03224000c0440c2203840340d0100d8001401800d00d1640e0300c40d413a8804000a582c079044408414003003a41c01c070405c51400618400c000c2220802e40d18514030301c210340c694591a0341d0905000c0d8050141101c160541c00c2c00740000d04445100e004035559071304d82110500d081c054003030009611a41080f0500015a444142c00704005030004400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12736185 1250 12734935 12734941
    0xf0108040f110a05040e0f06010501020c010504140301020f040305010905151b03040f020d0b070e090705040504020306040608030c0705190303081602030d060f05040e0120070303020706090b010305070b0c0303070503 94
    0x300803200f980c0c4200d07401410425851192070f0003003002014041400102c1d109a42c0319001aa2544003950390315000542c10700003001444099110540c010030b028000510349860080700c00100d500540003900c05a441c0c0701101d041000410042c9001800000304041c14202854054030a1001c03046590350810302201040030701101f017114258040e4000d01d240c13610003007803030700118100040703503241c010403510446180681401c5164038481e042c11703a03459280034280b00801000307400c0074050302c0c1c0140c0c1d82c0c14007107134401040005082600021004010b0700c0d19007010403408508055050ba0300e40311160701000082c2e00000307011b8111a003009804840da003032100491960140c40000ca00d0903050040020701c041440c2d0102040e00c0c0161801d000030006801481d0a0b62000b00c8590b87c6880c00b0a60301800c080e4140c050328405100745000b514100c041d445510a456014000790b441c040308100410030014100440b00041074200c5400e420031120312a081d48900009200005003c000000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12737435 1250 12736185 12736189
    0x1b0105070e010f0201150806070906051201050d0318091b030204030b0a05042a030b0f04050d0509010201060306020f03070f090e06010c060902030105091b0114091e0907020c0f0108040f11 82
    0x1b07101034014043c40450740315540d0304601d0f6071307032000d075110b40216520550102d80144544e088480940c54205581c0706640f1342800e0000380b03c1c5092094081040500c115070102c03030384840d0840240014000072400031601000c0aa001d059115180c040c1481000200001046002240c1e440234118500090b40da690b0700b44000c40b007240c50801219a00306035240c40c117100342d00b00c44074242e81c040d0001000d26640c00386e0807009a0000d41f0b001e0f01e15401005100c509500c5a8000e190749541840040342c5641e403992a88160b0300048007841101101004210600fa80720008442e8015207207041f100a030302d484d03400001c601000e84124104105080a0420705c0019000401d4407540507008102c80d2520740c140c03d4681d40780d6811032880101081d2090801d612418890b405034400c0364a45103807201c035804200342c20800d083c00c14580428400d0040d82b650703642401c01d03c40c1106070007414a0800c1d1004210706108015006811f01010f02d0034000440d110140d5409130b1036120701c7c1d0744154480c0d100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12738685 1250 12737435 12737441
    0x60905101a0d0e0a03030204030312090f060b0f0d03020105011701020304031202030402031204080615060408071e03050607080f0109110301030210020f01020f040503070f0605070206070c0503070303051b0105070e010f0201 97
    0x3c44000034822903003d04201549640240202c0380a59074601c07121f219036031420295410380700040d060b0001100890007040072507001540c0c0d003000901c00c0000d60b10302030200b01002c00a030f000b600940d40d213200420a01d040402d502000c0441c0d2030085146103001c0d50050301b0000d940d0006030350381d40d000c00000d04544040040c6040c040e00005001d8607155200407a80d601d1004a83c140650b40583e00b0041c0a41003080a65050b10141405401194101210440381075900300400b02c8011140b1380003c00708a0a0020038002c00c031a66480c0410b02e040041607110359810b90100f80403e180104504548501310242c074150380e13049540d1510380030406d00803032520748084103424580d44001444c0d4001c0b0b000c0701c000e01c00c4907030541c180c1e480b03247e9500000c1c030840c0b10391003044080f07503081100200601d407070401010074a00c51042c124032191188042440c00200390000c5010410009422504103002c0042ea0340c01c446c0310009100c2840c180c0b800514440121030031506000c0000f4810203000d000390 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12739935 1250 12738685 12738701
    0xf0f0204020f0903010c030b09011215020304060207020907110706140c0d08150d0503070f0c0b04090209010914030a02090a020c0303100303031103040309140f0301020c01060905101a0d 81
    0x10425915481d00e082442443d52016000074404e40c40c0c030007840081d901900030b0412055004012015603864041d114030070f0100443d040359030055140400724607881c00e20166020314050311006031240384620520440b0400648007005105004120028a8400240840c252505403500340c003030102d5200d0002c198000c400749030116016080740d0321417441e031096540d8452a000706106c0694541001884081d00c881c1001030080d400070451320011804551b00103654910698411004580d5040071220035080ba80105040710380000e541c401c55a8411000800307009107112001049141c00c0005c4c0e501c4106030300007800380c0035210003d400c0510302d0b030640d61104070f840d09590380c07481d100012650714492404200e01003860300c104580000d540b402581e20566050701c8410b4854103044400202c4c2040352007103030b4450040c2e020040241c0382800600180407081c80080780d442c0c05d02c1c507040c09540008282400780412030302d04012014041104046000c00541e285984421068211024019031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12741185 1250 12739935 12739939
    0x30f020d140307031e1119030207030203030307020a0b06040b011d0604150e04060b030f011205010204030c1707060503060d1b0302030304030f03030506010504140402160c0801020d0b15070f0f02 85
    0x12500710145034000c091005c038148010b601401c0301c40e0052042e075103460034003207911303c03948500d80250108803215020464a80a4011104103d55a41c0083d1440e4400c54010b00140c001c489201e00300903008400c40d4100804076018000c800c10200001e003440c148040003035441203800004850b6403281f00840340a0000d8514541815580c440080c00808803002440c0c002c500d0a04d0014241c0700c21401c0d030b400b41a50f200c02c641e40741d182603680b401d050070101d0143d4103950700300000000901c540b0000700081c0b196200522407860190100d40c2010340790b40c040c1c0c0922008204100185d503410f10200b0542d0350150700d403944075006152904284595800003509440001804024005104e02c01d00f1545d100740c0e0144105e5030f480340111204c1c01944520401c0043c203094022151a044d009004000c003040160b181c0c068058452141649143e403201010b65800180ba101090040c042c01c410144262403958103080d40c025542042d03c01d00902078581d070300d080000c104002120880c03400060b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12742435 1250 12741185 12741187
    0xd150f0b060c010209120102070b0c0705070b160212010603080301050d0807060903020a050d0c02060a11010209090c040512070506040509180a050706090806040b0106030509030d020f03150109030f020d1403 90
    0xd081289001754811803241d441501d1103003030500c001105008503000e4680c0304a500419403560906080e00313801c5001d048170280100c050129010303800b140a0f103400d491b040e5855080200034014040e0620400d1885002c2e80d06003070003400400c0141082740e0448a060320380c2060400d15050030786890251640082106060460407814598000341c894506401a41030394a5400d104d1420364968102c02e5000f5001001400440d4225001e2040614001c41810015150007a08030004034011000c440c0071071907070b0000c1014031003400e0040300c1c190010b03441c1e402040e04904010010b0218012846100c0c400c00d0f045000a52600c0d0030000c0c070380c01022031403c490f6039800629029885011500410002481012000905480026404d40201d03007001d03080c201d607404c18130103c0182c600201440850f03c410070086024500500c001e0041c01e200415058481c03d01c140e10300b507865480351809040007510071b0240b020034002540404600c0e4100d441c0d001c003410310300c1d00030351450008102c0401808 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12743685 1250 12742435 12742447
    0xf030905060a02070b0105090f0708040206070f030c030206090304050f060c0102040f09020d050c03130303050603010b1903060e1216050a061802010305060303030c09010c0203070e07020313050d150f0b06 89
    0x1855402402115105c2e103980301e400c0c0c0c2c803181400f05140045071401c200d0748808000c0790b071841c002e070601500f00d0f0010300710500d08013003a22070408446030044100d00042c5542c0d1402c0525605029090f0031200603c080c51401e803425000a5070050340b0300b20b0b20f100b0000000e135900402801d40c1100d00a00071a825a240c59035581c0b41e1000940000303080d400303920300b4180040c00500c0110107c0b84101003002c5506080c42c1c0d1514118000c050081003e9050366880c84121030719036860000c1040012180e140c501028154034009040d2005c81c85030107499400403a1400311140e40806460084182e90104d00b007030f04590901e01c1c80c01c0381494001c0c00d0103251280c11243c18201e91900703400c8600030303203007813100f41c40311401c1c16901e210031240c120f255101030001c0e00c50b540c481c09070f80c280d1500003000c68041e55111108003803107030310990f01c050240c0c4c0002a2120880030960410b00200001c4a66110502706521920f1107180c8130701c05085c1d170540d9140d200503082c2141c1d01c800c0402c08054500c41c0c48036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12744935 1250 12743685 12743701
    0x80c09061807091d010b0d0209030a0206041401020118030903020111010615200a02010905060a050702040515031203040203070b0a05071407060e0f15160503031015050c0d0f03090506 80
    0x90540222021319026282a900c1c0e0b212502e0f165040f1070540c409107142400e8481340000a421017844198940101007040d0096518040500081c2503034022001904207044c0003e82100c8444007440000c1001c0155840400e410034050380440e0780a09144609810443c5194010031f680d03007040071040300d0000a05030300c0790b00c28982c0c40892107031071400c646190020619a030312544840700078001000d522060000381069000b4090001c05402d14504004007940054192401101c089800e601c035032908050301c0c0307030030030010303e80007407100400745142401d4011a403149840d000c4c0e02640b210020f48200d41920841c2180c4045420500081ca1400d8283c801c50301d4031698814100010403245c901821450100311071843c0840040c03601e00c94102c13000140b509038101402900d011105914124041481403008502c540503100b01518403900704002800c00758984692101000700a0207003c60104000910b108d00746100c0c14030400c500c00240d000c07400307412a80402850b501411003448205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12746185 1250 12744935 12744947
    0x3030c01060b03060406080c030c04020901050d140406050f010e1314030a11070902040f05040504020303070c0305010209041d2a0a060201050a05130c0b0a0903080304080a0e01020601080c09061807 86
    0x713800300320790030301c0441d40d943c228503070b2a0740d46e451090f0305401101003e081850a5401001c41c0c9006040c014142481441d00c00e08881407801d10340400c0340108200810040e051180692048003910030304265410814410001c1030001d201104181c840c0340d9440a010030b0500004485810108482c0c2d1094010f00060228201c2090701c4494416034101043e030761128000e031070a0f1a1203000c44034442d0714000c10800601000707481645c05d40030820200001c60401c3c0c0003100514015000969503800b00c200b07100442d40030352541d0b000b07442030741190401d01740b0110742282012f850402c46c0e1101120f225030808010725100f101c0c1c0d07010841220018200f5010b42107107220381c0c045441044103503100807106000d003240c08002440710010703c070140f103a1941c480c09002d12402a20b8030040140d142d560380c920507030080d181558245008140314100c180c0c0802455040002031000c1d040c5940740c122556a14a01c40c20494410069a400503009480d409940910031126500c0c0754241d080ca2503020f0300e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12747435 1250 12746185 12746191
    0x403140d0801050f060f070c05040c0203040f0e01060e040525090509011403070e0702070302040606091404110d0c03020c030403110306130b01050d060917030a150f030303090203030c01060b03 84
    0x403078000c900015451401d80ca00842d2901d0150140d0700e03004035503960000c00c0e40409800c488880c0d55090100303141d101e078860f0340c00820b2103400641d903a42c28680825484180c030713032282e018030b0302400041c0070040d803203014034684400075580482c050f100c217880004e00e84c442e42040852000709030000007400d070340240010111882910004e000341d880341989505141c0c8010015007650049100b00030140720020055844490b61058404140d1240c0c0043c06891441c0e00002c0000c4913000180b00d40c0d0030311060603007a1801182c1c20008a5641c1001d80c49600a13514602605903464002c94146402901200d440344041c805030f17036445443c1d1030b0168207c00e0300c2c1c20307a034000d01c5140c00241042d5843d044209025410400910143c2e180804001440640060880700c01c2d4031020a1400288488440f00c01100d040c440c1c2903c034501407040c041142e030100b01c00c00c40390405140800c001c0210f02030328026a41c251501003660039450010a207103200c0c1040100d0b6035031800c90002481c440d410301441c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12748685 1250 12747435 12747437
    0xd0c1205040b060a05090103120804020d140a060605060a0c03080601020102071b060f08070c0f14030703121104030f080904021204050109050d030605010e01081801021611090403050703050c030403140d 88
    0x13201c0380c44a003442a404800d0200134814224030110031102806081e50310b0b0700034030041ca25030904840703680c1d0380720320b00790004100415800106081c042102c1c0b40160405050305580722400d040710355000400141c1b1046024041c4040303a4007080c10390340f00b034046480d0075410410b444114031482120000595192040c0d03c000f56080d002500094440c2c1d220030300031005c50303a818850030015201c1440d4030b100c00c0ca007281e28083c9007207003c50007c2e0900c041e080a80c002e4440b420003540701c0d035603403090341d414031a41401424100001d00002e00d40c000c00000e001e801c044000e84448501c40810002d2152004c5114600701c60342c2040104441500140c80e406d20940a888031801c481a066050710701714000c09010850542440314554800d20240383d005c0540c08501410410310b83c1002e0890380910300c1c1203c1002c02120244c01d200f00380000002001c2c00f514595480c1ca405e4500405034040c001d0001d080003400100c491070210104151800f850b0010800326503a0f148050055640c903801c44450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12749935 1250 12748685 12748699
    0x17060a1e1d010e01021c02030c160602030402100503060d06110702030f030a0e04061202010807020a140d08090a050c1504050a0608040605130b0109020708190207081606050d0c1205040b06 82
    0xf103050003040c003c0d1841e84042c0d00d4081d803c0820054950080d40004060f500012002d0000504d0311018410054510340102001a503d00f854018440c5010703001c0c5024040c0301080044c0195070f00c03481c500149164001c00d00040300c0e00385802c918414030644c600a945445540c0f890000300074040000c00c81035100c0c1d2545528103900c203050100380c481c24460f89540d17200b081040c0e0302550040ba0103940c0f09100340306440341c6d041c0c680d60314102e02040d2541164540c2c000c41111816039004019650040340400c000d003c900403a41c2e40c260b44140741340304540105040303222540303001e020300203030703000b40c0002010b030780c1080c0d150b08006180f044210b03400c0d02c0b010308060103e049045204041c1e03800a400a0070403400382e0800f580200030b0360103c0b0701214014400c01121542d42c00306072014002c90a568003a01000e454403406501e02900f0003c03a0240e0b80304910304000841d000300448400d034401040c007080007555418281c4800d0110740d28120824202001c000400900412442c03040e50120340071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12751185 1250 12749935 12749951
    0x606030f08030f0f010302010c030e0303070c0311010927180605010806071b0309091508030c01050f06120606010e0607080310030203010c090f030b0c0408070801050a0617060a1e1d01 80
    0x40201910280700190105000c402c09c600071a2080c8045041a0300241c2260324040d5569511030b00780465034000c0d21900c104043c05810707036a2005501000786601d0715541c01d8003a0b0003014104110307141d401d21829555940c000360501459040e02444103412400030001ca6945101c02c07500c0381d504845a000113100400200320480c0907040081081f6010342d9181d040c507040c10070a01c0100b9071101c01040016400e02c2c0058408030800003020003040600011445040603c01240321400242c01e65110740c40303510004540d40c07000591030303a00110034684045125500004180035214120b405851220300104000c0110039081d40039049034400d900821440204902c2280e01c7c07072680c080c044211184100810101e0342e840307410b5401030035481c46203140541e54004180740c0f0302250300c0405181d45500802103100303182d100b03690092948049201c0c4201c01100b200e511080000c001e1207003156900185140350104051520380780500343c80c20400881c0c00b20003a0f03d040c081c04120940d0750308108c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12752435 1250 12751185 12751201
    0x3090606041503050a030e01030204120606030b0a18080a052104050c01050f091302040906030302100f0b010503010e07120507020c1306050102070b0a12050403080115080c090d0606030f08030f 84
    0xb68011a034004002d4403c2d00d071503680455005200b6409607042507028403010844210b00036035010194401e8400003049880e51921110a01009004e030610b24a0300000116130443d500b40b0707840343c5502054440d0740d03410801d002d40751401103000003000e2510909040c2c034502104c400701c2c0e002e180141c00301c519008414004547d14854103201016090040c0b00c12419810310384000c1d080000305410241c2042d0f203c0045004850040d401a40141e205486410b004159441040b030080c600b00c03010301c81002000000713003ca10040c810102380504500c0001c0da40bd104480c0c40240c0b0000035800d0060303083c0f58030300941d203503055080203104000e448a81c1c00010903610a0000310340040c0c01401d40513203440e0a95400d80c01202e4007805001da0800340522041300c2c2e1103118403c61082d10340791a507505010007803900c02c0000660006018140c424060b805407400c042e6891400300325030308000f1214600e0541d001d400664402012080b12402e40c0c01000350748e002441c450402848081483c0e564150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12753685 1250 12752435 12752471
    0x5160b07170412110309060a170c090604050906010e10020106060f0509030c06030c0c030d091406040b040b0c04090f05090c09011212050412060b03060603161202040605060309060604 80
    0x2e4028030001d50050a101c029004d680032140d10701c060130941e410601c1c00c038085940c40d8071441c40302d000a1104100000c031040014401c0b5003007a403000645017010030b00e1340480c180b442a4050b41c2c3c850592800040c14981c8544500e1107031020191803a51440b0789803002a018041d14000c01c40482c10100541c01000e2140d0240ca2201c2070003801019000710407414886241e01c042d00c04003000c4e408024140d001c40082006142400082d00005862009400c04071000c00b2001040c0c6115046a0140070108151245054000380c100401184ca9264400c40c02071510640d030219008608042c5601c141400e543d00c0a4812200700c4243e6031041d005404210f180d4409004040d60703c20494041d0011955041b601001d000d55424083d25040e1543c81411140990410480f002515040001003a003014803040c1d41000043e13001f480354503074002e820380c640162170040600c650f11400082e01555100c0d04158002c241c05400d1030b41e42d08250180c3ca880b042c003140d43ca4000d600380105101e42c0c02c42c040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12754935 1250 12753685 12753691
    0x10207050607150207030e0306070c051507050a0e0301020904060e060a09020c070308070201051213030f05040b09041a150403050105060105070206030601050c0c1f140301050105040e040305160b0717 87
    0xf02049a0b9010901ca01e0003c0d040240141c0402c280101d10512503102008500c5c0207400c03a46a9850a02c1c407481c00c03174501546001102e40c1d51444d8014800b4164014046d51800c5406003480e088050038140070070700a02440100d030b90300a080010014920f0f10300301403240210002d58101380c00356241e00c41c0030141e01c2000e261150507032001d041003000c9000c0c0310142c80b456105140103450000400d071b894071800c0042c2c03070076580c16403098151002c0681140319544036644a0a000d800c00c0d10b041030001e0a401400b01641c00f56468200c1d040c04d980b5150300421b04020018800407840d51008a0b0346565000b070f001c00c94056113040301084240d8024425508950750060500349950f07169030044500c1e80111742c20342c06c00d1040b503510300e00a40e28101100d01c0c1907002040441b42000c280d000074a5818403c40100c04880100018001640d024040fa0162a854604602103445501c0c044807248200340400d80340104046046003006402082240507644903907942c07840c0e003501c50041440a60607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12756185 1250 12754935 12754943
    0xc170c03011d0c0d050a0b0a060e010e0106080601020c0306070f0306031a040201020d140301050d0f0506070315050405010b0406080c0408060103080409060806060904020907090803070501020a031803080408090a08010c03050105010207050607 105
    0x2040300380c2d0016061f0220341c0da01180610000ca89580d68107188900c6500a0308010b0f00d0248610050000c00c0d4007081e60365011409100401c0100c40c1d400110b5100e10000d0100401c00c9292514081d1550194010074001e41e0b22541e00034801c0200f102c444210001034038100c3c014000c2080c1a007096201d104d00100c403252802c58a0b1850b440c2c1001c000504485000440b60213140300d26101c0401d000b802414460b541e01d07280841d424055401e0100740780d6184c6c00c002d210303d00d00701c010321110394501c096a042d50717424141000d8646070360040f000e00d402070394080406882400300200c104061031000d003007115148202030085548501103d500ea030b8040b102c458101c2c807110300107009407401c03090280c2c20810074207002d2031884c0c80c0c00015040d81d1115409544980d00061840010f66140c0b0464a0f0344041590442e0608000c0d500144450310186c8041c4c100307200818801c109590b58581da500500c07d0600810140840c4100036010308800d201e03450260007611800552070400c1c0046644417a80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12757435 1250 12756185 12756193
    0x20d020601090f0e0f0109020405160e090c1303030e010201060b0301230105040503030406050c0613020907110c060703020609060123150904110403050c0103090c170c03011d0c0d05 79
    0x202490074008020f81e10b400c0c0402600ca2001d4513500a00b800120343c14000480046184030325801400155600a002000107800105044400c1503110111061410007116100903036202c0012801c024060402e031100a0200c80e03100100309a00031000c142c03600000c8c1c00a2101580e00d8011007840e001c2407041c26034002d860034105072700c41411503603001c0358001414120704080e11400403074916042600001b0100e039000801e144010001c029040d40221501000300c031048099000c80c1440e500540740c5003e21400c2d075442102500c0c140401d0280780706c0030300019110780980c2402942c480d0b0070796030980c0500070308002141000c0280d4000d05a00701c00d852040071404442d0910410380d45800d540034641809112040160b562030045030803403240c1d1010540c59902b10f040c05410800e22581c0785040c58a022940c10008102044520840d6040d44650181410081d002c9042900000c0208ea0552030300c0e6192400c0000001156260000c010131900c2c0f40304042c0500c0070040380040040c1050384 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12758685 1250 12757435 12757439
    0x20d020d150c02010b01020106050d0812150301020a081602070b03061002100504081c0c080a0b0d0506090615010203030f1b0d0e0105012d03020906030307140d0807020d020601 77
    0x2004448048035612071205480106140650a0110348881d00e4050041c1d441d28005801c66a09002d0040a40310803510a10503802030383d100141c501c202c40c001040303407212a0020b0300c203200340480e441040c400503000b9903888031840c1f0700034810303002121454822a920500845d03501d100054240543e0000c844052544c0c807003034204900081030007803010441c0b1a503007002c00504003a00496024510401c1c105403116884c810343c984032185030703c0302c200b02480c2803072a0f0862903102c0e9810ba00609411000654820000c0101e10760030382c51500600f4512804d402d1203403544002418078415001e0940310010f0303000030401244c581c8401d80c0c1140c00a02407901042420484040056190700c4000c03015150034806980242520401c601e443c80c039075940d1004010401c80011903014a42500103042a0f288c000c014011107000c0e2404083d0051010800041940d1420000c59041c56007040080001582064400390394103603c2001d1400201c0d000702040ea81782c000281510790710711036000b4041700d80c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12759935 1250 12758685 12758689
    0xc02060a050c03092805010e0a030215070203040902070c030206030403090906060f0c0204050601091a0309070603050103080d0903050d0e070f1205060114130603031205070e0a030b0411060c03030415050103020d02 93
    0x301044003952040442c1245c0400091000d114541100102d00082e29000c661401e01a0401514080c2d10240307000314010043e15541c00710490b815601da4080068440b011403c045104420030b800c029001280041800103041d040501881101c852541c01c3c850385403100d6040310b102058070a100042520700c14510700602c4e281c1c00c81d0340c1c00704061621441050380c9104403500302c05503555074052610000203020090109200d0b08001d0300302801c0910007545135580e41c003154032841c4140400b40d46c1d0340640b002090320501c1100d801e9600d113002400140703182e628003521945d05118501c0c03805403a04001950040c01341c0c0480e0005e402c02d01600700c1e07070710700400301c10b506492404a9034410020b248003112007000340b0500c005580280d0710301034152040300b80141160710250645090164503500c20b015555030003444000d0320361149000c9400d8641d8070b407040d40c444072070700f03a42d41c41080801c0402801d0300010155203c1c9003d828115600c980e02c40c000800c4403020b002c00b94000b02088440000340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12761185 1250 12759935 12759973
    0x31605130306020d0b030703140105061801060309110907020705030c030d080606070f060f06030501140420030f01020c01090215040302030c1e090703060501020c031606030905030d0c02060a050c0309 87
    0x107060304da00202c0c100c600303400028181070075504101c2e108040802c1648607000309100345640560159040050400b43c41c10710207007210140f0802c1c0c10103032548505010400003401c01d08422070301500c0c02249040070f00029480d9001170003514041e00c1154119001483d0c00600d10828040e6500c03064401d459800070722140d54405002078502c41c051007085800280d40b0703c2200100c000e1203600103032880c2140740460945401105c5802d0400624080c00b01040c6008007030600700a182081e911960b40c040c000c00d007070408081b41d460341c075440410083ea886206401942181e8401c8451340c030000801e5800354428019800040c3d00b40d030003e098a0f110b4106086844d03072249541d00c5c0c032401400c4100c0050382d10300b41295907800107501c2d500100000d503010880d500480c032084000e00701443c1d07104e07204081c9900c0340c4102c00030141c4804024003801024421280c411420035010304c0040b24007140039684503001c1d602c11503024030b8034000400e205030308404d07a4020320b0100058001044809246014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12762435 1250 12761185 12761197
    0x6040302060a090e070c0b070305070212090a0b0d06030303060f030510050403030b0405190501050301020a081303050405090a0203060f040902010516060f0e0a050d0201020301032103020d020d0203160513030602 92
    0x90140f000c0c030209802000303002c050b228070900e50b034907400340c40d2a20708001e00480c06003249092600301420f0040194000c201c9182412109403031a4440180b6800103000d209290700c070b241350560008055804102c60b410103400d59000341c0381805015611440030461407030368407020700190030aa0000a400000d034020a800900901c1c0205000d102131000030103d58042d655284c011484141c2c0c0a546465405801c1c0180f404038001c508042c0502ca0190141100030158081c1c0c01c0001e90301c0007054020801d81d00a0034001d00b180e09a80b410106400082d401512060b1145580c000402c1d5140b8150154191309030b0f040c0d4810b070a002c5410440118a00e00781c004a6095803200e9100e03012090710311902d107402c405c034001008921800d0900601b003a40100e00c150440e40100014404603001580305800104074400c1e910300721403464801c4000f4000c48800142c028000035141e00200c080380c01660040e084080c3c0c01e46400010314080d80d04c1d12601a00c50701c803441c640b404102040300355026080e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12763685 1250 12762435 12762437
    0x9010f060302030403021c020a0506010f060c0204090c08190b0907030206070803190f02090405010b07050607050d0e06010f060e01020f06010909020f180f0c03040b04080912070303020f1b06040302060a 88
    0x881d041c41c0c10781f03010018000b041c07000140e000c900b8041c284002080f215005041010340700c04c0c60ba041840050070000e0402d00030380a16160a940c0003013081e801d103a50000e1001e082604d070586003150b045800350540250982d010154407011994410020807034008480d4003c10180c40c00519903900b410541009201014214820801c4445104180233080200d42c0326040140d44a1010040104482c010307007040034280014016840054800110305411104d103013059500d800811340420041c0400c2d48800700340f40108000000c3c2c81e80101610b0707090f60341513101c0141001c1820012a6213014800c000f42490348400c00400c00e134546070380f0034076081f4000307001c0010185259000c00d00c8040055504444801450700700b04100d0a044106a0080410001945142089d031034440c01c0d00303800341000e44054000207a100e01d5503200303000340d506107241d901510840340d0703a41000b035290101107141134144d01403417000d0303203088842d21158090341380000c03c0141018150303020b0202ca0741161003044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12764935 1250 12763685 12763693
    0xf012402010e060c040f09110708030c07060614040e0d08010e07020a0515060306070f09030201050f07051005150102010e250e090106060e10200313091a09010f06030203040302 77
    0x2c4a144810301100b4400c0c1c00440b6001c0d41c0d149000301032184c062285d0f0003c0c82c424680b8004c815040301c01e0080b03ca10310f402141c07070790f182e454581c606030140c491610002c1082e8640130b030000c0c219214950b8641c80d65000c4408000d0003400010003610f810084043c500050a89030042c07001403144254079401025904c121401401550340d118903003800038075060700784905042048400d150800c081640104185040b400c1c0280600020b0a464400e020080c10b2180c0030501100204400c41550070407500041101e10441c524448079005210580e5115451000d26010120650050050489a504980041c00f4041c225200d4024054851140045203440c92138001596a00d4003540d174040e00303e0f0000020b05901d044806400c0c696650107040c0200404481c0380071a6801c6042880020100c648055040200501450451090704154004c5401c007110120310420140c0c0080c1e0002c2c03181700326001d141500d0f000c011496100b44515102c0e0151841c0038404103129401840d04644640100c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12766185 1250 12764935 12764951
    0x403020304080f010e01060b0909070509041506030b090a02130909080c060f1518060402030a060506030c0912010203060303070f030e09040b0415051b0a0203070206030a02030405060f01240201 84
    0x11800d03c60301001c00d40443e919a8000b41c401c0703500b8414407000306520240c0600c2c2c00b0504011450080c0000c1051060040100d520481512039820482040d0468112051016150f413000f4005011039010a030050f00c809002030070701c02c0e4034401c071400c0e212800840f8001c3c43c030740612800078192480d812122a4002e0144074882502003102ca80100c035050b5001101e4500b94201041c945414444103100d90045800155104150001d02d030f00702c4800e58002da540d07520044036070040d0210f41e10103500220b0000800c440c161074030014004d07041044541810343c021000e5910b090740010b84020342d00d60806c00904002405421a42c89000d120f42031142c01e412600c0001006a03a040381c007520210a00010802000482442000c00396281c2c8410003e03401c1130840e00b190203e41c540e4039240c080700040e01c480e1290082060b1014644e000308096503034038040200c0c60294106603400c17946441820041201c1c031101d000300c0790590312503100c4030702d40c10359204401607110a504c501c0003d40d560740d40b40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12767435 1250 12766185 12766199
    0x105010e100320030402030f150402090403020f07080c01141810090909060203070f02030307020a290a02070215040b0306010e120d02060402030c120a0b180a0311070603050105090a050403020304 85
    0x81c851071425008401c4d450b4589801418140121071031003903629001a40e20300c02a03000d070412540c0050301912560102d549525042c2d142a40095441105200e28480003a00000c00210b02c40b80c24070a0f0389200001c03c2c08189043e613401110307018801d40520300100c1c1d0395401c1c02d10480341c0c03071720305803904061440d40e82403c181140c20a200c1900c0c056000020001100d421400c05070010360244025031951400c490020b4a503c44d11100418005420301903060038040c0640c03040e00c00428a0403503c16041400c0803600a5100781d804900444207403a0306413400c6503e905030380c100ea5012401d94510b07594030780119001d0042c080304a501582c802070300e05489104201d50507611000e03400409690405004040c90010710070b034990321078001800300540c8010042034000381c1603071006100205459100c500c0008003440d0692071070901c20082c0e030b07405240d8409401c440b00211a4103881000f80c9850303088064a10902841d60003821a0001c80c0410500ba400994481c1c00392060f0b030300303254072290 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12768685 1250 12767435 12767471
    0x30106030206040b0d0b12210c01020a0305010f1212030e03040f0801090201030f0506060a0809010615080412050a0e010c03020a05030f070c05040605010e120106120605010801140105010e1003 84
    0xc44c1c01d82c2000708950b40c00c0c00305442106644c607800c44120b51100c10400344580da528000080c0c80058100124070800c200c4580b080e16000ea510100035511000c3d640703c01402041c09200c0c0544070380c0d00803000560f00c89040e461b10091900411000c0a040c4000402c0d0090b048103a0b000420303100400c8005000c135a101c03901005003103c40c0000c05d054155000040c2902c0228403a0a589441c0030280040359a80034121085010107003000d00c503660300c40e01c0b004d00424940d440490b05420072841c280c00540c1c0318420a00c1588034184003101d4010b402d10440341c501401c1c0002c3c3c0407609c00080c401180d8010b0110300d010b544644112400d4003501da0318103082d40c10070a10034210b140007044003c10461200050f0026100c00c0c0c03410000146490700080c5095080c0c2c2e10517000d03610907004406944420340200001d02650030305d05001d61a9450050f00a040c24803a0704500d51030b0001250307100342d0b5150010304031a01650b4000316120040b081006062088907100145540d440100e04501d03008a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12769791 1106 12768685 12768689
    0x40b0a1202010302070b010f06020f0a0309050108060d050706031b03050408030a050c0c010606050307091502070e0709050a03050706090506030c0d09080f030a0c030c0905010804060b03010603020604 87
    0xc00143c009101c4c280300a485103010100120701d441a10300342108840082d402c031000d043c40040d008c0c0c5c403000103c400500164040c2001c00c4558031a082241d0003c000901907140740e81e5075900e06190200907400000440d4a50410f8800d50b08010b000d10b00514807400d06104901e4555030392201c80c0f0000782030721039256030307500414103100c040403d9400c03162042000b00049619260007502c980c004070351010002d40703c0380021404502c1070700c5076042510705400928009081c00840140d4940c001c0010007040f44103100003d1641e10301c06020021405940a0620a424144000c1503001c468016034003518040044c8014080c2100071070303003405408403000a0a0183d4034154516208200d030356120345001105100203007002d84d00c640e0380022581c0b42005840c0c1110800c0d10f450015109290106c1c0c0380b01d0024001c18625003004151640c001c0000440d107880c0e07400207045411503 = true := by decide +kernel

theorem cover : BRFrame.Cov 12589935 12769791 := by
  have h0 := BRFrame.cov_init 12589935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12589935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12589935 ≤ n) (h2 : n < 12769791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
