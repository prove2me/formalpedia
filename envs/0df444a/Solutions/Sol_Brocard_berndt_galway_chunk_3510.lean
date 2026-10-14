-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:31.154722+00:00
-- url     : https://prove2.me/submissions/2d2caae5-53a3-4e83-8ffa-7459a63022be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 631115107 ≤ n < 631294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 631116357 1250 631115107 631115113
    0x8101a1e1c0609020f03070c030e12010504021002011b030e150c0a08090c0f090405010204050a031506080c131d06070e0a0e0105010e010f09030f03090801050a0902130b190e09 77
    0x14071580f000c0101d0160b60702c02c00380400f0500010b103015006451030392829000341440f512105804000404d92079503a2440d04043c4d44900c280310841c104481a0f41024000d40002d21650fa9602c08600c00d120041168800301902c075800c980f1001c00c00e025101800c81e4030000903e040c9444c124107207442c0e1001c00a8400503600400285000c02c5c085008111503000a002030b040ca100c80d420011501405807041e54107545c00c0000082c82d55841010030021403084410f10070b4942441d0b080002c0b0344540d401002240c0145006031032543d02c0915100701038042c400300103500c8021443d40002d05002000000151044006110700c1079080b80d04c11045400464401920640390080e012109000f0700c1070a000c039058003c4a4003641c000c0c41d00c0c2a1041562401450a5640e41c0740c000b0070003603a030002e40114103114820b020b80c3e04280140b07a44007510007800d1125054590105084990503000e1401d415514442c107941d0750341303101008004149000e60200910380301c01c80c0c1e040c07003601a82c844100f44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 631117607 1250 631116357 631116359
    0x40b0f18030a15090602160506010e100312050d140a15060212070624030303050411030c0310110c0303010f141c0f03030e03130608101a1e1c06 63
    0x11a0000b03080354041c2e84000301000c0f16083e0ba04581c00b52240391012a44650280210301d08400c5210304400054004d60040404d94500b6682421025001d080c140c09081c3c0c45a041c000f04001071156005426680b900720b179504090107030b45008009040f12400109100c0003840b90302c042a40040050324000000040c6442d41e130384003a69110036201034404191400d00c102000b01e4040e0b80300542d0311007144030540c2c203c500d110007420f2005041e0000c0340840e64603024441884240700c240c50541074154001c010072411080005d41d02c070340420200124644400c4542e0300b02055005650360098500300f02d1382c681d40c40743c40070b0020200038005d01007803840c460b171080782500e00807540c4840e030060440150150b505d2a201d80000d2940120180c080c503484d0021251102c1d81080108030709180340c211a4032036414840014010030f00544016149003440905201074070200341604480075858040c607540d03084000b00c02d5141d802c0c2411102c40448041145a200380c00b5400d025204c403501ca004100fa1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 631118857 1250 631117607 631117609
    0x711060a02070507050f120a0602120a0b0d1b08240c0307091203180909050c01053c0703021b031c080403090b0319050105040c23040b0f18 61
    0x82c0241c4201038004d600c550020000c90825a00100d0179050140c444a4604c2c1030b201c0319850b081041c03400301c40c5117a0000740c03010b2000c030616116420501042e018003844d0070030300020b03000d100e0031310000e0300da031120301c0d0711401104800300f9910042c00c283c01a2800d00c00e04040d0340081101e01008203040b6007158000410001c08502280c3c410b2031a178650660386402c0104101c90b09101c3c6904905000c035000d540d40d0b4914441c143d80d002414442400300d4680e60302e00c2e059007403d411f001103606000301401032036402054482000846100603040d08203207805000300000102400104841d0700b2000907000c0c090550202d202216202c00c0ba442d51502d801c42070034150340f031940165401c90b80400501d0080100d110740501504a070007450041012919100d00040d59402942c07080304000009004084500407070041c0c40c014030045604101c1c202c00c802d0040c000b4400001c28109800020440c80c0c0002e01c400282d401500410460300d480e058242e650002d2503109100554000c0c0d8186090001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 631120107 1250 631118857 631118861
    0x1e090302120316050309120d05190b0f040b0310020c010b0a0e010806180c0a230f090627070801061b0f080c030f1204030e09090c090604020708030711060a 68
    0x3c06407038004038045207100100300e5264102034005c0c4001d01600201c42080c054210140841660104000480d4107124000d903c02c400407200d65010740b820926652080c9d034074803d082c11200c10944e00440c42a00030b00c000b130b0611081c2c6684080061012030b00000e90a415030050759400b0382641e0440c07006490301c07200d8800c0b010034450001558010070020740368503006010070303251001a100f03c40e0558500c00025100c01d0403a04400090104080070000b1030300c0c1042c400070381941c16139840210741c01c0b9401060075030000402103801100700841c40b5242c1c1205460700c10310b1150500032150070b03003001403005105034020301c15680041c250301303280c1d0b05284a0800310950240e00444021481d68169644041504403c44884003070000307104450110540300700405203400001c100c83d01601e82072401504002d80044201e01a42011003081100c038000603900d02d00410444000344039660b000002001f17445500c0c8003c029220210a004c010ba801c40400880d03807081009070b6400341c0d01e03107400d242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 631121357 1250 631120107 631120111
    0xb03030313020d060b03060f071e1b0314030705090906061213020415080703050706020115090207021c0f03120b03070512070806010e091209010e0f041e0903021203 72
    0x4840d41c101c041c9100501c1c180d0950590f10b0310640d80460710b8140c101c0080d0030941d0464903010005050020482415803100c442c0b003004000b945d140e112240c2c1880000d040d280308500c44d4101e840a0141c14013414001c03072030301d0074203416500345d01d43d079140030203009005820800c90ba90107000040080780440ca80341c000e442c1048080d00c2a0303100340c2d07980d0458625102040c1c8069030800c0c2e44141c08115061080314080150100e18000c010f105e141d8903000c1e280c40f50350741c042c40445e490000e8010700160486400e804942d201e400140c0c44840b81e00000e500c07210502082602c1d0b880c44440c032010810107410901090b802520b0304403c0304000001c05090b00e001020496040c2c00100d000c0c007591820003908449080044203d51000761280803c2d49010130a801105070051664200300300807408009405034407026106a90400340c0304800a000501c04007943c030f10918800132400c0840e1a203500c21501c9081d00e002c9621090000d800c680004d1000c0003081e001406110010f68036803007e041164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 631122607 1250 631121357 631121371
    0x2a1e050f0d02041508030c01091b0e0705130503160e070e010509210105041b0609180209010e03151f0b040e0712150f060f12020a02010f1406040b030303 67
    0x1070480380710b07400c020003041000441280e82c0d030048408961a0010009002d1345003020000155112242c20290000c410680040034400350341c440601804a0021001c0e4002805080c801d8451102c0000070404649541089401d0b00c04c84480d001012269544201100c0390301580032429191024200c44030614012258080b0340b0800108155080c243d00d8038102400c5119140c04400c3c4c5d0b842c5d2242510400e8806683c090701250007080c034090940301e042d0081c6440d041008001c1c0c40c00b2000140c14010020041d120f84d80030500c0c0da1164014403074080c01c880010242c3c0e020607103410022090490a682d962aa1841c4840f0000b542459203484025a8082006103040c903203040c040b0222a04000d12034010044001020040c500e09405091544100b0005a0a001703003419048003c06840c1d80c048410001d00001820300290004003680b0003c3c640000540c2c0c1e0b841c40d0000f030340501030b62806031469074076003a801034221200010060140398200c4d400c1c8008005070b000c055483c0000d403403075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 631123857 1250 631122607 631122619
    0x1002010b1e030c0618040606020601080a11040914150603010b0a050907050f18040b010816031a19080d020c010f0309020a0b0408030c1c09032a1e050f 66
    0x201c103034070380195510301e04008014201e8418001c0b84010070b5072a0040c480745109840c108620900b5440c05014800c0a088544000c04d115890000b0307a903a40c05011a0180640c5619541142c0303d07100ca8120790b020b0b5400c400a440c0107407100c07010a58030480000700181f00d2080310045034461406000f00505c244000307004c00440d508140c10041d071060301408450038007104004480301000c2e00fa028100405174040c0148407100b1f85030038407082c0e0381040d200c141042001c9081100c24000240c00c2c540c140c00a24001515040b60701c1c140d0750300c1c030502030076540c0044041c0744035000c80025890070003076070902c2081e5072203d0300c151016a596100d502156002c6800c050603124590711035408049500d00003820005069500c5844140f15800ba4101c0c2e0843d800010340d00004101c1040704103980d245c04044000c059130440d800070545004c2e40402007c2c4015801213401c515054801c99003058090100c0300001176680d017880982074080200d940610000240004183c9018156004003460103824 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 631125107 1250 631123857 631123879
    0x3070f1e030509030c0601120326010306230a1d06040506012106020a0c0b1e01090906110c0c10050406170903120a050a200a0f02101a1002010b 63
    0x2078000e80300081c2000081d110600100001001c1044080c0c000d055030034140401d0702803420010b00f0946d00c000d1082140030343d14103480341c1d510082062411660403443c00903618a801c1c00302e60505088509a514941010741400205041030f80490700b1900010540103000c002213060648629044402410540040d8010000002100740c0c00c1d607003007898208450a14410340c1c0e08401c0760017405a403000103980204100c00c00c20340c01c108540012005d81c889a180340182c158440c04481402562083c617201c43c2c01400b005443c2e0003200208103400d017025180c0b0303603071110b9035a20712004041500c41d400c4007441d07058060140c1c1c1280c06680780c0d0360740d62000140c60b980f00a6581c40180c0700104900c02005488140d81007140c09502030341c61440701043c0c60800309404000e071b80e00b4600e4104441c1c032400c1c900001d04e02e00011185c1b00189810f050034040c440160503400c0c1601c00d003c5500d444c0c144042d41c1080c41c07801103007544843d42203514000001c5659422801c079a80d0450a580006103c12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 631126357 1250 631125107 631125167
    0x109180506070f090e010902041706040c0b160b191410140d05010c02070911040602031c0612030c030813030c0b041b1e090506090c0d090b010b03070f 66
    0x60f0721a483c5a2400c2420440c0e950f00954011554241c1c8000b40a550125003449080b510140d00981003602100812460500e511103c160390002d2160050710030300011800c03100c0325120f4030b1380302c0136820401c100c80915010010042c154501c1540110340d5242007403401300c070140c14603100d006000300505403a0742400d01078510507044c54110501d51000e86481000b0016009000761380d01c90381d181e40a0f0002501d008104e50684101c1c40646101150503c8203010040d0700000380c42c00c6245d100402d02800d4107411980b80107015580140c1d41458016808900780345d003064280f104203200340e503821955030f07030031038416401e0707000303100013400074928030341c2e24011a111103112a0054080c14205000725850030440100100ca0b52080100e8844210603140c1d5256011400004200c7c0d048180480d140c04000a03460600040c0740c18844900880d402904460b107074040044c041e48090700c500c1d1561280c1740301400d03400480b010000900e002c442417004500c20700a400d80d05400c0c081341e98402040c45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 631127607 1250 631126357 631126367
    0x30c1803030706020f0901090e012d0b0c06040b0f01030c050906030f0d09050f030d050f0c010b04060605030103020f0d11060a0e04111b07060e0f0316030b010918050607 74
    0x10806962500c414069400032841070b20040c04916501031a107959021094005003d110032944103041c500d0b000c1e401003280d660b681202d594000d1040151408010030b00d40100c0711915960400c680c4402c011420107502c1000241e40c2d07000e28014480840070743e5078103030707800c441640c2400000c2c40d00008040801c100d08115550503080040207050392102c056054000f071600c412084614005603141d4420051400c1920a41031001400e401030300c100d5040074000340c09071007141c1c04601224400112082c06020a501030380c10858000c000784107455903400024441d4100780000c0c0e105000400d00d8180a00e05101500481039000c0c220182c29840b9500304007440c0c0103030005c08180241030351851010342d01d52159074298510003480035202e0301d05c41a0380b44560040b9001200540c80f44405010a5400c060000521034003280d20401000d140400b090511000480d41c8450450040d400300401c41e105607858113031140e80c0320420881c07030254100705101000550280241d0044030209901c0381c460 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 631128857 1250 631127607 631127647
    0x9110103111605072c06190e010305030405011407050606040b0105040b0c010f050c040e06090402040204080105150f010504030b060402030402040b0310020903071703120907080f010917030c 83
    0x5140440e0070840300b4001103210b40c1c406201101c2c0c582012406110740d4400000416141c3c2c4503080d000398400c581c1e021107004003400741c1000d01c41c3d03d5101007125450003604940003d01003042801590396500e01e07100c0d03038a40140c041c85001c96500b003040d0110004060507030302c5540d00040141002d0311900180401000d01f82401e60410400708004559440c1040080150504080001844000c000325035800c480000d400303032089500800041240504490385260044422198150a80c40c4c3d4400240203100365407100380705509140801019003500c40104810507030544894240e0901c100044a540c451400000c2c52080300c00e0205d041418a6406180c2c810f01c0034000003400e1200900080c03030101119911341c1c030135400040300c45080c00d050040200070140380e1898603502c01040e030fa69869000d50840d1220460500c8005030011108012040051000340c1c20790320f49240c20b0104078042c0c144000b00b61886001200c0c0601d030107104d90101d91040c9985811142407120080011034001c0c8a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 631130107 1250 631128857 631128881
    0x228060f02090a06050403020a1d01140414040303090c0501030e07140d06181703040305030619031704060206010b1206060c0705032e09020319030c050604050a1509110103 75
    0x10a2003164520346408020501800e91380e140d4039202e03460740c8100320b03258100d500b01c05142c400100e00000840e40c184400d9055034901e03032014a01d18160341c0802d00070600410034010402508041c4002e06170168043c40031907004200290442d503c807801034050341c0728041d1292503680a03e1040225000d00c061080c07c1e500014542c0341c01c24480e480c0c4000351004000c40304045d044c0f8200d0a0201701603000c501c0c0030080044003080c1140750544010b0090302008040700c0c0201d4102c40118150050740d4000c902440c2e210190f005160b04211846260360424000c90300980306440c00400d6020f040015199144c1340000b04d010103558907000d0004070b03009000054810301c1103041c0401c65640501c42200f054240080d540c0440f003030500080f0500150301522644940741000300400b50320045404011094a600b000368943d03d2440d007281c5000c49500040c00900400091200300000880c01d100f5a9010f01000c0c610fa18503640c0d0780301221000c0c0303401031200740d5944840310254002c0e040350501c821 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 631131357 1250 631130107 631130111
    0x4060e0919090c0503030304030f0f1b060b060c01060b0c0f0a1127090c0a120302070e130f08072609040f021603030603020310061a0c03040314060103030228060f 71
    0x81e44d80040b0b855500b0646040300443d19140d1b001d00c07540d40c4081160414051480c0c600f0304003c1c85001550b149c6210003001d00207548070b4941f0302c5036448103c202c65007848020300801900355945811052038002c1030b0520404d0054010f001c506860000307051388165040240580800d0303d0204010710b14070804030080304802c1202c0a11802d0611071450303807094140c04003a15800000e8400c1103002441034204580c45a5100e000c4c20101758000391500a0b5141150101460b80b02c030b0391500c6d00794944d040300615280b421011a000c03c2003640281c0b4000340320354660040c00d07034013056080090301d4019803480502800e2000f42968a065049041c1503024608014580703900556040c1c2242500b80080d80403e44403c410003c504040201d000c1030800c034070080200c60300700b5554442c0490191100002e401011075058060a030900c1200c0095074840900601d0b001c150324000e03100c004c24070040e0058096600343c0d0840c0c1005a000045420085034021032401c5199200402000704c8920340c0c08190b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 631132607 1250 631131357 631131359
    0x1211060f070309022806050c030313081b03042120010516050c09090102040609060e0a0503030a09080d140a1b050f0a1e0203030702010c050a080f04060e0919090c 71
    0x2881710306100601e40e0a0b4030b44044261501602c080c0640b045a00c50410805c0400c00d48060480200c1525040710001080304508400c07800d00c625603018648815200c44207000003040d84800010007401190960003120b03a810b203d002c44000182d101000c098800d15000030305c0e403c0300c0001000340881002c141022802c124001020034054800d18a0840e4107a200e041400d440c2d00e42045000d0340100014025440c140c01c002009052035140d00c5017000740f10700c20024107001d554031082a409481c0103000c40b40c482e2200c0d000108085694803030000d83e4042e801d86069110310402c0140b0804d10180ca080385825000706003143d01c00354800001158000c400341400000c0c07014040007945820306802018903801c0b43c2410702c0400600b6403908039002d000501100145c03004800d8600060702402d060000d050f2900308641409030300369004200c041c1c001000e280f1004820042c1069607010380d50b11411641e040d05015002c1000d881c0701105824480c01c9001810444d041210030074898200800e1032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 631133857 1250 631132607 631132609
    0x9150e1609180e0606042f0d0c08010302011e02030f030603010f0606050a18080a0803041b0b0d061512050c090405090105090f0303010f060f1b050a1211060f07030902 73
    0x800d580412484030341d03444a003643c1414408001d4550040401c13581001413125901036146e0f10fa4070250850220000c2442d01529080c169055814071441aa414011803e25103402040384009000403404900410781420b0024042d64040c281d400d40398008501c1d1003600c100444058200802966066403610118101c660103409071400404007500c42c2500e8040071076000d00483c580b64209041c0d2402d203031341040541d400140b01e41c1d0142d00981007a0741c1e612603091031445408007503440c07004408507080005490a080004220001648404001043c0c942c41044600009508041e0018128216a0f0b2546002d648640c1c2c00c0010000301c0c0b85042e40c2580440d0070b6880031900b600c230a03503450f03040000c6420f041c4030083e502204880a50301d1503040c2945203204026034059101040340c0f0080c00350f0301c24003c85558a036884019045001141d02d40f0341250740309400700301140c110860420740b064150244451804811006000d02482e58a4601445071444001c002c0410141c8800554001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 631135107 1250 631133857 631133879
    0x141504091802040609141807030b040302160608090a1205210609010e071d010219060e0c120a030e03010f1803020606030309100c0201020c0301060f09150e1609 70
    0x71034518400e072100308010718010031003210300342c0d4810413465090040224560000380241c41d44070040c0920b180000301c9070540c4a02e89000d6410003015412590244414103400044400201c00c2083c826060b60f40c03140421a0150710580f464082944050100c900003400c4074602090a00185409818000d040202c045880d2032140b481c5c180007411410310505041100015016001c545845811800c001f0001007898003600c0c45451084003e01c4d0300a0f00780c2c0f00f44000c000b10201e0707c043c0c11124003282000c0000700b03001c4001c80050310840240341017608140c80024525114900035142c00b6549481c29903003442c0e14081075034103550394251400c0d42c000d02c0c400d15a41c0d50034a4003a10007807180b0303d1301918002018100724841d510a008152144e9545a0660540380d103d151000d4030201ca480140d10340a00f101c0c040f0f526508244000c5404500b5240240071211210014000501404844103240302c1c03034040d9040d14180c0303000082c00c21440001c444c00e10030b070b20b16002c800c20f9941d0104900c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 631136357 1250 631135107 631135121
    0x2301020a09060509121e120a020c0603040813030b06132c0708030c030901080903070f080c0102070b04120f090305030316140f04090507030b1f050702030609010506091014150409 78
    0x36015081b81400900041107a09100029800303100c2c503103010030802079600d01c04144110f205050000000b401c00c45481d082c0c1d4a40c1c2d42d081901000c864407854580361030303202241d0660145180d00409801d01c0e400d4002c00c445e580d12001c00360440420040144402d85801801c02c08521500c4000070340200100020110a003400c4051900c40d46003000040c1182d40c0901801321590081c405000400c10100c500c03080f142c3d106113015034807050440301c03074060300030803d01801c038943c00d10800003840b840300c071840300d400381a5407a1405028019015038101c0e4441c040070300340d5402400011003001920300c81c0b9400107070a0030044031079003e151000320190310544e6000d240e004089030802220782c82d40211500000135041c107104a541c050045007c0c450682011066852175540f0300405034001c008a070250380e005000c2e12840e2030503030401806130000b6180300b03001c0c81c8280c0000b1160011400c00400790340682d000502d0441a80b400c002c6444c0c05c100103600610310402001805081d10701c1801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 631137607 1250 631136357 631136383
    0x90c081509280c03020d0b090606030a030e0405040c03150e010506010309030f0320070b010e011403061501020c060307080a06090c2a050601032301020a0906050912 72
    0x202200c80d00340e8261011460203001d400d420b502421440034000074140240041d00d00c00007500400922506000000a069a0001c1e4214161a055006021018000320702c603040a0080b541503031105410704d07079a4045180c0c040e0004684550607805071030190002a00309000ea001f9201403074907a19100240c00d0110b400030520790341e451503c11040400e00415a001000b420108500c0c035168030060413601c40c041a00f410142d0303c4407100a2504410000740d012805201d4842e25084a07151080030103a01b801210148405140002034000184944c81080742d00078001c0d00703150b201c0310400c445840c10611034606502500e0134003e192703201c05020b1881242240e8500c0341c0c82c1040c9804000301c44da1508050811810200d0161030740c1c0e0004c1c4841d20080c0e03c44c80707a070301252503240e0141040d403910600610a000c0d41c40004207101c01e0b100056085c0854805104600290303050701c40c207d1081c0940d101c0802d2410004018250060001e447c0210015140c11881e4405c21021800c14903010000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 631138857 1250 631137607 631137613
    0x228021302121929090415110702030105010504230a0612030c06051302091602010603020a0605040f060504080d030207030201020c010c021c02030c060109021c020d051e070906050a03090c08 83
    0x403410180707607004600268070000c869000391041200c0f0b04d0282414000840d010f24080808a000c00c40040000c1a2100755544100200281e050921142e540201000da12075802c0c20004039251800d40710301010040c0c15030480000c2c8a41e48103041000c00c004180c108881e5444400203600d01c64005004002d501ca40e480148600c00f500e44241203c2001d004e00c100005030038159401071726100d003926005410361b101010003524841080707024010f90307000207401c0284040c0c001032494003c0050070640e0b0600001c5519103032079250444150046100360f29181e401241c0c1c030300d40c05001c2c0e802822260701a10025240440080d40d180c250744440089000682c444029403102500c01200d0350301c41384291000d0340c44e00301d400144681d1140b040c007400307807680e030300003901d500040d0782d00d01420301103861110a54030381c0c0075080404020881141e014194007a0b00209900c154030100042e8411074041d01c130041424188102217415030054000402415503805a960200c5c503c0140c960003440c0040007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 631140107 1250 631138857 631138891
    0x2042d0305060c190305130803060f06120403020705011130070c05010e01020f031b1903270803120a02040f0807051203041208070213050f07022802130212 68
    0x984c00c50490501850030945010705005800080c0801440110340001c00c458407511386e800003038800207113007046a40c000c4001030720394a4055001000d5104070b00036004c1e9003050342d03140015100c6290f20030020701035800084100b03101d0070041d58429900200401204021140003100da9450343c4500b0007620300b400c0418040000d582d11442040124100307101400340b2034103a1003c00c0e03407800781c402e2100c804c01d0381c548500503500080140c035a402d000040070051618144c18041e10003c019046401c1c81e14001d041c03070030781381e080e2191f1034200c6000300c00a500d4403002c4905051800c0011302114007a50b001c00c80016040003000b43c040c064100da0014041c103514044c104180c803d0702c0544c0c0703d11604107000400810a4040148100d560000759035607039404c8600c0014001e0650021152038a41340406100d013000c591101c0c580b291419800b284c68204c130b14903955400403050800c401070348100720007100050601d080c084445840200000d4180500a00000003500f0210b8034081103003c0800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 631141357 1250 631140107 631140127
    0x12020703050d290f0a050d06020d0c0801060e01081915050a2705060a051212030403030b120a0803190e060106030c180303170603030c0a2402042d0305060c 68
    0x100c440c3c10410445040280380349034400f081120805100721071048000f03200750018040e103601165540a0490010003030307403809010141c0381000a024141c0010b42030612a4483d500852140303005010481003d40601c58001000001d089a40200045208443c0000905494425655000d041c0c1226102001110340d03c0d400850008184030100150804080c05840d40700d84c00040146d407002c1e90303030107580c1101040030703440c002c103940d9090000d2200008000605a0540c086034132610b088440320726844001510ba903442c006150003500c10142080421280c072609500c115201c00b00b400d012852001120900b4203040c0e00742d0020020a465035500ca09c82e0303901420100c04002c0c0724034503814081c1103803001011559000703428210340101001103512503a0800903219104403450840300303c03610901d8000c060b0311b05c0006208c1600120342d19414640f50038000c2d0380c19903801c8801505420141e620059038940c0905160070402075070080800824428454984038002250219a607850004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 631142607 1250 631141357 631141421
    0x206090324011a09060a030b010219051c0c0c060815090c04060206160507030503070c020303070302010b12190f0f05030a03050403020d0914010804020301150608040b010e0712020703050d 82
    0x84054442442c100031030340c4265289800c0d0b5540070461f25002841d01004e0300140d03d0b0101240580002d42210340c002000c10200190300040800745808c100710181700180150f4642030031007001000301da42801c0520101d0b1040c4202507100c04000310950124000c0c20200b40400015588018507400010307080c421141c04009003504102080c2d08041c4401415200070138902602c90000c007040320020106a85603c25110200c06903002410359a0341c00b62464068001c1c0b035403028803405541c03944c05846564034080348124150481c04403052040e0300e181c1c5c07a8292910b5050b001c8800e90b0001100c10f000c00c400b04040c10745d190355524001094142030034043d1815540c101c1000801001003414422074100224004500c5070a0a046000351a90b100007800340c0310340c482c0b4450350007400800007040c0358441c801c21b000707d01843c09070401e66250100000c0d08402101d40c4404100c4200f442100151a80d008190342c50092501c02e04100d460040282621030404c04400700c0700000785804a001400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 631143857 1250 631142607 631142639
    0xa021005030609040b0a0204090c05090a0905010807121a010602060717010605120a090209070c060e01060f12060e12034804180915020f0304020609032401 68
    0x40c00c1441c21403814000180c0d50702c03402003000f08034410000110b04014100d07016038014000d0807074180054281c01c84020455001518080d12aa03100b01c00003400014910a503810b0b2540800a481007504180c1d40c1c441580080e41e048038940c00d6419111403100d504080d01f800303045154003030240ca052a0100030300d074400e0108485000c669040c0100081500310045070480c00300204c1044003030b80e4001103a4000c3c03150400203904001d01c80d0801000c03551091690359440c0c0711394001c0043c5070310710400c50301f2100c560080c42085641040305104040700105004202403050314041168907041d058242003640c4040b081d40030f0303903010051080c0d1300524400711841c0804451f183c2c1500100000c050441d44220000c0340095600d0100000b04072030a504480182041c4821311500c0f80d1002c901c08010030480b5001e840001030900304c403140d000c0c2c6000300c50b4a00d1401040c5030540e01c66801300609941b1042000ea454803561009079405e00c00c00c049096000e0a02080e40001e61401200203242080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 631145107 1250 631143857 631143889
    0x20f041d040c080d08041e060c03150902070210050702060417010501031e1a06010504170a03140307020706030f0f09120207060201060806010b130e0a09051006030807170f0a020a02 79
    0x401c04d89401d216500c9040305034056003224004107099400018041208065503015000c90300b0603004a5043e60503410030440142e0b1070b4036601299030f4902d030480490007000c0d00258090300c640ca0410040b4801c80213000407d0004241d20300c0c181c0e48280000c8140700c0280c6000490351288010428080080e00ca80c2c0301c02103c010716a00b50b1440d60b1000d2030008003543c01c2c5144400c00c0d000c10903691080301a070f8042d2060040d0100324414a0b4911640c4070a40e94044000070555110b580d03030510100e054a0181c1c0058004103003003400d2040940140014191800c0200e59408900e81806000c0c000c04c0240c40c003895039550000e00e4940c009051561940152003960b05210007084a0384000a095046030050742e0101e40310350303085050b0f08565080c1c4d885210b04185c1d58080c481010019803108036181e22440498001108801924098803594400070b0310301c1c0710034414074000c1081e06500b4403584a40b030743c242d0f241c50780d250b8180e80a030300300400d01d80c0180d101d030384188110704121501d6143c0c161 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 631146357 1250 631145107 631145113
    0x90516030908070f05011d0a0c060203040602072c07030b010306080303150915040c02032107050a110a2901050f0303160c12080c0c0901030c0504020f041d040c08 71
    0x1450b1161070042c4503079034005062403070400401051150039801000079084400c11510400074913019641e495520307c03400d03203810814103400283c42d070002007203c00319812030f0007409055141400e451010118048207031112080d0092943d9140d16000388144601c649880000c0e00220710400101122310a030002c1c03140e40d02c100280409a0030b0110710341021581154500642d96841030f1004003106924449900315042115044410b60040301901c0350b01c10307801c10403011489013000c49050445c184d59500120710200f010040140c1305184021880540c402102c41c43d8500344c1c1c031070203204c5030241071030f8080300480403003440c2c2c0c8401540203004180c21100f074112517001c503000949270302c14800c603480b18490300790025040104807821680107000e007040e099100d200170308211495a00c034103e031a07414050180c0700c00d42d62800e640780c54140c1390000348010086092105000003940007401040601109000c0011401c8090f982040d607150f10350000318072401d1524124013891040d80101e00250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 631147607 1250 631146357 631146371
    0x4120e030d09050d020d0506010609030b1e0c07050a0b181608060708180708010212090109350c0307020f011d0d0c08190c05030706050d0e011509051603 67
    0x25031204942050394402c0321418110441340c40042e01e4a000b00c0001003050041c640005000ca80000c8800112402808215920355502c0741808050074031200c00091141e05001060f41484c00c030000d00740d06440307541180c000e440c0545420385041c000702e805032107a100b038610a0240150a200010f000074000c414101e41c6420312030003544406004020004124002000a8001d4502c0c0d8008003444403902c00da0702d0058903040340c14040d46c40851303418140c082650104044043c1417080c4107085802c4134604004131520000e5229001252500380342000c4c0707091103c03030310a1604000b010100c8010f00119628212071042c400c05a00380304405061101074411031b940c0c0403001f0406403c0030000c440401c0c003001245040030000e2a070741c10582c50391181a044404000c2c00c28500c001c400d02810042904640e200d0401d80d407400769000301400140140145080480c0d40d400c45c091103140358001003030440b00d10669034020040d50340001002d545031401e00c1022440444948402c04052500384000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 631148857 1250 631147607 631147633
    0x90b0403051e0106120f02012604060903051e041a0a0c03030b06040b0403200411090603060a15020d030b15121506030109330501110a050604120e03 65
    0x86003040030054500d01c03420420b8034145429407140005d0480000c01000c42d4505040c0080410307481d000407804103060b0351080200700f0031040b40242c81285150b082200e595517549480280030490302c01c4090100c144041c1a0390a401140c802954030f18400e1113440c0c901e002c540c1d200e03c400015070401d039090200020715205921440c980000f6805040105030301d0400f002040c014421540b150407089004030340441017045103000c0541058072030017401c1c030300008a0108811245a80b030340408420040001c084141401c9000e19413100000380080006660303140d401c9007000d005a8071000680098200700707181c40d0984290100440207413803c881c0718000140226943c0310300c0380038030a213490110018182c1e000342c1b240c10714050000741000f9100d580d01c4410b24054016404441442c0840190152a60f40ca07040340c1500700030714100044820749002c0042d50a440042c0c5844107500640304a400402c204004440c0580e110780d40c859400080c030480240101c05132040188179801c00341d40940341c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 631150107 1250 631148857 631148863
    0x607050c0d0302160e07030b19051c082209050c041a0d090c061202070b0103080703020a0602071a18060109020f090d06050103020325030b19140106090b040305 70
    0x506030055a94041901040c182680781004c0800c56240c0c4456665002c02e0400c2d12050303544c090001d684041c4200c8440c0020440304651030107140c0c10003598540c0400491529684003502881640d201c01041c10b586d45403640b880d401102250201c60b59600315455990103121020000c2c0704080e8100028201a6a030080f20b129900c210b10410800140c4041864213003821100305101c01c000401c005a800d26006c1d48400c124800c100114104803d20950703034400b8000c031f03410302c0d500c000303250340982c00c0d551140082d4000050640031407081040002c0021014802004523500990180500c2c41130740c40e400c07031041d000034440c0e1858001c80d040d15501c07810014045040d00c40922026071200092202c0200900030034800d9940000800c85142c14031190341d0085c2e050b28000e070f0a880410340200c000b801d691886203146046e6494042e41000480c3d0100e20b540e4106503000301400701c0071469030f6108280c540111030000c0080681c801000240e402400540051041002c0d032800c0910316207406403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 631151357 1250 631150107 631150123
    0xa09060e060a06170703021b07080601140d0f030201020f030a291309020301150e0a0e0307080a0804060920040f0507090e34022e2307020a11060705 65
    0x369079500303103010031400c1d1b02036019110400740c5101c3c045407144c0101d208540e51b0305540300d910302a00030351001103541281000c000e1402207002d00084502c080fa0350f41c0c001909000c150642c1195030900408108400340030056006412202c00032a050103030291703940c020701003104c46020101e501040d1091b1a1a03146104460340b054072000684140607002103409003403400e95200018075803520100c2d01001d03a03603075030780901d0040c6030410070a400110415503071310a846010301005020312191310713000e105202c4161300a21036100450210100d688400b500b01c1c044842400c0b0074008030001600781814030800c00200306894003400a82050b40f03010388a0050b9004842203042000e00155000d10b04514404461503034040300c0f00540002241d079840260101c140b40d00601800b203035031040c103400d11200480f81441c01c3c2010007a9130f00c284a44020510b9142c0e0007520840d040d0002ca00f0b69803030000d94803590b4207030050b1801c0e0320b0910700b044032004958a0b51b44241800c0c4440d1002c40e0700010307589 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 631152607 1250 631151357 631151387
    0x312090123130c03060203010b070506011203050714010b06040b1207090f0512010b0d060209010801080703030504062a03030b0315010f050f13050a1a0919050606090a09060e060a06 79
    0x80b400051810603a1807940c290304007500142c0000b00000395100320000038908940501c0540d07400d170f62101c4900000020305503002d00000d03c00c2c0320220110380e8407040c1c4c41d801c10307400000241614030400880c4458100da0721100b1585004200c0506c3c81d4541d11030181e06c130391240341c9000c1050420500310310242c918090180120080c41480e904000c0940c0302d9165020024481e000d0310580e490014060360105144500042c1c0c01f01c0000362504001424400781c0c0e42c0f580f145420a41400d07011902d220306010495541c10f1480043d0740c029241150035944140695000f0a00400c104285458181c0100b441501c40400e0b50041103030400400d001000d4503000c03151015000c0d401c400051004041c840e1500d800780c5030005000c0d807240c60743e01582c110f0f8040006030030312186640030040c4000003190800807007103242d0103100700088964000380d448203000f082681020303141c40125903840216001061820340d500d005003d42c04101100d1a40140c084492081e0300d800c0005c010b140e42181c1d5858 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 631153857 1250 631152607 631152631
    0x7051806030726060f06032103060409020a0b0c06010f08070303140a05090619080a0c0804020103050421050d0509070302030d0f0c0209070201200306300312090123 72
    0x441c1041c404241c1c51084424948122041390400604e68120518141c50f103521a01c00c6240c41c4401414003000720b5141c0c0c0b010302259003165914801d210140c03a4030304003241d03c0600c006010400380b4441c4003030040b0076180401060158101140c0c80039480c41034001d000240e01441c020000a5804950074000a200008090f00e6800a403002c1da0743d80108684a5070000001c1001400400d00311081c07180c9075119a90541961144280403049480c1c1800380c00004040b0400a80554003e03000150014480e80d0340c00300c8a00d1145440d040c803910080c035000010b8001030a0511201c840c040c035a0040600703006407030400e01e1039002036600c03258041404140044a09281c0c4440c2c0985102c1c40400c2c0c0262880c51189003c140081c003d2001004915a0303440703210520341d001030361070180e0740314000c040c10103000020741e1101551400f504900301521525480c00c651004031041c400381079094000d604002c0d40f0308291a1040c01d680c19000313100c00d8440b140150300b20340c2c80c010000e1030300b1042c07034000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 631155107 1250 631153857 631153889
    0x5160207050a091a06031801050123040c0c120e0a080d020706140f1303021c08040b0f0702062107080408030f040303091a15030c03060a18060608070518060307 70
    0x1340340c034204059880c081e484013000c000c11140881120b04031000c26486802000280c0c8c961400030700040f007948462035902c1e810f4020f950641842c2e40025034000c80c84c1080c1c00080419070703a0038886074a001c000800115211410300c0d007030502090b104050320000f4050241c00310000d0340295504801d01c2510104403624850540508100f03045a41202c0c10003900c0340c0d07c001d98038031000d20481a00c000c80c000c1c480b46040520b482490380c0d4100455a10005152400d8034081d4408010f4100c4100c034008240200064001692400001d0400c0e03444010640103800e0301e4136040040300c0c0e000b4801700030300030920108030000f28010100d80e8010000d07120340301c240e00d86003811801418030340c070000c3c44c144003245140309111078400701521404050b254410301d0b1107004181900c1d400a036104a42561003c0040b501c2850140c200d9800048001c200c203103211040e44800c010344d00346030f00491450704145014455400c008520720b5800c07a6160900b10365040c0700b40840d0340d0301d0785880742d25102190500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 631156357 1250 631155107 631155131
    0x60905030a0809011b0b10080a05100b0a0e01140405070219030807050405100e0906030c0a0b031302030307140606060306010f080901110c0c100c03091a090a0905160207050a09 77
    0x2100c0385c1c5910b16030b400041c030003c29161040140c001900c8400324070000c0f0100040d21302c0d00041d100207180c1e1040c0948000e0080d81c40380c8002e40740d41e44100780c1c48441c000300440c01c6504802042d009100108440a41165010502c0102d03240613000d00c08540100300fa60a005441c0f1005061065042c5046045aa1110030845e25402943c100603482568901c070f104d00c00f98052050f00050500711062966611400c08165030b1303100d0950704e00c0d0012122102000b00c040c110019642c0002064886510401c0c55400603007141e00a1500303d4283c0041503440414075802c02c00700390300990a4074040c0c950b0605170006041c410800070044108801c01c00020000042074206032012081d650328640c03503881c0203c80c01d40781c44801905600070102c1c200d50140452040341428110b0703416445240b2585c1c10000900301c10000400c4501900310704000703882140d100d000e03400b0001c20312440e000400e07045c041040c8034400c82d87c544150865110560600c101d940c4d941c05c00c0201d42c49004009520444c0c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 631157607 1250 631156357 631156367
    0x18100e0705042102030c061309180204110301180203040b0c0304020103090501020d062c012105120409050901050105010516020a08010905031201090e0d050906070b011806060905030a080901 83
    0xf400421860b04415000c070301020050101d6000c0c140308a055503c2d0f01071000901030039000c0d03038003100740d40303101400e08001d012415449000c403424141d0515251480c182c002c00d05407008402480044080003004200540300f00307510001c40316200509510318106502c64104c2c5035006804405e0700140003003c00c0440e8004d50001414513440030095480d4501240c80e01c00400451007021000039941a10440d522070252000601c9000a6003282060b420000e6011503c0703c1070802054940d90000d001011490400070048090300411060340d0329420420258250ba2000d41000c40c0c680c1007034010300c0241e8104050300c0c81c080c140e841c200002c05290000a002d462164041101d80d440c00e2010340034000040300030300400c1d40212504400366030312042202250441004040300303411040c030620009228000804615034014181800c0c02c4031611911f001c8035081c0e1000d2070241e0302400c1054051554020740e03000303200500703015040350302c0c1c4000700361079070b20a20b00100703511380c00200c44203035078059 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 631158857 1250 631157607 631157609
    0x80a020f031e0606030f150403110712050304150e0a150521010503190b0609100e1014011b060203040203030c0f0d1e051c0b040e0c18100e070504 64
    0x80d000da0100e140103542c2e1580c41c0c0905a40d00c5002c0d00a084210403075104c0001c1d00c00d0719102d8904030101640c1c2e42d86085030340540b44450000113028921f40003a90010064000c0a86802400a140d40b5803621003040002c80b03148180c4804d001d601450008035944114405c011654080c24000e0051102102145c0620075907404000a4840a0180d500080e010300300034141c070300550407074202d500990088050802880d000800400c1084001007007810300d11140c68216128500003010785451700601031141104903002c405850a6030070400503920320070b0303510703000303042c2030900341020b4141c51110900800c120a014043c3c5070004046401c6403001c00868503105002c0c0192070781caa00d1015241c0d140e841ca40745000020390b12044010380b50704100010903a600741501d0300c0d440c0c990398407002e1080c601c69203240c0440c00d9a401038440c660300e1764021013000f50042c001800c506031040307040126121022284000e019103440c1000400200005903005540141d103d20065a54a603000c035580d10503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 631160107 1250 631158857 631158883
    0x120312100f06050d0b04020909130807020a060807020c150405040b060408030708040608090d090312110106120303060f05010e060c010b0a060507050c03120910020a0215040303090f080a020f03 84
    0x14140080c2031540b01000e400213101c80242401001461002c02c0280d020f411304150b48410403401294244108405010701c480c410786c0d0160420f56241c00007040c10f140d0f03a004401090301e0708100b2100581c140108204c81c03a0849003246030b441c02001d903103040d00507801014000c42c0e4490754541103a036031205072001022040101c035070b1041d2524002c003136504544200740104452070301007247e5031004100c140449800d0f50f1106a581c0c90746d151041c041c480605294140b040400324a9183e54080c0189406071800002d074103900300e00d0340303002011078689500001980c480300005100c00d030390120452110305021102d0a0302c0b103080018090051400c42490340c0d100041e00800105036820602400032a07004000f030710b06ca071210780d05054403515100741c3c0c200100301c10444d0701920710307003c9407407841440944121071b04001e2503804a0050520074201042240010401b041015442945500501803480100e90864a0822400d0361144c1c1514000d204450b0f1003885070340340c1c0b02000941a0041c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 631161357 1250 631160107 631160129
    0x220204020a110622080708221401030b031c050c01020a26090c060d0b0303030c070b07020a0c0504021b011e0c09061205040201020f06150f12031210 65
    0x10800700103000111050100d106034021240003a08005201e1608111000a1000140e1030303811a5210000340e4010001111649003d010303001300294039400100400100007846035034682046a0211686604101c0d541014181010702c40d980c1c50116000b0181c141d12600241036160a24043d0b0301c0740207a01107041c140d8400b040303030340b40c0f280c5c0040e80100c5400c40c048010800031000c64101c51644084903000c5c0641d10901201585051040003444a24000d20700051351000040000e81164001d0b2a0548640c001003804c10910200c1410702d500005540001d02500201e039490755030324032080c0324241c407669000c130700500614844000c1d0b0340101c0c4204020044980800d4044100003a04c6840030f10403480c1c070394000c6240e801012803200f40c840c07a854210358582c80d00c0560003e080000e100b24114025808801c10341c00040000500504007068405007400540c0f080c40500d100745038080d80b250040516031012080c0103c11202042c1c80c8407104003941d41d5141c49008001c2550f801070400c0b3f9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 631162607 1250 631161357 631161367
    0x2102703021f14010504020c03090f060408010c0c110910061404031e14070503070302060f040b04060908150f07030504060e060a1505040c0219030c0f08030a050a1422020402 76
    0x115469001d03c003103c2d40850000030a98a03501484200d00403c66181901d900810095110b440c2c142c10b043e4804000a0069150644070082d4601392521030380b408000c40c0820000c0001c00c181d400d15403000d00010f403541c403806d240000003803940c2400c034817851040c003600c0d01380329501c580c0d003408031805590401e050300c020303101c1041880d07144031140b001a580a03070140031200c0381000101d9090200d40e4014001c120340c40c2940c00700461540914003100c4400e000300b000140d10340000d07000c1c2006291b1602c807410091724026010781444110955089080d81d0102001440b81b640c00c85903410081314540000d00b6030381d80c901040140f404580c982e69602c01d0f4410030030444000d4002090f002e9140e8090000541d54509101c103485600c3c1110016030095071030342541225283c1102e0b12503010f40f03170101000703400b529000c0020b03a01007016100f942d00041080b0124400c4c0c000c482c1c2200c00d89408009c03a80f02c0e1000740d8120070024003080d4882400400000fa2901d07080d6501644580080c0704550310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 631163857 1250 631162607 631162663
    0xb21070309061109010e0f030d0e0a08070f0f06050f07060b060918060a060c1e05030f03040606030308071b06020901050d0e0106060f022b032a0210270302 68
    0x1079041132000d01d000800d2060081d0003400d2007156840c644c1c401900034002520200c2c01a83c42c0fa8026004a80080100340001200002000428001c040100348551924201002d940485089402c0f110500104100282c1807500c0325041304c104940158000601700450800030300140701c0c2d51031003a41300c90845008070030b0b4841d84907910701500003100d2170300e5003595400d000d46900361038120103000810b0012a1008a800040c1981e050301c0c400c2c01640e20f00115480c84054a030426102501e1050380c81c00c090040503080b0800d03903040103003420818001d0030b1212600b1100c0380740e000d00422240d000314804032039902403070560b05003070764848060200c0700040400c10700a025a00c60400024400c812011a20f40046440b0146004d0b1044403150b04201505480041851203040c400f095a20003118601c141d0510b0f98040102d846c0034804c0c0050742e00c1000900c1d1a10241c400c2c03078040d03d02302580307414110640d1095403003500c0003141190341900703080581c02c0481c2c984040c050526460307810b14030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 631165107 1250 631163857 631163891
    0x200705100c09050915011211070f0203150f06091506090d03122f0304080f031f0803191d09150d0b191401050418050d020d03060b2107030906 62
    0x820000380d072201c0047d9140c0840e07038152140290114146002007100402043d0781f8040841041c0c0040e0071903455049a16606d2800c1d4000c865000c0144d166000384005807800d140c00c1c0e0742041c2c0e105582030400117620005851442040750b2144920b880e111090205801000d203800b50450b50481080700c40340440740080780c008a503000d050780840c4118203510419583c000d41e03000340d400050b140d080480319008403183d90301c0603040b00c2d9124409040124400307154100c207009020501c3c040c2d80c644078016003209042544c107040c8020f100010030f00d041d600032100c1c2644603a110031108542d10303894000c020115030141201182d00b102c10900d0345c00c02c0c05840e010160040084c074030310306e40761242e5a55070000c44c0c42c040011480f01c44c0e0040104458601a0011500d42c1800f80c45040f00d42640d40e26686041c003c0003212001d0b802401801c1d0501c0d80501c5007000a0900e4000d451a01d550345058114040144085216600d010000724600b64840e6000506840d03000c2420001000180380e0261 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 631166357 1250 631165107 631165141
    0x24040e060112140601030807350706050708040305030a02071a070e03150708131a040302060709060509031c0909060338040b150a09200705100c090509 66
    0x14082e81c594074040c3c000c1c200025428101c81c1c10028480c200940d0b99200b0790503207800c0301040142200400030b803080e503001c500e081c0c0000c0f50f030004103692600d191801d0420b48800820320014030201318100030110360400112035016005c0000160b41e00414948090740031408941900045040410001c800e9008a40501d60b4141141100c945800100c01400c05803800c0355a8030014103020045a107541000b900d04021610840c0084451200603030040d1082c11704480070383c01130380f022082c0480507800040e0070015200e149007480c03411183d540460f0352441a005243c00c505802d01448120038822584000500605e100a001d1140d4a0401d4000900c40b032800c0c0f920406514040b0180310362405809090352400c44408505949584940d10392200060050404401000700d02c9181c1d50340d1015030010b07102d845000075803e00d508001d443e820000340500741071030104104240c00b081000581300d40c3c007142e4150110b04181030103000c6034070102c141e200c560414003401c24886918400440c80c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 631167607 1250 631166357 631166363
    0xf080d020105010807060207060e0f04051e0105010504211a010909030206010608134d0102060919020d02090a0203061201020a090b070606080d1d010824040e060112 72
    0x1010b0399032500303a0b19817100294440c00016a115030300c2081418090070b008101072400900c070000c03201010700400c042e40e41c00c4074002e2091080441034003904c1c00c1d0158103030241000b807072710a0410f414220710030304c2802c405020300003508000c0610b81c100a02d204980804a491f4041760025507900d01f5000054110900102d0141c09101d0011031114030550f03405104210904011010b5140b980358003031441141e505006030132010160b05115811203948a800740440240100c0703000c8050200b610044010160460440d04070300b00f44003900400050201d100c003050380140074030020520000702006504a0700075089141131042041c58101603016512030002030b920070032221a02d1050354201c0c030a5580c0d640200e074415106100f08909800030782545803103002c0000c0d501d9150b42c0e509103480b0320000d20b24005080c1c110105010140e012400e202410700707003040c80107424080303c03044404904200b00402692070380302d0382e8800d5a0701c1e00f0108032601618260b802c0b82d43c542c50722045680c0d242100f5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 631168857 1250 631167607 631167611
    0x60207150c1706101e090f0621020f120a0902090a052406030c0a050705011401050118031e03031b1805010503010e06090405030f0309150109020a0206010911040f080d0201 75
    0x10b4082c01c0c51619001c0b0f0b0703842650740c8151084804445e00030482020300d264200b011a060201e0b1743c4818034403070400341c0000d440e03d500c000c4003c9512203001e0421008811210b0041c0220301e0380c075080300e046c0d9100000304000020f80b590742160030b0000b0058544040e40c01841c95040c40840700700d5038440381c084c00c450804149e02a00700c03107103a00d42224140c42d00c0d401810420001d0b0200c0000e802424100d041480c0c118070b404441d0322140c1c2076825401e61071515041d11001001207680100d1240700070480311040002d074600e1601c0301038000b20100307001e81c0042c08001c00003040502c070f81e00240710608058641481d158a04c2c8000302807040d24600403c4810002c58045074a600aa069034102e800080c9041000d0f03840009100719420050000c40c0c56100902107000d540c2d03840070103513100303003401c0004090103900d40803490445401a0b01ca80b0340396104100139454540d000c82c1d0300b41586c4680d10701060100e1044910880b920907988205640c9426800115011101007864800c0000503402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 631170107 1250 631168857 631168861
    0x103060507021c030c0309050303010e1806150d0204090206160203010501061d120330060a06080402151e270102070e0a021e0a1119060207150c17 64
    0x30a0740e0724241c040c01c0c0e19005051070f41d001051846a0006500f01645180105001c0d909a0360203107950400e8003d41114420b071000c102000f1662818119640403440c0140100d0500c0c07269001c0103802c264501e4005e00c01301c4c0c0b444055407142d4001212035580a041c2e150340d00c401200741501d96810700412403203035090500001c0d01c14800d00340c0740440101041004140c4a02e80c0420880200c0c44440d1002800300f80140003840e08403069200005c084207840e6030490200039040c2c98100001003c0714400c211303040041c0700c1d160f4001d14941d441503040d200700c03840080c221340480d1280241c0240d40102d000603916610354000e91005065150b0541c4911101c8104200d4410700154140003100c0c01680942070800c00d900383c2440c020b80003150b2046c01450700207400a040035802070082d0001c02050001003441806501241141203079007a10040e00c01030350511302c80194103044010242c019a00403c0c060244800201c584d4a0111203003000c10078611183d4020f08404001400d000b00e5a0000b40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 631171357 1250 631170107 631170121
    0xb0d06020d050f0114120c060a0807090806040f110f03030f090109090e0a0209070c02040507090602061b030c09150c160b03060109090e010e01060e09010c1110021b070e01030605 78
    0x11054183e88800505d403806907041030030710681000c46154210580710310319610380e20b0344544009103e100300da6600c4a0f80742c940300700b0107003041c100c1d44d000004940c418400c200105151091040c0040e910401c07191b0014030500020300c0145044d0030300c9505000c005140c003403d03c032010051a18040c00c0e2191000d8079560001c1400312952500d0b03580d080d4201c1c0c9038a00051604d51266584150281000794900d4036503008541114000c803440c1001c2142040c003804525010440140e0088440e50707206001d590105040708207020103443e007010110302150f0707103410740d817505200703000d401043d9900fa480d96064040d40d030395044c03040c0c000309404426400c040f9400d001a41124030800047c1c603243c42071817420400f1002410440c035a282d90b07541e0391000070441542070190781c00408230b40038001d07040c0c14142034190840745044c51001c24080c10a803580704180002c54030504105843c2d9005031641d0710492000084d00c064a220a00780c090103d02084241d100210541601d000b10400c02450f41c07420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 631172607 1250 631171357 631171381
    0x1b070807081005060312220305030d0f0504030c03030b0d05150a05070203120c0304060615020d14070b060f150a08010f0b0403110904150c0c020f040603021f02010b0d06020d05 77
    0x2441185e00354008a1220002280f407000500c02c0382680031090002c002c6500c503070100c070491070300700b20384907000000c902d419101107004e000e8400c44d60010070061810180c1c0c010f00040500040142415158074000d902640d865192413410b0742c01ca800d8442d00c07403030402501000e040458940d148549031a004c100c0d02840081541c81084200c015040706031915841c5810755000244110780d01500c60f4030114030318a00d150004412181074008281500342c1d600d02030244200f05c0c986103481c003003d01407040441c0c14440480d41102055800302e001c0c1e40c414003c1150100c2e0064079034584c2d90300040303001e03180b43d104c11294102d0310b2500c001c081039900c41480011a200c0c40c800580500070146103001030b446d04191683e0000c0c420080e81d5590342844c0c5110080e25681494600810112050141542002c0c40c0d0764440f45003c460070401c007401c0d9400294180e94081c000310506441840d80d8083c14001d40c011015040002c0162409030401c0c80d2050288d44111244c00301d15040002194211040d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 631173857 1250 631172607 631172611
    0x1030c21061a0618010905060c19150501080a1104050f0a0b0a051e01080603030304030c0b0705070c0b0d0e010b010210110d140103020306090c010c0204021b070807081005 75
    0x1242050085a0329625100050300d91403581460510100710100d1040e0381d4000109814040d00d0040d1580c0d0a4100014110102c2607010f580154400c100c2584586400306420801c0c41c261085004d6012681c1000c1d20380741d5070102c0240c1c101d85001e0010501120004170040c00511503284103035281d540000740029594151a2007001c02c60440c041640c07030143c3c0d000540d00603000760152070642d582d6800a80d2086607170806c094030403c0340ba0811b0481d6030101002d03034420310603001140b642c1841e64005200f09a04e42c0080c0c14040c641700030035030640c80344003245d0520f5000101c0e0010a0349405103251503501c01a030036007426203400584000e070303001030050400c4014140c02920440c28032a044034040c11200107210742141d001c0000711440c4c0060b102d142e20349a1403200c1d0b11070719030451060605c2c2c2000a4440c1100390b0018031103003100e81e40144280c00b61340e419a000b517115030b4901403003d05000080c4081a4900801c0c00110b400c0d000002c01d1001c50b2091400c0307800a100c1038048208441c41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 631175107 1250 631173857 631173899
    0x15091e1005070f030309022409040605040b370803030a0b031501050108100806091e07080a11061903092102061f0b0301170705011409040c02030c10020301030c 70
    0x4011a00400d0091b40244100b50019003040701141d01c41c3c00c61141108030200009910102141c0d042590606200300400703402c06880800508402c000050b0142c1c200200b0b0300d03240100c008080084414032802c8003d13403203001061824080d2a007010380d4582d0001c6500300b240720302e444288505880c00164281c000b20014181c868113900305001180c0c00c0c10700400f18000112880b80015204004202d0680708a143c003000d45040c0301807404203002e0031100c03424035a007507005403410300c801000860481801a400010b450054010501244081c003900c134400d00c0602c40d00c42c541c0000c40e0036800c10801c030b910a00f001000303d40040100724040007030800350001a0312035000920817a900e24140411503003103103950051595186900c444d16070098001169800c60540300c03141d145010000040030307103000d08042c0d040740d24050155050740a07903407009110300e40300c402c8410118002d00840715082045d43c20fa408aa60543c4204082d50080c40f007102c000c2001d1a0006104c52811808008000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 631176357 1250 631175107 631175123
    0x302060703180b060316080604120306030312050702010f0c0203121f0506090a0504060605041505030106080606130e07050909010b0f1c15270c0e15091e100507 70
    0x2102d494291140600804c2d0a805100303003040c5010f40f14442502c1001030100000038581803900f0f1901c030306c03071080d081000d00c1410f05011085c80002c0d0006a00111041043c10000301d40e6242c0000f00d02406030582c0b000714091500c5808805540d001c402400c854075182d603190160740b03603c1c4801c0c02000c3c0c461203649075041100001e02407803400070010320b00c0c000c00814601c005910340c0c0c005000c03a9021703031005020446c002410071442d144680c01782802c032181c0c10051704540c54000003801c844002400d00c1d12450000401480b01c1c10905030301405407198031010000d52400c581c001e4500d0780440c40c601c0c450100d2000000e245100b1608591586554016050801c48450f215803101d58240b219042d4842d00d540004440529800b08803005082c10103860241c2c00c05102c41c050f400061011058516080184000256401a40d40e4510f09000c0c1d5128105a50311414102d0501404240c5d030f6026088141e8690350700d008168002c04000f003210b81401c00c150003030086e1902d1141e0200104621 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 631177607 1250 631176357 631176401
    0x931050709021e040b03011d011202060a02100c02010b0a050d02030c0d3e0405060a031704170304050307080a0c0b070c08100906111608030a1503030504030302060703 73
    0x40c054003d803119011401e6201504540541d10380583d411540049544900100c010004810b80208500ca000780070f141c0070b0306035410401103003500c40c6600c0003e0700901c4000750300003c0390310801034000c008000b8401001a941650802800f03003002e09409442000790020201d410728129640b415680d07401030040251142003801e1204c600900321043e54074802d4808042400000140700036108996070b180d00e4014921002e0426415480d803d030b180c0101d242504011403501d07040400e006480d08502003154168100c504140c043c4180e41042c0e00301811441ca02103001c100201901c180d5504500f43c85c00075854210301a0340b0280040090b2107182403840c100482c46216004205440c01048040c007503c2d00c0b101100d1801d07502c28170f401d007a1a03803400e07007030144100c0e84960760a10f07a400b1211882c3c8540444030080400424001511201c40040803400381c00181e844054042410303100d410389141e40e82000340c034980051000b07030054000c0100044003a4442e200340c0707100084040c4101042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 631178857 1250 631177607 631177619
    0x4030e03012304060902060f03042102030720180609090616030b18070c05060c030105030c130902090c03070908030310090b0103060515130b030609040308070e09310507 74
    0x20380c0303020f8000d60740255101c4850740580c4500c03004003101e45096219030b540741001e1030452040447c4002900500a1419014414681c040115031125800404a0070b0505d40f2a0354404001c104c80801070b40981c1741c90762003d541a042103410300c240022121100c8a58840b180f00d5250380013100d1080006c7c051010500c505800f0b944620404040507013251041c82031040101c20701c400a0754a00c001c5408001c4c210304001c01040800d6001036615011804c40d454400400c3e554000742d240180710320812140c98290440c10343c06100d0081c0c0040400d80030307041c00306040840e0ba0040d6a0340340000d00d00d160104a0400020480740116090031043e405185042c0c0120300401000b2040c904050f15135000040c10341e640403010000340e581c0d2000c0c2d40d96050107003081c813580c1010752001010040610801c100c1e0381da82281c2c1c40d4400d130503041120035656100c1c012544004000041036000000038140804100c400766a0000700c401000340185643d8803828221000590b00e400600346d500c800810301c12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631180107 1250 631178857 631178921
    0xf2106090703022115011206151a09031906092310020f091504080706170f04080d110a11151614040305010b0108012102040c170f04030e0301 62
    0xe82c5402c079054400d03003040641031071004c800030391141f5030304102041c0e42c005001b580d1050403040e100460100c15000d2600900300f822003c11103c0141c0c88401203504241d9407002d101d0112088006246842d45071103038500344004000b10201030f40c094150000c00b0071040e140c1e4070f0700003035039022000510702d040c0907401c15000703075010300303009139142c9c4042c0b0640080c0c0d102c03988501d01c4207507010381c0c4680312810440c080b0316203010350780400c0030006002020040301040180d41303504903027041c4920410b43d5407803c25402500c103050900112620706504090000d1458002d041004450350b07801186071a0403403007e5540032011001c40c48690b2520216020541511464180c4480c03801c000d207a8814040e010001c80d0440d91041d562651140c4042c64079603408800c15002d89142c041400410604280c8070421102d00d100c02409243c0d96440311000c14090b80c241000c006c90000076012501c0c0200b04400120741c1502c04901103400c0d84058941c80c6818060800c0c2c109421141d072542c54403807088101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631181357 1250 631180107 631180159
    0x3070b040f02190503060c120a02090f0a06050706050f220203190606140a15050c0328020106140123070c0e0912040b030708060f210609070302 63
    0x241200e20250711801038a4004032446441c00b0001101c02081c640000d141c24001d0007004020000b5080003890818031460800c0b98100344082c10040e299000503010818020100d400d56030b001c3d100010000d0b10755401001031065038410081403020780c54080744075400102c00e440e049001048108c0700d00c071282c1e6820360425618002030132160341c0103d00740208a07961600340292030840e1121024030807003c034082a4000c81c08141d47c0807994030329018001c02d00f49aa06190010403c00180e000c0074600e040003a06e103007001c18202820355a80585001d030044e41d101100c01c01550805000141c480c44151002d4150f10068450303c8a80d6499804000c04d003049041c0a440100284000b0380865450300140000e84500784400d07482e030410201e0310b868281203c403003005031541000306100c45c42c40c4000303403a007041440c1007101c40d5440b2400002d08410852030300316002225904014590b00c0c0084c0e1505c54840e0321807d0300d0140d00c405100989404440c000690003405040700c40241581051540c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631182607 1250 631181357 631181363
    0x17040c031e0501270f021306120203010b030d020c2116030203060a0c120f0f02031e1323010f1401180501080d0c03020f030c07150819050601030906051e0f0903070b04 73
    0x6200c07240c403888504c110364042d00a8071902a0f559276160440c1000d2003400c0d610380b401c9000708090100321200035518000c418115020300351071088014054040a01104050848410303615560991041c4050195040c4810791003403191a011034600501846140301c801c40a135078501062001d643c9a9000d0f05038624000007048d5a998030303c103c40f04ca440614050f88200c1203c20a02c1c40200002e9010f480180401219090400034200040c400750300094600454401c0c0a58504400c1c0c4900c1c010840034640101c441d0038407030301c410180c00c0d402e50309060716a01c2a01d05000050003801c0c6e001c40c4c2d0b00b40102120780c0e104a0312984464028190f01c2140c038403a00c111040003075104101030940e0001e00074149554048031082c800403518083c0d821907004030340342485003440c00030071461901250000d80a61203940e4030200e01c0d03d03446034011101e650b42080c1d05010344d062450740d080c098124440005140e29000012034404030010045c54004c0c15180010360804c030868a4252031039134090412 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631183857 1250 631182607 631182619
    0xf03070305012f03090c010e0a24020d0f050714010216060c0e12030307030e07080703030207050f0105070203030a080a0209120c030d03050717040c031e0501270f02 72
    0x5442401040f29010001c4440000500411a421184000c05400d54460320080c810412022000625001511000d00c0c0100d4560781c0d405c04140c0031640d5802910303148004c103550030701740c83e0a00b2040318242100e40c00c542117480c0b4808121b81d1111708806070400200e04100c60800711321001c1c549600303200808001450100c80d0350b400204c10400000c11a1515110003c6a21083e000400c002c040841505c00e046858012801907499201c018000c5050690703414950038042e00405c400d80c00b034900507044403031683d16420081d685c0c0045101c0e55101d444502d2182c907881d4814025181b41c0340c2e0140085041c482400380a0b500303070000070004100039034284a0744c0e556589500b003200581e000300001d00300f0024000f0505007010014603440e01803505041c140400564003910f44064800f064103c1c00d0aa02e45c1d280c4107815441a43c4094440711400d50060900c2a030200107003074161040c0000c0182c0c150901482d00310101d201c9414a0310510b800c080c80225640c84844401c01c1e01c01011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631185107 1250 631183857 631183859
    0x6050915060a030b0a2d050a0203010501051b070e0a0905060105030a03090312021207030903060506011107090906020d050a1b08040308070503070219051020030112050a061b12050f060f0307 83
    0x5040201b40105004000740116040450049026482403580040000d071080d03166604000c000382c158410055400ca580e00d040c503218000340c105000c904050040f15004680e5400c1080d95074002d085e40100a54090003503100004d20361800146902076107a16886681e011031440d1a050385400061503200c00754003031440018508455200104481031182d202c0208150a6043c5a002c0707540091800d418480130105c44040d01e540025009c0c03c5500250300410840401c0c94144064002d81b01907204090903e810300c015812076420841d5803840000d03c903441521180d5084940c00400d4501a0220305100c000c9500980700d83e00541c0d200706240110b07600303410900510301c0c821180e003006580d503411004207028140424011400889844c2c1070b20000c080c01c0b200c0c803002c14130040c4242e24a0301507003000d0b2810050280b110000f810741150301002007090406c0c21004003c0c10880c0680001c044520002c3e0210b028440e03503000300001c1c051010300ba0784940511a000c644c14013520742c14071458070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631186357 1250 631185107 631185131
    0x1021e031b120406050a0e0715030209060309071a0708390f070b0406140a09080609030904050708220201050c070b070c120803130606090906050915060a030b0a 70
    0x40144070b480303512010302d00e003490107040c26002c440010f0400c851290400280c1d283c140300005008040d01c0307108001100b14600c82c0001d0b00244a00c0d40c21541180010003000f403075001c007060440403944052208502e4406200020314244280302005208403003c1c8000c0011505c00200c0700801c0650180807021094605c0c2040d8800d40c0c1400000807990180303200c0e500808050005030002c120580c0e0312800c10307040803405021482e480806003400d81010813103040c0107120340c207244002c01c0054261340c02401c00d060b07002c0d00e952088031900d005a06200120b40e10034070500a41344108001ea030074088a005003141d08048221480d01a4100902401007070200442031010741d008194600d0b815a8170f074540c3c540050000c00640c8040c0b1003d40c42403450000c5901c601c03c03660300ca888180c00451902c294a046801400550001642c3c10310b80710034034041103400c0d800720303006100e03020450b00c21000d00140c403920242c2c00c907010b40d04001c40c00d00c200005141210444e400858011010900c284804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631187607 1250 631186357 631186411
    0x60f0702150d090201020106061b0b0606071a0a050c040b09011d0a0602010c020c0a0806070f020a05010f1d0f1902010e09040804240504150c0506042301021e03 70
    0x102600846076100843c004541c0c0910a400040c605424588410f000d42c103000a0140c100410240c140b140d4540010240c1e61084d040340d0740580d01c801210011800d800c07131501c0d002ea040b15940005440c041c046603181c0c00200a444c21540c030588040e103400030700c800441e07414102c04082180350a28080074003407940e841c41103801030800383c0d0001520000c4440c0c000d00e0440c580500600407110a8406d000180010030041d40c8114281071900c1807142d0008101d140c102c00c41c1020f801946004500040c0300096040300090401c220500441040542c01d8a511004410440c0d440c6e9801f85070701d82401c41660450b4800c03076005040200206019801203911307541c0841e404c564841c030000c0c06018101a2801e030340514041e02e03d00110382c91803000f01900d1845107006000080c0c1c00324000b00452841f407014404855844000d80b0240e040528042514440407003064200100305202420301c001e05100791500300841020700d801c80b58000082000701da201034079040003040d00c07460040c0162001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631188857 1250 631187607 631187617
    0x403081b0c130e1005090a02041119020106050a08010b010225031a070201050f0403091e03080d06080c03030c03040b03090309371212030e070b180f060f070215 70
    0x604001c01c0b0f07251004207142c141101140e071005894030302001d011601c203000452084083e415100054405514449000eaa00481e40c0c0440c0350717400410031065555040d08030104442c000c2d035001e070443d610b0b00e881d2800d0311400810640140d11100007410300c040b50b40c90b8000120540303400260095120f4441e02502c5040100d8064203920010038842d01c50390900c0380c268040d80403138058080b408c0a0794000c0500d41c0e50303c03511a0380d081d80d0032241c18035428541848001c40d440925980d44243da1545a401382209108070007007401145242d03419420040116140c0360100b402030352410f81401c41e034101e035806c0508560060300c03003071000e9541e0382c03192409440a541c06910680408001c0e082110030040d1640541424040d8400200070150303400c01681d840540c0240365646414400300d0450090180c1c80402c003452203130342000100400301c0c5000b4529644546004c0c00e440f0074071014000001402c0c201c1700c0d008581004500404d81003803001c0c00c0035130320040032840b2031340d12005240503607005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631190107 1250 631188857 631188889
    0xb0403051c0806030a0f021f18051207052416210504061b06110c07080102090f0d06090f0602041e03020f0f010309080a03020403050d03020403081b0c 66
    0x1081404480d034003018101c280d054640d242c803010500c0c0140229840310010342d0001d143c0e000c10400b0101b15943c120081d0103a082c1d80c08900c80d544074504000b024410a40081c00039561505030100302414801115403800b80403600500202d81b91009111b01c3c1a0120403003900d50352010504c6050703d030036100400c109445401107001c00d030000c0c14601d800107844040032140c600e0b02c14080392a150001d0541302120b800f82801501c00240b04420041598103500c0240803c1c03600300e01d094100c905401505081da039050403900f0090710359030b01c81e08074400c42107800d60209504880f101207189c41520702c000c070340c030640c070119002c1c19507030302c16030b5010240d94100c4200707401103030600400205070141e404524401103c4956207244d500814500001c500071180616403040d540003440c2d000360040c008a0303a118240640d12015650010029003003400100c0395405401c6201002620a0082e034041d240c101d40098580203c62151105003140c0e07a100d203030140a9104003003a165200403088000c1c1c52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631191357 1250 631190107 631190113
    0x6070605040302071a04050922021201060602100e120f040e09010c0e010c0215031005120a0b1003030e060318160503060a061a0f04050306090c030d050910180b040305 73
    0x820604620f00d0170a41002031031208009120412169480d140c2c0076800c856800c501d080603111503514200010607402c0c011350054951850b590450f141540400700722101c5600381c1c0c0503035210101010031340b81d80e03208222a50744200c0c2c0c02da01c18800d48000b040790303201d13201c03829144c541d0303c1c3d414481020046464071980d0759903081c1d4010781c03504800100c034880c03400d01c0c0610000e0316a5001409440c01d10003138403110440480000c2002e2140c0102e60040c080007441c0860f407506c500780156a80072845d4003283c0701454003001c41ca00700208080301d4141c03581038564018500c00c00e030502400380c200800c80184d01d1a04600b040d42e42c00c0c180040081000c0303d404900d4414181010315103444000b508420486107426010002d0310100c1c03513041403140b00014820381e12981c9811342c0d03d10740035981090394140654070610a404c040016140000c0381c0c1034094500407000c5803405d44407801005d030b101d03401c02511018080d00c14411308040d80e82d01c070030803003000a6680b12030000d00c1b0741c1c00a0700210358a42c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631192607 1250 631191357 631191359
    0x9090a0606020705010c12080402040f090c091a090c0703091215060602160605070c050307170f03090f102d0e09060307030b0c040902030a02250507140607060504030207 74
    0x682d041c0070f800c0c094103080c00c000000e80700650b03c00031040700c441100c60801400002060841d559034000300501c48004005001210086c203100500d040c1d544101c5050525000b299089422050031990f881503000f001d0003241d50f40c00d036640080e40d1040c503003201045203c0102280350340980d1725141c075050280d03c801e9004002003018070119903460700079409540c0861804002213072180002e5043d11210729060340c070b43d1002d03c2e05036540d07085a00300e5517040c0102c1601003400f8544005034140300400204480048103055500760712881120b0303100e904041d00380401c280508140d403807007150946034a00310410a03c1c00b0788668a400780050786010103a00960024800d5500c225100c103800000c442100c8203050280000f60745030460321000340042c4451000607910201c0c44c05a13801012888400e66413407920030702043c020b40c4442c0034a400c03260640100e090051070220480130142d03010004018503800e00c0c403601d42184a4035803aa034804c03001c11850380010304074010b01d409103100e41c00800c1c0007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631193857 1250 631192607 631192619
    0x6090209101107060c0f060c050910050c0d0c0f0b07020607021b030715050408030406030f0e030a21060305011a0406050303030412050a090b1801090909050304090c030209090a06 78
    0x1140c8040030003040024501c42c06000820101e14801190050300b041ca0b0b40790428984900105117a00c030142c6200d2428a40740805a0400014282c0135000c8071409604641c1990956050041072441040d40d40001d10802010303019215440a0500039078259420f10001e564413804440100d07043d0005070170220920280c0d03601004190034010350b4104403241101c242c00400d503144043c4c4a0000e920210551102d056802041100c0c0503141e050160b0340d9640d200c2e41b020b0041c1100c00e00801d1201d103480032081c644d0340f010041e68078038141b41c2d4410394540541c03030386003100d80703070209103c40400c6d40d0300e40002c0014004d10842c0d00c400162a00b07910302d965420104000c83d0181c1d40014025001001040009a1405a140e40144c02802c1003034503040200421a1032000320303080403807030709400240c4c00c45400300e01e2000c01d00302c0000d03aa1285a42e4903014800d040d29508440200154410301c41417141428682020020702105c0c6401400d140b002c1d8001200c2d4801901c40c0c41440743d03141c0b410300c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631195107 1250 631193857 631193869
    0xc0d080c12150d1b03150515040b04060f03060b0f0103230405160303020f011a0a09020c190b01030b06030d0e09090a08270a06090303180906090209 65
    0x200c0390800150508150607840d803480d1840008002000e60018220060310702c0c1d68510304041d410350080c4941d0340b01c040c590700070007004d1124001900c031000d105001070130f00980c900800d03128800106115a081150300e00b132101070840d1b040b41580c01a143c9101240003180320415000441c0070303201c04601c100c42d060500c05649544082181054100b1314680c2400c003c80224400700280341500410b0355450341001402c059a2035080000c1c05409003000040c0760740090b041c030307c554a15000300424041c40304040100c2e0340712520140c102e407001500300060030807a800791811801c8582a2410300c40500031410001d504000300f1191400c8010052042c4500f125aa030f81c0180183c00a003100096007401501580e9800d100170701c50b8a0710000990319070340500c402d044080c5d20002207500ca42030b1180a03032000005541109070b40c100100c0c00c071102d241c070003440c0c4100c031030640300c1d81026030541d2401c8902030301100000d4002955842c0014491003180f0420b030027015050740060715170120b8020090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631196357 1250 631195107 631195111
    0x10020403021e0d030c06060810021803010b011b030516031107060302040506030a0b01020312040309060e0f0607080c1903020c090c07020906010822060b10050304080d050a0b060c0d08 80
    0x90b150105004260a03071a040c9084240941500300001e510310649170030300c0a840d5507082481d660240e0800d40030040c15a4015012031a00c1301c03000700c98400402e00b070500b01c0356024125800100c81c0082e0005034040040849001c3d07001e0b1900d18a0045014062f144449240204500040d4146441d2929903c140f00103000f4088528040d4034080ca440d001805900010b8030201303036203030303144d0403980f00740c2c003c00446840c40032801501019181c28240038103555858443c8101090003820041040c0c0762540d00d861091500500540c18041c1c19201d06055401c0380107000301da8454512080040d200508941100c18429801030201c50781c401d042c421040c1000d030250941103001c2c0700c0030700181d80c2e100400e50301c0102881d005000380c2d1a94120580c0200a02c400d00110426021103000e002140d0231a20107070314240c4505030740000c0700408840d1440200c402800d10241030249840c21005c6410880d0030200700710300800c3c010900b00c0010b1055200c41c620b208190300c440d0001c00501d070070000ca19 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631197607 1250 631196357 631196389
    0x601020715080103060f0f18050c10020303040609060b060c06160305011d04170711030d0c05070e060a18150504060605040603091502031006030b040902010e0f0d051002040302 77
    0x588440792200040c0000070b0601000b42515181c14140b06070943c260721070100e484091405001d11030010705000c00710300f4481800e407854050240c16003028100400c0b181c29414040c1d005500d5641e8a84507800103100c608001c440300b1f40c130b81101549079520364025041110200740640070b00d052441820b41e03001c00100224040c141450010007148841000141d004d00e010b03c4a00001e43d12850301c1030303901104440405054801085110500c450305500118590081e000c64060500344141035920090240c8010401e6000b08028001c0b0848141440e80140001c1e001d09441a29030566079040c5181c00c00ca4155940d45102c0742019840c0085050018607040d0741c100010b500b044070081543c8214040e04051585401d1404100700c00c0c07140303064804d07181803011901d03420094070044079007215105050019044c0f4448140307038582440742452a60741611500072004c54078061100010000c4056940807071f03060900404204148000c1484c5000c003c00103948600b94810004400700040c980 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631198857 1250 631197607 631197629
    0x1050c0315010309030c02041e0606020705090939090a0506190b190e0402070605061503151e030d02010507020f0f030d09050304030c080c01200c0103051008060f06010207 75
    0x40170030340010000c55640c0d0156008910000144041c030500d450900458042c40d02d00f050001c0c8040d404100340090795821100c44002d500c901c402103640b054200b225007980015041a4842e207a94075074030840419101820f0001038406d0400510491070407510101940c0e101d00420046103012224541508458081005020b04004502506004841111140017040040c80350700741c1c09400c0310414014000c0c8155913840c003600d80342c4040c1105981140c0610100c09002881c1840302080e00d20481880c41e0600030080001d0402c544500304004500184803012100f102c180c50030300100c0f4851030fa81d00041241c1c200714034001d142c038801d04405200c83d00165920855018044102c03140203562890202e8008540e003407180c02c51060798030013000c659002c00c0010b0b4025000c6003015044409882c0c120340c0c40c220b0b0002d021002c1700c81e10080520b41102c07042620541c041e42c0440c1d0401b215170340f1a0b83c21622421018900242070358010b819000340c10401001d980e0400084014000303030901 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631200107 1250 631198857 631198871
    0x30c030b0c0c060c0d0902032a0102031608090d0b130b0615072010031a04140601031a0a030609021f0917121206030c01050310030b060406050301050c03150103 70
    0x800d588403c0e02500516561000050b660300ca503a06800c0350142680042c1550556501c407410f11030515240a1841584019800710140f15030020003a03901161209001c001c003890b030307581c961500d58801e01d0040c2d80b00c5645800d1402094500701072511450b65201c5d000c501881a0904020042000300700d80c2c49400d80745001103103040840140c030a82c3c0d031f10003140342c0000e0035072074400d514800590020f0b03080201c84483d60126035158010040b1070090528162041101c10700f40801d030f481c0c80c502d050408204102045d419442948107410007a500440b103200204810005001b15000383d00c2582e0040c0c0304c04050055151a41026521f41d034000f010f42160103640ca0090a0600c162240c41d4030711941c2e003030b24081020107018088042d90101003040e910b40c01007130f4040c695082030321081d000e4400d400030380c840c0d94080e8044a01402c511138030200014619520084003080040641c0d8001e13881d1100050192400d00995010b2914288016280e10703103440c01038481c8048401084c101414150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631201357 1250 631200107 631200127
    0x80f04080415111006051e040216031d0a0509070f0306090f0e060a06080a030c05030c06010f1707031106070201140c1f090c0506071103060f1f18020c0f07030c030b0c 73
    0x9250303c01403508800700947c3d01c0600c0004c0080c00781c1001c0c2a4000003440e50202010360280b424914100580c2c8400d940810b1401801030b00c0545000c3d040d001161480410882800703032904151145151074082280d41e01c4406100540760040c0d0300752035550301d59800c08501c2c04180300031030f48034020090820a45180510f12651a40300000140038400e03003179044400d001d018422290401c00c0e4400711425540d640503d9450002248660710f482003441c501e030982c0c0701002c40e0a404894020500e65400e85e5480208021a4804036049040c0800050510400007030080680309121000d000341c96101780031190214802c41582a016010b4a0503108800050302001082c007619001e4174116151900c0380f520f105c400c005112481d50603c601020000c00702c005040c01489800a21540714460080e0388204e24198418003030000001480c5a002c1d48113689030780a094850840c108a0700c880c075a81b02150b003480c3d01c0350400d40e140b56400c0003e000b4032441d80c0d4a10340000c0d100e02d01070b103804400c0e8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631202607 1250 631201357 631201369
    0x510090e070b0306060d0515120a020a0510120906060e0619090207020d0b090a1704030c0b0a02030f0a051905030903070b062704110907080f0408041511100605 70
    0x405480c51030b10020000c40c80580b501d00c140c95200400c074a003003203c2c1c10081054a0f402c12100b15139882403411402c00300c4c803440f0219842141590203809518024101420042c2c00c03480101e0a5040125035011826070034114003071110310354054003000076944d05203400120002d1000701220300070400e2200301c00d0f01404c01c82150301101c407159401a101c209520004800126048000d801403100c04c090200c00d2002040035100d02e0300c140b02601388400010311030b181c503015920020345007800a090400502c8003107001402483c0c0c1600c140c07868900e05400b502100e8104030b61180c001400030070b08541d50704041c0c0c048448071569060150451800021075545d074410040000c00e810610800305500d81c5400e6840c080034628850080d915046400e0034694007402190251120100b5085035005828020b1649001e071100707030384807005641c80300d040c1e0603403038405002102d400a00f0400019407007401d88000700c0c42c20301760340d606c9000b020100c07081e0700d011840c840e441c081d00e01e401d6041166035158 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631203857 1250 631202607 631202609
    0x12031905030c040b0403200420070203010f051e0601080f070e1302030c0a080a0603050d0810080604150e0c0307090c110601090b2b080c011e0510090e07 67
    0x180c54030380c0d929910046840b049000d00c1c0e01c454003241d4017003008005c00101220302080350461000280384520394400b0401076510040c03404040c0c00c0341c902e1005078000041d00800e181d0340064000315800314101d2558088070300031900100506a01101881c400d640140c0c070a030803030824030705000c507405c15203801c1e088000c01408083c01d12550045449050700e03845034a0b584100c40c15421501ea242c00c615000c070560000300301100243d40c1e440041d40d111118800e110031380b500030004000011100c0002d907820900541900b0700000d0b264000034580304101b280c640308610848518960001000e05413090303544281c480013868010010408560320001042c0c0211511100d022a10301d100070000e80b941c20b0201d0700820700340601c10000c04c0003542c54006000c5a00142c6078104140075140c038540381496400741d500200340c0b0340380502c8042007855002c0d000c1c9040c020000114419000c00c11401d85903401d05c1151034075204c004020701c6240d14558807000b000e00010a1100c01e2910b41380030345980712 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631205107 1250 631203857 631203907
    0x450607020f0a0c2106090311010c1b03030222060201140f07141c0212040515040f0201050f0f0315030d0e03071e0f030f060501141c1e111203 62
    0x100c0784031a020b814a540750a0a17034000c0c5003089207507641c0c100104020010901006c442d82013030351039650781d8422202c0303100c101c0c500c209001c00c05003a680c048010350b005008681c001415880707040000b10700460134900030300541d00005243e01104411644640c030082c8518032440d1440100040980c110802400310080d000c0c90f580ea03400c84140080081c2442c50b00c0113950751000c5001c007001c030350104009005a00074411141c18124600c080c60800030211401401d800402c042c08005500403030140c0b00c50105110402d003020034424150305103410403209030031060b0b10314204994500381446102e45400c000d00d0007980e140340c40340c0402d54a0354035100300c40f000300d44999031441e5100c1100d0b090002d406502c090040d0b541d0341c0e040c91859000c0454003a282c452401c40000b40203004815048420307c0c02038407507890171203038003400c43d120103031401c040d20303841d54107044084d00c1d000344211495080c1c440c04400000c801c0e2041032080c000c800c04800186035108003c07054404008250302d100000d070b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631206357 1250 631205107 631205129
    0x7060915110115031a0606130b03090a241a03070302010c050309041b0f0216140315070306030507050406031a1008030a050307020105060306450607020f0a0c 69
    0x700000790500510f140100701030080ca00726404420007000030548410301c0207840c002e080e107494100410109120b650b80d080b000403c0d001d070820020036201c000d9903121491400707903588006c40e916803500c05201030310741d2881201030144003074982049105250b0303000b401c0715a030101f011000b030210b55180301e03e0102a040c442500719400c1004005c00c115040030501801c203000c12400c0f40c111b10207441a200c18180803a80001100307034400d20000f0314000808014500030301d480c7c40d0101c0c1004001c62101c1243d0107000b007540000c0c5100301c4030765041c0100125030b000a090303840d5040240c2080d4581c3c000b64072417800e104040020030110342e104411605400c270402040d8079150000d440e441c00d1070740310030070a000110346c0c00c21198020f0051407080515400078803440e943d1700b04064480c1011501c00d8080341c6501030418020200001c400c462102850600c034500400c0305000114041c8001c04806d10741c004030400010b0340d41804070307c034403012a1000381110f03600c556480703209041501450144007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631207607 1250 631206357 631206377
    0x11120a0e0c0f040e0703050706020f01090515072304060e06030c070201050c070e010b0a260a020d0608120403050c01021212040c031b0509011205030414040b1203070507060915 77
    0x9034841e8421004c1e14810b50458205991781d16000b0f40b1400c582c468000940208442c1c268003007010301554000341d40c003402a00c0200c0c42d050b07c0c2158840301400410403c5040a0103210f080c2564964040c40d6564080c07550706c1d649480d070000d04100c01208028041e24090041c49400b41a1300191603010750b090074205d443e05020003000b85805181e5118000001005c0300000b60120080b0062030300503020754406456071042c110500b280111000c610082224660000751210160f81c080d00320505c81c65008648950f07202412445c101c02208807070005480010104100310041144200d01e40d003e002410f4601c40c8200f6002290040981c4803080c5134030300380010100300801880c100555405401146149001c0031070148001060080f0781c000c0d000f220001c03904000a0001c8003c1030f601c0300045140a0034202900e60350039000c8042c0d0b80160320b070002c0c03210596800c44803494000b000c600540e12001c2c0740c180180f8000c1a41d0040c802d00003442c5c824003000000d003254440079616802c1c008041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631208857 1250 631207607 631207609
    0x30309091a0a030303020a030b120309042a08010503011a010c060f021603050309070e090c0f030a2f010c020f010804020109180c092c070e0411120a0e0c0f 68
    0xc055000c0c07041d0b40040154030110405415501801c000c07040ca40c2e00300b01c05503a920920050710003001c107209559106100c8040a07282c070360048040ba04800f480050150b1410300440260a03d469424012601c0d20740140b03c03d003024071640102d0003210f4102d2241280610020b041c1c0300700144003070f004980f83c1e000c008040d8603c0c0c0441d0308000a1400760103840d5018100140b841d0001c0e10f2110340c50140385400906c500d084420715001d6070b60f84014080800c04e040070803081c0a100701003e5010300851012030081200388040ba001c040290121040c60130491020409d003451001009060020928042e000358880c00b0030300c03d0311802030038200600c0d251400140e0b0307400144d5000080c1110200719000b0030007140c2e00700206182c0c0700c0e190740081d0740d290508946811280c02140c0f00303881c040c01600d041500107140c1e10703800c6222818011a22a00a07011405444412000103600203000494102040c484140d2642c803c1c0130010820810314440d13a11912039290918a0384260541c10750ba16007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631210107 1250 631208857 631208891
    0x8071a2208010203070309062f07240e160b03130f02060301030609050d02011a2b0606050f040513170c010507021b01050705070e07030e03040f0f0f0f0b0d09021008010e1003030909 79
    0x342240d0440000700342f104844102e010701101c4d4607194549c000e17012030f48120341c0b4506450094a00d5440300c14150307580c0ca4241820040001815201030420319600d001503112f0000448c040c0d805210f001c42c1107200c0d41045450030744440c1e440001c5a15200a40b031020b2440106000031103812a68103050f80d01c0b28003490040446408025010400c4206035000c2180d41d0784804100d030020758034081078410f00c6041000702d030740c01c64808041414061011002400c1a00d0180101c02091009030401c0010198142107507000c4031a000968015005800c00c46010314180720800003d203482450102541c0e42c075500d4100030310134000860440b402040302680681c000020a030302c184100d980380d40d41c594103500c401116224403404040c03140d00c0800c0142001c461201520001c022032103403149003000d0707441c41d60700a02c049410700d5581d00000005948086900343d100c00944d44c0e0700d60399414055861036a1001400b070356010000c901c002c00029400000d200200c4510360400a02c0207a00074030380c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631211357 1250 631210107 631210133
    0x12040303230f07020d050412060204030b0a1a06030108031c1b081501020601081902040b0406090c080c0c070302011803081308071a2208010203070309062f07 69
    0x28040d0650440ca00c81c5600e900c01a114444400449520342c458940581e1a03480103540180000c204000c04d0014520741108508018031a010042c5410341c2c2e40c490754502c480c181c40c0600c000c0d460b007025251a0240e07011403071010b40d048440c1c52440d4036000b0182d540380310b100c2c11264035100b56165100070041079804101c281c01c0c0c000700e01e280040c540c0e0004181c1070040300e40d031004412098200d1615480081c0490594482d00b0050407aa481c80148032540100404100d03803103500c940050b0300d075448138001c02005140e8a800861740110642c0003031300420000b03000c1883e641e010f0108401c4c034440018040c0440e030702821b20340c4900003c0c241c0300000c080345800203040842c0005480d02c4111081880c0c034121a110815900d04036200c144004403500c0c52007450114a9007070244216442600d041000322071220b054900d58655698040c5d401e903041101c6400100742c0d0ba014a1062001c24028000c400d0060034500007400e56050b00c0140c03080100d8820300003100081042410400d00c0c444c241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631212607 1250 631211357 631211381
    0x80d0c180f121b0f08030a03140906040b1008012309061506160b0c0a0f0908060106050c390a0b04090207030c05010603050c1f020601050913080403050d1103030c12040303 75
    0x41d400302d1719941c500d950b0358004840100006c0ca058a10891107100380351540c090322401020f0074058503162141502c0e00800b502c00c039080d40c48440001601c1e0803d1180104140101c00428401c01c600c007045203002c1c01c020003004154004a08010f541500084070303074072410044035900d072240209040da0f0110445400000c142505a000b8031a0380740f04c0707201500c030801d800c1d81c1e40980231007407250403181160a441131784c480342c2c00030340140210790007034024103203580ca0102154031900c6545040c1d034048400300d0007503007071150450210608180d4051406d6148200b510040350302481d0423103022451259114214449034040340710703020544207907602410303940c10500070312125403070b414410784401910800d5403081030303200080140214404e0f40184081c43c560080d2090f60300e03080900c401c032034000380040300d10010074034502d000a003800d0182c00514042c10040c540c100089031301408505240c012805107034401c0c4208007120074030004880502d08503284424254440d443d00f81c0261240310503074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631213857 1250 631212607 631212629
    0x90c05070206030f1008032503030b10030e010c030c0903060903030213170c0d020d0609020102071a0d06060203040302150d020d0f0507030b01081b07080d0c180f121b 73
    0x441803a60403045202e01401c5d5020551300c80c03942d2088450f03034900c0b41c0e4640703449401240345032605070b01103200080041400390802103422110300303000441182c0c0031417292012070341d64124192012001d00c0b81100c40003050078108102c84952202809010007880001e1400d500c038800002018030a4041e1640e0302741d49c1c0e03400c11042d80c0380c000c46102d0003050713901c0004a100d250151482403809940200d010750300130b005002c50048603290440503151403501641076224400000501d1030070035081003101d5200000786074031004446400404c0c3c401c590300200455000f4041030016a072400a51410f1902a400c0d1a43e41c00b81c4070503070070290040229107011240351481c00d001c03400713054111510609030ba90b000c01c49900c1d00c03801502c60305002c1d03072113031b0303104104844107903100803408004c0503094000e5283c581803003051282d01054a1144007050b000a1544000d004904070303020054014000b0320010803c11824020740718081c207034401010301381030702e14038100c0028250610f549025243e0b010303075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631215107 1250 631213857 631213861
    0x10e13020d0b0603040c1502030313110a05090a0b09011d3c04110409120f170103050f06070504080d120b0a231206011403100e06010e0f090601090c0507020603 70
    0x1049030144030b244a07c860000903011a443e41b030744003000b16807040046000a01c140542610340c4030300007100c030345a40c5d0400348803880411541d641441c145d114890001c400b1403038003505814031511407c180d00c0386480031b605420651403650000d25107a400042c1c1807040010041490a10310032100d13140c13130401c984200340d0329a034101c40c1499001d8805c070702801289144c008440103000031200740e103401078030740c1448103548400d00d4421080318440d005145408140200e08620440100340d0a0313204803169030201240b04851213040c030041d41d00c4141420100c1c1050f01d8800d145489520030145c600c1005552521401c100d006030707000b0b85203088081c010008481d1942500480b050480d0148842c40505e2001e0280700d2a0102e682400c2464200c09400a80d18080e4107500c1d004400ca10399526000703e07081d4001c28660381c403c07a03008100220051000394545038802080b4440a440031030340003c4802000a000c80000b04541121000c0304001801007082e142101c00e0f000c5d80b01d000b50b00c4000002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631216357 1250 631215107 631215113
    0xb1611180405282105071403040303030608030712030b0a080a060b1e0d060504021503070201020301031205040518190216050c040902010921020402040602100506010e13020d0b060304 80
    0x4410241c1c001044a01c50142d18410100d03c51911107407000f04001c40305003124000c00c0c0549602c480c0304025040c15401c211740c0d90741e2a0141c104d01c4040c070030160710110702042810b81c14002c00c002410303080040c42c9040001d0310355009030a0251030403001d0686541528405c0d48402111400503c81103090322214855803a218014001d07980c0341511419001c00d01000d0559074410181c0b0140340101a10102e11003030391060003819008209907800801c20912141c10030b000c80085104540a900060380c941c110b2400d501200822882c0c0b0041000900040c00715403146130450146018003d007034900b82c0d81d0b0401060400340c9184003d41103500100780510f4200c0c0840701e030140307240711b03109450030000d24500b0304c02111010032002c0e0010380c50b034004101d5081d8203010421411162140407042c040ca40e0040b0301682c2c0326512803001a40140854010086a8407845401c030500b440c0601d02c0002200c00555248040b11402d240d290703002605d80c0c1c0f07419103a0f10142107004084c042c1c9480385001e003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631217607 1250 631216357 631216363
    0x420060a05070b0c03010501050a2a03020d080106140d020711040c030b0109080102030f180a120914030a0803072105010303170c1c09060e15060a0b1611180405 70
    0x342c00c861a04041c00810004000ca1099a05a41041c1d544604141c0b4442e0116941e18950083ca460300b0304003261084804c4028084403c11030007900203140c002c0d40840001c00c404016400303135081007524000071161082960448003048080c041c0961181d0407030800443d00703101282619030040c94030a0040d411030f0140c100f0000da020076290314050300d40c0c60140c80c4c01d17403004440040d0f00300b441d4400240103a0000c0094408265003c044440440707183d540c00b00700011460164011a0141204200f1491840d80710311710300710b0a0703024000d034400e2507980342e03071600000d02803c09100005410015541194250380945e18980c041808996541c1c20040d00210a03207089082c10812440000e04015044045400780060300841005601d80001020000d0846c0101280c1540e1105008810b804c4104810340c0d410380d00d0140700c450b0781064405c12034080300c59030085160100034000c08014005404039a0032440e0000e0b00300e10611100e1001504809850001840a030143c0e024442400f02c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631218857 1250 631217607 631217617
    0x904030203132c04050613031707082205120918040b0a151a0a0c0605090705030d02010b09060603090312011517040206091e1203091005120420060a05 66
    0x40f600030210380303142000480f4821011107019140703500200c003040e8140d02c411760364809603019240680a0070b01104807100f01008c02e50f00301e03000456040610100c1140440050380c581154556880308260550f510f98880c035a01d0710119102c0d802051a1480d0340358100d1142d807588400c41150050b260034a00070605805c141c3c2c0b101011450600130b18504940d03014120b040c1c820150032504159224000c2424681c4040c540508114581c41c1e00000038420340240d0740030341400b81c05082c049040c201810b140c803011003001000c42e0304046620005441d2010410b4229905031281d595a0f607a01c6c0c0402d20318440d400003004442005d000004241407050140400d141c0c542e503d012020400b1500c2160071001030714080c1d84500200078841d500e28248061490103c00360411200002c0b03281c00040242c0c4500c00c88071490380000404a640e46084000c410101d09282032050401d01280c91040c010100204002d02c4803080c1741d603410b492034804075641c03c880c0d0001d00c0d6507503c84050390001c21a401c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631220107 1250 631218857 631218899
    0x3050a020405060d3c020c030d2f0418020c010204050a030c1a0301060503061e121f0527012d200306011815020703050d030b03030405090403020313 65
    0x101704440903048002401c0e500c0c3c103211450f8180005007413080c0340f00035440f52810410790304c000c1144c1100105207014540e05200305441794070312801d0703c81414444516522003600030100810050100c1070804e1802c501c4110221001600e408208180f64020b102e84d4012550107080418000f003080081500748003618502201170700c1d0300c0407002e5942400d00080c0112408a8400d1001a41609185c41180d034255050a61024141d00580c0420403043c908a180d4425406c030380c00e018502d600701084500070404a0100300100e1800404d000c6c039403074561000020386010591801d802c4142504400c40412140000480c0c909901c1e0403404680c41001c07410741c4003404c11243c2da030701a501b035100b0340c040c0a007a400c8030724543d6000b00446129401180c0c1c0c4800000003040412050030308142c1c0c29200c200c54000b4500c0c5411400c0c41131030420034401d450201414804031901685000c000c2d5012a00240c1d01e510090711a40b40503411401215a03842016090113000902096801907001051007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631221357 1250 631220107 631220141
    0x9020c160f03030203030112030528030e0c030a020f150a0903020109050904260408010207050a03080f09030a030c0302280306050409020d02060d0b0603040803010501020105010b03040f0303050a020405060d 90
    0x1a541c4800c6601c03900521001d00540c00620041000e010025204110300344a444c09526101401240d40c0c3c9402c10b00520158402c002901000301607018402e03580b500360200006c140101c00000060743c1c8011401009006e40301d00c2c118205240c4940a90628000107101042d440d800496002090402184400c0c1c1c0001d040380e50000b80d90400004881c01541c00c02401e0052844682d054140030724400204071030703403070100000100700340c080c07014001c0c0034460800307481e10500e1410001d1441d0000307082c0256201001c0d0500c0241c80d400421071380c041a0307d00b004070b40028001c509038028002c2e00b007c85a0f41021625481d40d4052074111111040183d403070400c0840e807a8008c0c4811140c00c07031002034200818038451800340c54010040e00c803001c0d00444c0824181428030100f03801c1d400959044801131004401031019607020f000c0c1e10f01400000425a0651409031107a448258000174080c0503d0381c0c58020513001e81031901118042c02d0040c166569400754a94140c004043c031140342d0b44441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631222607 1250 631221357 631221359
    0x21070b010303211b080702030c0a06050411040b0303041512050723031605090d05070303050705010c020a02010c1b080f030714070b0f2d040303120506130b03030409020c16 75
    0x202441203001c03003144c043c0d4000c0e40e401c10080556500034080c00020940c44280400300303071202c0411268105c030340b18807000304180c14141fa01501e0300c6900c3c00c0151140e82480d2000131261000420341c1d04039007030040382c044040d40392441a03c103003c418030034030708140c182810005031541080c840320585001a100c010041c4902030350902d0790000b81c5022a42c1000191301c035482d944100058508000028244592010940d41c2d961800c940e0b94012004204003040040030702c2000c0c4600400301050b03001a2800c0b400c2680024005114030a00404d0040300451030a103500c070021000002d01050421216103c0030700c4461543c82c0c111100c1115015441c40300e82000b403002003041c3c01103039440c48040d0300300b6500ea400410150018804580c529008050301017071a000380e16441d040c45244240c9903683c41c15420001d00940201c580112898101402c0c0900c5444001a000090480540000d43c40c102c02000a003507201e10707800b154440f8004241c0543c013480124040d881c26090740d0a8640c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631223857 1250 631222607 631222667
    0x1509020a1701031e020a08060109061a071e110904080c01060f14090702031e0406030b0102060f040611040519150809030304030509040204031505240321070b010303 72
    0x18803002d00000f00440014005644c824214030090030780382d03100400010806451703142661030075100741c0c00300303190f83e854240400c5160b420f845017180004640c94090301d842e00310b8a0b000d804003e80c06500d4020304110011005010654406441d5994018410b00d054200342c24908940d4010f640910215482d0540c005451040320300308104032906480080c0d0000d01e072908008658400074514000d5000422140c1960113044600c40d1021209018207602d90b400c0ca0001802c403500d000d4841c2c10355004409014848914011190b0b02681c002c00102e103840ca80d0300c43c42c0c5140075030741c8581d03040551503c1e01000010906030480c1a554a4800b01c0f84404640380122004007081d80d480f5400c0c0c2041001c1000b081c0700384020198280c0140c0058989607407a0740302007082c2103e18240c01c2282c0c0d02c0d4240181c103101040038516040101111840c0403291f03a00091303c51070440c403003008120314071074202041017105d0280e0710307010303001429103105603503908010b049100600c1c41b1550a2804032620444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631225107 1250 631223857 631223897
    0x9050109060503100b0f1503070f03051311120312010306050f040b04110a1505071109150402130b04080d022509090321060906140f131509020a 63
    0x403194003d00030000908224000401801403d9a06410a0709101c19400949540e0040b1600510010760720b0f58a1601c00402001100401da40300b04040c01c1c44140024440420686154240c02130740c091410641c02c1c000030507070209513209036030f10702002c2441501fa802038185a41224069030003403000b40d50b01450709140c0c40c01114001e01d40b92f40c0c140881c012032540f50304a10344083c0036028201c529150035000c240e0b801400341903400600c0004601c8208004042082d903800c805554807030450909800086032040002d4440703000b142d011503840e10b00761000042070700800848916a5841d80ca90154130744034803000340003a001d03200e11235440d902d034800b800c00f0820584c0c02c4080e0040c100d09200d40034010300ba082030141c042020185045000c803c11028544a200e0346900c0022210320b0701241c4001d89100d94000a0840c80f604a41456601c1d2445507240c0314000b00c1c0c0c100780000004a8503401040b248d1070032040c50309407070004503540c1502d5004102c4940c00d500d449106441d011600c41d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631226357 1250 631225107 631225109
    0x9060e070801061a1b01020c0a0f05101506050c07050402030c041d010b0706020307030e0114070201060608090604030e030a06140402010824060306180412110303040305160602040504150905010906 86
    0x1300008080028182c03000e880c908109540c10ba04001503d00440301150600e051807814007aa200800e610788881006020000402d0703201a800050120081003455624400400d11801052220000d0b4141c9114801e0140032f025000040c000c40d102e040404095806030894090243d011000700e400380703060a5010820380c12a0740103202580361111503a5030001030f42020b848101816204c0c1145000d202c028064500c01030750a00c042412460499002030944050f0f600480500044009000f955000801da02ea80640c00d82010082e0541080109103032400343c4101604103880c0203407080905102c503910382e00440c000d80e2640300c1503c0d07203218071b803042c001141110026001541050100d060203c05135610840041203400b501d0280200746c8416038007180e088880c45008018030442d1a04a40040d8000314164010340c1036184c641d502a01510035082700951700414490b2001c10011190115805400b000c0c20a00111020280b91903540c070003401141d0ba0581441c001180f40f466500c1070f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631227607 1250 631226357 631226399
    0xb0103121d01030f060b1602041b0c2d0501060905070e010c0215090d110a0905060a1208040306020d050702010f0c020c01050726071b1a09030109060e07080106 70
    0x4200e41d1074000540040c81d00c4000c07100019200c0078002409240c2102134454203404070b803541031681d0741e0700c1080300b268844c6000f410b2804034038013001d044950088081b03800035848000c1c0076149c2c0b500e40808214403015125090a4440909004204001900064100c5404440c14800b0340c54549081d603100d1280b070b80a5000400041800740907240408041c00c7c00381003250744c00c1c81d080072040840c031000c41062042c0c83c4401030080103001b5041c01c12410b0002d11000c1d004001900340100002d82c25186032198800d480507189030314090110300e8081310011a800f030001c6603981e01c541c10f504040c2c00100c42c0d0002551a2901c0c0c5070032520303d402070544181007640540300c18802440191055000624240c91040640800c038404035020101c2030704101c3c11f50401e0351170b003032686030002103001030719200c948000001e1410801c1461001076588460320607031059466030703145004240144100440903000c14148000104c0034640441d1400548101500a2000c19121800040140301c00c04d080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631228857 1250 631227607 631227647
    0x7020d0f14011e051015090e010806010b090607060608190605160206011e05040c0305010e0106030603120318060f0506030d090803031f030501063f17070f0b010312 72
    0x41000f0641c0c0415030208683c000022960f848a0b100e4901e045145210f0b40842da8540c401d0101c0c50302112010300614070200200042d43c101000d491860145200c058013602c03010640000308141604001c01070b0201c5002c8840c00c0c600c0036060510422003942c286d4a5500d131101080120300034900b1201140100d40040034240d00e00380c440c0300040003078044219011f2601601141075540d42c018004141880e6a000c2103650408003c0d402a920691140d170926181510410003c1e0b95980341c130743d8032400381c14005548440c07403034010075080412400400241c07500c0305146041003260b00081c018141078003100c00e1030021440c192620945802413844541c400e00004102d00848408400c807810411001704c5241d42da6a9aa406e584c0a0382108810340041c1a840740c43d0b8007504101c401144c880c0388508042d154030300802e01d040c0000a00075050b21440e08217241160454001c4031346141c1d0010300204203010a050a044485c000c0c04112060482c17250076121080c401c0c01640151481c00981d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631230107 1250 631228857 631228901
    0xf0c0305090a140114100807050d030f05090103110705071712181203030901021e2104020109270e0705150c0106320907020a08030a0207020d0f1401 65
    0xd500c1d01405040382c00f1099034031074101000031a041a64907000b0b41000b040f90461341d0401141a041a00350340116000d031034202c11741804268011104041c503030300780c10035940ea140b0780e000481c0940320510301000080780009142c0308009001400a044514000201044580d060f45094442c260095151045142400103401c142d42d2520043c0003604020705050102c11110741d66821500212408402a54040b900c041c0990403010500344840c4c2c80c411440c07a104003404034403040c91000c00e080c0380340c2e04060001011a400f81c1c4400380504141725042c0c0c181d001d8403035501e045061004848659034107100181c2071601001a01c442a0f0f2001819100545031002d0b103626140c205403001001076403107110010f00304241200e003000440d641c00d411451602c042d02405070f004100d2074024000da0652040154142e40441d0950099500490b002d50387e80b12241d000000e07014804020794072100f200c110b002080030380c81c0b80d42d41c110702c52400404c40104c211407135400c80d24025000410500c050003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631231357 1250 631230107 631230113
    0xb0306130e0c220509120a030507021204090e01140402030a030c030216060306052d01030c12020c16230d050a0c0b040503070816090c210f0c0305090a 66
    0xd0000e69071180700301c0780d14001041c0000c00441d54001190968031071030307040403080561405035603030000352240203044402c42c1c0d4100b041c5910485220004069444003c122018420f000040088400320241c40c1c4840d1100c1e5400b004014918078140c86e5880c01038034bc1d0f48034020008252080d50001c010782540c0701030351016101007500080440850040249500000094081f004080e041c1650005030355030518090008442400d5007500f000c0340302c0078040c40c850009078010003140c1c80a19020a00c801c0200054075040300b01c00c5078106240c000b244105000c1400a036902c1004d806040b004031541c1c0e24200d16640800e0006002980702400910102900b010401d180c0810b108000b118081c919a480304000005c1c2c54104051011001404004a00d403c001d080c014200c807802a0401015100300c80200d03000ca17106041344036868072060315140740107075960b41c0d0090181481444490460783d0b844000d003082840705103ca0318204456415030300c2440345512425902004100c02c0503161 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631232607 1250 631231357 631231361
    0x702010e072306120f070f11071a09031507080705040303050a05031302032d070e1501180603230c12060a150201020c0d02010513060509010b1c0203070b030613 70
    0x58440343c000108000b01d03654005885000c501c190800b103221360715402c081600521208400c0c00c1c480030404080410720b141800440c440080303584204401ca03034084044040b811038080e03185400c2d40f6003e51003411601d0900c2c61105485244c2c10ba88140881c2d0b01d6034030646050040d8000030380000c0e814051070101340c0c0104001e54010201142c140f03001c0c0029400203150504080d40c2ea85035040c80c40d001c004050340c410795685107984040141c41c03084d00f41040e555030326000601d8044106440c8800e0340403a40200a4110a000b040c400801055129030000d00038001189002a0005000040841c1106409680e41c00b864201e011329191041034203102142031405445254485600d00c8009000444121000008480c58002507200d41c00c178602241004100b811400a590600080140100c41031844098080d80041c00050702d4586000c00d82c0180108070f2055003110140b4100000d40f400120b45516191089049407031281d00c03602c0780d420501050b61025004150140c44085280842d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631233857 1250 631232607 631232669
    0x706050903100c02010207120305060607030302181801151d09070207081903110c0105040b1602030d090e150a0504180c03030315080a02010f05160c0e0702010e07 71
    0x3000c03102e1080c1041840000c4907588042500980e50005480301003020317102d07c00410180394241041603261010209a80c0e110b000740040401d40d00041c00014880c00180c0d01d9803014001d882146400017038860081540e400307000c3d5109400182700c0c00104280f007002d40c1c0ca054503c10324051070003403000040c4070140101800503420b6004103103020410340700030442044072802e66410607070300c12001d040103008450101c03140c4401e608030b80146101a6001022242100c4610b0707695582c079440172002c03410691b020071000f5814054804003035032031903106038410b050f11601048114075455901e4501c1a2000404003942c1000701036404100c289040c2e0310131007010a01d01038040a8081c0c43c0e0301c1c120740c805036402c1200860703921004074240d13159044e03580c006807043e0001040795513256000a0401140301c3c144108025000484070f0507000341110404100f9030041c0c0a1001c0c54440c0c0c60a800c42100700c0e0110019031a004510050510002d051001c0f5140c4469095604010185481c460a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631235107 1250 631233857 631233859
    0x1b04021c06170307081608070b090709060501030e070e040c0b0408010605010e04290112020d02030901380a0b0a17160c060e0f06010303030623062b020c0a050f070807060509 76
    0x1172000a01040d82700560034814241079018144071414101000101c0784647c0200e41010b2900702d0310001184001000410382d0301c14000c100c4942d07654500455000ca042c4c10014110f94045400a2406c00542000c000c0c0e8400762075100c00304a2071020f01c4100c07580700f8581c40c0380c10100210303803141c1d10072b038201c90148101c10300d00986e001c1e00e1070340d005c01640c2c00f00080c09200b43c0e0000c104040c0c10020710510b1041c141d001d50500d40720203540e0702c0e035400074100001c10442490f0090400303141e0703a038148440002c2c41310f51265500e0b68003841001d403040003201000c5421403801c200142d00780260613500c03004842107465100b00011107032154001017480710b20300411403190380f44000c5071840802c0f8603402140700f079401050700350411885400842b1156000c20042032540140c140701d0350f801c1c0070303140c0c0c25139090080016004c036048000c005488005894004d40e02c00529450880c001081030000140650115030441d0103141c445990f0300151b06c03c000c00c6410242050128911031001000b000780 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631236357 1250 631235107 631235123
    0x1120b040218030607020f0304091109150d061403030a1b05150a060b040b03040f3e0303030c03060d0501062411060402031b04021c061703070816 64
    0x200090205089a00c0300c0030b9020398a481c4181e00003a0715040140c02d602c03d407184040e14035400c0c0441825500d010f140652245075860305c0040c28145546002c0c0d6604c0c9000804560324548441e89009140d80070b00b100d5a080346c06c03c040403c546544200c40f500c044d002400841c601103c07038004039500922400c5040d13141003180401e40100b9410000203030752002040c1d07200e0190400d2801e100494215900404502805100801070f0f03801c100705603540150803c1500c9038209451800c03981d070200d0454400429401160488009032000394a0005107071400c241808280f01c503800c2581e20f000c125044907a8907410000105a0300b0150f2060781c06070b2044002142d455252012141d000d42c046407150150409039a041d02c1c1e440d40329407512032800c81e0300302410881c201900440d4503aa41e00025440e0500403100d05a03946d00d61764111400d611031400070352220800c040c1c000000c0c08a500c205105050091751040341e440c004000c4a0480c1d501c48525460803805440e5074035546181202039660700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631237607 1250 631236357 631236371
    0x1f1806050901230f04182304141606030e011503060b06130306050709090c0206040b0916090207140d050d0c17070207030611070506010b0c030405030d17130b060112 72
    0x2c08140050003d0440c200501a1903d003081861551000c540c40101192414030142035070704c2c003007c50203071200e4002d0b404540d0aa902c130b09145100b081070b1164400a40b1840c03038202c81564000400d2400c1d580c0640d002c1c0700b5003131000c13903890030780b240d91241d1919007101010810001d4841d0307014101c0840c001c0d00c01c034180103012405215445071a4002d4070305548902c100100039900200139009443c0100c4108a4030602d05030083d60740c0300003000100380c1400c00020414181d401c01c0031140442c4120490902c10352244902c001035008000221a0229088000c0300343d008085603502500d10b560703913190b040c07121451405004c1e02036a940c0100340b1840e6500d40c2c9518102c0303040341d8424440c81c0c00820702c252841c40c101084501c2041c20070460b402c14002c400c009a0302040c078504450044400d1a100e01500101d070b41180f250350f01c026803500ca0000200002604000151483c3c10300c503a143c10542d49803101041e900183c0c4100400c0d08001c800051903660080816112031940180009420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631238857 1250 631237607 631237667
    0x61906030203030a030b01032d05100911040302042a0e040204050a0e040c08030901050901051803060f160915080403030b09090307061b080412020c1f1806050901 71
    0x143d880f000f13039840001d458820103451940c140c000d01100d11507403502c640300e160b04c1d10940c0d0b825aa0000d00700e442c1381e460b4001726103044165003010024000460b4104500081181403000f01d40c0b01d41303c00c0340a182000c0c1050107444444240007015000b1400c2e4a81d1112081022540c001c02c0102c1c25502680c244130102e1142c80305002d10000d0300032001d2302c2c8140c2c2494202010007422660203403803103a00c10030403070695991010558850120030300f059600c9140306001c040e4000e02c0d81c85030a40500ca0b62041203040b00d01d41800e213000b041004805401c010410301c045500083c00d005084819402000f2480c0710b030b10a01e42c15a1190080c070f40080d24141541c0000c00030078081d90b005140754804505581441440d108001116510050780704150307011480203000780340020700241c9072100c14003000ea242402030102900c141070040501400382c551005100b03a490640580400141015400305043c00e0b06500701d1051720030b03907203134107040640090046402d1010034104100807000303103400c5540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631240107 1250 631238857 631238863
    0x108040f0f0c0b0901021c092309160f020a080405280803041503060e060402072d030e300a050a05060402042901050a0c050d0f02060c0705061906030203 67
    0x240144415113642c4041c498002172900705180d00d200805a03201ca1500e111a411601d0413007110140d0442d041c9080c96000032038164901a0000c0d0741044214080000c141c4601c0c2c0440030100c11601e42924038a40c60200700c0c1d03a00207040c2d000344550004c20041c0011300c0c001034500c810345080003801108001f10601d12144502030f60109000354800300301400071903c0d0300f039580b20315051458100030b1989001582030b0001405888103010380d500058a10600a960030003c09070503a06071030a4140c0c9031440002da001c2e002020540c0010803100c030400d240e00e030043c062202500c544121000403d49510015010400312030140458414010351900040e800d0026084160140020385004e140600600050340e1541c160080072111204c000400380503288500305030000207181554842c110440252020400100050404d110b41000c1000c004da100d01e0380d48080f601c5600b03544503900c880b07140306203d0048810081c810f40000001130b000e0b008402d00d10005080f045008101c1c555680c012a003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631241357 1250 631240107 631240109
    0x50a091b0503070b0a0903020f0f0a0e0a0b041a102a120819021c0203040803040215162901030c1422091b06050918060108040f0f0c 58
    0x9003a03452400030030607454240521030040580e484054648070003601c0003442d80300e0318003000388103044000301c0c5035603615900d04002c0180c1003d000f000c0038a45030748003507011150841d143c184060a00b0f01d400e401d4203184c047c0c0ca1030200300394001c0021100c9a810070050001e41e1005004214008000440e44500a00601458007a08081680107903080c00e00344e40e150004135890051002c41e1050142c000d2109040c4078850340018001a119036150160102c01c0e40364100c1003d851340040107202c00d00040c8070041d0700503882100d80050741104400c503502513016403560708980c00c9400000380013003540122640407081c0c0304120144440920400960301ca102030300141e407a0020a40e052003541c581e20403220640e42c04a0704003407812401489045100b0b09020300400d8182c07100300c6113080080a41035101e104c0100e10061807119100c00d001031081d0070421409105000c0d01c10008402284012010700400c2c0c10b946e9800c0d0ba568940307920482d60081d65040b1844104080007201060140303103920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631242607 1250 631241357 631241393
    0x3041113021b10060b030103030f120c05040905130c0b310e09030c0307030509011b05011a09040804030803061207140a0b0c15100515030103020a120510050a09 70
    0xe550800d0a00d60107250103803060151600c9444c085060105500311000d480c11030781d00d03140800c5071044c0080101d500c05811806400c0003428030f11070700c000c0e64001000d441640e2258404100725550100b44121805400b4070152165040c01010311096101fa030041940a00d0f00d52050807414100103d001000e5405c0030b006072003c8184000c0c0000d25041410a8002491718000c5003402071040c241a10380c401c045000702442000543c5a0660f400780540ea1180c0c110a90003541e030303a0441c2001d40c064041c0149a5a00e1101000a5035036480c00200b0503006a4203c003d0b1070510b42541d4420744183e001174000e581c084424544901d486800300a858040c10303210800c0c41c11174008400303103c0a5141078024001e811303c20b01005110341e60010301d1a12051500b48099640e8513540b1501001d4142c03904856040001d02d844215040b03080070045040320320907181e00450320b50b40c3e010401c00b40c20510004050741c00c20032400806100395004240c03c10b108a20001c1e08030704659078503a1022880c4001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631243857 1250 631242607 631242637
    0x8100203060f011d011803080705012007050a0209090c0603092a0d0f1104020d0b10030605060a03200c060703051524120112060608120304111302 64
    0x580d414003101d42c0b1a442c0d070a0030400e00c88134494140350030940e0498000743c100160b0000c074480d03580d03003418508003d681044072955152058201213028002904010900341807440f03003001c1c001c40381c1c03080f40c4490760080d0140c14000415400c100c5110406421800c03548144420481240e661074000d50288510b04003c212901d60000501701c113045c0143d402614840c01d26aa007290b45034400058502035219014070301242131458808019100101507980152011503090196002540803241d0540100c4880c00c01c010311100490a541282c01810741090050041c2c41e61140039411000ba010107032841c0b8010b8203810001e240d0160420461201140d000707806201400380c040c071640340c00c00e182d0690296800c0e5a070700030400c8031010160112a46400e14030b61081d500407002601d03521400c040b001d40141d6500c8042040075002c2c040e05581081c034104000541c002c000800c0342c0007c4c8840302c5e060841e03440b5150418100300d001d03400354005c2e021004c0480f0307007002480108002002d007191 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631245107 1250 631243857 631243861
    0x4150602010c0203160f030210020f0d1103041a07091e1409160c03110d0320030f06010813060e07060908010b030a12020304090509061602010c0e1908100203 69
    0x4000d00790744640b2150800d54004204c0d141c000140e00b6800207005410860a100310b42041c90300300c0c078012000b000d2100c21840406e800c00b01302c442000400068540540c2030012412804406c1132030b20003947e00030442c0241100150040c8a051800b9501c070263303051000700c451b6110361840380522000303070182c40800340d02d0301800241190000000000d10544c0c1842c8507150405100c46070580e04045581448043e29446d402c1502c2822582c018181040c01c1d142200400e240240140800d00720101c1181d136000751416440c0707196001e51f8854100014a1001503c550380191807006c406441300c0300c4428580f80c24004a9114080d403070b5010382120040410340c1ca03098005041e070015801000c943c0c0d042034074101e055900040d120700c1a0f078202c0c060b10802124900284d2562043d07512011140d801d01c420410585004180c043c840da8101c041005030034202903089080350208042c03400410000c0707455203118100403250802c100e440418802c20305444203d40391a0441205017903601c2500001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631246357 1250 631245107 631245119
    0x2805060a0213060219080c01090c09060602010e0f07030308040201110a051b0a050315060a170a020301152102150d0501091409030f031f0b0d24051504050415 69
    0x141140c003c01c21803001d01801036428600c01400414050060a6050080360344050f0840c2940300c0325820b640594103000c46030f0b44818103809001c3d50300c01c03035001d5464000f2440d40c0d0000410000000145040940b0f03402d402c6643c192024000030b0426410801c00c01210001c1000030890b45810700d01030341c01000300d0002a00d0000c3c2c03d0b9800c50700c140c010030a001d0208551380380000c10740c1030500855024a111f548480c007140030034055901241505000202010020340c0200d02406c6140c0254000e001c040040d00c010400090746104900007181824006482d2a1078011110a803505c020490041c81d01014803510385a04000194154103076a880100421400f0344101c140f003506002440055203450f5040385e44900403118001a880c41c004000b030584c0e420350007909134080024001c2c040b9581c840641d2421500400d5000d0640d41c40e0004500660480d040c151070880780300c04124034000d00300301c00d1026500a41c80c0281e28841e090001046070354032030207000c640315044580760005030301d007103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631247607 1250 631246357 631246387
    0x9210b0a090210111b0d1b08070b030105061b100203100611070308030c0307030b0d0b151e103c090b0307031107240c112805060a02 58
    0x902d41014400313800c82d4a90202004038103a0341c0b56006202d5450040710f02408a072400031004c0000b00110060781e860891240300c05400c100340c0700700c030045400321a12210810020300c800c1c060158040010320110005645c040c801c40d01ca84c124005540544c050140324200b660001d4410b000a10710303d0005002040c2d000c0f542d036011103020401482d100d89191180c200304d1101412102c03880308000b002070ba485000303800c007401c000c1c4081c05008411450f428000c08110007034544100002c402e0724072100ea494002c51101c1c1d100400d040d034071205d1801e40104460b0301920b10034803040c04100c8602078030500552150324120f5203020500341c0c1d804181c41c00103440b0080c0184080910000034428400d0401d40f00c29681c3c48000e9050001c5d001c0c0355190034021034090a980100f0348203a51042c1c003030501f0120002d00c1d07102d80700101401101505103041d01e440460041500c0240d20181c2840401e103e221070518418007004483c400e40c441c66181d00341460411221001c1044d00001c00c804458918 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631248857 1250 631247607 631247629
    0x1022104090c02120d0b120f07260705060d0b03100b0f09041a0c07060c03060312091d10030b0f04030e0409023a140106090b0109210b0a0902 62
    0x80c3c4050140140e6844019050740210218460310b26554004140789460711007980c010180c0c56411101d403080c48046040e913a03159400307030201c8103103c0c0c8043d520040e00c981b4a03914074000e04000d01b00003400c05092001079004144400d56841e10b50301c0e5001035440500865442401c03a060200e041c100c01814091a06000390301c541c000c42404041001054501d210000503c040244103510f0392100d04003401300780202d14026001c20f1400c10280607030b80d0507038800d400316031203402c14007000717055240705a60041d101d1146c001c40d03035580b094103400b0100001129a03ca8010089090300e00d880f6101c1101c0305008645816030201e44c0301c01d12041c15001207120310041d400712010b1061420341c1d40407070303113500000d01c00c0d2046108100d03192220050491040d0000e2104d07849907064807806003031050b800d002c0b50641039103035480c004d00402c1e03c2d031990084e00d00250040c1c441908581c5801e40c0002998800840082c0b039140304051000090f03c8007400e9401811440c501040403209401001002110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631250107 1250 631248857 631248881
    0x207050c151c18140105250e040209040917040f0b0306010903020f040e0d02030703080c0906031305070807030f05060901050f1503160602011b111504020102210409 72
    0x1c14040c0240888040740b4803082484203841c04203c81e00c580082e03003403014030781200420605058071201c14400055001601c9403482c11540785c00400605a031020710300c4402d20341000184d150798200c486003059001099202405000000c00382c1c1180c132000c140e12052038964181d488002130410444d464010000094402ca401c030300d02d541401400a01511401c2c88003d0145110030041030607540c036548042490041031090780c40c4544600002516031707129543c2100454889404100a50049400e5649060340039042d9495900c1e00c21954400030319480b0100c46512a0b6000030402c10414805c240c0114401c104000c1090740307a2034032a041c014014074100c41d581c940420048003065080500d0b40250440d4107100b0044034210110b800e200c040c086202c14000001c000141342d5505500c84082c82c001e404040007410540c031005c40b003036030042d40108406d50241510780f10311391358509007079000391050040382d05a004200d0326540201203200c00d4403840ca00494100700f8084603004402e0f01ca41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631251357 1250 631250107 631250149
    0x317131d01091107120504051206090a03052a0109150203040b2a0c0d0810060e010503100e04051606023004030206030411031c021507030f0207050c 65
    0x1440346580d09208405104900030349490300a6030006280ca0070450b150650030030182c00c1a0554160050701c168410b12400d4000d03000801040b59103000032030003078058920781001d018603078503988040303960385c01080161030424a8040149480d84c0300d284d035001c091010500215000d4602c1c18072541505610000030600b6004200300701c006281c40134036660015102404490f011041080d00c240b81040100c0d1220082c400100c00c001075800041070001e490762562441c0c0d141d5500d0304803010900480c0709480c080b46401d140d880c0725601032070103035a100e0f060f903c0803407425581c0e0440b89a0300c80c0c1658162010742000380104403c1081801800240c02c240c0010600c2e5450143c44050000030442c0e2400e06003041240e03641c402c1e2424045400942e00144001e4403800c0c142001d5034030011224015101c2d1040b003212081c0954214080800300b42e003030700900300d6190100d09654004034014081410140c0c1c822900c0101030035880135214050086000344070a080c05801d200000910700851401a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631252607 1250 631251357 631251389
    0x319110c0d0b060d030905100315090903090306050a1404110108010806070f050c0c0303070b010e060a05060f07030908072c0115052b0209011d1018031713 68
    0x518003007a50b0f40c000109071091050b0807860308003160b1001d0a504810762101c45011052092036140c6c01003190080e240c642040304690703c0d00c2581c00c49150f0300340100440c2c040b080800102d11030380c2c01140d0200c0a590042171003d940f850310110000107c400f150311551401102507256800303508203001d403d081e8010041e50406070350142442c0c000780e50b00e004100000810b02c21f04081403041401c4413001034102d0751208481d00d03000008010900841d4064101c602c0010300928044002104650000c2c00c040c0c905078240f0040c902d140e003c00c0066091141c480c01c0050145020881d03080101500c07294807141401115030314446000c924403407000b01d900000140903540b004208240e00c0c0c140303030a0095480c02691640c03460701c0300004d200381d000b61070301c019070704109000e03001020080e20981e5440c445440940c0f0310800d03030301c40c42d11040c0c101d6a04480121000d000c0d1004160f0300100310344c0d40c900e0681e81c0e074415007014810425001103c0005c00d824015555042180380501036099400f5808 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631253857 1250 631252607 631252613
    0x803183403031e090b0a0c170a05030f0402040e0f0c10110c010f021002040623180909030412120906050c1f0b0d060c0806010302120c0c0319110c0d 65
    0x140c24004401070398401c885510101c0c441c0130b2243c48000741101d1001644401040c54081d00404045406440c4180d22210850b05402c0005c1112412601500d03081d0071510780711000b00d00721744011b00883e0883d07920f0b40200000c500801c2005000f144400040100043c0030b41401480082500c11809110b506a0540700d00c00e40495114890407081c07810714584031403254201e282080501912a040348009070114295502c646150700540c803000348480c40c0c444006500315580714808031058245001701c1c20702d00c503180031011550803030f0390107088034145501d581c3c0901c0c0c0000758030030440b180ea414000401e02c1a400c4080400180000c0c01e195081c0f044001016484120b6401c0d0111000004082454140415800210081c00c0608024019034103441c280c002000109086000701c0c0b02007000511561290007160b1075404400344c8012551a01898120640c02000303404c905800244030820b00d0003c1204030030465100b5583d0034401c410500d802a01f01b60f200202a4011001c0130490008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631255107 1250 631253857 631253867
    0x10180503030a020c0a0c03080d0c110307060e030d1103061c050d0c030c080703110c100507241401090614101b05010c0f030e0a02030703080318340303 66
    0x100480202c0302503910485a4012410405000b5000305101d00c0e090021091050302d10260002d5401e08004000341c040807241501c001c042100180503c2d4810064600041c19541220840c142d6410849042c44042864442914072030891291110310100030840e50749850044010a180303000c24809031000036845440d15500c404030701c0d00601c900205c90b007042500c2440c0a09406800c00ea1041d107401c00e51400418070929061900c1c028403911102050300d2406103c0c000c4103a14603240d061030100c6550711541412600d904000c00c1140041072420207c2041c001c000c3c401c180b0400c6d0107420b41c1000c0d100c2c0101e41454110001e01108101a05038644600350b03c4008804d080c01c203020f413500b00c030750744442c00c100385040146254205038140141942114480318008041e0301c1c10320090300074407840da9030340c0d480070030103981580720020800200d41190021500001c210440031440405485000e02d8a0182c80e101c0004080c0030340401401c212580310000101444d1201202c1d07585075840083c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631256357 1250 631255107 631255111
    0x9020c0c09161b02060406110d0806010f1d0904080909010b18150d1103060a08031e030615040b071703040b060f04021620010203070b0109050402011b051018050303 72
    0x2060200341840c5110038a256100568800d500801c0070303a0b21b544600d00141994606d4140c041c03144200105041e5250288003404d208501c181d40300d000a03030401303d00310390103c0b01c10b0710603550000741e0000c0421038881d4064644514081c2d40c4250341d4140d0704080c01401c81d4141e010320b64550781440101c50020005144030550704040b560700c450020290b11000b0f4a20030745503070034001454640a160a00c82540207544140c13403c861617080c01d5580d59240b40c80b80701d85400040e0f414460b6030340c28080240c1001440c0c100340d01409641343c40d00320303803642d2041e54080d17044981d403a000801c42600b00031130112402105002d44c0d80c0641182042c0c0c0d14004000307070140c0440c2c42081c1041d448400764450743e05484420b8110741448040d1080c07810030120460018174100401c041c2403082c2e030107035400003045455445d8048120030b41d41c0e00c1d000010008003c090412810440380004c2d02d94403050180401900034015406005482524413440c011102220b01c0140000c0880c545480419008020b903a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631257607 1250 631256357 631256401
    0x180a2c070c150f02070308090c0105040b09060703090b0c0a060501060318061a0406030b010518131101050f0307050c01051602150c040801051303141303020f011809020c0c09 76
    0x4032510b038000d103009019110310801c000f45248042490400d150340030f141d89000720840415520591030b001e0044956100f80c0c000c0c10101d038001c00c11403500c4e0030140000c001c5640603203441c007203454940b8003400c0355500c0040c01c0e00055100900340000e10903030f84100e600500180c20100810141e5440030620100240300c09002c040d591801003042d08940c18050500c500300070b1040002c82d0300c0c0d03e0f04a05410082c0245802080387c0004132400c4035440081070b00540c081c4905062404035582e5030f08440007501c8046040041c1440303050950020080a54064049600c031161a41c8619088508550f001000c8004122502e5034069140d9000b00355225014400b0741c1002c030b1540c0342d402d902807521441e441b0030002d40ca420b00708801e2411229004107103601c0381e52004618402079600c44201d00880140390760003e100001040145402c42c59098410018107140b51503a4284428000144296201c2c0d41d52540018082e100d00328140140203c1d150216941c402c58200890705203040c0c01500548 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631258857 1250 631257607 631257623
    0x1031503020904030215090a05010b09040816050a081303060b03070e190905071715101401110d020601051011120304020102030408010509010c0801080c01080408180a2c070c 76
    0x40f8080c10302c28000001b217900e10300005a503030308000c0c0c0d00b59628100b003081030743c99510344002d580c0309282000c5c54074007441c0c0240845042092428224088001011080341d1510510145c0d000244e81c850180181c0c000500c540c2e81030500e9810540c2c1602d031a0100144a0340041d04240400a001030115420804140d151124030461182d810300600341d0002c0582188180e039400650901e00703a21040703a50b89500f09031100c03080c10080742e030f00c800300c161508400040f00001c10700c401c8a0118583c1c0705018149405411001d24a010504002d01c1555800068210b036006018600f00010103003c214924034217000d040170000d070300c0354031249240c3c031126103a4400408107043d03a200300180c401038009940200320a08005a80a00803e4510113401c0170031102d90001030000004203a03c180e0031810386421500c0c0e030700c6984960155000103c0119660402030490200e42c840040c907a009e0310407001003c00d4440450b40b100c81d50364010742005440003041081180c815440807420f1211540a510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631260107 1250 631258857 631258861
    0x60711010b030703120e150a03020a05090d061a0117060d0c080304090b030705010e0d030c1e0812090321073b0901050a0302090a020903030a1d010315030209 69
    0x14640c09401c2801c0260751502c1030704004010710602d00048603040d00241c6031200100b01e980c0a006e141c5120490000002030140b01d86529a4042c1d002054003401c9842c00780c1c0340103060301c00104a403004440a0700d05d259150070400c680b04041c04084c0401000b401c6c604060108084080702c1c40c1001007034140280840c0c1c40705000c2180c2510380d00e024181c050f003a03944071b0341c40c3c1000d00f00800541c1d00c69403284c45071604c0001d1550052071084041c26006d000100607503000d84007541c40710410744e001c03036100c100c4103045e14031001003000c200d110910500c00c850f42d403040205515883c40010308a00c0d20740c1c00070003c0c0740e20968450b0700348030301940e45603418046d6560b000d004e80b6a00f2003546044508502121030711210301c050168240541010001c07420111071480901046100c01d0150701d404c034400090a00240ca0130750081603100030841005440c00703c47c0800310741035402682c00031001c100e52401c1e13a090104407040031443c190080c60100308120702d0004811000c1800d20000c0c0c0980c6c0c641e40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631261357 1250 631260107 631260137
    0xb090f0d05010504030c0506010f050622050406081b0a0e010512030708120108060a061503091403160b010909030210020d0b040606050c0d050c0c0f01050c010c03020301030605090307050607 83
    0xd801020160054002c0165181500740a010503807854412203003401468008134800e0300c81c040000943c0c02c06002581030002ca900a00c2c1d008904011150380400e00c01d5001a29130748031f0003008003804e411000f500c09040c12810082c05103607440300a078420700001038144040b0060403421070445004441c0b1078890f000f40004e043c07c5100f06600038000c4100010340d881045030344d1041e10304852252046481a40e59a0845001ca072100c1c040c01044040c16402003d94074403d4105000040c000d102c51305040341c082c00d07001d1943d032140c140202128044001c1d038040c88021082180102043c04083c00390307501d80d68000352282c03030714140008413990201e003041e4042c1c400d034803015074903001074010041c0c41e40304d0f03002a103e900a800000494822810400300442c480d009840d1842c903c0d074010046c01c0ca030300c4d08024180421a10050420500b031002d141c00d0b0380b0900800030705100640f00141e807941941050001e444004002600d280d0080241c240003940010341581c0c0310340e40c1d02d0b1440c64074080700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631262607 1250 631261357 631261369
    0x71e05030c15160609110109080a030f110c04050901050105040e03041514040b120f0610080c0d20040303090e01050904060e070513020c0c01030e10200c0f160b090f 72
    0x3c4064903680c6050f040e0750030400d45007080c00c21860700340c903601c05541da00c022150b511104404010001049200d503000503138000e0927003103c2c200340f690541e03015070701c0b6001180444008540000140e0b4558004112a0510384501080d000d032280140d45007508101b42c0d40c2e804115140d9940405c00ba06482e5008520211709a6000d0310500054035501c0c41200d40750b81c291001618141c064220306e401040c4e041c6046400ca2050a00c1621055030030b584109141c003458010a4412940039243c40b00c4007002c002c4c0c040d6040740d5008100900c0d4a6a0035400c000317080015607042404040329a00051205503544072055034442c0d800b440c00304004607032601c03207801d01604c0d0740704075000a840c0e1200008104581c000d8051800e41004562418000100460650f00c1910240049401201c103101c40035986403ca260460002d03846001d0008144c1065401a44980000d0303049401900b101e036040307032061015090365000c2d090200d000303030f040400d8030385284a0481c040b8410507000c1e0b00d80005031291 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631263857 1250 631262607 631262647
    0xc1401080f060a03140a06050f1317070210090602070b0307051b070b04180f050c0307140702091e1f090222030f02090f0103050a0221071e05030c15 65
    0x6203608841041c0e605c0056548400311011158203051200007103c25203058a440d115052040c00040e076807803551507520510220b0345001c1c050a00400c158800340c0c0380d14000f0040301c1510341e25506e181e0718100000b818600185c05c4043d90b858104280611703158040280c03800c0c422a40b00c00f44e41186145c525614140541c0d0090701c1b401408a0001028034507000201020340300808180608000c0c036514a0807070300121149108090184081a00d05201c1c100c010900c0d04c00c802001e240a91980014101a00c122024040483c411040c0c16541550485807904100441401e0038208220b481000159405000740c00d44541d01180005181070918495051044140ac0c0d8458054403030429611900315843e043c3d000b440c0010100e0041c0c01880c1c6583e041300e030004050702d1568596400c020000f85119192000a5000102c102180000341700e580c00400050341094182440c4e1607138900880c841e80e001612070b4011114071070081d214060032155045c5444003032a960052964020760109103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631265107 1250 631263857 631263863
    0x120a080f07050c01060306020d0f020415050901170f150d031e09030b0c0d060b030912130b1c050603010c0c02060a050f03010807030611040621020d020c06040c1401080f060a03 77
    0xc085c2e002043c484258020041140a13100c240701f1160302da0102c81c02ea104a10526103c0000285501c0401e03105801038441001305162003580080c09a40004290400340c807a045050440d4003403014030003001219084900c416203900400100c00c0d2000340800c6c00101e15003140c00441400e4481240c40341030b900c0061a480145100c1504081ca030381c170500d810030b0740e54180e002e140c41c20229a041a1030f0503039100b4110300008004400514600014580040c1a03a44052745a4840850f14022a80c080c0845400040d5420107512603404900c1c1900d00184c8002d00992414a944440d59030143d0040144c9405546296a901e1224001c0300c145c8036121090401c14404070020812040200b0f502048030700600050003002561019034003940314511500d004a44542d0002c040c0040350b525103050b41c0c0f03d1000043c1800101c00c02c010032303a40000a00a4036402110801042207000020880600340964100515008120000e045080c010b000d0040c50110100002c03103540d55011260702441d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631266357 1250 631265107 631265111
    0xb040b0a240305060603010912120908070501050601140c03070206070c0806090a1a1512120301140312090132070c030b07030b0f01050c0709020f030405120a080f07050c01 75
    0xc03001d140c80303000700c02808100c9040c0a0f020100b07200e854140140a45241c102c000c11034014079a0b0b400b82e400214640e0078503441134448504a001c1b641d5000641702007801903002040914088000400d0341d2124001240406410b1200002c240320010507a85000c1e81954825626003c5091162880340a50b02c0500b0038800c0104000c07098401042586030b0500c100314516580e000c10ba11503e070510126070754401451544070b843ea8911700a41b00311450034404040d05c00341e10100b2580805503009070007840030700d00e044e0a801650300b8100854040180b9001005003010000702c0020405403124821465128108804810841c8c0c070b00e48942a100300c500360113a40d07141c2481c0140240550f44401d80c4d130707882d40c1000281103d00038042c02c5070044004210142c00100c64005583c15004155408107134805d41e10040340b107909510040403102d940d042e0658a914042c50281d141542002c0b145002c4039043c02241c0005400080ca140c001411040c00d004642d00e42038100d8180c054084140350941c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631267607 1250 631266357 631266401
    0x2011a0d03050d2a0507020d030c0624080c090c0912030c0a050c0916080703053c0c0f0403020904030302190e0108010f0302030a20100e040510030b040b0a 68
    0x210034641844600e400c020190784c003400c2c08100c00e941d24051842c02a4019000c074410f6000240301d141e140350310380d200d940c0004d41c0c1e812601226078113150441012000341141d103018030100808003e0707054005d0085074040c4240c6440e02d81c01429001d010310040c000e20a00000501c20780c41070040e00c040070300301c0044030100016820f00e16501d0381c244a0040c00341d007907000803945954840210308814080c030b480300059510350038402c60040c90000c0071130085a115810840380742c04d4200a6501526141c0701c04001c0028844030900300b50406002c070210307190300b04004041003c1e402c060341c003101d8040752104010b40d114102500644608070410070342c0740d807001007265a03a0f00300544c0e101030503080c2c2e18115903030b0300e441041015061901000e9895408107030081c00181c15444020202c442980c00c0940e20f002110205020501c0e010403036010841200c041120b80c1000e01c95194403e051403140c3d00c0c042d00d562075030001e6603000342c4007900219000000588504207a0020800380f80800c0c1648190 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631268857 1250 631267607 631267631
    0x2150a0b130213090504030206041b050a030305120c04050904080c10050703020c0601060206091f060308070c23010905091b0f070b010b0a05160c080a080d05060102011a0d03050d 78
    0x3940100801c03034000701c0c12000404c0030a03451043c0c901c10380e4943c0007043c49498175151002c40ea640030003031150068180c03001007900c1d190000c201000f14803a481d00364488102118a01241e14001e00080290381c09200800140e41c03584280d54100d5000312103035a8400c10b58906c0b5041051003035440030541c0c140300500c040991701d607004080600004080d02c641e40d8841c0f00480c0c0310101030310140c80c0e560200c075000b545140007403100020b0701b04048002070310300d503640d072030300020380005600740c81400c8007090812002203115a404c48801000388240055a100000030b000c10410b07008490090700c0c0000041d2801c1c107901d42e00035600008604803925003140003030700708003980811001c80b00e5185000001403124412003c0d0740ca140c40c2a100d0600b0031130340380d0192501c1000fa03002981c06442950002402c0c1303806002c2200298050300d000c1d40d41d0303100030508030103885000d00701504581c945154462141c50a13010202841c20880d4003c006840c0b901f81101c082c003d0100041c1200d16100d004448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631270107 1250 631268857 631268861
    0x10e15121003060b01080601020607030b0d0b0a050403090e070f080a0209040e01060f1a040b03070207030f061a0d0b01140409061406150715020d020d09050c0f0a0602150a0b13 77
    0x2c60b88036100910500c40514011a840c0c10301740c45050250b4010350105d640e140c0285c101d03659588000d031065000070039a0b260101c0004040d42c4402031250f90303000744003d050380050b00c00f000d001c49410303030b0f10381d424480001071800541403503c604000c4c1040200c3e00c0c85840c0d404641c1d4000c07000b081804100102d03003a41b4001d140c14442d0320520000b01d44000340b204a8102d03181c250b440740280e081d0900e07140030150354071640b006181d14114050b40c900800013079040c905522802d070049600080c022805540058807110b000c4840e4403407803c01a0540018110340e82a134155241c01e0038603100343c3c1402e03002c00c2c058a02c0354002003006080602c550034001e50410b01e10301c909011544070031000410030702d8030340c03911a21030058010701c0c95480d070002070700c42c540050618a0480e14010b1401415802090444903000d204542c80c0d0000d0a10200503e005500241c196400302c0e00c1c01a03c5207843c4c00a27689640802280143ca48078400098802c0c80d254051515220003401d04e441c0328021480c0140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631271357 1250 631270107 631270109
    0x19021c2004050907060801120201051e031902040806060103092102010203040507090b03100b01020307081602030106170a06150e040311060108030a050a081003020307060e030c0f010e151210 83
    0x401603140c02c0014202c60400681001104c0d2943c5400c181c0ba42007034070314841c1c0d07000104103a051020800c1400302510a109980d0200201103240e84e889003010710541803220440c8007803040850041c0000d04c110900849c5040e0410401d00300002d0b100410310380b1f00e2440490340e2040c00d0345200100d490f030b0a00d80640045205500c60800c0d1030303100d502c0d910500f046aa4400841d50550b00180b1104240f0007141e00460541c2c0c0b0500489003032078020350b6001c60365401441c0d01144221514900421801c00b400b400e00034080d181c071060340c0070b000c101c4107607580e51f01d110000e800581c46500c00c29008c0c2218184001510001d00c0c002c203503192034180605002075021f2290442d1150070000116110080240c44d00484d1030b0396054900b81d604101141d030344001070024071800610000010050b83c1c1040300c0f030700070106502c60528040740501018149020244602d01403101c800021303006aa01140c01440200101e802303c0000ca2040e00c004802d0086101040d02c22000d2001e03c40c0d10840c90400314 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631272607 1250 631271357 631271359
    0x5090114010503010e03040302060a050f0304080720060d02160f0303200a14090f040e01240f0e040312050103050a0c15080c160c0b07031119021c20 65
    0x201107640d81c2c00034103080314039030140356415400c1480280010300d0000c1c020260019149405c508196040141c108541d2040d00e02b00c0740c40100080c15406c114203100342116042c00300345d51504014620011900c14425030180d02d819a5002070046107503252860304030003450700006030700c054150900e4040c4c01051507d114a900c0058483c450242d983d400c03040717500d03000c226a01e865032a048038a07004115000406c0c0d1590003a514603c00302580c80300d102d40c1c2da810307683c1e50001c685405158029881040c0c00c11b0002c0c80d20850340010300800180f0305080d0112009a01640c0843c0d41c2c0303060440d00c0c8030b400130040182a0500000000740708001070b48120850084c207c1710f00c019584c084c12192462071300000380c0840e150354001760b8443c420001070b02202884503503452102041c0e540b60b080034515034021103041c0502150300024540c0c05403500b4503103202880140700302c01d485003a1a8100000260007440351603d403d03044100a0070030000f6290316841101c0d11008001505003d904101c200556 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631273857 1250 631272607 631272641
    0x1820030103170403030c06020a11031c0c18141c0f0203060c090f0d050f070e01090e01060b031303051b0615010201020a1434050f0304030317060a09050901 68
    0x4480a8520b0104440031a58592030b28280c080042d0342d280041d401443d2540c061115110b0001070707042c2c0034402400d403584051307005d000040c5042d0000b070482e0780c450000c404100d001d112107840010305005030429603114417046400000544005007960002007205144000991f826008020300c42e901c0f0781c4501d1088041d2401303a501c5004400c00c500030031031451390007801004421454200f010396a80c00c1d0780108180e6240d07084240f600e40c0350200c203501001e941041c0300d00401c0444201d200d204601000003000340801e46c074060100c0843d01014080485180f01a81c051080500410440f40c031000c80c82022500c2d00400000141c441400f150165030a1f0300400c01c3c40c40561062080b40e25200306c2c0e80300d4000c16000e108105d4059080b000b030380a14003c42400000d9100710f40340740001c60b260040d079682c01900c0140342403070810507904e400e0f50460b40180001c4c00001c0d001045140c00c08641e0ba0f9800d0b0580c6c030f41c1c0018440300307180e0307124a900618003814070500b2181900618416441007080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631275107 1250 631273857 631273883
    0x60309050f030f21060108040f05070b13060e06030609012102030706030618110a0e0303090909060103050f150f0c1c020414091e0c04031406040b09010506010206011820030103 77
    0x15040c4e9030038112011030014840d0340008000031140f003003944046005070112020340e51203100400c2c00380c0c00301c003403244e411040440402c00c003070348070440746a946401e660f500c2c11401c19901103000d0303c0b410f01411401e2040c00291021480000e44030100c001c0d0000d00315079180d035480d0720107001460140145d01042d1a0b414110904203118054240130f0004614250303d0031003400e104448180880030410f500d03000c20400000540e40302c15240b4060341540000d4103d0b545145041894040365002c05441500151414200040d141d0b1751140d1240c110582c010860343e5000701d40180e03101d480b02142c4c850180c40300504400c1aa41d01801c1511040c3d5120130844200604008810004451000f070719603010b103410443c094040c0c481c9400000c0818a607081545958440390b07000562401c0c080382e80e101c2010401401107010507140c02c090408000c2000b0700300000000d45a043c140929a01c1c0c0c0c0003c00b41c034101800350350001082c0f809007007030a500c00c0b1010780425029402807100f038410180c1030320 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631276357 1250 631275107 631275157
    0xc0308090c0a06030209040207080301080309120a030804020405060d0807050714010c050c040902040b0d0303050a14070f1107081002090a140a090b0414040501020a0f08010f060309050f030f 83
    0x52401d4101401014440400d2901508601943c0800895030300281c00b40080030009803514051406803208202070b5441d21a030605000910381241c903d8a00f90b80040c9940c2c002c290042c6c0c0668100390160780c04100e591b1150085000740103960002400480e0000e0704c08140a004146442230302d0074807142c402c42480200045a810000c520088c0194001c0c8030500c48503d41a07000300c0c20700348040d10110307100159400140081d801c1038026808640c1ba50100310950015100e44c00d00c0c224038100003100340c10300680040a110701c19a1020034015224800643c900003005400b00138801e031021160400780e004800d10203900211081802886441c0003c00c0d10a02e11507248003100001e80002000c034540b2140c88040d251001e0195082503a5500341c40380e02c4040c1c0a041d10441c06080007594811110b08000c2254207554600c500300a05c1000600601c00203c03900003c40300386180104043c500c2d07051450034440c01c06000c90052100182400038002841c000c1d214030b0682020b051442038100c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631277607 1250 631276357 631276363
    0x902090a2009061c09080a1d04090f121815020601080706080f0c0c01020f0901110114010b0a02070906030b0f090706140a0c05150109230601030e1203070c030809 71
    0x1106040d403001e030601c01140390f1841412510b0b500c020441011801aa268492401c20392185407d140065401004011000c00c54611010070f080151010019180140caa0085152040100411600010115036482403140076400381000040011221059071144003820011001a289015018200000945160101d010b01c102d81e840d40703c0c40b1680d81c90361414240d4060091400079040c0052281c4256288240b000e455807030b5950031300541c0d9822000025104d20101c00030001d40340c0c10070090126002e80c42544a0444509404007600c40104440903410039041d50026400c103480e00c01c002041c09a00c1103124010410005044a43d07102c451441b908c0d446e00307010b100007251600003a030102051120050919102c20f1a01e80300e10b207060b07940e841c1030020031400e8426000c0400c006220185062060903400b4011680c0d507114003800c070005104040c4000c013070b94103150351018480094031050214445072214480c0017962031400040140a90700301240030f600051300d9000042d4a10400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631278857 1250 631277607 631277617
    0x51507020a0f0614090307120c350a2d02090a0605040b03030703020706050706060902030a0f06090207051005130209130510050405060f04170d060329010e0603010902090a20 76
    0x2030060006c140c10100d03488230380c240c200402c0300d61b00b400e03040002301042150254100c01c1d1408082d00c0000c1d11001c2405900c100c0310151700038682290204500041c10152003030084a5400c1000b842120020f500c80340800f881070740a504551030784100003c0702d10f85d5128005903081103404102408101c4107165a90090642c010096404000107000c50341c0031f00054404a4803a02000c107803581c40b0346501060b600160341800200d81c840c05001c81c0da0940b0300900d4003a01541804501b48100350b200d0310b50320342001940466044d941c1c00402c8a504281403500406500906a0141c82c1403608030307416503410340e44007560b4502400c1c0106408480034001d2070302940d00034005280c9502d811003c0b49100d10058000c035030407075514030103031800c0c00080d0152461240e0140005100761950400980345003564018190040c40c180e9010581c43ea04940030f4155140640107400720340e94000464010210000d02a51144807542003060740061900109400c00c2c0b180340b07403201e1400c0012010820b00038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631280107 1250 631278857 631278859
    0x3050f040314090a0e0f162f0706081801060f2309070c210516170f09040e070b180d0c0608160206040309051507020a0f061409 56
    0x80880828007080c840c1a2500414080c02886443c000d90341c4009200b803807155102000040e090802c0008842d0380781013171940540250f100340e10081a10b100245695a900d10f4100c408030740c5500740c0140c0c1b90444111208500f0941280c161644500024182c2c1200319035030309081034041008080b2072018010341e01191160b0503480012030404104408001128510140d0810fa503080c2d94140e0b0348012565010321055100c201c013140305400c1c08108521f100000d041c5038294040f010b42c26036844030455172008040304102520048900d0054240b201c90b001242110202142c40d14510600d00000d10f465001140e0401c01c03051607854a40d02c42c0031900c201244c80c0e0040c0100e260651a92040c0c202c10040240148640c00e0070b80e80d0f13604800101c0d0032520010f00d001007001a0602050744411062002d03000600745851f16a070010b0003c1054001c5034025540702911091000404064030071141d402404103405a8455012a07415551441003500013100400c80b040442c4421044500003d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 631281357 1250 631280107 631280131
    0x60f060e0109060f060e0d120e0f01050c0c0f13140a0b010f12022224020f21190e01140703050d0b011407051c320c0f0c09070305 57
    0x850038105803102c0204600940d0450707581c2d03020340c7c0022554450703030f208081182c80d0300c0e40b00484042800101c0000320601c50501c9410030401c500300703800050081d80164211882d80c48070301d421012035415941602c0d0070010a007404185000c000d940b0040c1c030311030035803000100702c2c050300038004440b2101c13202c0a1801140f103c00c0c0f00300d5a000350390024054890000c1050210824080249100300d68a901034400c562845207213103454807039410a140c003180d91b1b01c000c00d031202d80c41c5403080e165101b00c8100c0000156006a1640e03290045050b9408002040c09800d4910811200071340003100c120140da000900c100703001c0702e0804105099542c01c982580d41c046c1041040110200204070103c0b145041c00300b03c152681200c000c0e400145081845000a4401000103160025005070156450001e000030050003180325045411a0944800c0004072807641809005601e100e502c030306018440d030350050808405802e50000b90301480580240c0340320040d5034518900b201140d60544842d02a80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 631282607 1250 631281357 631281359
    0x70c0b240907231806070507060f03140f04020a06081b0c0c06070c090e0c090a0f0b030f0f0c0a1d091002031006030f0e1c020703060f060e0109060f 65
    0x106140c486994442c072075040141c400e640d11550100b14044944820100040c0003540304204004088403100052050f9282c60034000b0079510380762100d58078010441000214402d8018607031183d0866401001d4207402080355040c64908070003072210442d41a03000788414031000401510400c240351180380340c05c810409011403c00006510703804204d50b800c80748034107030803960b555880740e0041031410312444140030654a820560420303907008546002c00c42c0c110280c041410345600c08025803114516400246507441c5121040c020003030310300959054444d001101807202d8000501050381000541190348510f510030400c003070b0030300600500c080c60101c043d070a01c1d4002d2030041d25811808000c03e40300605d580c0c0f4481c00c1282c00880d5045000d09400c3d00c2004000d4251180c41c5034042c00000070710880e9010200207982c0c10030303c000c001809010320101c851380b074400c1c0303c0507001c0c5912040038040140c3e40c16442019010703034041d034054800b034540000b032841e00511a00c000c42c0d0b55030481c0c461503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 631283857 1250 631282607 631282609
    0x150a0306050906071d19090e031b0105010f17031303060218030109020d140304080307030302120a0b0d02120a0602030408030a060608040b041b120c230a03020d0f0b070c0b24 76
    0x200083c646d60704840542020210700140345001c1c04003aa8400030081da1110342c164150b015180804000c0c0c0f8541c1d24020040c00358140c100981003d440030b003001800019052400d6501c1d40c071844030010513400b562080441001110f80007450303410701d00348207080110590703802c060032076034494802035200344000201d600090091904200300e0100c0801c1c5da00306507607030020300d05503071003900110000b80d800282c0101e6440204482a00a441c2c1801044101011000304481000051019108082c205000e6540803000c101c7c01811503840b14055460741003030b1801c8141500182c1300d0148103400c041012540700d1050764007921894000003c507003907031181d413590030fa4545003403c1495403138005503010681030b10609818000078451110801c17007603d0a41c10345c550510007210700100745081e41c1d4035442c82e03554600314002d4980440b510280c1e40201d2400c4a6900014a80108060f403a00e080180850300b001d01161414000c04034001d02c2c0d940c59010346007607800d182c0003298111041e80d403d046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 631285107 1250 631283857 631283869
    0x609161e0e0a020c0706050408160806070c02060c10060f05010509030607082a07110a08030f090301061d070e0105090d03030b180a060503100212040308150a0306050906071d 76
    0x11200c06040107203800444c01105090030000d402210101d00000b80411407080c08001200c50402703800481c1d81100e0802c05185e8032120b000d03044804116041e0503072000e6595440c12280103c505c0f4040301c0d6150906018800984098841c4041003600396100040a5001d039048070b00c85000240030304181c1d500c01c5000d84109070040d013180c0c0711041d000042000d04258009251910420010b002d464441a16080241800c84000c1a000d1081e52104001071600041515804942241c80584409543c0b02190041802e5402652044100c5d244030724204880c0103540c1c0101895a03075580e0041403c4019100791040c100625008904107078008086446540700340724030000248841c842d0041280ea07070030f1500ac1502c4080010b03a907240100b00c1840e0810404000310f02400d415030804400c0007031009201001040a024480c1607000221011388001e40032414050040000d25141c1d00c0b420054003e081c202c0d51070005108540204040e2405109035402c1802c000075040c3e010f01c0e2040c1401b803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 631286357 1250 631285107 631285111
    0x80a03091701110f1c09051f020d020a090510020a1509150e101802060f0a1101060b190e090a1a030136030504050d0807050609161e0e 59
    0x5140e550725507003103501e142400000c04c210384940c0b202c80e884603020380244d480219012030202c000d0f443d0a010000040010420001613542c0d81d19a19040c0b241c440700102030b02c03685010f0104644005030040005802a0082054800c1903d451116074008032050380e9407105803402401001c050402c6030340e0528660800316540c0c1c45009007046840341a000142500c03001c09a00c006600710b00c0c0d8039004044988100304201d16860400c84020907623402003180d40c819119004100e410006040f081e46005540c2c0c01c0d45484134030001c02510742c0d14801005590001d040e091200310303004030040d00c1c55101c0c100c4280d243c0b10090003106540c54114110000f003126200e40051704036070000362502554203100e46042d52040c0d0240114280502c451f00b411481d00714a000301d41c5001032003401c0480d0744442034a0039654255402c030366072652420082c01c0c9024030007004145204200800031107500101e1403041801e4201060081103403125410381d05107040c0140301042005c2ea4608020442c0007107400d42d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 631287607 1250 631286357 631286399
    0x120f04050d030c060c1707020304030f0b090a1704030605072a110409050703121b2909010e2a0405130206041d0604180201080709170c0109080a0309 65
    0x2400c8103a88000654844d840010080b036031606c0d1040400a0060005a00c401c8605c095464581036a0f0380c3d43d01d80e40c91030009081165000001400a18204040403545821110650088101c000360701072542c42400300f19111424400428003a42c000c1e0001000b1101001e140c0242a800400050322080304030b00a88482c4481c260181080d1214456462250300413005003041a05500300400c045220151000812030010700c44996042c48450810b50190300230f0ac0148501101000c41c0483d0311040c1404810580c85020b10450300720545c001c41d14801e406055801c0181d8581c5104015841910240019801208150028a0650b01403a80308042c02402c8604111540210307a498109030441c081d0bd120b5000501c02c1e078000580d1655129204560602c405032030030605080c3c0b0f88852200a06000d0300001081c0c00324003956803c806000072051031544000380c46c5c0c0495550110b03813062808141a1040410324803401304107002c0658041d100c180801d032510344601840c0e08514000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 631288857 1250 631287607 631287617
    0xe0316051909180209090613080c030403080d0903030e060105062a15040203060a1b120b03060a1b0908120f0d06030602090f060a020607030b010c0b09030c120f04050d03 74
    0x86000c8245103c0d1855400702ca290354041082e41e4814000d541d0030107040c0003001c0e4800400c2001400034070707040d070015652050780b4641f90082015818603500458000400c107020102d03446903412101d5201d0502d0301e000e50390500400702040301d00e54550300c0a011302030700000b041026580300712b41202c2906001c11984040c10000800081c41e90030a0b42c01043d84080d2200d140a010561a04000003608060281002c00c1103403001800c07135000540d204442e030140009008452000d00c000c1d480300c1849031004d41504c91500d00700c3e0751a4000c04189600a0b070601c41d0141002c1c0d4540f01d05002019100848014800314242c10300700d030040d40101d401c1c080002d2080188445032001400340c1e1004510404000d0b8813051240d0400840d030301d1031123034907004000c00c4c800504500d03400121681c200c0b01c5e50800254030360400d80125024440020041c14912020051000d520710000082040c0001e00080e10080748081030031406600c10108a01a02901440240300c50701e007003442102401d21a081c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 631290107 1250 631288857 631288859
    0x1905090a080708010507020d140a0806010c06020c0a060c020f060402151c0501060e040b10030c1407050c09060f011403060d1e150e070b0913020f0a0e03160519 70
    0x39907440c102e00754100c2601651201c040c000c02d690100042480d240444c10a54141080070070b0740642400394082042c10002000046113484c5d01520280c3c0c01540c01400941d5039071109440c490f41d58113180300403500c079858090400e03d4144007280b4825080c5405e405024607407101c0d000c0001440c0c00d800d00e046580390130800d002400c413580c00c019600007035100000c248c0e9072515501514003000d0b2212940a1400c203c48018241c0d5032901c8600200190b060001e500e2510000841d1640b80c1d0018004141703000103540d000f405030015100e40c15070001c64030507406541d00d5081c00307001c07034081602034041a10b2411242021f02d4420281d070f0f0221001e841003142410948844440007004c0c10900300e9141510f04900502c4038100004000b840300c00424014986401e035650396641c020b1040075203240020070342203110340d40c0440b040011001c0410554681504185d80e00380d95000c441207a02080248085100034240400d49000b503014000720780f035450303203041d05020003203250800c03041f000820380310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 631291357 1250 631290107 631290119
    0x418020309101e0605030a02010503070f020c03030c0109111801061407051509161521062d03150e011506020c180f06101202030c030a060b1905090a 65
    0xc43c61005039802d0b035014003c0d034048078411086400ea50000c40c0240c01c482d4100000d40d80080c101c90f0411000d140c150b801c225410000c906003142c80080513418000005d1006002c1c0c01500500b901e0f40c0140c140f03107461429a004c120000e01004105584103200b800100000c41c090240852070b500191041442d25031595146424203142c0c540038404800e014007807044d2080100862910202c052106980e20360400703255100d2200d68903500c0c01000744c21000c100c80c105a42c00641210600244203000c1640c0302c406c859542000c11401c0c2850191802c134550300700c198070003180300301d980002040481c009500b02120243c2010403030f4080320f640b01c070ba95018a0140c40944001800241d01910381d5465080c02c216000e200f094400c2801119507051054001c20340c18142c0c0c000d44101da000704c001410940c1502c012840c0300300700340c8807071010081050f01405200150b2081c214410104611601c0c1c5030301046902a0041e541807203000300307420340d0440b401003004080752000140340810701c940e110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 631292607 1250 631291357 631291361
    0x1404050105100309020a0e0f0403080a020702130e0309042c0a0803010b0f0906030403020c03061006020712060e10050402040c0f020c01201e01050105010906140f09060301080a17041802030910 84
    0x551442d045223019010401819489012103420046000c81946400325940014180e0441350b03440000469890408400b04501042240c000f0340011740705101071502c1d51f501c11801d0102c5000114880c814510200301e4140100e2910716055001c17074820b08590a01c08031440c1d50300400e80f1070340b00a4080041d0b081d0b070780c1c640000e9842944694010202404c251040c5410840081c01c0303059010480401845001c0c3c010544600340c0d002410b42000c400b60034204000a0056030503d2001c500a4200698441a05400241c0304a00030b4400340b08404280008940144031441c2000040e000428100c402e1f40c45250301c0302d101640d5040c044a07004044050320700300340b122080c0b0343b02c0001940008060160a000d51401403c090130804407192805a01a144103980c581c401004000068075207100b0070240d003602c001e100003030041d0740c41b03607181c15029546d03402020098501381c025264040418a12800721010b0b6120f600350f1000315000b07400300b0006900050009401d80c05030001010401180b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 631293857 1250 631292607 631292611
    0x301020708071b06050c0706050d0902191a1801110106080d0203091c110904061401060804150506130f06030602070c0509070201051e040212060f011404050105100309020a0e 76
    0x1c080041c182502c036054140005184d900c48002d00009209085810300045041e10031034030142031a5035140307580050301f0010500311100075804450b083c1c0070444401000c4c2c0140c25580b5202c0c80460b8000d201038030321300d940910144214004100304264101e54800c020480303001111400110302e55032a07540071750504a195820000590021800940c41c0c54000c030b500410803001300c0c075000d610b161a00c1e8411101c4205451a014820090106041060b25481307a428150042600300071940c48140c01040346c80165015516483c48003030b0443c28541030b10541d4001e040040038161007801c3c0a0310f1102804400100d508a00d564080000125801d40001c0115501c21640c42c20014205410040c1151000d0086c40443e8508401c10003001d00d003206401c01c003107003010700d4019603980e407002640864103500d0f80785d0540103541c1813219110b629030b0b5090507502c0702c60751114080380781010300085031800d01c01c2c10340c0030501c1c0708562841e50081e408041100d001a10421006440f41007a41c00340700c0c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 631294964 1107 631293857 631293863
    0x111031021082803020702040e150103020114070503040810141e060a1d07020d110309093102100c03120506040e0109030314070c02031b030102070807 66
    0x140240074440f814a50021000340a108200100a0342240310124051b90400e0250b040400c8080b98046820011002848546e880c6800440707100c00d003d04020ba41410800500b004502d0a00c0144003900380000107144003212103c020003110000b10b05200c14a41c0340e42030000b8082d5501d510701426100030305a0340385440d01c400207692406503600800c4038451100c0704000c1d0b0070302e40d03416500c140d006800f59031843c00f00075400e0710751400100085065802c00c010b100380c036280082d0704070380000300000080200e80b011008842040030b000d500102034025440d0b240214a4450708505c1201032910f8007012000705540d02400880c403480880300c4050315400040c025843e5a841a000c3d125010003e0000740c0050a014004081c01c4090f41c0c2400f00070707000500d2090040b0094040c45178080d0013031180703d030000500820380106415203a81035400304000004102a2000b409120740 = true := by decide +kernel

theorem cover : BRFrame.Cov 631115107 631294964 := by
  have h0 := BRFrame.cov_init 631115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 631115107 ≤ n) (h2 : n < 631294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
